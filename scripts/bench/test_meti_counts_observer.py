"""Check region accounting and argument forwarding with a minimal C stub.

The stub checks the observer's protocol, not the Lean runtime ABI. A real
instrumented producer build and capture must still validate that boundary.
"""
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class ObserverTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cc = shutil.which('cc')
        if cc is None:
            raise unittest.SkipTest('host C compiler unavailable')
        cls.temporary = tempfile.TemporaryDirectory()
        root = Path(cls.temporary.name)
        (root / 'lean').mkdir()
        (root / 'lean/lean.h').write_text('''typedef void lean_object;
static inline const char *lean_string_cstr(lean_object *s) { return (const char *)s; }
''')
        observer = Path(__file__).parent / 'ffi/meti_counts.c'
        source = root / 'probe.c'
        source.write_text('''#define HEX_METI_KINDS "first", "second"
#include ''' + json.dumps(str(observer.resolve())) + '''
#include <stdlib.h>
static unsigned writes, forwards;
static void *a = (void *)1, *b = (void *)2, *c = (void *)3;
lean_object *__real_lean_io_prim_handle_put_str(lean_object *h, lean_object *s) {
    if (h != a) abort();
    writes++;
    return s;
}
lean_object *__real_lean_nat_gcd(lean_object *x, lean_object *y) {
    if (x != a || y != b) abort();
    forwards++;
    return x;
}
void __real___gmpz_gcd(void *g, const void *x, const void *y) {
    if (g != c || x != a || y != b) abort();
    forwards++;
}
void __real___gmpz_gcdext(void *g, void *s, void *t, const void *x, const void *y) {
    if (g != c || s != a || t != b || x != a || y != b) abort();
    forwards++;
}
static void marker(char *s) {
    if (__wrap_lean_io_prim_handle_put_str(a, s) != s) abort();
}
int main(int argc, char **argv) {
    if (argc != 2) return 2;
    hex_meti_count(0); /* inactive work must not be counted */
    if (__wrap_lean_nat_gcd(a, b) != a) abort();
    if (strcmp(argv[1], "no-begin") != 0) marker("METI BEGIN\\n");
    if (strcmp(argv[1], "duplicate") == 0) marker("METI BEGIN\\n");
    hex_meti_count(0);
    hex_meti_count(0);
    hex_meti_count(1);
    if (strcmp(argv[1], "unknown") == 0) hex_meti_count(999);
    if (strcmp(argv[1], "overflow") == 0) {
        counts[0] = UINT64_MAX;
        hex_meti_count(0);
    }
    if (__wrap_lean_nat_gcd(a, b) != a) abort();
    __wrap___gmpz_gcd(c, a, b);
    __wrap___gmpz_gcdext(c, a, b, a, b);
    if (strcmp(argv[1], "no-end") != 0) marker("METI END\\n");
    hex_meti_count(0);
    if (__wrap_lean_nat_gcd(a, b) != a) abort();
    printf("{\\"writes\\":%u,\\"forwards\\":%u}\\n", writes, forwards);
    return 0;
}
''')
        cls.binary = root / 'probe'
        subprocess.run([cc, '-std=c11', '-I', str(root), str(source), '-o', str(cls.binary)],
                       check=True, capture_output=True, text=True)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def run_probe(self, mode):
        result = subprocess.run([str(self.binary), mode], check=True, capture_output=True, text=True)
        lines = [line.removeprefix('METI COUNTERS ') for line in result.stderr.splitlines()
                 if line.startswith('METI COUNTERS ')]
        return [json.loads(line) for line in lines], json.loads(result.stdout)

    def test_bounded_counts_and_forwarding(self):
        rows, forwarded = self.run_probe('normal')
        self.assertEqual(forwarded, dict(writes=2, forwards=5))
        self.assertEqual(rows, [dict(schema=1, valid=True, counts=dict(first=2, second=1),
                                     lean_nat_gcd=1, gmp_gcd=1, gmp_gcdext=1)])

    def test_invalid_regions_and_counts(self):
        for mode in ['no-begin', 'duplicate', 'unknown', 'overflow']:
            with self.subTest(mode=mode):
                rows, _ = self.run_probe(mode)
                self.assertEqual(len(rows), 1)
                self.assertFalse(rows[0]['valid'])

    def test_missing_end_produces_no_completed_record(self):
        rows, _ = self.run_probe('no-end')
        self.assertEqual(rows, [])


if __name__ == '__main__':
    unittest.main()
