"""Observer selection must preserve workers and include their tail iterations."""
import unittest
from pathlib import Path
import shutil
import subprocess
import tempfile

from scripts.bench.meti_counts import KINDS, classify, instrument


class WorkerTests(unittest.TestCase):
    def test_actual_worker_and_tail_label(self):
        source = '''LEAN_EXPORT void lp_Hex_Hex_DensePoly_gcdAuxImpl___redArg(void){
_start:
{
/* } not a delimiter */
if (again) goto _start;
return;
}
}
'''
        changed, functions = instrument(source)
        marker = f'\nhex_meti_count({KINDS.index("gcd_loop_tests")});'
        self.assertIn('_start:\n{' + marker, changed)
        self.assertTrue(functions[0]['loop_tests'])
        self.assertEqual(changed.removeprefix('extern void hex_meti_count(unsigned);\n')
                         .replace(marker, ''), source)

    def test_forwarders_and_specialization_callees(self):
        source = '''LEAN_EXPORT void lp_Hex_Hex_DensePoly_gcd(void){
lp_Hex_Hex_DensePoly_gcd___redArg();
}
LEAN_EXPORT void lp_Hex_Hex_DensePoly_gcd___redArg(void){return;}
LEAN_EXPORT void lp_Hex_Hex_DensePoly_gcd___boxed(void){return;}
LEAN_EXPORT void lp_Hex_Hex_DensePoly_modImpl___at___00Hex_DensePoly_gcd_spec__1(void){return;}
LEAN_EXPORT void lp_Hex_Hex_DensePoly_gcd___at___00Main_spec__2___boxed(void){return;}
LEAN_EXPORT void lp_Hex_Hex_DensePoly_gcd___at___00Main_spec__2___lam__0(void){return;}
'''
        _, functions = instrument(source)
        self.assertEqual([f['name'] for f in functions],
                         ['lp_Hex_Hex_DensePoly_gcd___redArg'])

    def test_specialized_worker_and_fast_gcd(self):
        self.assertEqual(classify('lp_Hex_Hex_DensePoly_gcd___at___00Main_spec__2'),
                         ('poly_gcd', False))
        self.assertEqual(classify('lp_Hex_Hex_DensePoly_gcdWithImpl___redArg'),
                         ('poly_gcd_with', False))
        self.assertIsNone(classify('lp_Other_Hex_DensePoly_gcd'))

    def test_malformed_worker_and_label(self):
        with self.assertRaisesRegex(ValueError, 'unterminated'):
            instrument('LEAN_EXPORT void lp_Hex_Hex_DensePoly_gcd(void){')
        with self.assertRaisesRegex(ValueError, 'tail-recursion label'):
            instrument('LEAN_EXPORT void lp_Hex_Hex_DensePoly_gcdAuxImpl(void){return;}')

    def test_compiled_tail_iterations_are_counted(self):
        cc = shutil.which('cc')
        if cc is None:
            self.skipTest('host C compiler unavailable')
        source = '''LEAN_EXPORT int lp_Hex_Hex_DensePoly_gcdAuxImpl___redArg(int remaining){
_start:
{
if (remaining == 0) return 0;
remaining--;
goto _start;
}
}
'''
        changed, _ = instrument(source)
        kind = KINDS.index('gcd_loop_tests')
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            program = root / 'loop.c'
            program.write_text('#define LEAN_EXPORT\n' + changed + f'''
static unsigned calls;
void hex_meti_count(unsigned kind) {{ if (kind == {kind}) calls++; }}
int main(void) {{
    return lp_Hex_Hex_DensePoly_gcdAuxImpl___redArg(3) != 0 || calls != 4;
}}
''')
            binary = root / 'loop'
            subprocess.run([cc, '-O3', '-std=c11', str(program), '-o', str(binary)],
                           check=True, capture_output=True, text=True)
            subprocess.run([str(binary)], check=True)


if __name__ == '__main__':
    unittest.main()
