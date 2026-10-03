"""Record post-capture disassembly of the unchanged measured executable."""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
meta = json.loads((args.output / 'metadata.json').read_text())
exe = Path(meta['samples'][0]['command'][0])
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
record = {'scope': 'post-capture disassembly of the unchanged measured executable',
          'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'script_sha256': digest(Path(__file__)), 'binary_sha256_before': digest(exe),
          'objdump_version': subprocess.check_output(['objdump', '--version'], text=True),
          'outputs': []}
assert record['binary_sha256_before'] == meta['binary_sha256']
for symbol in ('__gmpz_gcd', '__gmpn_gcd', '__gmp_tmp_reentrant_alloc'):
    command = ['objdump', '-d', '--disassemble=' + symbol, str(exe)]
    result = subprocess.run(command, capture_output=True, text=True)
    result.check_returncode()
    output = args.output / (symbol + '.asm')
    assert output.read_text() == result.stdout + result.stderr
    record['outputs'].append({'command': command, 'file': output.name, 'sha256': digest(output)})
record.update(binary_sha256_after=digest(exe),
              finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
assert record['binary_sha256_after'] == meta['binary_sha256_after']
(args.output / 'gmp-disassembly.json').write_text(json.dumps(record, indent=2) + '\n')
