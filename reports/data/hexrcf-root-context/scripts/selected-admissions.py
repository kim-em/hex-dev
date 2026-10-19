"""Scan the native context assembly sources using the repository admission lexer."""
from pathlib import Path
import sys

repo = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(repo / 'scripts' / 'ci'))
import check_named_admissions as admissions

paths = ['adapters/HexRCF/RealCoefficients/RootContext.lean',
         'adapters/HexRCF/RealCoefficients/SignatureQuote.lean'] + [
    f'conformance/HexRCF/{name}.lean' for name in [
        'RootContextConformance', 'RootContextProofs', 'FrozenSignatureConformance',
        'FrozenSignatureProofs', 'RootHeaderPacket', 'RootHeaderProofs']]
for path in paths:
    assert not admissions.find_admissions(admissions.code_only((repo / path).read_text())), path
print(f'{len(paths)} native context assembly source files contain no admissions')
