"""Scan the changed quotation sources using the repository admission lexer."""
from pathlib import Path
import sys

repo = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(repo / 'scripts' / 'ci'))
import check_named_admissions as admissions

paths = ['adapters/HexRCF/RealCoefficients/RootQuote.lean'] + [
    f'conformance/HexRCF/{name}.lean' for name in [
        'DependentQuote', 'DependentQuoteData', 'DependentQuoteProofs',
        'DependentScalarQuote', 'DependentScalarProofs', 'PublicSignPacketProofs']]
for path in paths:
    assert not admissions.find_admissions(admissions.code_only((repo / path).read_text())), path
print(f'{len(paths)} changed quotation source files contain no admissions')
