"""Reject counter classification of specialization suffixes and forwarders."""
import unittest
from scripts.bench.build_nested_normalization_counts import instrument


class InstrumentTests(unittest.TestCase):
    def test_workers_and_forwarders(self):
        source = '''LEAN_EXPORT void lp_Hex_Hex_DensePoly_gcd___redArg(void){
return;
}
LEAN_EXPORT void lp_Hex_Hex_DensePoly_gcd(void){
lp_Hex_Hex_DensePoly_gcd___redArg();
}
LEAN_EXPORT void lp_Hex_Hex_DensePoly_gcd___boxed(void){
lp_Hex_Hex_DensePoly_gcd();
}
LEAN_EXPORT void lp_Hex_Hex_DensePoly_xgcdLeft___at___00Main_spec__1(void){
/* { ignored brace } */
return;
}
LEAN_EXPORT void lp_Hex_Hex_DensePoly_xgcdLeftAux___at___00Hex_DensePoly_xgcdLeft_spec__2(void){
return;
}
LEAN_EXPORT void lp_Hex_Hex_DensePoly_gcd___lam__0(void){
return;
}
LEAN_EXPORT void lp_Hex_Hex_DensePoly_gcd___redArg___lam__0(void){
return;
}
LEAN_EXPORT void lp_Hex_Hex_DensePoly_gcd___at___00Main_spec__4___boxed(void){
return;
}
LEAN_EXPORT void lp_Hex_Hex_DensePoly_gcd___at___00Main_spec__4___lam__0(void){
return;
}
LEAN_EXPORT void lp_Hex_Hex_DensePoly_modImpl___at___00Hex_DensePoly_gcd_spec__3(void){
return;
}
'''
        output, names = instrument(source)
        self.assertEqual([row['kind'] for row in names], ['gcd', 'xgcdLeft'])
        self.assertEqual(output.count('hex_nested_poly_count(0);'), 1)
        self.assertEqual(output.count('hex_nested_poly_count(2);'), 1)
        restored = output.removeprefix('extern void hex_nested_poly_count(unsigned);\n')
        for number in range(4):
            restored = restored.replace(f'\nhex_nested_poly_count({number});', '')
        self.assertEqual(restored, source)

    def test_unrelated_source_is_unchanged(self):
        source = 'LEAN_EXPORT void random_worker(void){\nreturn;\n}\n'
        self.assertEqual(instrument(source), (source, []))

    def test_malformed_source_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'unterminated'):
            instrument('LEAN_EXPORT void lp_Hex_Hex_DensePoly_gcd(void){\n')


if __name__ == '__main__':
    unittest.main()
