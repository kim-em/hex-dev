theory Hex_BZ_Export
  imports Berlekamp_Zassenhaus.Factorization_External_Interface
begin

export_code factor_int_poly in Haskell module_name Hex_BZ file "code"

end
