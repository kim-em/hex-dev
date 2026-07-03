theory Hex_LLL_Factor_Export
  imports
    LLL_Factorization.LLL_Factorization
    Berlekamp_Zassenhaus.Factorization_External_Interface
begin

text \<open>
  List-based wrapper exporting the verified polynomial-time LLL factorizer over
  the suite line protocol, mirroring @{const factor_int_poly} from
  @{theory Berlekamp_Zassenhaus.Factorization_External_Interface} exactly and
  swapping only the reconstruction bundle.

  The Berlekamp--Zassenhaus interface is
  @{term "factorize_int_poly_generic berlekamp_zassenhaus_factorization_algorithm"};
  here we swap in @{const one_lattice_LLL_factorization} -- the AFP
  @{session LLL_Factorization} bundle of the verified direct-LLL reconstruction
  @{const LLL_factorization} (von zur Gathen--Gerhard, full-degree lattice) with
  its soundness proof. The shared content + square-free + @{term "x^n"} front end
  in @{const factorize_int_poly_generic} is reused unchanged, so the exported
  result has exactly the BZ shape @{typ "integer \<times> (integer list \<times> integer) list"}.
\<close>

definition factor_int_poly_lll ::
    "integer list \<Rightarrow> integer \<times> (integer list \<times> integer) list" where
  "factor_int_poly_lll p =
     map_prod integer_of_int
       (map (map_prod (map integer_of_int \<circ> coeffs) integer_of_nat))
       (factorize_int_poly_generic one_lattice_LLL_factorization
          (poly_of_list (map int_of_integer p)))"

export_code factor_int_poly_lll in Haskell module_name Hex_LLL file "code"

end
