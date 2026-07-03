theory Hex_LLL_Factor_Export
  imports
    LLL_Factorization.LLL_Factorization_Impl
    Berlekamp_Zassenhaus.Factorization_External_Interface
begin

text \<open>
  List-based wrapper exporting the verified polynomial-time LLL factorizer over
  the suite line protocol, mirroring @{const factor_int_poly} from
  @{theory Berlekamp_Zassenhaus.Factorization_External_Interface} exactly and
  swapping only the reconstruction: where the BZ interface calls
  @{const factorize_int_poly} (= @{const factorize_int_poly_generic} at the
  exponential Berlekamp--Zassenhaus reconstruction), this composes the shared
  content + square-free front end with the LLL reconstruction
  @{const LLL_factorization} (von zur Gathen--Gerhard Alg 16.22), verified in the
  AFP @{session LLL_Factorization} entry.

  BUILD SPIKE (issue #8545, carica): confirm the exact combinator the BZ
  interface uses to lift a reconstruction @{typ "int poly \<Rightarrow> int poly list"}
  into the full pipeline. The expected form is
  @{term "factorize_int_poly_generic LLL_factorization"}; if the AFP release
  instead exposes the reconstruction hook as @{term "int_poly_factorization_algorithm"}
  or a differently-named generic, adjust the single application below. If neither
  composes cleanly, isabelle-lll is dropped and the suite ships the other five
  systems (see reports/hexbz-factor-sweep.md).
\<close>

definition factor_int_poly_lll ::
    "integer list \<Rightarrow> integer \<times> (integer list \<times> integer) list" where
  "factor_int_poly_lll p =
     map_prod integer_of_int
       (map (map_prod (map integer_of_int \<circ> coeffs) integer_of_nat))
       (factorize_int_poly_generic LLL_factorization
          (poly_of_list (map int_of_integer p)))"

export_code factor_int_poly_lll in Haskell module_name Hex_LLL file "code"

end
