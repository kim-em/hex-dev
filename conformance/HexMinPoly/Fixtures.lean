import HexMinPoly

namespace Hex.MinPolyFixtures

structure Case where
  id : String
  n : Nat
  matrix : Matrix Int n n

private def matrixOfRows (n : Nat) (rows : Array (Array Int)) : Matrix Int n n :=
  Matrix.ofFn fun i j => (rows.getD i.val #[]).getD j.val 0

private def mk (id : String) (rows : Array (Array Int)) : Case :=
  { id, n := rows.size, matrix := matrixOfRows rows.size rows }

def empty : Case := mk "empty/0x0" #[]
def scalarZero : Case := mk "scalar/zero" #[#[0]]
def scalar : Case := mk "scalar/seven" #[#[7]]
def zero3 : Case := mk "zero/3x3" #[#[0, 0, 0], #[0, 0, 0], #[0, 0, 0]]
def identity3 : Case := mk "identity/3x3" #[#[1, 0, 0], #[0, 1, 0], #[0, 0, 1]]
def nilpotent2 : Case := mk "nilpotent/jordan-2" #[#[0, 1], #[0, 0]]
def nilpotent4 : Case := mk "nilpotent/jordan-4" #[
  #[0, 1, 0, 0], #[0, 0, 1, 0], #[0, 0, 0, 1], #[0, 0, 0, 0]]
def diagonal123 : Case := mk "diagonal/1-2-3" #[
  #[1, 0, 0], #[0, 2, 0], #[0, 0, 3]]
def diagonal112 : Case := mk "diagonal/1-1-2" #[
  #[1, 0, 0], #[0, 1, 0], #[0, 0, 2]]
def coprimeBlocks : Case := mk "blocks/coprime" #[
  #[0, 1, 0, 0], #[0, 0, 0, 0], #[0, 0, 2, 0], #[0, 0, 0, 3]]
def equalBlocks : Case := mk "blocks/equal" #[
  #[0, 1, 0, 0], #[0, 0, 0, 0], #[0, 0, 0, 1], #[0, 0, 0, 0]]

private def transposeBase : Matrix Int 4 4 := matrixOfRows 4 #[
  #[1, 2, -1, 0], #[3, -2, 4, 1], #[0, 5, 2, -3], #[2, 1, 0, 4]]
def transposeOriginal : Case := { id := "transpose/original", n := 4, matrix := transposeBase }
def transposeImage : Case :=
  { id := "transpose/transposed", n := 4, matrix := transposeBase.transpose }

private def similarBase : Matrix Int 3 3 := matrixOfRows 3 #[
  #[1, 2, 3], #[0, -2, 4], #[5, 1, 0]]
private def transvection (c : Int) : Matrix Int 3 3 :=
  Matrix.rowAdd (Matrix.identity (R := Int) 3) 1 0 c
private def similarImage : Matrix Int 3 3 :=
  transvection 3 * similarBase * transvection (-3)
def similarityOriginal : Case :=
  { id := "similarity/original", n := 3, matrix := similarBase }
def similarityConjugate : Case :=
  { id := "similarity/transvection", n := 3, matrix := similarImage }

def companion6 : Case := mk "companion/degree-6" #[
  #[0, 1, 0, 0, 0, 0], #[0, 0, 1, 0, 0, 0], #[0, 0, 0, 1, 0, 0],
  #[0, 0, 0, 0, 1, 0], #[0, 0, 0, 0, 0, 1], #[-2, 3, -5, 7, -11, 13]]

private def huge : Int := 9223372036854775808
def large4 : Case := mk "large/near-2pow63-4x4" #[
  #[huge, 1, -2, 3], #[-5, huge - 1, 6, -7],
  #[9, -10, -huge, 11], #[13, 14, -15, huge + 1]]

def all : List Case := [
  empty, scalarZero, scalar, zero3, identity3, nilpotent2, nilpotent4,
  diagonal123, diagonal112, coprimeBlocks, equalBlocks, companion6,
  transposeOriginal, transposeImage, similarityOriginal, similarityConjugate, large4]

end Hex.MinPolyFixtures
