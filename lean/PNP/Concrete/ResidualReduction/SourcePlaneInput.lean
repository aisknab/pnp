import PNP.Concrete.ResidualReduction.SourcePlanePreparedQuery
import PNP.Concrete.ResidualReduction.SourceDirectionInput

/-! The raw plane-query interface reuses the original direction packet.
Only a list of exactly two normals is eligible. Malformed packets and other
normal counts are rejected; an absent query witness is not a global SAT claim. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneInput
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding

def answerFor {n : Nat} (F : Family n) : System n → BitString
  | [a, b] => (SourceAffineOutput.witnessCodec F.length n).encode (sourcePlaneQuery F a b)
  | _ => [false]
def answer (input : BitString) : BitString :=
  match codec.decode input with
  | none => [false]
  | some ⟨_, U, F⟩ => answerFor F U

theorem answer_canonical (n : Nat) (F : Family n) (U : System n) :
    answer (codec.encode ⟨n, U, F⟩) = answerFor F U := by
  simp only [answer, roundtrip]
theorem answer_pair (n : Nat) (F : Family n) (a b : Affine n) :
    answer (codec.encode ⟨n, [a, b], F⟩) =
      (SourceAffineOutput.witnessCodec F.length n).encode (sourcePlaneQuery F a b) :=
  answer_canonical n F [a, b]
theorem answer_malformed (input : BitString) (invalid : codec.decode input = none) :
    answer input = [false] := by simp only [answer, invalid]

theorem answerFor_wrong_count {n : Nat} (F : Family n) (U : System n) (wrong : U.length ≠ 2) :
    answerFor F U = [false] := by
  cases U with
  | nil => rfl
  | cons a U =>
    cases U with
    | nil => rfl
    | cons b U =>
      cases U with
      | nil => exact (wrong rfl).elim
      | cons c U => rfl
theorem answer_wrong_count (n : Nat) (F : Family n) (U : System n) (wrong : U.length ≠ 2) :
    answer (codec.encode ⟨n, U, F⟩) = [false] := by
  rw [answer_canonical, answerFor_wrong_count F U wrong]

theorem answer_length (input : BitString) : (answer input).length ≤ 2 * input.length + 1 := by
  cases decoded : codec.decode input with
  | none =>
    rw [answer_malformed input decoded]
    simp only [List.length_cons, List.length_nil]
    omega
  | some problem =>
    rcases problem with ⟨n, U, F⟩
    have bytes := (canonical input ⟨n, U, F⟩).mp decoded
    rw [← bytes, answer_canonical]
    cases U with
    | nil => change 1 ≤ _; omega
    | cons a U =>
      cases U with
      | nil => change 1 ≤ _; omega
      | cons b U =>
        cases U with
        | nil => exact SourcePlanePreparedQuery.output_bound F a b
        | cons c U => change 1 ≤ _; omega

end PNP.Concrete.ResidualReduction.SourcePlaneInput
