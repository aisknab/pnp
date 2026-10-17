import PNP.Concrete.ResidualReduction.SourceLinePreparedQuery
import PNP.Concrete.ResidualReduction.SourceDirectionInput

/-! Raw line-query interface over the original direction packet. Exactly one
normal is required. Malformed packets and other counts emit the absent tag;
for valid inputs, absence excludes only the stated line-witness condition. -/

namespace PNP.Concrete.ResidualReduction.SourceLineInput
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding

def answerFor {n : Nat} (F : Family n) : System n → BitString
  | [a] => (SourceLineOutput.codec n F.length).encode (sourceLineQuery F a)
  | _ => [false]
def answer (input : BitString) : BitString :=
  match codec.decode input with
  | none => [false]
  | some ⟨_, U, F⟩ => answerFor F U

theorem answer_canonical (n : Nat) (F : Family n) (U : System n) :
    answer (codec.encode ⟨n, U, F⟩) = answerFor F U := by
  simp only [answer, roundtrip]
theorem answer_single (n : Nat) (F : Family n) (a : Affine n) :
    answer (codec.encode ⟨n, [a], F⟩) = (SourceLineOutput.codec n F.length).encode (sourceLineQuery F a) :=
  answer_canonical n F [a]
theorem answer_malformed (input : BitString) (invalid : codec.decode input = none) :
    answer input = [false] := by simp only [answer, invalid]
theorem answerFor_wrong_count {n : Nat} (F : Family n) (U : System n) (wrong : U.length ≠ 1) :
    answerFor F U = [false] := by
  cases U with
  | nil => rfl
  | cons a U =>
    cases U with
    | nil => exact (wrong rfl).elim
    | cons b U => rfl
theorem answer_wrong_count (n : Nat) (F : Family n) (U : System n) (wrong : U.length ≠ 1) :
    answer (codec.encode ⟨n, U, F⟩) = [false] := by
  rw [answer_canonical, answerFor_wrong_count F U wrong]
theorem answer_length (input : BitString) : (answer input).length ≤ 3 * input.length + 1 := by
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
      | nil =>
        have bound := SourceLinePreparedQuery.output_original_bound F a
        rw [SourceLinePreparedQuery.result_output] at bound
        exact bound
      | cons b U => change 1 ≤ _; omega

end PNP.Concrete.ResidualReduction.SourceLineInput
