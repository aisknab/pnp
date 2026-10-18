import PNP.Concrete.ResidualReduction.SourceRowCoefficientInstructions

/-! Compare every coefficient of two canonical quadratic words using the
existing literal XOR and zero scan. This is coefficient equality, not a
sample of evaluations; in particular off-diagonal terms are not discarded. -/

namespace PNP.Concrete.ResidualReduction.SourceQuadraticEquality
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra
open PNP.Concrete.ResidualReduction.SourceRowCoefficientAlgebra
open PNP.Concrete.ResidualReduction.SourceMenuBytes

theorem equal_zero {n : Nat} (p q : Quadratic n) :
    qEq p q = !nonzero (SourceQuadraticEncoding.word (qAdd p q)) := by
  induction n with
  | zero => cases p <;> cases q <;> rfl
  | succ n ih =>
    rcases p with ⟨a,p⟩
    rcases q with ⟨b,q⟩
    change (aEq a b && qEq p q) =
      !nonzero (affineWord (aAdd a b) ++ SourceQuadraticEncoding.word (qAdd p q))
    rw [nonzero_append,equal_word,← word_add,ih]
    cases nonzero (affineWord (aAdd a b)) <;>
      cases nonzero (SourceQuadraticEncoding.word (qAdd p q)) <;> rfl

theorem equal_word {n : Nat} (p q : Quadratic n) :
    qEq p q = !nonzero (List.zipWith Bool.xor
      (SourceQuadraticEncoding.word p) (SourceQuadraticEncoding.word q)) := by
  rw [← SourceQuadraticEncoding.word_add]
  exact equal_zero p q

def ready (r : Registers) {n : Nat} (p q : Quadratic n) : Registers :=
  {r with input := SourceQuadraticEncoding.word p,target := List.replicate (quadraticBits n) true,remaining := [],excess := [],mode := SourceQuadraticEncoding.word q,output := []}
def finished (r : Registers) {n : Nat} (p q : Quadratic n) : Registers :=
  {r with input := [],target := List.replicate (quadraticBits n) true,remaining := [],excess := [],mode := [],active := [qEq p q],output := []}
def block : Block 9 := SourceRowCoefficientInstructions.equal
def fuel (n : Nat) : Nat := 12 * quadraticBits n + 5

theorem block_exec (r : Registers) {n : Nat} (p q : Quadratic n) :
    Exec block (ready r p q).store (fuel n) (finished r p q).store := by
  let base := {r with input := [],target := List.replicate (quadraticBits n) true,remaining := [],excess := [],mode := [],active := [true],output := []}
  let loaded := {ready r p q with remaining := List.replicate (quadraticBits n) true,active := [true]}
  let xored := {base with excess := (SourceQuadraticEncoding.word (qAdd p q)).reverse}
  have load : Exec SourceRowCoefficientInstructions.prepareEqual (ready r p q).store 3 loaded.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have xor : Exec xorLoop loaded.store (7 * quadraticBits n + 1) xored.store := by
    simpa only [loaded,ready,xored,base,SourceQuadraticEncoding.word_length,
      SourceQuadraticEncoding.word_add,List.append_nil] using
      xor_exec base (SourceQuadraticEncoding.word p) (SourceQuadraticEncoding.word q) []
        (by rw [SourceQuadraticEncoding.word_length,SourceQuadraticEncoding.word_length])
  have scan : Exec SourceRowCoefficientInstructions.zeroLoop xored.store
      (5 * quadraticBits n + 1) (finished r p q).store := by
    have checked := SourceRowCoefficientInstructions.zeroLoop_exec base
      (SourceQuadraticEncoding.word (qAdd p q)).reverse true
    rw [List.length_reverse,SourceQuadraticEncoding.word_length] at checked
    simpa only [xored,base,finished,nonzero_reverse,← equal_zero,Bool.true_and] using checked
  have cost : fuel n = 3 + ((7 * quadraticBits n + 1) + (5 * quadraticBits n + 1)) := by
    unfold fuel
    omega
  simpa only [block,SourceRowCoefficientInstructions.equal,cost] using
    Exec.seq load (Exec.seq xor scan)

theorem fuel_encoded {n : Nat} (p : Quadratic n) :
    fuel n = 12 * (SourceQuadraticEncoding.word p).length + 5 := by
  rw [SourceQuadraticEncoding.word_length]
  rfl

end PNP.Concrete.ResidualReduction.SourceQuadraticEquality
