import PNP.Concrete.ResidualReduction.SourceBilinearMatrixInstructions

/-! Search directly from encoded matrix coefficients and an existing weight
map. The linear family is constructed by the program, not an input premise.
All failed candidates and canonical optional-witness emission are charged.
Parsing and the source-derived solver/direction handoff remain separate. -/

namespace PNP.Concrete.ResidualReduction.SourceBilinearSearch
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceAffineOutput (core setRegisters lift9 lift9_exec)

def ready {m n : Nat} (M : Matrix m n) (s : Space m) : SourceAffineSearch.State :=
  SourceAffineSearch.ready (SourceBilinearFamily.family M) (SourceBilinearFamily.space M s).forms false 0 0 n 0 false
def withSource (r : SourceAffineSearch.State) (word : BitString) : SourceAffineSearch.State :=
  {r with core := {r.core with core := {r.core.core with source := word}}}
def start {m n : Nat} (M : Matrix m n) (s : Space m) : SourceAffineSearch.State :=
  let r := withSource (ready M s) []
  setRegisters r {(core r).core with input := coefficientMatrixBits M, target := List.replicate n true, remaining := [], excess := [], sign := List.replicate m true, output := []}
def converted {m n : Nat} (M : Matrix m n) (s : Space m) : SourceAffineSearch.State :=
  let r := withSource (ready M s) []
  setRegisters r {(core r).core with input := [], target := List.replicate n true, remaining := [], excess := [], sign := [], output := familyBits (SourceBilinearFamily.family M)}

theorem start_matrix {m n : Nat} (M : Matrix m n) (s : Space m) :
    (start M s).store.get 0 = coefficientMatrixBits M := rfl
theorem start_has_no_family {m n : Nat} (M : Matrix m n) (s : Space m) :
    (start M s).store.get 13 = [] := rfl
theorem start_map {m n : Nat} (M : Matrix m n) (s : Space m) :
    (start M s).store.get 16 = mapBits s.forms := SourceBilinearFamily.forms_bits M s.forms
theorem start_rows {m n : Nat} (M : Matrix m n) (s : Space m) :
    (start M s).store.get 4 = List.replicate m true := rfl
theorem start_columns {m n : Nat} (M : Matrix m n) (s : Space m) :
    (start M s).store.get 1 = List.replicate n true := rfl
theorem start_parameters {m n : Nat} (M : Matrix m n) (s : Space m) :
    (start M s).store.get 17 = List.replicate s.parameters true := rfl

theorem conversion_exec {m n : Nat} (M : Matrix m n) (s : Space m) :
    Exec (lift9 SourceBilinearMatrixInstructions.block) (start M s).store
      (SourceBilinearMatrixInstructions.fuel m n) (converted M s).store := by
  exact lift9_exec _ (start M s) _ _ (SourceBilinearMatrixInstructions.block_exec
    (core (withSource (ready M s) [])).core M)

def finish : Block 22 := .seq (.action (.copy 13 8)) <| .seq (.action (.clear 1)) <|
  .seq (.action (.clear 8)) (.action (.push 8 false))
theorem finish_exec {m n : Nat} (M : Matrix m n) (s : Space m) :
    Exec finish (converted M s).store 4 (ready M s).store := by
  let copied := withSource (converted M s) (familyBits (SourceBilinearFamily.family M))
  let reset := setRegisters copied {(core copied).core with target := []}
  let cleared := setRegisters reset {(core reset).core with output := []}
  have a : Exec (.action (.copy (13 : Fin 22) 8)) (converted M s).store 1 copied.store := .action _ _
  have b : Exec (.action (.clear (1 : Fin 22))) copied.store 1 reset.store := .action _ _
  have c : Exec (.action (.clear (8 : Fin 22))) reset.store 1 cleared.store := .action _ _
  have d : Exec (.action (.push (8 : Fin 22) false)) cleared.store 1 (ready M s).store := .action _ _
  exact Exec.seq a (Exec.seq b (Exec.seq c d))

def block : Block 22 := .seq (lift9 SourceBilinearMatrixInstructions.block) (.seq finish SourceAffineOutput.query)
def cost (m n k : Nat) : Nat := SourceBilinearMatrixInstructions.fuel m n + 4 +
  ((SourceAffineSearch.directionBudget n k m + 7) * (k + 1) + SourceAffineOutput.outputBudget n k m)

theorem block_exec {m n : Nat} (M : Matrix m n) (s : Space m) :
    ∃ used after, Exec block (start M s).store used after ∧
      after.get 8 = (SourceAffineOutput.witnessCodec m n).encode (affineBilinearQuery s M) ∧
      used ≤ cost m n s.parameters := by
  obtain ⟨used, after, checked, output, bound⟩ := SourceBilinearFamily.query_exec M s
  refine ⟨SourceBilinearMatrixInstructions.fuel m n + (4 + used), after,
    Exec.seq (conversion_exec M s) (Exec.seq (finish_exec M s) checked), output, ?_⟩
  unfold cost
  omega

theorem cost_mono (m n k M N K : Nat) (hm : m ≤ M) (hn : n ≤ N) (hk : k ≤ K) :
    cost m n k ≤ cost M N K := by
  have conversion := SourceBilinearMatrixInstructions.fuel_mono m n M N hm hn
  have direction := SourceAffineSearch.directionBudget_mono n k m N K M hn hk hm
  have search := Nat.mul_le_mul (Nat.add_le_add_right direction 7) (Nat.add_le_add_right hk 1)
  have output := SourceAffineOutput.outputBudget_mono n k m N K M hn hk hm
  exact Nat.add_le_add (Nat.add_le_add_right conversion 4) (Nat.add_le_add search output)

def conversionPolynomial : NatPolynomial :=
  .add (.mul (.add (.mul (.constant 16) .variable) (.constant 21)) .variable) (.constant 2)
def directionPolynomial : NatPolynomial :=
  .add (.mul (.add (.mul (.add (.add (.mul (.constant 9) .variable)
    (.mul (.constant 24) .variable)) (.constant 98)) .variable) (.constant 22)) .variable) (.constant 1)
def outputPolynomial : NatPolynomial :=
  .add (.add (.mul (.add (.mul (.constant 9) .variable) (.constant 29)) .variable)
    (.mul (.constant 8) .variable)) (.constant 13)
def costPolynomial : NatPolynomial :=
  .add (.add conversionPolynomial (.constant 4))
    (.add (.mul (.add directionPolynomial (.constant 7)) (.add .variable (.constant 1))) outputPolynomial)
theorem costPolynomial_eval (L : Nat) : costPolynomial.eval L = cost L L L := rfl

theorem bounded_exec {m n : Nat} (M : Matrix m n) (s : Space m) (L : Nat)
    (hm : m ≤ L) (hn : n ≤ L) (hk : s.parameters ≤ L) :
    ∃ used after, Exec block (start M s).store used after ∧
      after.get 8 = (SourceAffineOutput.witnessCodec m n).encode (affineBilinearQuery s M) ∧
      used ≤ costPolynomial.eval L := by
  obtain ⟨used, after, checked, bytes, bound⟩ := block_exec M s
  exact ⟨used, after, checked, bytes, Nat.le_trans bound (cost_mono m n s.parameters L L L hm hn hk)⟩

def program : Program 22 := block.program 0 8
theorem program_run {m n : Nat} (M : Matrix m n) (s : Space m) :
    ∃ used after, BitRegister.run program (used + 1) ⟨.running 0, (start M s).store⟩ = ⟨.accepted, after⟩ ∧
      after.get 8 = (SourceAffineOutput.witnessCodec m n).encode (affineBilinearQuery s M) ∧
      used ≤ cost m n s.parameters := by
  obtain ⟨used, after, checked, bytes, bound⟩ := block_exec M s
  exact ⟨used, after, checked.program_run 0 8, bytes, bound⟩

end PNP.Concrete.ResidualReduction.SourceBilinearSearch
