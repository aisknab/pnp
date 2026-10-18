import PNP.Concrete.ResidualReduction.SourceCandidateCorners

/-! Compute the exact ordered candidate code from encoded matrices and seed
indices. The eight corner values are derived internally. Point-vector recovery,
source-prelude handoff and raw-machine compilation remain separate obligations. -/

namespace PNP.Concrete.ResidualReduction.SourceCandidateSelection
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceCandidateCorners (Saved store data)

def handoff : Block 16 := .seq (.action (.copy 0 8)) (.action (.clear 8))
theorem handoff_exec (r : Registers) (s : Saved) :
    Exec handoff (store r s) 2 (store {r with input := r.output, output := []} s) := by
  have core : Exec (.seq (.action (.copy (0 : Fin 9) 8)) (.action (.clear 8))) r.store 2
      ({r with input := r.output, output := []}).store :=
    Exec.seq (.action _ _) (.action _ _)
  exact Frame.execution core s.store

def block : Block 16 :=
  .seq SourceCandidateCorners.block (.seq handoff (Frame.block 7 SourceCandidateChoice.block))
def choice {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) : Option SourceCandidateChoice.Choice :=
  SourceCandidateChoice.choose (SourceCandidateChoice.corners A i k j l) (SourceCandidateChoice.corners C i k j l)
def fuel {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) : Nat :=
  SourceCandidateCorners.fuel i k j l + (2 +
    SourceCandidateChoice.fuel (SourceCandidateChoice.corners A i k j l) (SourceCandidateChoice.corners C i k j l))
def result {m n : Nat} (r : Registers) (A C : Matrix m n) (i k : Fin m) (j l : Fin n) : Registers :=
  {SourceCandidateCorners.result r A C i k j l with
    input := [], output := SourceCandidateChoice.outputBits (choice A C i k j l)}

theorem block_exec (r : Registers) {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) :
    Exec block (store r (data A C i k j l)) (fuel A C i k j l)
      (store (result r A C i k j l) (data A C i k j l)) := by
  have first := SourceCandidateCorners.block_exec r A C i k j l
  have transfer := handoff_exec (SourceCandidateCorners.result r A C i k j l) (data A C i k j l)
  have decide := SourceCandidateChoice.block_exec
    {SourceCandidateCorners.result r A C i k j l with input := [], output := []}
    (SourceCandidateChoice.corners A i k j l) (SourceCandidateChoice.corners C i k j l)
  have final : Exec (Frame.block 7 SourceCandidateChoice.block)
      (store {SourceCandidateCorners.result r A C i k j l with
        input := (SourceCandidateCorners.result r A C i k j l).output, output := []} (data A C i k j l))
      (SourceCandidateChoice.fuel (SourceCandidateChoice.corners A i k j l) (SourceCandidateChoice.corners C i k j l))
      (store (result r A C i k j l) (data A C i k j l)) := by
    simpa only [store, result, SourceCandidateCorners.result, choice, List.append_nil] using Frame.execution decide (data A C i k j l).store
  exact Exec.seq first (Exec.seq transfer final)

theorem output_exact (r : Registers) {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) :
    (store (result r A C i k j l) (data A C i k j l)).get 8 =
      SourceCandidateChoice.outputBits (choice A C i k j l) := Frame.get_core _ _ (8 : Fin 9)

theorem choice_exact {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) :
    (choice A C i k j l).map (SourceCandidateChoice.decode i k j l) =
      (BilinearSelection.scan (BilinearSelection.accepts A C) (BilinearSelection.candidates i k j l)).1 :=
  (SourceCandidateChoice.choose_exact A C i k j l).symm

theorem fuel_bound {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) :
    fuel A C i k j l ≤ (6 + SourceMatrixEntry.budget m n) * 8 + 26 := by
  have reads := SourceCandidateCorners.fuel_bound i k j l
  have decision := SourceCandidateChoice.fuel_bound (SourceCandidateChoice.corners A i k j l) (SourceCandidateChoice.corners C i k j l)
  unfold fuel
  omega

theorem entry_budget_mono (m n M N : Nat) (hm : m ≤ M) (hn : n ≤ N) :
    SourceMatrixEntry.budget m n ≤ SourceMatrixEntry.budget M N := by
  have rows := Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hn) 4) hm
  have address := Nat.add_le_add (Nat.mul_le_mul hm hn) hn
  have skip := Nat.mul_le_mul_left 3 address
  exact Nat.add_le_add_right (Nat.add_le_add rows skip) 7

def entryPolynomial : NatPolynomial :=
  .add (.add (.mul (.add (.mul (.constant 3) .variable) (.constant 4)) .variable)
    (.mul (.constant 3) (.add (.mul .variable .variable) .variable))) (.constant 7)
def costPolynomial : NatPolynomial :=
  .add (.mul (.add (.constant 6) entryPolynomial) (.constant 8)) (.constant 26)
theorem costPolynomial_eval (L : Nat) :
    costPolynomial.eval L = (6 + SourceMatrixEntry.budget L L) * 8 + 26 := rfl

theorem bounded_exec (r : Registers) {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n)
    (L : Nat) (hm : m ≤ L) (hn : n ≤ L) :
    ∃ used ≤ costPolynomial.eval L,
      Exec block (store r (data A C i k j l)) used (store (result r A C i k j l) (data A C i k j l)) := by
  refine ⟨fuel A C i k j l, ?_, block_exec r A C i k j l⟩
  exact Nat.le_trans (fuel_bound A C i k j l)
    (Nat.add_le_add_right (Nat.mul_le_mul_right 8 (Nat.add_le_add_left (entry_budget_mono m n L L hm hn) 6)) 26)

def sourceEntryPolynomial : NatPolynomial :=
  .add (.add (.mul (.add (.mul (.constant 3) .variable) (.constant 4)) (.mul (.constant 2) .variable))
    (.mul (.constant 3) (.add (.mul (.mul (.constant 2) .variable) .variable) .variable))) (.constant 7)
def sourceCostPolynomial : NatPolynomial :=
  .add (.mul (.add (.constant 6) sourceEntryPolynomial) (.constant 8)) (.constant 26)
theorem sourceCostPolynomial_eval (L : Nat) :
    sourceCostPolynomial.eval L = (6 + SourceMatrixEntry.budget (2 * L) L) * 8 + 26 := rfl

theorem source_bound {n : Nat} (F : Family n) (alpha : Affine n)
    (i k : Fin (SourceLinePullback.leftSpace F alpha).parameters)
    (j l : Fin (SourceLinePullback.rightSpace F alpha).parameters) :
    fuel (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha) i k j l ≤
      sourceCostPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [alpha], F⟩).length := by
  have bound := fuel_bound (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha) i k j l
  have entries := entry_budget_mono _ _ _ _ (SourceLinePullback.left_parameter_bound F alpha) (SourceLinePullback.right_parameter_bound F alpha)
  exact Nat.le_trans bound
    (Nat.add_le_add_right (Nat.mul_le_mul_right 8 (Nat.add_le_add_left entries 6)) 26)

def program : Program 16 := block.program 0 8
theorem program_run (r : Registers) {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) :
    BitRegister.run program (fuel A C i k j l + 1) ⟨.running 0, store r (data A C i k j l)⟩ =
      ⟨.accepted, store (result r A C i k j l) (data A C i k j l)⟩ :=
  (block_exec r A C i k j l).program_run 0 8

end PNP.Concrete.ResidualReduction.SourceCandidateSelection
