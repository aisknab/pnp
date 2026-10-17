import PNP.Concrete.ResidualReduction.SourcePlaneMenuBudget

/-! Source rows determine the entire ordered pair menu: candidate extraction,
sorting, strict pair selection and output copying are composed as instructions.
No candidate menu or homogeneity certificate is supplied by the caller. This is
the prepared source-family boundary; raw parsing and complete selection remain
separate obligations. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneMenuFromFamily
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourcePlaneMenuBytes
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (codec)

def enter : Block 9 := .seq (.action (.copy 0 7)) (.action (.clear 7))
theorem enter_exec {n : Nat} (us : List (Affine n)) :
    Exec enter (SourceMenuSortStep.initial [] us).store 2
      (SourcePlaneMenu.initial us []).store := Exec.seq (.action _ _) (.action _ _)

def held (t : SourceMenuSortStep.Held) : SourcePlaneMenu.Held := ⟨t.pending, t.width⟩
theorem handoff_exec {n : Nat} (F : Family n)
    (s : SourceMenuCompare.Saved) (t : SourceMenuSortStep.Held) :
    Exec (Frame.block 5 enter) (SourceMenuFromFamily.terminal F s t) 2
      (SourcePlaneMenu.full (SourcePlaneMenu.initial (sourceMenu F) []) s (held t)) :=
  Frame.execution (enter_exec (sourceMenu F)) (SourceMenuSortStep.frame s t)

def block : Block 14 := .seq SourceMenuFromFamily.block <|
  .seq (Frame.block 5 enter) SourcePlaneMenu.block
def costPolynomial : NatPolynomial :=
  .add SourceMenuBudget.costPolynomial (.add (.constant 2) SourcePlaneMenuBudget.costPolynomial)

theorem costPolynomial_eval (L : Nat) :
    costPolynomial.eval L =
      SourceMenuBudget.costPolynomial.eval L + (2 + SourcePlaneMenuBudget.costPolynomial.eval L) := rfl

theorem block_exec {n : Nat} (F : Family n)
    (s : SourceMenuCompare.Saved) (t : SourceMenuSortStep.Held) :
    ∃ used after, Exec block (SourceMenuFromFamily.initial F s t) used after ∧
      after.get 8 = pairBits (planeMenu (sourceMenu F)) ∧
      used ≤ costPolynomial.eval (codec.encode ⟨n, F⟩).length := by
  obtain ⟨menuUsed, middle, retained, menu, menuBudget⟩ := SourceMenuBudget.block_original_bound F s t
  have handoff := handoff_exec F middle retained
  obtain ⟨pairUsed, last, pending, pairs, pairBudget⟩ :=
    SourcePlaneMenuBudget.block_original_bound F middle (held retained)
  refine ⟨menuUsed + (2 + pairUsed), _, Exec.seq menu (Exec.seq handoff pairs),
    SourcePlaneMenu.result_output (sourceMenu F), ?_⟩
  rw [costPolynomial_eval]
  omega

def program : Program 14 := block.program 0 8
theorem program_run {n : Nat} (F : Family n)
    (s : SourceMenuCompare.Saved) (t : SourceMenuSortStep.Held) :
    ∃ used after,
      BitRegister.run program (used + 1) ⟨.running 0, SourceMenuFromFamily.initial F s t⟩ =
        ⟨.accepted, after⟩ ∧
      after.get 8 = pairBits (planeMenu (sourceMenu F)) ∧
      used + 1 ≤ costPolynomial.eval (codec.encode ⟨n, F⟩).length + 1 := by
  obtain ⟨used, after, checked, output, budget⟩ := block_exec F s t
  exact ⟨used, after, checked.program_run 0 8, output, by omega⟩

theorem output_original_bound {n : Nat} (F : Family n) :
    (pairBits (planeMenu (sourceMenu F))).length ≤
      SourcePlaneMenuBudget.outputPolynomial.eval (codec.encode ⟨n, F⟩).length :=
  SourcePlaneMenuBudget.output_original_bound F

end PNP.Concrete.ResidualReduction.SourcePlaneMenuFromFamily
