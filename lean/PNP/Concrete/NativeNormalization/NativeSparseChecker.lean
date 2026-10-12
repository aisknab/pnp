import PNP.Concrete.NativeNormalization.NativeSparseSystem

namespace PNP.Concrete.NativeNormalization.NativeSparseSystem

open PNP.Concrete CNFCore NativeBasis NativeSource NativeEquations
open NativeSourceEquations NativeCoefficients

/-- Check one supplied row assignment against the emitted finite data.
This is not a search for an assignment and is not a SAT solver. -/
def System.check (D : System c) (u : RowValues c) : Bool :=
  eval u D.b &&
    (D.e.all (fun terms => !(eval u terms))) &&
    (D.a.all (fun entry => !(u entry.1 && !(eval u entry.2))))

private theorem negate_true (b : Bool) : ((!b) = true) ↔ b = false := by
  cases b <;> decide

theorem System.check_iff (D : System c) (u : RowValues c) :
    D.check u = true ↔ D.Satisfied u := by
  simp only [System.check, System.Satisfied, Bool.and_eq_true, List.all_eq_true,
    negate_true, and_assoc]

theorem source_check_iff (F : CNFFormula) (three : ThreeCore F)
    (failed : Fin (positions F).length) (hf : firstFailed F three = some failed) :
    F.Satisfiable ↔ ∃ u, (assemble (selection F three) failed).check u = true := by
  rw [source_assembled_iff F three failed hf]
  simp only [System.check_iff]

theorem source_check_recovery (F : CNFFormula) (three : ThreeCore F)
    (failed : Fin (positions F).length) (hf : firstFailed F three = some failed)
    (u : RowValues (positions F).length)
    (hu : (assemble (selection F three) failed).check u = true) :
    F.Satisfied (recoverSolution F three failed u) :=
  source_assembled_recovery F three failed hf u ((System.check_iff _ u).mp hu)


end PNP.Concrete.NativeNormalization.NativeSparseSystem
