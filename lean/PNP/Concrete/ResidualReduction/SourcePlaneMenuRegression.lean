import PNP.Concrete.ResidualReduction.SourcePlaneMenuFromFamily
import PNP.Concrete.ResidualReduction.SourcePolynomialMenuRegression
import Lean

/-! Exact ordering, strict eligibility, duplicate handling, dimensions, nonempty
accumulators, source derivation and instruction bounds. General execution
theorems are kernel-checked; the final small runtime checks are regression
assertions only and contribute no theorem authority. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneMenu.Regression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceMenuOrder
open PNP.Concrete.ResidualReduction.SourcePlaneMenuBytes

private def a : Affine 2 := (true, (false, false))
private def b : Affine 2 := (false, (true, false))
private def c : Affine 2 := (true, (true, false))
private def z : Affine 2 := (false, (false, false))
private def ac : Affine 2 := (true, (false, true))
private def bc : Affine 2 := (false, (true, true))
private def ab : Row 2 := ⟨true, a, b⟩
private def cb : Row 2 := ⟨false, c, b⟩
private def constants : Row 2 := ⟨false, ac, bc⟩
private def repeated : Row 2 := ⟨true, a, ac⟩
private def zeroLeft : Row 2 := ⟨false, z, b⟩

example : pairWord (b,a) = [false,true,false,true,false,false] := rfl
example : rowPairs a [a,b,c] = [] := rfl
example : rowPairs b [a,b,c] = [(b,a)] := rfl
example : rowPairs c [a,b,c] = [(c,a),(c,b)] := rfl
example : rowPairs c [b,c,a,b] = [(c,b),(c,a),(c,b)] := rfl
example : planeMenu [a,b,c] = [(b,a),(c,a),(c,b)] := rfl
example : planeMenu [c,a,b] = [(c,a),(c,b),(b,a)] := rfl
example : planeMenu [b,a,a] = [(b,a),(b,a)] := rfl
example : planeMenu [a,b,a] = [(b,a),(b,a)] := rfl
example : planeMenu [a,a,a] = [] := rfl
example : planeMenu [b,z] = [(b,z)] := rfl
example : planeMenu ([] : List (Affine 0)) = [] := rfl
example : planeMenu ([false,false] : List (Affine 0)) = [] := rfl

private theorem homogeneous {n : Nat} (us : List (Affine n))
    (h : (us.all fun a => decide (aConstant a = false)) = true) :
    ∀ a ∈ us, Homogeneous a := by
  intro a ha
  change aConstant a = false
  exact of_decide_eq_true ((List.all_eq_true.mp h) a ha)

private def saved : SourceMenuCompare.Saved := ⟨[true], [false,true], [false]⟩
private def retained : Held := ⟨[true,false], [false,true,true]⟩
private def Produces {n : Nat} (us : List (Affine n)) (ps : List (Affine n × Affine n)) : Prop :=
  ∃ used last pending,
    BitRegister.run program (used + 1) ⟨.running 0, full (initial us []) saved retained⟩ =
      ⟨.accepted, full (result us) last ⟨pending, matrixBits us⟩⟩ ∧
    (full (result us) last ⟨pending, matrixBits us⟩).get 8 = pairBits ps ∧
    used + 1 ≤ bound n us.length + 1
private theorem produces {n : Nat} (us : List (Affine n)) (ps : List (Affine n × Affine n))
    (h : (us.all fun a => decide (aConstant a = false)) = true) (expected : planeMenu us = ps) :
    Produces us ps := by
  obtain ⟨used,last,pending,checked,output,budget⟩ := program_run us (homogeneous us h) saved retained
  rw [expected] at output
  exact ⟨used,last,pending,checked,output,budget⟩

example : Produces ([] : List (Affine 0)) [] := produces _ _ rfl rfl
example : Produces ([] : List (Affine 3)) [] := produces _ _ rfl rfl
example : Produces ([false,false] : List (Affine 0)) [] := produces _ _ rfl rfl
example : Produces [a] [] := produces _ _ rfl rfl
example : Produces [a,a,a] [] := produces _ _ rfl rfl
example : Produces [a,b] [(b,a)] := produces _ _ rfl rfl
example : Produces [b,a] [(b,a)] := produces _ _ rfl rfl
example : Produces [a,b,c] [(b,a),(c,a),(c,b)] := produces _ _ rfl rfl
example : Produces [c,a,b] [(c,a),(c,b),(b,a)] := produces _ _ rfl rfl
example : Produces [b,a,a] [(b,a),(b,a)] := produces _ _ rfl rfl
example : Produces [a,b,a] [(b,a),(b,a)] := produces _ _ rfl rfl
example : Produces [b,z] [(b,z)] := produces _ _ rfl rfl

example :
    ∃ used last, Exec SourcePlaneMenuScan.block
      (SourceMenuCompare.full (SourceMenuInsertStep.ready c [b,c,a,b] [true,false]) saved) used
      (SourceMenuCompare.full
        (SourceMenuInsertStep.ready c []
          ((pairBits [(c,b),(c,a),(c,b)]).reverse ++ [true,false])) last) ∧
      used ≤ SourcePlaneMenuScan.bound 2 4 := by
  exact SourcePlaneMenuScan.block_exec c rfl [b,c,a,b] [true,false] saved
    (homogeneous _ rfl)

private def FamilyProduces {n : Nat} (F : Family n) (ps : List (Affine n × Affine n)) : Prop :=
  ∃ used after,
    BitRegister.run SourcePlaneMenuFromFamily.program (used + 1)
      ⟨.running 0, SourceMenuFromFamily.initial F saved ⟨[true], [false,true]⟩⟩ =
      ⟨.accepted, after⟩ ∧ after.get 8 = pairBits ps ∧
    used + 1 ≤ SourcePlaneMenuFromFamily.costPolynomial.eval
      (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length + 1
private theorem family_produces {n : Nat} (F : Family n) (ps : List (Affine n × Affine n))
    (expected : planeMenu (sourceMenu F) = ps) : FamilyProduces F ps := by
  obtain ⟨used,after,checked,output,budget⟩ :=
    SourcePlaneMenuFromFamily.program_run F saved ⟨[true], [false,true]⟩
  rw [expected] at output
  exact ⟨used,after,checked,output,budget⟩

example : FamilyProduces ([] : Family 0) [] := family_produces _ _ rfl
example : FamilyProduces ([] : Family 2) [] := family_produces _ _ rfl
example : FamilyProduces (n := 0) [⟨true,false,true⟩] [] := family_produces _ _ rfl
example : FamilyProduces [repeated,zeroLeft] [] := family_produces _ _ rfl
example : FamilyProduces [ab] [(b,a),(c,a),(c,b)] := family_produces _ _ rfl
example : FamilyProduces [cb,ab,constants,ab] [(b,a),(c,a),(c,b)] := family_produces _ _ rfl
example : FamilyProduces [constants,zeroLeft,repeated] [(b,a),(c,a),(c,b)] := family_produces _ _ rfl

example (n k L : Nat) (hn : n ≤ L) (hk : k ≤ 3 * L) :
    bound n k ≤ SourcePlaneMenuBudget.costPolynomial.eval L :=
  SourcePlaneMenuBudget.bounded_cost n k L hn hk
example {n : Nat} (F : Family n) :
    (pairBits (planeMenu (sourceMenu F))).length ≤
      SourcePlaneMenuBudget.outputPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length :=
  SourcePlaneMenuFromFamily.output_original_bound F
example (n : Nat) : bound n 0 = 6 := by rfl
example (L : Nat) : SourcePlaneMenuBudget.costPolynomial.eval L = bound L (3 * L) :=
  SourcePlaneMenuBudget.costPolynomial_eval L

-- Small, bounded executable assertions supplement the general execution proofs.
#eval (show IO Unit from do
  let cases : List (List (Affine 1) × BitString) :=
    [([], []), ([(false,false),(true,false)], [true,false,false,false]),
      ([(true,false),(false,false),(false,false)],
        [true,false,false,false,true,false,false,false])]
  for (us, expected) in cases do
    let final := BitRegister.run program (bound 1 us.length + 1)
      ⟨.running 0, full (initial us []) saved retained⟩
    if final.control != .accepted || final.store.get 8 != expected then
      throw (IO.userError "Ordered pair machine regression failed"))

run_cmd do
  for name in [
    ``SourcePlaneMenuBytes.pairWord_length,
    ``SourcePlaneMenuBytes.pairBits_append,
    ``SourcePlaneMenuBytes.pairBits_length,
    ``SourcePlaneMenuBytes.rowPairs_cons,
    ``SourcePlaneMenuBytes.rowBits_cons,
    ``SourcePlaneMenuBytes.rowPairs_length,
    ``SourcePlaneMenuBytes.rowBits_length,
    ``SourcePlaneMenuBytes.rows_cons,
    ``SourcePlaneMenuBytes.rows_menu,
    ``SourcePlaneMenuBytes.rows_length,
    ``SourcePlaneMenuBytes.rows_bytes_length,
    ``SourcePlaneMenuBytes.menu_bytes_length,
    ``SourcePlaneMenuScan.discard_exec,
    ``SourcePlaneMenuScan.emit_exec,
    ``SourcePlaneMenuScan.gate_exec,
    ``SourcePlaneMenuScan.selected_state,
    ``SourcePlaneMenuScan.step_exec,
    ``SourcePlaneMenuScan.step_cost_bound,
    ``SourcePlaneMenuScan.input_present,
    ``SourcePlaneMenuScan.block_exec,
    ``SourcePlaneMenu.load_exec,
    ``SourcePlaneMenu.enter_exec,
    ``SourcePlaneMenu.restore_exec,
    ``SourcePlaneMenu.step_exec,
    ``SourcePlaneMenu.input_present,
    ``SourcePlaneMenu.loop_exec,
    ``SourcePlaneMenu.seed_exec,
    ``SourcePlaneMenu.block_exec,
    ``SourcePlaneMenu.result_output,
    ``SourcePlaneMenu.program_run,
    ``SourcePlaneMenuBudget.costPolynomial_eval,
    ``SourcePlaneMenuBudget.outputPolynomial_eval,
    ``SourcePlaneMenuBudget.bounded_output,
    ``SourcePlaneMenuBudget.bounded_cost,
    ``SourcePlaneMenuBudget.original_input_bound,
    ``SourcePlaneMenuBudget.output_original_bound,
    ``SourcePlaneMenuBudget.block_original_bound,
    ``SourcePlaneMenuFromFamily.enter_exec,
    ``SourcePlaneMenuFromFamily.handoff_exec,
    ``SourcePlaneMenuFromFamily.costPolynomial_eval,
    ``SourcePlaneMenuFromFamily.block_exec,
    ``SourcePlaneMenuFromFamily.program_run,
    ``SourcePlaneMenuFromFamily.output_original_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourcePlaneMenuBytes.rowPairs_cons
#print axioms PNP.Concrete.ResidualReduction.SourcePlaneMenuScan.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePlaneMenu.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePlaneMenuBudget.bounded_cost
#print axioms PNP.Concrete.ResidualReduction.SourcePlaneMenuFromFamily.program_run

end PNP.Concrete.ResidualReduction.SourcePlaneMenu.Regression
