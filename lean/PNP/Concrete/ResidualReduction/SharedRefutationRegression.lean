import PNP.Concrete.ResidualReduction.SharedRefutationAlgebra
import PNP.Concrete.ResidualReduction.SharedRefutationCircuit
import PNP.Concrete.ResidualReduction.SharedRefutationTransport
import PNP.Concrete.ResidualReduction.SharedRefutationSourceLift
import PNP.Concrete.ResidualReduction.SharedRefutationContraction
import PNP.Concrete.ResidualReduction.SharedRefutationExtraction

/-! Targeted positive and malformed-reference checks for the shared lift.
The general statements are kernel theorems; these tiny computations are regressions,
not an all-input completeness or runtime argument. -/

namespace PNP.Concrete.ResidualReduction.SharedRefutationRegression
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SharedRefutationCircuit

def seed : Code 1 := [.input (aConst 1 true)]
def inputBit : Affine 1 := (true, false)
def oneRow : List (InputRow 1) := [⟨0, true, inputBit⟩]
def twoRows : List (InputRow 1) :=
  [⟨0, true, inputBit⟩, ⟨0, false, aConst 1 false⟩]

theorem one_row_values (b : Bool) :
    outputs (compile oneRow seed).1 (b, ()) (compile oneRow seed).2 = [!b] := by
  cases b <;> decide

theorem one_row_gate_count : (compile oneRow seed).1.length = 6 := by decide
theorem one_row_code_valid : codeValid (compile oneRow seed).1 = true := by decide

theorem mixed_weights_values (b : Bool) :
    outputs (compile twoRows seed).1 (b, ()) (compile twoRows seed).2 = [!b, true] := by
  cases b <;> decide

theorem mixed_weights_gate_count : (compile twoRows seed).1.length = 9 := by decide
theorem mixed_weights_code_valid : codeValid (compile twoRows seed).1 = true := by decide
theorem empty_root_count : (compile ([] : List (InputRow 0)) []).2.length = 0 := rfl
theorem empty_gate_count : (compile ([] : List (InputRow 0)) []).1.length = 1 := rfl

theorem invalid_forward_reference :
    compileChecked ([] : List (InputRow 1)) [.xorGate 0 0] = none := rfl

theorem invalid_input_root :
    compileChecked [⟨1, true, inputBit⟩] seed = none := rfl

def transportedShear : Code 2 :=
  SharedRefutationTransport.chartCode (0 : Fin 2) (true, ()) (compile oneRow seed).1

def transportedSwap : Code 2 :=
  SharedRefutationTransport.chartCode (1 : Fin 2) (false, ()) (compile oneRow seed).1

theorem transported_shear_values (a b : Bool) :
    outputs transportedShear (a, (b, ())) (compile oneRow seed).2 =
      [!(Bool.xor b a)] := by
  cases a <;> cases b <;> decide

theorem transported_swap_values (a b : Bool) :
    outputs transportedSwap (a, (b, ())) (compile oneRow seed).2 = [!a] := by
  cases a <;> cases b <;> decide

def headEquation : Row 2 :=
  ⟨true, (true, (false, false)), aConst 2 true⟩
def oppositeEquation : Row 2 :=
  ⟨false, (true, (false, true)), aConst 2 true⟩
def sourceRows : List (SharedRefutationSourceLift.HeadRow 1) :=
  [⟨headEquation, 0⟩, ⟨oppositeEquation, 1⟩]
def oldRefutation : Code 1 := [.input (aConst 1 true), .input (aConst 1 false)]
def falseOldRefutation : Code 1 := [.input (aConst 1 false), .input (aConst 1 false)]

def sourceResult :=
  SharedRefutationSourceLift.liftChecked sourceRows (qOfAffine (aConst 1 false)) oldRefutation

def sourceResultValue (s z : Bool) : Option Bool :=
  sourceResult.bind (fun r => SharedRefutationSourceLift.originalSum sourceRows r.1 r.2 s (z, ()))

theorem source_result_returned : sourceResult.isSome = true := by decide
theorem source_result_gate_count : sourceResult.map (fun r => r.1.length) = some 10 := by decide

theorem source_result_refutation (s z : Bool) : sourceResultValue s z = some true := by
  cases s <;> cases z <;> decide

theorem wrong_source_guard_rejected :
    SharedRefutationSourceLift.liftChecked sourceRows (qOfAffine (aConst 1 true)) oldRefutation = none := rfl

theorem source_root_out_of_range_rejected :
    SharedRefutationSourceLift.liftChecked
      [⟨headEquation, 2⟩, ⟨oppositeEquation, 1⟩] (qOfAffine (aConst 1 false)) oldRefutation = none := rfl

theorem missing_coefficient_rejected :
    SharedRefutationSourceLift.pairedSum [true] [false, true] = none := rfl

theorem missing_source_value_rejected :
    SharedRefutationSourceLift.pairedSum [true, false] [true] = none := rfl

/-- A valid checked guard is not by itself a refutation: zero old coefficients
remain zero. The universal old refutation invariant cannot be omitted. -/
theorem valid_guard_does_not_invent_refutation (s z : Bool) :
    (SharedRefutationSourceLift.liftChecked sourceRows (qOfAffine (aConst 1 false)) falseOldRefutation).bind
      (fun r => SharedRefutationSourceLift.originalSum sourceRows r.1 r.2 s (z, ())) =
      some false := by
  cases s <;> cases z <;> decide

def nonlinearTail : Quadratic 2 :=
  qProduct (true, (false, false)) (false, (true, false))

def nonlinearRows : List (SharedRefutationSourceLift.HeadRow 2) :=
  [⟨⟨true, (true, aConst 2 false), aConst 3 true⟩, 0⟩,
   ⟨⟨true, (false, (true, (false, false))), (false, (false, (true, false)))⟩, 1⟩,
   ⟨⟨false, (true, aConst 2 true), aConst 3 true⟩, 1⟩]

def nonlinearOld : Code 2 := [.input (aConst 2 true), .input (aConst 2 false)]

def nonlinearResult :=
  SharedRefutationSourceLift.liftChecked nonlinearRows nonlinearTail nonlinearOld

theorem nonlinear_result_returned : nonlinearResult.isSome = true := by decide

/-- The selected guard is s + a*b. The conclusion checks all original head
and remaining bits, not only points on the nonlinear substitution surface. -/
theorem nonlinear_source_refutation (s a b : Bool) :
    nonlinearResult.bind (fun r =>
      SharedRefutationSourceLift.originalSum nonlinearRows r.1 r.2 s (a, (b, ()))) =
      some true := by
  cases s <;> cases a <;> cases b <;> decide

def zeroRows : Family 0 :=
  [⟨false, false, true⟩, ⟨false, true, true⟩, ⟨false, true, true⟩]

theorem terminal_selects_only_first_violation :
    SharedRefutationTerminal.roots zeroRows = [0, 1, 0] := by decide

theorem terminal_even_violations_still_refute :
    SharedRefutationSourceLift.pairedSum
      (outputs SharedRefutationTerminal.code () (SharedRefutationTerminal.roots zeroRows))
      (zeroRows.map (fun r => r.eval ())) = some true := by decide

theorem attachment_missing_root_rejected :
    SharedRefutationAssembly.attach [headEquation] [] = none := rfl

theorem attachment_extra_root_rejected :
    SharedRefutationAssembly.attach ([] : Family 2) [0] = none := rfl

theorem empty_history_wrong_dimension_rejected :
    SharedRefutationExtraction.unwind (SharedRefutationTerminal.certificate []) 1 [] = none := rfl

def contradictoryInput : Family 1 :=
  [⟨false, (true, false), aConst 1 true⟩,
   ⟨false, (true, true), aConst 1 true⟩]

theorem source_history_extracts :
    (SharedRefutationExtraction.extract contradictoryInput).isSome = true := by decide

theorem source_history_refutes_every_input (b : Bool) :
    (SharedRefutationExtraction.extract contradictoryInput).bind (fun p =>
      SharedRefutationSourceLift.pairedSum (outputs p.1 (b, ()) p.2)
        (contradictoryInput.map (fun r => r.eval (b, ())))) = some true := by
  cases b <;> decide

theorem source_history_growth_bound :
    (SharedRefutationExtraction.extract contradictoryInput).map
      (fun p => decide (p.1.length ≤ 11)) = some true := by decide

theorem positive_dimension_unknown_not_refuted :
    SharedRefutationExtraction.extract ([] : Family 1) = none := by decide

theorem satisfiable_terminal_not_refuted :
    SharedRefutationExtraction.extract ([] : Family 0) = none := rfl

#print axioms SharedRefutationGlobalStep.globalStep_guard
#print axioms SharedRefutationGlobalStep.globalStep_values
#print axioms SharedRefutationTerminal.scalar_identity
#print axioms SharedRefutationAssembly.liftRecorded_exists
#print axioms SharedRefutationExtraction.unwind_linked
#print axioms SharedRefutationExtraction.extract_of_false_verdict
#print axioms SharedRefutationExtraction.extract_contract
#print axioms SharedRefutationExtraction.extract_unsatisfiable

#print axioms SharedRefutationAlgebra.row_head_quotient
#print axioms SharedRefutationAlgebra.refutation_lift_sum
#print axioms SharedRefutationAlgebra.refutation_lift_contradiction
#print axioms SharedRefutationCircuit.compile_value
#print axioms SharedRefutationCircuit.compile_growth
#print axioms SharedRefutationCircuit.compile_root_count
#print axioms SharedRefutationCircuit.compileChecked_contract
#print axioms SharedRefutationCircuit.compileChecked_value
#print axioms SharedRefutationCircuit.compileChecked_outputs
#print axioms SharedRefutationCircuit.compileChecked_growth
#print axioms one_row_values
#print axioms invalid_forward_reference

#print axioms SharedRefutationTransport.chartCode_outputs
#print axioms SharedRefutationTransport.chartCode_length
#print axioms SharedRefutationTransport.chartCode_valid
#print axioms SharedRefutationSourceLift.liftChecked_sum
#print axioms SharedRefutationSourceLift.liftChecked_refutes
#print axioms SharedRefutationSourceLift.liftChecked_unsatisfiable
#print axioms SharedRefutationSourceLift.liftChecked_contract
#print axioms SharedRefutationSourceLift.liftChecked_growth

#print axioms SharedRefutationContraction.planeRows_values
#print axioms SharedRefutationContraction.reduce_values
#print axioms SharedRefutationContraction.contract_values
#print axioms SharedRefutationContraction.contract_guard_value
#print axioms SharedRefutationContraction.contract_row_quotients
#print axioms nonlinear_source_refutation

end PNP.Concrete.ResidualReduction.SharedRefutationRegression
