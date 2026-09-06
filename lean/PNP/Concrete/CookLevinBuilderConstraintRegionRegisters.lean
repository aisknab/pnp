/-
Copyright (c) 2026 PNP Labs.

Source-derived lengths for all five constraint regions. The polynomial
postorder is shape/control/preservation/4/initial-tail, not schedule order.
Locate existing operand cells without evaluating a new input-sized control table.
The initial length still needs its literal +3 adjustment and final acceptance
its literal 1. Region selection, local decoding and the complete loop remain
separate from these register-access contracts.
-/

import PNP.Concrete.CookLevinBuilderClauseCoordinateRegisters

namespace PNP.Concrete.CookLevin.BuilderConstraintRegionRegisters

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count width)
open BuilderClauseDividerOperands (clauseWidth quotient)
open BuilderDividerSourceExecution (sourceSpan)

inductive Region where
  | shape | initial | control | preservation | accepting
  deriving DecidableEq, Repr

/-- Existing polynomial subtrees; initialTail excludes the three fixed slots. -/
inductive Term where
  | shape | initialTail | control | preservation
  deriving DecidableEq, Repr

def termPolynomial {language : Language} (verifier : PolynomialTimeVerifier language) :
    Term → NatPolynomial
  | .shape => .mul (formulaTimeCountPolynomial verifier)
      (.add (formulaTapeWidthPolynomial verifier) (.constant 2))
  | .initialTail => .mul (.constant 2)
      (.mul (.add verifier.certificateBound (.constant 1))
        (formulaTapeWidthPolynomial verifier))
  | .control => .mul (.constant 9)
      (.mul (.mul (formulaFuelPolynomial verifier) (formulaTapeWidthPolynomial verifier))
        (formulaStateCountPolynomial verifier))
  | .preservation => .mul (.constant 3)
      (.mul (.mul (formulaFuelPolynomial verifier) (formulaTapeWidthPolynomial verifier))
        (formulaTapeWidthPolynomial verifier))

def termValue {language : Language} (problem : VerifierTableauProblem language)
    (term : Term) : Nat :=
  (termPolynomial problem.verifier term).eval problem.input.length

def lengthPolynomial {language : Language} (verifier : PolynomialTimeVerifier language) :
    Region → NatPolynomial
  | .shape => termPolynomial verifier .shape
  | .initial => .add (.constant 3) (termPolynomial verifier .initialTail)
  | .control => termPolynomial verifier .control
  | .preservation => termPolynomial verifier .preservation
  | .accepting => .constant 1

def regionLength {language : Language} (problem : VerifierTableauProblem language)
    (region : Region) : Nat :=
  (lengthPolynomial problem.verifier region).eval problem.input.length

/-- Semantic schedule order, deliberately different from polynomial postorder. -/
def orderedLengths {language : Language} (problem : VerifierTableauProblem language) : List Nat :=
  [regionLength problem .shape, regionLength problem .initial,
   regionLength problem .control, regionLength problem .preservation,
   regionLength problem .accepting]

theorem orderedLengths_values {language : Language} (problem : VerifierTableauProblem language) :
    orderedLengths problem =
      [termValue problem .shape, 3 + termValue problem .initialTail,
       termValue problem .control, termValue problem .preservation, 1] := rfl

theorem orderedLengths_match_schedule {language : Language}
    (problem : VerifierTableauProblem language) :
    orderedLengths problem =
      [problem.dimensions.timeCount * (problem.dimensions.tapeWidth problem.tableauInputMode + 2),
       3 + 2 * ((problem.certificateLimit + 1) * problem.dimensions.tapeWidth problem.tableauInputMode),
       9 * (problem.uniformFuel * problem.dimensions.tapeWidth problem.tableauInputMode *
         problem.dimensions.stateBound),
       3 * (problem.uniformFuel * problem.dimensions.tapeWidth problem.tableauInputMode *
         problem.dimensions.tapeWidth problem.tableauInputMode), 1] := by
  rw [orderedLengths_values]
  simp only [termValue, termPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant]
  have hTime := problem.formulaTimeCountPolynomial_eval
  have hTape := problem.formulaTapeWidthPolynomial_eval
  have hFuel := problem.formulaFuelPolynomial_eval
  have hStates := problem.formulaStateCountPolynomial_eval
  simp only [BitString.size] at hTime hTape hFuel hStates
  rw [hTime, hTape, hFuel, hStates]
  rfl

theorem orderedLengths_sum {language : Language} (problem : VerifierTableauProblem language) :
    (orderedLengths problem).sum = problem.formulaConstraintSlotCount := by
  rw [orderedLengths_values]
  change (termValue problem .shape + (3 + termValue problem .initialTail +
    (termValue problem .control + (termValue problem .preservation + (1 + 0))))) =
    (((termValue problem .shape + termValue problem .control) +
      termValue problem .preservation) + 4) + termValue problem .initialTail
  omega

/-- Read exactly the five existing direct decoders, preserving padded empty slots. -/
def orderedSlot {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    Option (Option (LocalConstraint problem.FormulaWidth)) :=
  DirectSlot.append (regionLength problem .shape) problem.shapeConstraintSlotDirect
    (DirectSlot.append (regionLength problem .initial) problem.initialConstraintSlotDirect
      (DirectSlot.append (regionLength problem .control) problem.controlConstraintSlotDirect
        (DirectSlot.append (regionLength problem .preservation) problem.preservationConstraintSlotDirect
          (DirectSlot.singleton (some (.require
            (problem.stateLiteral problem.finalTime problem.acceptingState))))))) index

theorem orderedSlot_eq {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    orderedSlot problem index = problem.formulaConstraintSlotDirect index := by
  have h := orderedLengths_match_schedule problem
  have hShape := congrArg (fun values => values[0]?) h
  have hInitial := congrArg (fun values => values[1]?) h
  have hControl := congrArg (fun values => values[2]?) h
  have hPreservation := congrArg (fun values => values[3]?) h
  simp only [orderedLengths, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq] at hShape hInitial hControl hPreservation
  unfold orderedSlot VerifierTableauProblem.formulaConstraintSlotDirect
  rw [hShape, hInitial, hControl, hPreservation]

private def termRegisters {language : Language} (problem : VerifierTableauProblem language)
    (term : Term) : List Nat :=
  registerValues (termPolynomial problem.verifier term) problem.input.length

private def rootBefore {language : Language} (problem : VerifierTableauProblem language)
    (term : Term) : List Nat :=
  BuilderOperandRegisters.rootPrefix (termPolynomial problem.verifier term) problem.input.length

private def afterControl {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  termValue problem .shape + termValue problem .control

private def afterPreservation {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  afterControl problem + termValue problem .preservation

private theorem constraint_layout {language : Language} (problem : VerifierTableauProblem language) :
    registerValues (formulaConstraintCountPolynomial problem.verifier) problem.input.length =
      termRegisters problem .shape ++ termRegisters problem .control ++ [afterControl problem] ++
      termRegisters problem .preservation ++
      [afterPreservation problem, 4, afterPreservation problem + 4] ++
      termRegisters problem .initialTail ++ [problem.formulaConstraintSlotCount] := by
  change (((((termRegisters problem .shape ++ termRegisters problem .control) ++
    [afterControl problem]) ++ termRegisters problem .preservation) ++
      [afterPreservation problem]) ++ [4] ++ [afterPreservation problem + 4]) ++
        termRegisters problem .initialTail ++ [problem.formulaConstraintSlotCount] = _
  simp only [List.append_assoc, List.cons_append, List.nil_append]

def constraintOlder {language : Language} (problem : VerifierTableauProblem language) : Term → List Nat
  | .shape => rootBefore problem .shape
  | .control => termRegisters problem .shape ++ rootBefore problem .control
  | .preservation => termRegisters problem .shape ++ termRegisters problem .control ++
      [afterControl problem] ++ rootBefore problem .preservation
  | .initialTail => termRegisters problem .shape ++ termRegisters problem .control ++
      [afterControl problem] ++ termRegisters problem .preservation ++
      [afterPreservation problem, 4, afterPreservation problem + 4] ++ rootBefore problem .initialTail

def constraintNewer {language : Language} (problem : VerifierTableauProblem language) : Term → List Nat
  | .shape => termRegisters problem .control ++ [afterControl problem] ++
      termRegisters problem .preservation ++
      [afterPreservation problem, 4, afterPreservation problem + 4] ++
      termRegisters problem .initialTail ++ [problem.formulaConstraintSlotCount]
  | .control => [afterControl problem] ++ termRegisters problem .preservation ++
      [afterPreservation problem, 4, afterPreservation problem + 4] ++
      termRegisters problem .initialTail ++ [problem.formulaConstraintSlotCount]
  | .preservation => [afterPreservation problem, 4, afterPreservation problem + 4] ++
      termRegisters problem .initialTail ++ [problem.formulaConstraintSlotCount]
  | .initialTail => [problem.formulaConstraintSlotCount]

def constraintNewerCount {language : Language} (verifier : PolynomialTimeVerifier language) : Term → Nat
  | .shape => nodeCount (termPolynomial verifier .control) +
      nodeCount (termPolynomial verifier .preservation) + nodeCount (termPolynomial verifier .initialTail) + 5
  | .control => nodeCount (termPolynomial verifier .preservation) +
      nodeCount (termPolynomial verifier .initialTail) + 5
  | .preservation => nodeCount (termPolynomial verifier .initialTail) + 4
  | .initialTail => 1

theorem constraint_selection {language : Language} (problem : VerifierTableauProblem language)
    (term : Term) :
    registerValues (formulaConstraintCountPolynomial problem.verifier) problem.input.length =
      constraintOlder problem term ++ [termValue problem term] ++ constraintNewer problem term := by
  have hRoot (selected : Term) : termRegisters problem selected =
      rootBefore problem selected ++ [termValue problem selected] :=
    BuilderOperandRegisters.registerValues_rootPrefix _ _
  rw [constraint_layout]
  cases term with
  | shape =>
    rw [hRoot .shape]
    simp only [constraintOlder, constraintNewer, List.append_assoc]
  | initialTail =>
    rw [hRoot .initialTail]
    simp only [constraintOlder, constraintNewer, List.append_assoc, List.cons_append, List.nil_append]
  | control =>
    rw [hRoot .control]
    simp only [constraintOlder, constraintNewer, List.append_assoc, List.cons_append, List.nil_append]
  | preservation =>
    rw [hRoot .preservation]
    simp only [constraintOlder, constraintNewer, List.append_assoc, List.cons_append, List.nil_append]

theorem constraintNewer_length {language : Language} (problem : VerifierTableauProblem language)
    (term : Term) :
    (constraintNewer problem term).length = constraintNewerCount problem.verifier term := by
  cases term <;> simp only [constraintNewer, constraintNewerCount, termRegisters,
    registerValues_length, List.length_append, List.length_cons, List.length_nil] <;> omega

private def afterConstraints {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : List Nat :=
  registerValues (BuilderClauseDividerOperands.clauseWidthPolynomial problem.verifier) problem.input.length ++
    [count problem] ++ BuilderOperandRegisters.newerValues problem index remaining .clauseCount

private theorem retained_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    BuilderOperandRegisters.retainedValues problem index remaining =
      registerValues (formulaConstraintCountPolynomial problem.verifier) problem.input.length ++
        afterConstraints problem index remaining := by
  have hRoot := BuilderOperandRegisters.registerValues_rootPrefix
    (formulaClauseCountPolynomial problem.verifier) problem.input.length
  have hProduct : registerValues (formulaClauseCountPolynomial problem.verifier) problem.input.length =
      (registerValues (formulaConstraintCountPolynomial problem.verifier) problem.input.length ++
        registerValues (BuilderClauseDividerOperands.clauseWidthPolynomial problem.verifier)
          problem.input.length) ++ [count problem] := rfl
  have hPrefix := List.append_cancel_right (hRoot.symm.trans hProduct)
  rw [BuilderOperandRegisters.retainedValues_selection problem .clauseCount index remaining]
  change BuilderOperandRegisters.rootPrefix (formulaClauseCountPolynomial problem.verifier)
      problem.input.length ++ [count problem] ++
        BuilderOperandRegisters.newerValues problem index remaining .clauseCount = _
  rw [hPrefix]
  simp only [afterConstraints, List.append_assoc]

def coordinateSuffix {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    List Nat :=
  [count problem, 0, index, width problem, quotient problem index,
   count problem, 0, BuilderClauseDividerExecution.constraintIndex problem index * clauseWidth problem,
   BuilderClauseDividerExecution.clauseIndex problem index, clauseWidth problem,
   BuilderClauseDividerExecution.constraintIndex problem index]

/-- Additional already-built registers are frame data, not region certificates. -/
def inputValues {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (appended : List Nat) : List Nat :=
  BuilderClauseCoordinateRegisters.finalValues problem index remaining ++ appended

def newerValues {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (appended : List Nat) (term : Term) : List Nat :=
  constraintNewer problem term ++ afterConstraints problem index remaining ++
    coordinateSuffix problem index ++ appended

/-- Each compiled copy offset depends on verifier syntax and a fixed frame length only. -/
def copyOffset {language : Language} (verifier : PolynomialTimeVerifier language)
    (term : Term) (appendedCount : Nat) : Nat :=
  constraintNewerCount verifier term +
    nodeCount (BuilderClauseDividerOperands.clauseWidthPolynomial verifier) +
    BuilderOperandRegisters.newerCount verifier .clauseCount + 12 + appendedCount

theorem inputValues_selection {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (appended : List Nat) (term : Term) :
    inputValues problem index remaining appended =
      constraintOlder problem term ++ [termValue problem term] ++
        newerValues problem index remaining appended term := by
  unfold inputValues
  rw [BuilderClauseCoordinateRegisters.finalValues_eq, retained_layout, constraint_selection problem term]
  simp only [newerValues, coordinateSuffix, List.append_assoc]

theorem newerValues_length {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (appended : List Nat) (term : Term) :
    (newerValues problem index remaining appended term).length =
      copyOffset problem.verifier term appended.length := by
  simp only [newerValues, afterConstraints, coordinateSuffix, copyOffset, List.length_append,
    constraintNewer_length, registerValues_length, BuilderOperandRegisters.newerValues_length,
    List.length_cons, List.length_nil]
  omega

/-- The exact previous endpoint is the zero-extra-register case of this input layout. -/
theorem source_tape_handoff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (BuilderClauseCoordinateRegisters.finalConfiguration problem index remaining output).tape =
      endTape (inputValues problem index remaining []) (inside problem.input output) [] := by
  simpa only [inputValues, List.append_nil] using
    BuilderClauseCoordinateRegisters.final_tape_layout problem index remaining output

def copyMachine {language : Language} (verifier : PolynomialTimeVerifier language)
    (term : Term) (appendedCount : Nat) : WorkMachine :=
  RegisterCopy.machine (copyOffset verifier term appendedCount)

def copySteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (appended : List Nat) (term : Term) : Nat :=
  RegisterCopy.steps (newerValues problem index remaining appended term) (termValue problem term)

/-- Physical read-and-append of any of the four source terms; all original cells survive. -/
theorem copy_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (appended : List Nat) (term : Term) (workspace tail : List WorkSymbol) :
    workRunExact? (copyMachine problem.verifier term appended.length)
      (copySteps problem index remaining appended term)
      (workStartConfiguration (copyMachine problem.verifier term appended.length)
        (endTape (inputValues problem index remaining appended) workspace tail)) =
    some {
      state := (copyMachine problem.verifier term appended.length).acceptState
      tape := endTape (inputValues problem index remaining appended ++ [termValue problem term])
        workspace (tail.drop (termValue problem term + 1))
    } := by
  rw [inputValues_selection problem index remaining appended term]
  unfold copyMachine copySteps
  rw [← newerValues_length problem index remaining appended term, RegisterCopy.machine_acceptState]
  have h := RegisterCopy.workRunExact (registerWord (constraintOlder problem term)) workspace tail
    (termValue problem term) (newerValues problem index remaining appended term)
  change workRunExact? (RegisterCopy.machine (newerValues problem index remaining appended term).length)
      (RegisterCopy.steps (newerValues problem index remaining appended term) (termValue problem term))
      {
        state := 0
        tape := {
          left := tail
          head := scratchEndSymbol
          right := (registerWord (constraintOlder problem term) ++
            registerWord ([termValue problem term] ++ newerValues problem index remaining appended term)).reverse ++
              workspace
        }
      } = some {
        state := RegisterCopy.stateCount (newerValues problem index remaining appended term).length
        tape := {
          left := tail.drop (termValue problem term + 1)
          head := scratchEndSymbol
          right := (registerWord (constraintOlder problem term) ++
            registerWord ([termValue problem term] ++ newerValues problem index remaining appended term ++
              [termValue problem term])).reverse ++ workspace
        }
      } at h
  simpa only [workStartConfiguration, RegisterCopy.machine_startState, endTape,
    registerWord_append, List.append_assoc] using h

theorem copy_run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (appended : List Nat) (term : Term) (workspace tail : List WorkSymbol) :
    run (compileWorkMachine (copyMachine problem.verifier term appended.length))
      (6 * copySteps problem index remaining appended term)
      (encodeWorkConfiguration (workStartConfiguration (copyMachine problem.verifier term appended.length)
        (endTape (inputValues problem index remaining appended) workspace tail))) =
      encodeWorkConfiguration {
        state := (copyMachine problem.verifier term appended.length).acceptState
        tape := endTape (inputValues problem index remaining appended ++ [termValue problem term])
          workspace (tail.drop (termValue problem term + 1))
      } :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (copy_workRunExact problem index remaining appended term workspace tail)

theorem source_selection_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (appended : List Nat) (term : Term)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    let bound := 9 * (sourceSpan problem.verifier).eval problem.input.length + 11 +
      appended.length + appended.sum
    termValue problem term ≤ bound ∧
      (newerValues problem index remaining appended term).length +
        (newerValues problem index remaining appended term).sum ≤ bound := by
  have hSpan := BuilderClauseCoordinateRegisters.final_register_span_le problem index remaining hBalance
  have hLength := congrArg (fun values => (registerWord values).length)
    (inputValues_selection problem index remaining appended term)
  simp only [inputValues, registerWord_length, List.length_append, List.length_cons, List.length_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] at hLength
  rw [registerWord_length] at hSpan
  constructor <;> omega

theorem copySteps_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (appended : List Nat) (term : Term)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    let bound := 9 * (sourceSpan problem.verifier).eval problem.input.length + 11 +
      appended.length + appended.sum
    copySteps problem index remaining appended term ≤ 4 * (bound + 1) ^ 2 + 9 * (bound + 1) + 5 := by
  have h := source_selection_bounds problem index remaining appended term hBalance
  simpa only [copySteps, Nat.pow_two, Nat.mul_assoc] using
    RegisterCopy.steps_le _ _ _ h.1 h.2

theorem copy_rules_pairwise_query_distinct {language : Language}
    (verifier : PolynomialTimeVerifier language) (term : Term) (appendedCount : Nat) :
    (copyMachine verifier term appendedCount).rules.Pairwise WorkMachineChain.QueryDistinct :=
  RegisterCopy.rules_pairwise_query_distinct _

theorem copy_noRuleAtAccept {language : Language}
    (verifier : PolynomialTimeVerifier language) (term : Term) (appendedCount : Nat) :
    WorkMachineChain.NoRuleAtAccept (copyMachine verifier term appendedCount) := by
  intro rule hRule
  exact Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState _ rule hRule)

theorem copy_acceptState_ne_rejectState {language : Language}
    (verifier : PolynomialTimeVerifier language) (term : Term) (appendedCount : Nat) :
    (copyMachine verifier term appendedCount).acceptState ≠ (copyMachine verifier term appendedCount).rejectState :=
  RegisterCopy.machine_acceptState_ne_rejectState _

end PNP.Concrete.CookLevin.BuilderConstraintRegionRegisters
