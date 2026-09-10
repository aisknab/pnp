/-
Copyright (c) 2026 PNP Labs.

Physically prepare the actual-source body-clause search frame. The program
writes ordinal zero, reads the payload's list count where present, includes
the implication conclusion, and copies the original token position. Only the
three fixed source families choose control; no runtime magnitude does.

The enclosing dispatcher must select the family from the actual source tag
and choose body versus exclusion clauses. This adapter does not claim that
dispatcher, the complete formula loop, or the packaged reduction is complete.
-/
import PNP.Concrete.CookLevinBuilderPayloadClauseTokenSelector

namespace PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Family Request family body requestValues)
open BuilderLocalConstraintPayload (literalValues literalListValues variableValues)

def countMachine : Family → WorkMachine
  | .required => RegisterConstant.machine 1
  | .implication => WorkMachineChain.machine (RegisterCopy.machine 13)
      BuilderConstraintRegionAssembly.Increment.machine
  | .positive => RegisterCopy.machine 13
def machine (route : Family) : WorkMachine :=
  WorkMachineChain.machine (RegisterConstant.machine 0)
    (WorkMachineChain.machine (countMachine route) (RegisterCopy.machine 2))

def countSuffix (tag : Nat) (request : Request) : List Nat :=
  [tag] ++ request.gap ++ [request.clauseIndex, request.originalPosition, 0]
def countSteps {width : Nat} : LocalConstraint width → Request → Nat
  | .require _, _ => RegisterConstant.steps 1
  | .implication premises _, request =>
      RegisterCopy.steps (countSuffix 3 request) premises.length + 1 + 2
  | .exactlyOne variables, request =>
      RegisterCopy.steps (countSuffix 4 request) variables.length
def workSteps {width : Nat} (constraint : LocalConstraint width) (request : Request) : Nat :=
  RegisterConstant.steps 0 + 1 +
    (countSteps constraint request + 1 +
      RegisterCopy.steps [0, (body constraint).length] request.originalPosition)
def countOutside {width : Nat} (constraint : LocalConstraint width) (outside : List WorkSymbol) : List WorkSymbol :=
  (outside.drop 1).drop ((body constraint).length + 1)
def finalOutside {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (outside : List WorkSymbol) : List WorkSymbol :=
  (countOutside constraint outside).drop (request.originalPosition + 1)
def initialValues {width : Nat} (constraint : LocalConstraint width) (request : Request) (older : List Nat) : List Nat :=
  requestValues constraint request older
def finalValues {width : Nat} (constraint : LocalConstraint width) (request : Request) (older : List Nat) : List Nat :=
  initialValues constraint request older ++ [0, (body constraint).length, request.originalPosition]
def initialConfiguration {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine (family constraint))
    (endTape (initialValues constraint request older) inside outside)
def finalConfiguration {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  {state := (machine (family constraint)).acceptState,
   tape := endTape (finalValues constraint request older) inside (finalOutside constraint request outside)}

theorem countSuffix_length (tag : Nat) (request : Request) :
    (countSuffix tag request).length = 13 := by
  simp only [countSuffix, List.length_append, List.length_cons, List.length_nil, request.gap_length]

theorem implication_count_layout {width : Nat} (premises : List (BoundedLiteral width))
    (conclusion : BoundedLiteral width) (request : Request) (older : List Nat) :
    initialValues (.implication premises conclusion) request older ++ [0] =
      (older ++ (literalValues conclusion ++ literalListValues premises).reverse) ++
        [premises.length] ++ countSuffix 3 request := by
  simp only [initialValues, requestValues, BuilderLocalConstraintPayload.values,
    BuilderLocalConstraintPayload.front, List.reverse_append, List.reverse_cons,
    List.append_assoc, List.cons_append, List.nil_append, countSuffix]

theorem positive_count_layout {width : Nat} (variables : List (Fin width))
    (request : Request) (older : List Nat) :
    initialValues (.exactlyOne variables) request older ++ [0] =
      (older ++ (variableValues variables).reverse) ++ [variables.length] ++ countSuffix 4 request := by
  simp only [initialValues, requestValues, BuilderLocalConstraintPayload.values,
    BuilderLocalConstraintPayload.front, List.reverse_cons,
    List.append_assoc, List.cons_append, List.nil_append, countSuffix]

theorem final_values_search_input {width : Nat} (constraint : LocalConstraint width)
    (request : Request) (older : List Nat) :
    finalValues constraint request older =
      BuilderPayloadClauseTokenSelector.initialValues constraint request request.originalPosition older := by
  simp only [finalValues, initialValues, BuilderPayloadClauseTokenSelector.initialValues,
    BuilderPayloadSearchSource.initialValues, BuilderPayloadSearchSource.baseValues,
    List.append_nil]

private theorem chain_run (first second : WorkMachine) (n m : Nat) (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

private theorem constant_run (value : Nat) (existing : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (RegisterConstant.machine value) (RegisterConstant.steps value)
      (workStartConfiguration (RegisterConstant.machine value) (endTape existing inside outside)) =
      some {state := (RegisterConstant.machine value).acceptState, tape := endTape (existing ++ [value]) inside (outside.drop (value + 1))} := by
  rw [RegisterConstant.machine_acceptState]
  exact RegisterConstant.workRunExact value existing inside outside

theorem count_workRunExact {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (countMachine (family constraint)) (countSteps constraint request)
      (workStartConfiguration (countMachine (family constraint))
        (endTape (initialValues constraint request older ++ [0]) inside outside)) =
      some {
        state := (countMachine (family constraint)).acceptState
        tape := endTape (initialValues constraint request older ++ [0, (body constraint).length])
          inside (outside.drop ((body constraint).length + 1))
      } := by
  cases constraint with
  | require literal =>
      have h := constant_run 1 (initialValues (.require literal) request older ++ [0]) inside outside
      have hLayout : (initialValues (.require literal) request older ++ [0]) ++ [1] =
          initialValues (.require literal) request older ++ [0, (body (.require literal)).length] := by
        rw [List.append_assoc]
        rfl
      rw [hLayout] at h
      exact h
  | implication premises conclusion =>
      let values := initialValues (.implication premises conclusion) request older ++ [0]
      have hCopy := BuilderRegionComparisonOperands.copy_workRunExact 13
        (older ++ (literalValues conclusion ++ literalListValues premises).reverse)
        (countSuffix 3 request) premises.length inside outside (countSuffix_length 3 request)
      rw [← implication_count_layout premises conclusion request older] at hCopy
      have hIncrement := BuilderConstraintRegionAssembly.Increment.workRunExact values premises.length
        inside (outside.drop (premises.length + 1))
      have h := chain_run _ _ _ _ _ _ _ hCopy hIncrement
      simpa only [family, countMachine, countSteps, BuilderPayloadSearchSource.body_implication_length,
        values, List.drop_drop, List.append_assoc, List.cons_append, List.nil_append] using h
  | exactlyOne variables =>
      have hCopy := BuilderRegionComparisonOperands.copy_workRunExact 13
        (older ++ (variableValues variables).reverse) (countSuffix 4 request) variables.length
        inside outside (countSuffix_length 4 request)
      rw [← positive_count_layout variables request older] at hCopy
      simpa only [family, countMachine, countSteps, BuilderPayloadSearchSource.body_positive_length,
        List.append_assoc, List.cons_append, List.nil_append] using hCopy

theorem workRunExact {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine (family constraint)) (workSteps constraint request)
      (initialConfiguration constraint request older inside outside) =
      some (finalConfiguration constraint request older inside outside) := by
  let values := initialValues constraint request older
  have hZero := constant_run 0 values inside outside
  have hCount := count_workRunExact constraint request older inside (outside.drop 1)
  have hPosition := BuilderRegionComparisonOperands.copy_workRunExact 2
    (older ++ BuilderLocalConstraintPayload.values (some (some constraint)) ++
      request.gap ++ [request.clauseIndex]) [0, (body constraint).length]
    request.originalPosition inside (countOutside constraint outside) rfl
  have hPositionRun : workRunExact? (RegisterCopy.machine 2)
      (RegisterCopy.steps [0, (body constraint).length] request.originalPosition)
      (workStartConfiguration (RegisterCopy.machine 2)
        (endTape (values ++ [0, (body constraint).length]) inside (countOutside constraint outside))) =
      some {
        state := (RegisterCopy.machine 2).acceptState
        tape := endTape (finalValues constraint request older) inside (finalOutside constraint request outside)
      } := by
    simpa only [values, initialValues, requestValues, finalValues, finalOutside,
      List.append_assoc, List.cons_append, List.nil_append] using hPosition
  exact chain_run _ _ _ _ _ _ _ hZero (chain_run _ _ _ _ _ _ _ hCount hPositionRun)

theorem run_compile_exact {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (machine (family constraint))) (6 * workSteps constraint request)
      (encodeWorkConfiguration (initialConfiguration constraint request older inside outside)) =
      encodeWorkConfiguration (finalConfiguration constraint request older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact constraint request older inside outside)

theorem original_request_preserved {width : Nat} (constraint : LocalConstraint width)
    (request : Request) (older : List Nat) :
    finalValues constraint request older =
      requestValues constraint request older ++ [0, (body constraint).length, request.originalPosition] := rfl

theorem finalOutside_length_le {width : Nat} (constraint : LocalConstraint width)
    (request : Request) (outside : List WorkSymbol) :
    (finalOutside constraint request outside).length ≤ outside.length := by
  simp only [finalOutside, countOutside, List.length_drop]
  omega

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineChain.QueryDistinct ∧ WorkMachineChain.NoRuleAtAccept program ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧ program.acceptState ≠ program.rejectState
private theorem constant_good (value : Nat) : Good (RegisterConstant.machine value) := by
  refine ⟨RegisterConstant.rules_pairwise_query_distinct value, ?_, ?_,
    RegisterConstant.machine_acceptState_ne_rejectState value⟩
  · intro rule hRule
    exact Nat.ne_of_lt (RegisterConstant.rule_source_lt_acceptState value rule hRule)
  · intro rule hRule
    have h := RegisterConstant.rule_source_lt_acceptState value rule hRule
    rw [RegisterConstant.machine_acceptState] at h
    rw [RegisterConstant.machine_rejectState]
    omega
private theorem copy_good (depth : Nat) : Good (RegisterCopy.machine depth) := by
  refine ⟨RegisterCopy.rules_pairwise_query_distinct depth, ?_, ?_,
    RegisterCopy.machine_acceptState_ne_rejectState depth⟩
  · intro rule hRule
    exact Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState depth rule hRule)
  · intro rule hRule
    have h := RegisterCopy.rule_source_lt_acceptState depth rule hRule
    rw [RegisterCopy.machine_acceptState] at h
    rw [RegisterCopy.machine_rejectState]
    omega
private theorem increment_good : Good BuilderConstraintRegionAssembly.Increment.machine := by
  refine ⟨BuilderConstraintRegionAssembly.Increment.rules_pairwise_query_distinct,
    BuilderConstraintRegionAssembly.Increment.noRuleAtAccept, ?_,
    BuilderConstraintRegionAssembly.Increment.acceptState_ne_rejectState⟩
  intro rule hRule
  decide +revert
private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
   WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
   WorkMachineChain.noRuleAtAccept first {second with acceptState := second.rejectState} hSecond.2.2.1,
   WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2.2⟩
private theorem good (route : Family) : Good (machine route) := by
  have hCount : Good (countMachine route) := by
    cases route with
    | required => exact constant_good 1
    | implication => exact chain_good _ _ (copy_good 13) increment_good
    | positive => exact copy_good 13
  exact chain_good _ _ (constant_good 0) (chain_good _ _ hCount (copy_good 2))

theorem rules_pairwise_query_distinct (route : Family) :
    (machine route).rules.Pairwise WorkMachineChain.QueryDistinct := (good route).1
theorem noRuleAtAccept (route : Family) : WorkMachineChain.NoRuleAtAccept (machine route) := (good route).2.1
theorem noRuleAtReject (route : Family) :
    WorkMachineProgramGraph.NoRuleAt (machine route) (machine route).rejectState := (good route).2.2.1
theorem acceptState_ne_rejectState (route : Family) :
    (machine route).acceptState ≠ (machine route).rejectState := (good route).2.2.2

theorem initial_scalar_bounds {width : Nat} (constraint : LocalConstraint width)
    (request : Request) (older : List Nat) (bound : Nat)
    (hSpan : (registerWord (initialValues constraint request older)).length ≤ bound) :
    (body constraint).length ≤ bound + 1 ∧ request.originalPosition ≤ bound ∧
      request.gap.length + request.gap.sum + request.clauseIndex + request.originalPosition ≤ bound := by
  have hParts := hSpan
  simp only [initialValues, requestValues, registerWord_length, List.length_append,
    List.sum_append, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at hParts
  refine ⟨?_, ?_, ?_⟩
  · cases constraint with
    | require literal =>
        change 1 ≤ bound + 1
        omega
    | implication premises conclusion =>
        rw [BuilderPayloadSearchSource.body_implication_length]
        simp only [BuilderLocalConstraintPayload.values, BuilderLocalConstraintPayload.front,
          List.length_reverse, List.sum_reverse, List.length_append, List.sum_append,
          List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at hParts
        omega
    | exactlyOne variables =>
        rw [BuilderPayloadSearchSource.body_positive_length]
        simp only [BuilderLocalConstraintPayload.values, BuilderLocalConstraintPayload.front,
          List.length_reverse, List.sum_reverse, List.length_append, List.sum_append,
          List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at hParts
        omega
  · omega
  · omega

def copyBound (bound : Nat) : Nat := 4 * (bound + 1) * (bound + 1) + 9 * (bound + 1) + 5
def workBound (bound : Nat) : Nat := 2 * copyBound (2 * bound + 20) + 8
def spanBound (bound : Nat) : Nat := 3 * bound + 4

theorem space_time_bounds {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (outside : List WorkSymbol) (bound : Nat)
    (hSpan : (registerWord (initialValues constraint request older)).length + outside.length ≤ bound) :
    (registerWord (finalValues constraint request older)).length +
        (finalOutside constraint request outside).length ≤ spanBound bound ∧
      workSteps constraint request ≤ workBound bound := by
  have hScalars := initial_scalar_bounds constraint request older bound (by omega)
  have hCountSuffix (tag : Nat) (hTag : tag ≤ 4) :
      (countSuffix tag request).length + (countSuffix tag request).sum ≤ 2 * bound + 20 := by
    simp only [countSuffix, List.length_append, List.sum_append, List.length_cons, List.length_nil,
      List.sum_cons, List.sum_nil]
    omega
  have hPositionSuffix : ([0, (body constraint).length] : List Nat).length +
      [0, (body constraint).length].sum ≤ 2 * bound + 20 := by
    simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    omega
  have hPosition := RegisterCopy.steps_le [0, (body constraint).length] request.originalPosition
    (2 * bound + 20) (by omega) hPositionSuffix
  have hCount : countSteps constraint request ≤ copyBound (2 * bound + 20) + 4 := by
    cases constraint with
    | require literal =>
        simp only [countSteps, RegisterConstant.steps]
        omega
    | implication premises conclusion =>
        have hLength : premises.length ≤ bound + 1 := by
          rw [BuilderPayloadSearchSource.body_implication_length] at hScalars
          omega
        have hCopy := RegisterCopy.steps_le (countSuffix 3 request) premises.length
          (2 * bound + 20) (by omega) (hCountSuffix 3 (by decide))
        simp only [countSteps, copyBound]
        omega
    | exactlyOne variables =>
        have hLength : variables.length ≤ bound + 1 := by
          rw [BuilderPayloadSearchSource.body_positive_length] at hScalars
          omega
        have hCopy := RegisterCopy.steps_le (countSuffix 4 request) variables.length
          (2 * bound + 20) (by omega) (hCountSuffix 4 (by decide))
        exact Nat.le_trans hCopy (by simp only [copyBound]; omega)
  constructor
  · have hOutside := finalOutside_length_le constraint request outside
    simp only [finalValues, registerWord_append, List.length_append, registerWord_length,
      List.length_cons, List.length_nil, List.sum_cons, List.sum_nil, spanBound]
    rw [registerWord_length] at hSpan
    omega
  · simp only [workSteps, RegisterConstant.steps, workBound, copyBound] at hCount ⊢
    omega

def argumentBoundPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 2) bound) (.constant 20)
def copyBoundPolynomial (bound : NatPolynomial) : NatPolynomial :=
  let shifted := NatPolynomial.add bound (.constant 1)
  .add (.add (.mul (.mul (.constant 4) shifted) shifted) (.mul (.constant 9) shifted)) (.constant 5)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.constant 6)
    (.add (.mul (.constant 2) (copyBoundPolynomial (argumentBoundPolynomial bound))) (.constant 8))
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 3) bound) (.constant 4)

theorem rawTimePolynomial_eval (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) := rfl
theorem spanPolynomial_eval (bound : NatPolynomial) (input : Nat) :
    (spanPolynomial bound).eval input = spanBound (bound.eval input) := rfl

theorem source_polynomial_bounds {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues constraint request older)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues constraint request older)).length +
        (finalOutside constraint request outside).length ≤ (spanPolynomial bound).eval input ∧
      6 * workSteps constraint request ≤ (rawTimePolynomial bound).eval input := by
  have h := space_time_bounds constraint request older outside (bound.eval input) hSpan
  rw [spanPolynomial_eval, rawTimePolynomial_eval]
  exact ⟨h.1, Nat.mul_le_mul_left 6 h.2⟩

theorem uniform_body_preparation {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues constraint request older)).length + outside.length ≤ bound.eval input) :
    ∃ rawSteps, rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine (machine (family constraint))) rawSteps
        (encodeWorkConfiguration (initialConfiguration constraint request older inside outside)) =
        encodeWorkConfiguration (finalConfiguration constraint request older inside outside) ∧
      (finalConfiguration constraint request older inside outside).tape =
        endTape (BuilderPayloadClauseTokenSelector.initialValues constraint request request.originalPosition older)
          inside (finalOutside constraint request outside) ∧
      (registerWord (finalValues constraint request older)).length +
        (finalOutside constraint request outside).length ≤ (spanPolynomial bound).eval input := by
  have hBounds := source_polynomial_bounds constraint request older outside bound input hSpan
  refine ⟨6 * workSteps constraint request, hBounds.2,
    run_compile_exact constraint request older inside outside, ?_, hBounds.1⟩
  change endTape (finalValues constraint request older) inside (finalOutside constraint request outside) = _
  rw [final_values_search_input]

end PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation
