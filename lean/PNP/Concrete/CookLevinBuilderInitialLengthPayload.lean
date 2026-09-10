/-
Copyright (c) 2026 PNP Labs.

The arbitrary-width initial certificate-length clause from the actual source
packet. Existing source/literal kernels derive the canonical length-block base;
fixed arithmetic reads the written certificate width and computes the complete
range bounds. The existing finite exactly-one writer constructs every variable,
count and payload tag. No runtime count or semantic list builds machine control.
-/

import PNP.Concrete.CookLevinBuilderInitialConstraintPayload
import PNP.Concrete.CookLevinBuilderLiteralArgumentSource

namespace PNP.Concrete.CookLevin.BuilderInitialLengthPayload

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderRegisterExpression (Expr)
open WorkMachineProgramGraph (Node Graph)
open WorkMachineProgramPath (AcceptPath)

def plan : BuilderLiteralArgumentSource.Plan .initial 0 := fun _ => .constant 0
def kernel : Expr 8 := BuilderLiteralIndexExpression.expression .certificateLength

def baseValue {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  BuilderRegisterExpression.eval kernel
    (BuilderLiteralArgumentSource.argumentEnvironment problem index .initial [] plan)
def countValue {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  problem.layout.certificateBitWidth + 1
def upperValue {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  baseValue problem index + countValue problem

def baseValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  BuilderLiteralArgumentSource.finalValues problem index remaining .initial [] plan .certificateLength
def Arity {language : Language} (verifier : PolynomialTimeVerifier language) : Nat :=
  BuilderLiteralArgumentSource.inputCount verifier .initial 0 + 8 + BuilderRegisterExpression.nodeCount kernel

theorem baseValues_length {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    (baseValues problem index remaining).length = Arity problem.verifier := by
  simp only [baseValues, BuilderLiteralArgumentSource.finalValues, BuilderLiteralArgumentSource.writtenValues,
    List.length_append, List.length_ofFn, BuilderRegisterExpression.values_length, kernel,
    BuilderLiteralArgumentSource.inputValues_length problem index remaining .initial 0 [] rfl, Arity, Nat.add_assoc]

private def view {arity : Nat} (values : List Nat) (index : Fin arity) : Nat := values.getD index.val 0

private theorem view_ofFn {arity : Nat} (values : List Nat) (hLength : values.length = arity) :
    List.ofFn (view values : Fin arity → Nat) = values := by
  subst arity
  have h : (view values : Fin values.length → Nat) = fun index => values[index.val] := by
    funext index
    simp only [view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem index.isLt, Option.getD_some]
  rw [h]
  exact List.ofFn_getElem

private theorem getD_after (leading trailing : List Nat) (index : Nat) :
    (leading ++ trailing).getD (leading.length + index) 0 = trailing.getD index 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

def baseField {language : Language} (verifier : PolynomialTimeVerifier language) :
    BuilderRegisterPack.Field (Arity verifier) :=
  .argument ⟨Arity verifier - 1, by simp only [Arity]; omega⟩
def certificateField {language : Language} (verifier : PolynomialTimeVerifier language) :
    BuilderRegisterPack.Field (Arity verifier) :=
  .argument ⟨BuilderLiteralArgumentSource.inputCount verifier .initial 0 + 3, by simp only [Arity]; omega⟩

theorem baseField_eval {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    (baseField problem.verifier).eval (view (baseValues problem index remaining)) = baseValue problem index := by
  let leading := BuilderLiteralArgumentSource.inputValues problem index remaining .initial [] ++
    List.ofFn (BuilderLiteralArgumentSource.argumentEnvironment problem index .initial [] plan) ++
    BuilderRegisterExpression.prefixValues kernel
      (BuilderLiteralArgumentSource.argumentEnvironment problem index .initial [] plan)
  have hValues : baseValues problem index remaining = leading ++ [baseValue problem index] :=
    BuilderLiteralArgumentSource.final_index_register problem index remaining .initial [] plan .certificateLength
  have hLength := baseValues_length problem index remaining
  rw [hValues, List.length_append] at hLength
  simp only [List.length_cons, List.length_nil] at hLength
  have hPosition : Arity problem.verifier - 1 = leading.length + 0 := by omega
  change (baseValues problem index remaining).getD (Arity problem.verifier - 1) 0 = baseValue problem index
  rw [hValues, hPosition, getD_after]
  rfl

theorem certificateField_eval {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    (certificateField problem.verifier).eval (view (baseValues problem index remaining)) =
      problem.layout.certificateBitWidth := by
  have hLength := BuilderLiteralArgumentSource.inputValues_length problem index remaining .initial 0 [] rfl
  change (baseValues problem index remaining).getD
    (BuilderLiteralArgumentSource.inputCount problem.verifier .initial 0 + 3) 0 = problem.layout.certificateBitWidth
  rw [baseValues, BuilderLiteralArgumentSource.finalValues, BuilderLiteralArgumentSource.writtenValues,
    ← hLength, getD_after]
  rfl

def expression {language : Language} (verifier : PolynomialTimeVerifier language) : Expr (Arity verifier) :=
  .binary .add (baseField verifier).expression
    (.binary .add (certificateField verifier).expression (.constant 1))

theorem expression_eval {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    BuilderRegisterExpression.eval (expression problem.verifier) (view (baseValues problem index remaining)) =
      upperValue problem index := by
  change (baseField problem.verifier).eval (view (baseValues problem index remaining)) +
    ((certificateField problem.verifier).eval (view (baseValues problem index remaining)) + 1) = _
  rw [baseField_eval, certificateField_eval]
  rfl

theorem expression_values {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    BuilderRegisterExpression.values (expression problem.verifier) (view (baseValues problem index remaining)) =
      [baseValue problem index, problem.layout.certificateBitWidth, 1, countValue problem, upperValue problem index] := by
  change [(baseField problem.verifier).eval (view (baseValues problem index remaining)),
    (certificateField problem.verifier).eval (view (baseValues problem index remaining)), 1,
    (certificateField problem.verifier).eval (view (baseValues problem index remaining)) + 1,
    (baseField problem.verifier).eval (view (baseValues problem index remaining)) +
      ((certificateField problem.verifier).eval (view (baseValues problem index remaining)) + 1)] = _
  rw [baseField_eval, certificateField_eval]
  rfl

theorem count_le_upper {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    countValue problem ≤ upperValue problem index := by
  unfold upperValue
  omega

def scratchValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  baseValues problem index remaining ++ [baseValue problem index, problem.layout.certificateBitWidth, 1]
def payloadValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  BuilderRegisterExactlyOnePayload.payloadValues (countValue problem) (upperValue problem index)
def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  scratchValues problem index remaining ++ [countValue problem] ++ payloadValues problem index
def exterior {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List WorkSymbol :=
  (List.replicate (upperValue problem index - countValue problem + 1) .blank).drop (countValue problem + 6)

theorem payload_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (payloadValues problem index).length = countValue problem + 2 := BuilderRegisterExactlyOnePayload.payload_length _ _

private def zeroLength {language : Language} (problem : VerifierTableauProblem language) : Fin (problem.certificateLimit + 1) :=
  ⟨0, by omega⟩

theorem count_canonical {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) : countValue problem = problem.certificateLimit + 1 := by
  rw [countValue, problem.certificateBitWidth_eq_of_paired hMode]

theorem base_canonical {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hMode : problem.tableauInputMode = .paired) :
    baseValue problem index = (problem.pairedLengthLiteral hMode (zeroLength problem)).index.val := by
  have hEnvironment :
      BuilderLiteralArgumentSource.argumentEnvironment problem index .initial [] plan =
        ((.certificateLength (problem.pairedCertificateLengthIndex hMode (zeroLength problem)) :
          BuilderLiteralIndexExpression.Request problem.layout)).environment := by
    funext field
    rcases field with ⟨field, hField⟩
    have hCases : field = 0 ∨ field = 1 ∨ field = 2 ∨ field = 3 ∨
        field = 4 ∨ field = 5 ∨ field = 6 ∨ field = 7 := by omega
    rcases hCases with h | h | h | h | h | h | h | h <;> subst field <;> rfl
  rw [baseValue, kernel, hEnvironment]
  exact BuilderLiteralIndexExpression.eval_eq_index
    (.certificateLength (problem.pairedCertificateLengthIndex hMode (zeroLength problem)))

theorem length_index_offset {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hMode : problem.tableauInputMode = .paired) (length : Fin (problem.certificateLimit + 1)) :
    (problem.pairedLengthLiteral hMode length).index.val = baseValue problem index + length.val := by
  rw [base_canonical problem index hMode]
  change problem.layout.certificateLengthBlock.offset + length.val =
    (problem.layout.certificateLengthBlock.offset + 0) + length.val
  rfl

theorem length_variables {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hMode : problem.tableauInputMode = .paired) :
    (problem.pairedLengthVariables hMode).map Fin.val =
      (finiteIndices (problem.certificateLimit + 1)).map (fun length => baseValue problem index + length.val) := by
  simp only [VerifierTableauProblem.pairedLengthVariables, List.map_map, Function.comp_def]
  apply congrArg (fun f : Fin (problem.certificateLimit + 1) → Nat => (finiteIndices (problem.certificateLimit + 1)).map f)
  funext length
  exact length_index_offset problem index hMode length

theorem payload_canonical {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hMode : problem.tableauInputMode = .paired) :
    payloadValues problem index = BuilderInitialConstraintPayload.lengthValues problem hMode := by
  simp only [payloadValues, BuilderRegisterExactlyOnePayload.payloadValues, upperValue,
    count_canonical problem hMode, BuilderShapeCoordinates.descending_eq_reverse_finiteIndices,
    BuilderInitialConstraintPayload.lengthValues, length_variables problem index hMode]


def rangeNode : Node :=
  {name := 2, program := BuilderRegisterExactlyOnePayload.machine, onAccept := .accept, onReject := .dead}
def upperNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 1, program := BuilderRegisterExpression.machine (expression verifier) 0,
   onAccept := .node rangeNode.reference, onReject := .dead}
def baseNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 0, program := BuilderLiteralArgumentSource.machine verifier .initial 0 plan .certificateLength,
   onAccept := .node (upperNode verifier).reference, onReject := .dead}
def graph {language : Language} (verifier : PolynomialTimeVerifier language) : Graph :=
  {nodes := [baseNode verifier, upperNode verifier, rangeNode], entry := (baseNode verifier).reference}
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineProgramGraph.machine (graph verifier)

private theorem machine_accept {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState = 0 := rfl

theorem graph_nodes_length {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).nodes.length = 3 := rfl

private theorem base_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    baseNode verifier ∈ (graph verifier).nodes := List.Mem.head _
private theorem upper_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    upperNode verifier ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.head _)
private theorem range_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    rangeNode ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

theorem graph_wellFormed {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).WellFormed := by
  have hNames : ((graph verifier).nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0, 1, 2] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact ⟨BuilderLiteralArgumentSource.rules_pairwise_query_distinct verifier .initial 0 plan .certificateLength,
        BuilderLiteralArgumentSource.noRuleAtAccept verifier .initial 0 plan .certificateLength,
        BuilderLiteralArgumentSource.noRuleAtReject verifier .initial 0 plan .certificateLength,
        BuilderLiteralArgumentSource.acceptState_ne_rejectState verifier .initial 0 plan .certificateLength⟩
    · exact ⟨BuilderRegisterExpression.rules_pairwise_query_distinct (expression verifier) 0,
        BuilderRegisterExpression.noRuleAtAccept (expression verifier) 0,
        BuilderRegisterExpression.noRuleAtReject (expression verifier) 0,
        BuilderRegisterExpression.acceptState_ne_rejectState (expression verifier) 0⟩
    · exact ⟨BuilderRegisterExactlyOnePayload.rules_pairwise_query_distinct,
        BuilderRegisterExactlyOnePayload.noRuleAtAccept, BuilderRegisterExactlyOnePayload.noRuleAtReject,
        BuilderRegisterExactlyOnePayload.acceptState_ne_rejectState⟩
  · exact ⟨baseNode verifier, base_mem verifier, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact ⟨⟨upperNode verifier, upper_mem verifier, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨rangeNode, range_mem verifier, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def baseSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderLiteralArgumentSource.workSteps problem index remaining .initial 0 [] plan .certificateLength
def upperSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderRegisterExpression.workSteps (expression problem.verifier) (view (baseValues problem index remaining)) []
def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  baseSteps problem index remaining + 1 + (upperSteps problem index remaining + 1 +
    (BuilderRegisterExactlyOnePayload.workSteps (countValue problem) (upperValue problem index) + 1))

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier)
    (endTape (BuilderLiteralArgumentSource.inputValues problem index remaining .initial []) inside [])
def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  {state := (machine problem.verifier).acceptState,
   tape := endTape (finalValues problem index remaining) inside (exterior problem index)}

theorem fields_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    baseValues problem index remaining ++
        BuilderRegisterExpression.values (expression problem.verifier) (view (baseValues problem index remaining)) =
      scratchValues problem index remaining ++ [countValue problem, upperValue problem index] := by
  simp only [expression_values, scratchValues, List.append_assoc, List.cons_append, List.nil_append]

/-- One fixed physical program; no source-derived runtime value is a machine parameter. -/
theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining inside) = some (finalConfiguration problem index remaining inside) := by
  have hBase := BuilderLiteralArgumentSource.workRunExact problem index remaining .initial 0 [] plan
    .certificateLength inside [] rfl
  simp only [BuilderLiteralArgumentSource.initialConfiguration, BuilderLiteralArgumentSource.finalConfiguration,
    List.drop_nil] at hBase
  have hUpper := BuilderRegisterExpression.workRunExact (expression problem.verifier) 0 []
    (view (baseValues problem index remaining)) [] inside [] rfl
  simp only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
    List.nil_append, List.append_nil, List.drop_nil, view_ofFn _ (baseValues_length problem index remaining)] at hUpper
  rw [fields_suffix] at hUpper
  have hRange := BuilderRegisterExactlyOnePayload.workRunExact (countValue problem) (upperValue problem index)
    (scratchValues problem index remaining) inside (count_le_upper problem index)
  simp only [BuilderRegisterExactlyOnePayload.initialConfiguration, BuilderRegisterExactlyOnePayload.finalConfiguration,
    BuilderRegisterExactlyOnePayload.finalTape] at hRange
  have hR := AcceptPath.step rangeNode .accept _ 0 _ _ _ (range_mem problem.verifier) hRange (.terminal .accept _)
  have hU := AcceptPath.step (upperNode problem.verifier) .accept _ _ _ _ _ (upper_mem problem.verifier) hUpper hR
  have hPath : AcceptPath (graph problem.verifier) (.node (baseNode problem.verifier).reference)
      .accept (workSteps problem index remaining)
      (endTape (BuilderLiteralArgumentSource.inputValues problem index remaining .initial []) inside [])
      (endTape (finalValues problem index remaining) inside (exterior problem index)) := by
    have h := AcceptPath.step (baseNode problem.verifier) .accept _ _ _ _ _ (base_mem problem.verifier) hBase hU
    simpa only [workSteps, baseSteps, upperSteps, baseValues, finalValues, payloadValues, exterior, Nat.add_zero] using h
  have h := WorkMachineProgramPath.runExact (graph problem.verifier) _ _ _ _ _ (graph_wellFormed problem.verifier) hPath
  have hStart (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node (baseNode problem.verifier).reference) tape =
        workStartConfiguration (machine problem.verifier) tape := rfl
  have hMachine : WorkMachineProgramGraph.machine (graph problem.verifier) = machine problem.verifier := rfl
  rw [hStart, hMachine] at h
  simpa only [initialConfiguration, finalConfiguration, WorkMachineProgramGraph.endpointConfiguration,
    WorkMachineProgramGraph.endpointState, WorkMachineProgramGraph.globalAcceptState, machine_accept] using h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining inside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining inside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining inside)

theorem final_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    finalValues problem index remaining = (scratchValues problem index remaining ++ [countValue problem]) ++
      payloadValues problem index := rfl

theorem final_exterior {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).tape.left = exterior problem index := rfl

theorem final_inside_preserved {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).tape.right =
      (registerWord (payloadValues problem index)).reverse ++
        ((registerWord (scratchValues problem index remaining ++ [countValue problem])).reverse ++ inside) := by
  simp only [finalConfiguration, finalValues, endTape, registerWord_append, List.reverse_append, List.append_assoc]

theorem final_canonical {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hMode : problem.tableauInputMode = .paired) :
    finalValues problem index remaining = (scratchValues problem index remaining ++ [countValue problem]) ++
      BuilderInitialConstraintPayload.lengthValues problem hMode := by
  rw [final_suffix, payload_canonical problem index hMode]

theorem source_canonical_payload {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hMode : problem.tableauInputMode = .paired) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining (BuilderDividerOperands.inside problem.input output)) =
      some
        {state := (machine problem.verifier).acceptState,
         tape := endTape ((scratchValues problem index remaining ++ [countValue problem]) ++
           BuilderInitialConstraintPayload.lengthValues problem hMode)
           (BuilderDividerOperands.inside problem.input output) (exterior problem index)} := by
  simpa only [finalConfiguration, final_canonical problem index remaining hMode] using
    workRunExact problem index remaining (BuilderDividerOperands.inside problem.input output)

theorem payload_initial_slot {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hMode : problem.tableauInputMode = .paired) :
    payloadValues problem index = BuilderInitialConstraintPayload.values problem 2 := by
  rw [BuilderInitialConstraintPayload.paired_length_values problem hMode, payload_canonical problem index hMode]

theorem payload_decode {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hMode : problem.tableauInputMode = .paired) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index) =
      some (problem.initialConstraintSlotDirect 2) := by
  rw [payload_initial_slot problem index hMode, BuilderInitialConstraintPayload.decode_values]

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise (graph verifier) (graph_wellFormed verifier)
theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept (graph verifier)
theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject (graph verifier)
theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := by
  change (0 : Nat) ≠ 1
  decide

def baseSpanPolynomial {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderLiteralArgumentSource.finalSpanBound verifier .initial 0 plan .certificateLength (.constant 0)
def fieldsSpanPolynomial {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial (expression verifier) (baseSpanPolynomial verifier)
def spanPolynomial {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRegisterExactlyOnePayload.spanPolynomial (fieldsSpanPolynomial verifier)
def rawTimePolynomial {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderLiteralArgumentSource.rawTimeBound verifier .initial 0 plan .certificateLength (.constant 0))
    (.add (BuilderRegisterExpression.rawTimePolynomial (expression verifier) (baseSpanPolynomial verifier))
      (.add (BuilderRegisterExactlyOnePayload.rawTimePolynomial (fieldsSpanPolynomial verifier)) (.constant 18)))

/-- The complete actual-source work, all three graph bridges, retained history,
variable-length payload and remaining blank exterior have encoded-size bounds. -/
theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial) :
    (registerWord (finalValues problem index remaining)).length + (exterior problem index).length ≤
        (spanPolynomial problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining ≤ (rawTimePolynomial problem.verifier).eval problem.input.length := by
  have hBase := BuilderLiteralArgumentSource.source_polynomial_bounds problem index remaining .initial 0 [] plan
    .certificateLength (.constant 0) rfl hBody hBalance hRegion (Nat.le_refl 0)
  have hEnvironment :
      (registerWord ([] ++ List.ofFn (view (baseValues problem index remaining) : Fin (Arity problem.verifier) → Nat) ++ [])).length ≤
        (baseSpanPolynomial problem.verifier).eval problem.input.length := by
    rw [List.nil_append, List.append_nil, view_ofFn _ (baseValues_length problem index remaining)]
    exact hBase.1
  have hFields := BuilderRegisterExpression.source_polynomial_bounds (expression problem.verifier)
    (baseSpanPolynomial problem.verifier) problem.input.length [] (view (baseValues problem index remaining)) [] hEnvironment
  have hSpan : (registerWord (scratchValues problem index remaining ++ [countValue problem, upperValue problem index])).length ≤
      (fieldsSpanPolynomial problem.verifier).eval problem.input.length := by
    simpa only [List.nil_append, List.append_nil, view_ofFn _ (baseValues_length problem index remaining),
      fields_suffix, fieldsSpanPolynomial] using hFields.1
  simp only [registerWord_append, List.length_append, registerWord_length,
    List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at hSpan
  have hCount : countValue problem ≤ (fieldsSpanPolynomial problem.verifier).eval problem.input.length := by omega
  have hUpper : upperValue problem index ≤ (fieldsSpanPolynomial problem.verifier).eval problem.input.length := by omega
  have hOlder : (registerWord (scratchValues problem index remaining)).length ≤
      (fieldsSpanPolynomial problem.verifier).eval problem.input.length := by
    rw [registerWord_length]
    omega
  have hPayload := BuilderRegisterExactlyOnePayload.source_polynomial_bounds
    (fieldsSpanPolynomial problem.verifier) problem.input.length (countValue problem) (upperValue problem index)
    (scratchValues problem index remaining) [] hCount hUpper hOlder
  constructor
  · simpa only [finalValues, payloadValues, exterior, spanPolynomial,
      BuilderRegisterExactlyOnePayload.finalConfiguration, BuilderRegisterExactlyOnePayload.finalTape, endTape] using hPayload.1
  · have hBaseTime := hBase.2
    have hFieldsTime := hFields.2
    have hPayloadTime := hPayload.2
    simp only [workSteps, baseSteps, upperSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderInitialLengthPayload
