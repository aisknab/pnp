/-
Copyright (c) 2026 PNP Labs.

One fixed graph derives an ordered exclusion pair from the written count and
clause ordinal. Arithmetic preparation, invalid-slot rejection, frame packing,
safe decrement and the complete row loop are one actual execution.

The input frontier is explicit. No pair, reversed ordinal, validity certificate,
or input-dependent program is supplied. Source-payload extraction, variable
field reads and the complete formula-builder integration remain separate.
-/

import PNP.Concrete.CookLevinBuilderExclusionPairPreparation

namespace PNP.Concrete.CookLevin.BuilderExclusionPairLookup

open BuilderUnaryPolynomial
open BuilderArbitrarySlotHeaderRouter
open BuilderDividerOperands (endTape)
open BuilderExclusionPairSelection (reverseCoordinate selectedPair observePair)
open LocalConstraint (pairCount)
open WorkMachineProgramGraph (Node NodeRef Graph Endpoint endpointConfiguration)
open WorkMachineProgramPath (AcceptPath)

def outputEnvironment (count coordinate : Nat) (index : Fin 25) : Nat :=
  if h : index.val < 20 then BuilderExclusionPairPreparation.arithmeticEnvironment count coordinate ⟨index.val, h⟩
  else
    let result := RawRouter.compareResult 0 (BuilderExclusionPairPreparation.quotient count)
      (BuilderExclusionPairPreparation.boundary count coordinate)
    match index.val with
    | 20 => BuilderRegisterCompareResidual.environment result ⟨0, by decide⟩
    | 21 => BuilderRegisterCompareResidual.environment result ⟨1, by decide⟩
    | 22 => BuilderRegisterCompareResidual.environment result ⟨2, by decide⟩
    | 23 => BuilderRegisterCompareResidual.resultBoundary result
    | _ => BuilderRegisterCompareResidual.resultCoordinate result

def rowFields : List (BuilderRegisterPack.Field 25) :=
  [.constant 0, .constant 1, .argument ⟨24, by decide⟩, .argument ⟨0, by decide⟩]

theorem outputEnvironment_ofFn (count coordinate : Nat) :
    List.ofFn (outputEnvironment count coordinate) = BuilderExclusionPairPreparation.history count coordinate := by
  let result := RawRouter.compareResult 0 (BuilderExclusionPairPreparation.quotient count)
    (BuilderExclusionPairPreparation.boundary count coordinate)
  have hSplit : List.ofFn (outputEnvironment count coordinate) =
      BuilderExclusionPairPreparation.arithmeticValues count coordinate ++
        List.ofFn (BuilderRegisterCompareResidual.environment result) ++
          [BuilderRegisterCompareResidual.resultBoundary result,
            BuilderRegisterCompareResidual.resultCoordinate result] := rfl
  rw [hSplit, BuilderRegisterCompareResidual.environment_ofFn]
  simp only [BuilderExclusionPairPreparation.history, BuilderRegisterCompareResidual.outputValues,
    result, List.append_assoc]

theorem row_values (count coordinate : Nat) (hValid : coordinate < pairCount count) :
    BuilderRegisterPack.values rowFields (outputEnvironment count coordinate) =
      [0, 1, reverseCoordinate count coordinate, count] := by
  have hView : BuilderRegisterPack.values rowFields (outputEnvironment count coordinate) =
      [0, 1, BuilderRegisterCompareResidual.resultCoordinate
        (RawRouter.compareResult 0 (BuilderExclusionPairPreparation.quotient count)
          (BuilderExclusionPairPreparation.boundary count coordinate)), count] := rfl
  have hNotLess : ¬ BuilderExclusionPairPreparation.quotient count <
      BuilderExclusionPairPreparation.boundary count coordinate :=
    Nat.not_lt.mpr ((BuilderExclusionPairPreparation.valid_iff count coordinate).mpr hValid)
  rw [hView, BuilderRegisterCompareResidual.resultCoordinate_eq, if_neg hNotLess,
    BuilderExclusionPairPreparation.valid_residual count coordinate hValid]

def packMachine : WorkMachine :=
  WorkMachineChain.machine (BuilderRegisterPack.machine rowFields 0) BuilderRegisterCountdownControl.decrement
def packSteps (count coordinate : Nat) : Nat :=
  BuilderRegisterPack.workSteps rowFields (outputEnvironment count coordinate) [] + 1 + 2

private theorem chain_run (first second : WorkMachine) (n m : Nat)
    (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

theorem pack_workRunExact (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol)
    (hValid : coordinate < pairCount count) :
    workRunExact? packMachine (packSteps count coordinate)
      (workStartConfiguration packMachine
        (endTape (older ++ BuilderExclusionPairPreparation.history count coordinate) inside [])) =
      some {
        state := packMachine.acceptState
        tape := endTape (older ++ BuilderExclusionPairPreparation.history count coordinate ++
          BuilderInitialRowLoop.frame 0 1 (reverseCoordinate count coordinate) (count - 1)) inside [WorkSymbol.blank] } := by
  have hCount : count - 1 + 1 = count := by
    have h := BuilderExclusionPairPreparation.valid_count count coordinate hValid
    omega
  have hPack := BuilderRegisterPack.workRunExact rowFields 0 older
    (outputEnvironment count coordinate) [] inside [] rfl
  simp only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    outputEnvironment_ofFn, row_values count coordinate hValid, List.append_nil, List.drop_nil] at hPack
  have hDec := BuilderRegisterLessThan.decrement_workRunExact (count - 1)
    (older ++ BuilderExclusionPairPreparation.history count coordinate ++ [0, 1, reverseCoordinate count coordinate])
    inside []
  simp only [hCount, List.append_assoc, List.cons_append, List.nil_append] at hPack hDec
  have hAll := chain_run (BuilderRegisterPack.machine rowFields 0)
    BuilderRegisterCountdownControl.decrement
    (BuilderRegisterPack.workSteps rowFields (outputEnvironment count coordinate) []) 2
    _ _ _ hPack hDec
  simpa only [packMachine, packSteps, BuilderInitialRowLoop.frame,
    List.append_assoc, List.cons_append, List.nil_append] using hAll

/-- The first width-one row attempt consumes the single cell released by decrement. -/
theorem positive_row_frontier (remaining length coordinate : Nat) :
    BuilderInitialRowLoop.finishOutside (remaining + 1) length 1 coordinate [WorkSymbol.blank] = [] := by
  have hPrepared : BuilderInitialRowLoop.preparedOutside 1 coordinate [WorkSymbol.blank] = [] := by
    unfold BuilderInitialRowLoop.preparedOutside
    apply List.drop_eq_nil_iff.mpr
    simp only [registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    omega
  have hAttempt : BuilderInitialRowLoop.attemptOutside 1 coordinate [WorkSymbol.blank] = [] := by
    simp only [BuilderInitialRowLoop.attemptOutside, hPrepared, List.drop_nil]
  have hContinued : BuilderInitialRowLoop.continuedOutside length 1 coordinate remaining [WorkSymbol.blank] = [] := by
    simp only [BuilderInitialRowLoop.continuedOutside, hAttempt, List.drop_nil]
  by_cases hLess : coordinate < 1
  · simp only [BuilderInitialRowLoop.finishOutside, if_pos hLess, hAttempt]
  · simp only [BuilderInitialRowLoop.finishOutside, if_neg hLess, hContinued,
      BuilderRegisterHalve.row_loop_frontier]

def rowNode : Node :=
  {name := 2, program := BuilderExclusionPairRow.machine, onAccept := .accept, onReject := .dead}
def packNode : Node :=
  {name := 1, program := packMachine, onAccept := .node rowNode.reference, onReject := .dead}
def arithmeticNode : Node :=
  {name := 0, program := BuilderExclusionPairPreparation.machine,
    onAccept := .reject, onReject := .node packNode.reference}
def graph : Graph := {nodes := [arithmeticNode, packNode, rowNode], entry := arithmeticNode.reference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph

theorem graph_nodes_length : graph.nodes.length = 3 := rfl

private theorem arithmetic_mem : arithmeticNode ∈ graph.nodes := List.Mem.head _
private theorem pack_mem : packNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)
private theorem row_mem : rowNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
    WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
    WorkMachineChain.noRuleAtAccept first {second with acceptState := second.rejectState} hSecond.2.2.1,
    WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2.2⟩

private theorem pack_good : Good packMachine :=
  chain_good _ _
    ⟨BuilderRegisterPack.rules_pairwise_query_distinct rowFields 0,
      BuilderRegisterPack.noRuleAtAccept rowFields 0, BuilderRegisterPack.noRuleAtReject rowFields 0,
      BuilderRegisterPack.acceptState_ne_rejectState rowFields 0⟩
    BuilderRegisterCountdownControl.decrement_control

theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun left right : Nat => left ≠ right) := by
    change ([0, 1, 2] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact ⟨BuilderExclusionPairPreparation.rules_pairwise_query_distinct,
        BuilderExclusionPairPreparation.noRuleAtAccept, BuilderExclusionPairPreparation.noRuleAtReject,
        BuilderExclusionPairPreparation.acceptState_ne_rejectState⟩
    · exact pack_good
    · exact ⟨BuilderExclusionPairRow.rules_pairwise_query_distinct,
        BuilderExclusionPairRow.noRuleAtAccept, BuilderExclusionPairRow.noRuleAtReject,
        BuilderExclusionPairRow.acceptState_ne_rejectState⟩
  · exact ⟨arithmeticNode, arithmetic_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact ⟨True.intro, ⟨packNode, pack_mem, rfl, rfl⟩⟩
    · exact ⟨⟨rowNode, row_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def endpoint (count coordinate : Nat) : Endpoint := if coordinate < pairCount count then .accept else .reject
def workSteps (count coordinate : Nat) : Nat :=
  BuilderExclusionPairPreparation.workSteps count coordinate + 1 +
    if coordinate < pairCount count then
      packSteps count coordinate + 1 + (BuilderExclusionPairRow.workSteps count coordinate + 1)
    else 0

def resultValues (count coordinate : Nat) (older : List Nat) : List Nat :=
  if coordinate < pairCount count then
    BuilderExclusionPairRow.resultValues count coordinate (older ++ BuilderExclusionPairPreparation.history count coordinate)
  else older ++ BuilderExclusionPairPreparation.history count coordinate

def initialConfiguration (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    WorkConfiguration := workStartConfiguration machine (endTape (older ++ [count, coordinate]) inside [])
def finalConfiguration (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    WorkConfiguration :=
  endpointConfiguration (endpoint count coordinate) (endTape (resultValues count coordinate older) inside [])

private theorem configuration_eq_of_fields (config : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : config.state = state) (hTape : config.tape = tape) :
    config = {state := state, tape := tape} := by
  cases config
  cases hState
  cases hTape
  rfl

private theorem lookup_path (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    AcceptPath graph (.node arithmeticNode.reference) (endpoint count coordinate) (workSteps count coordinate)
      (endTape (older ++ [count, coordinate]) inside [])
      (endTape (resultValues count coordinate older) inside []) := by
  have hPrep := BuilderExclusionPairPreparation.workRunExact count coordinate older inside
  have hPrepTape := BuilderExclusionPairPreparation.final_tape count coordinate older inside
  by_cases hValid : coordinate < pairCount count
  · have hPrepState := (BuilderExclusionPairPreparation.final_valid_iff count coordinate older inside).mpr hValid
    rw [configuration_eq_of_fields _ _ _ hPrepState hPrepTape] at hPrep
    have hPack := pack_workRunExact count coordinate older inside hValid
    have hRow := BuilderExclusionPairRow.workRunExact count coordinate
      (older ++ BuilderExclusionPairPreparation.history count coordinate) inside [WorkSymbol.blank]
    have hRowState := (BuilderExclusionPairRow.final_accept_iff count coordinate
      (older ++ BuilderExclusionPairPreparation.history count coordinate) inside [WorkSymbol.blank]).mpr hValid
    have hRowTape := BuilderExclusionPairRow.final_tape count coordinate
      (older ++ BuilderExclusionPairPreparation.history count coordinate) inside [WorkSymbol.blank]
    have hRemaining : count - 1 = (count - 2) + 1 := by
      have h := BuilderExclusionPairPreparation.valid_count count coordinate hValid
      omega
    rw [hRemaining, positive_row_frontier] at hRowTape
    rw [configuration_eq_of_fields _ _ _ hRowState hRowTape] at hRow
    have hR := AcceptPath.step rowNode .accept _ 0 _ _ _ row_mem hRow (.terminal .accept _)
    have hP := AcceptPath.step packNode .accept _ _ _ _ _ pack_mem hPack hR
    have hA := AcceptPath.stepReject arithmeticNode .accept _ _ _ _ _ arithmetic_mem hPrep hP
    simpa only [endpoint, workSteps, resultValues, if_pos hValid, Nat.add_zero] using hA
  · have hPrepState := (BuilderExclusionPairPreparation.final_invalid_iff count coordinate older inside).mpr (by omega)
    rw [configuration_eq_of_fields _ _ _ hPrepState hPrepTape] at hPrep
    have hA := AcceptPath.step arithmeticNode .reject _ 0 _ _ _ arithmetic_mem hPrep (.terminal .reject _)
    simpa only [endpoint, workSteps, resultValues, if_neg hValid] using hA

theorem workRunExact (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps count coordinate) (initialConfiguration count coordinate older inside) =
      some (finalConfiguration count coordinate older inside) := by
  have h := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed
    (lookup_path count coordinate older inside)
  have hStart (tape : WorkTape) :
      endpointConfiguration (.node arithmeticNode.reference) tape = workStartConfiguration machine tape := rfl
  rw [hStart] at h
  exact h

theorem run_compile_exact (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps count coordinate)
      (encodeWorkConfiguration (initialConfiguration count coordinate older inside)) =
      encodeWorkConfiguration (finalConfiguration count coordinate older inside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact count coordinate older inside)

theorem final_accept_iff (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside).state = machine.acceptState ↔ coordinate < pairCount count := by
  change WorkMachineProgramGraph.endpointState (endpoint count coordinate) = 0 ↔ _
  by_cases hValid : coordinate < pairCount count
  · simp only [endpoint, if_pos hValid, WorkMachineProgramGraph.endpointState]
    exact ⟨fun _ => hValid, fun _ => rfl⟩
  · simp only [endpoint, if_neg hValid, WorkMachineProgramGraph.endpointState]
    constructor
    · intro impossible
      cases impossible
    · intro hInside
      exact False.elim (hValid hInside)

theorem final_reject_iff (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside).state = machine.rejectState ↔ pairCount count ≤ coordinate := by
  change WorkMachineProgramGraph.endpointState (endpoint count coordinate) = 1 ↔ _
  by_cases hValid : coordinate < pairCount count
  · simp only [endpoint, if_pos hValid, WorkMachineProgramGraph.endpointState]
    constructor
    · intro impossible
      cases impossible
    · intro hOutside
      omega
  · have hOutside : pairCount count ≤ coordinate := by omega
    simp only [endpoint, if_neg hValid, WorkMachineProgramGraph.endpointState]
    exact ⟨fun _ => hOutside, fun _ => rfl⟩

theorem final_tape (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside).tape =
      endTape (resultValues count coordinate older) inside [] := rfl

def observedPair (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) : Option (Nat × Nat) :=
  if (finalConfiguration count coordinate older inside).state = machine.acceptState then
    BuilderExclusionPairRow.decodeValues (resultValues count coordinate older)
  else none

theorem observedPair_eq_selectedPair (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    observedPair count coordinate older inside = selectedPair count coordinate := by
  by_cases hValid : coordinate < pairCount count
  · have hAccept := (final_accept_iff count coordinate older inside).mpr hValid
    have hRowAccept := (BuilderExclusionPairRow.final_accept_iff count coordinate
      (older ++ BuilderExclusionPairPreparation.history count coordinate) inside [WorkSymbol.blank]).mpr hValid
    have hRow := BuilderExclusionPairRow.observedPair_eq_selectedPair count coordinate
      (older ++ BuilderExclusionPairPreparation.history count coordinate) inside [WorkSymbol.blank]
    rw [BuilderExclusionPairRow.observedPair, if_pos hRowAccept] at hRow
    simpa only [observedPair, if_pos hAccept, resultValues, if_pos hValid] using hRow
  · have hNotAccept : ¬ (finalConfiguration count coordinate older inside).state = machine.acceptState := by
      intro hAccept
      exact hValid ((final_accept_iff count coordinate older inside).mp hAccept)
    have hNone := (BuilderExclusionPairSelection.selectedPair_none_iff count coordinate).mpr (by omega)
    simp only [observedPair, if_neg hNotAccept, hNone]

theorem workRun_observes_canonical {width : Nat} (variables : List (Fin width)) (coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps variables.length coordinate)
      (initialConfiguration variables.length coordinate older inside) =
      some (finalConfiguration variables.length coordinate older inside) ∧
      observePair variables (observedPair variables.length coordinate older inside) =
        (atMostOneBoundedClauses variables)[coordinate]? := by
  refine ⟨workRunExact variables.length coordinate older inside, ?_⟩
  rw [observedPair_eq_selectedPair, BuilderExclusionPairSelection.selectedPair_observes_canonical]

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

/-- Packing writes the actual count before its safe decrement; the decrement cannot increase span. -/
theorem pack_polynomial_bounds (count coordinate : Nat) (older : List Nat)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ BuilderExclusionPairPreparation.history count coordinate)).length ≤
      bound.eval inputLength) (hValid : coordinate < pairCount count) :
    (registerWord (older ++ BuilderExclusionPairPreparation.history count coordinate ++
      BuilderInitialRowLoop.frame 0 1 (reverseCoordinate count coordinate) (count - 1))).length ≤
        (BuilderRegisterPack.spanPolynomial rowFields bound).eval inputLength ∧
      6 * packSteps count coordinate ≤
        (BuilderRegisterPack.rawTimePolynomial rowFields bound).eval inputLength + 18 := by
  have hPack := BuilderRegisterPack.source_polynomial_bounds rowFields bound inputLength older
    (outputEnvironment count coordinate) [] (by
      simpa only [outputEnvironment_ofFn, List.append_nil] using hSpan)
  have hPackSpace := hPack.1
  simp only [outputEnvironment_ofFn, row_values count coordinate hValid, List.append_nil] at hPackSpace
  have hDecrease :
      (registerWord (older ++ BuilderExclusionPairPreparation.history count coordinate ++
        BuilderInitialRowLoop.frame 0 1 (reverseCoordinate count coordinate) (count - 1))).length ≤
      (registerWord (older ++ BuilderExclusionPairPreparation.history count coordinate ++
        [0, 1, reverseCoordinate count coordinate, count])).length := by
    simp only [BuilderInitialRowLoop.frame, registerWord_append, List.length_append,
      registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    omega
  constructor
  · exact Nat.le_trans hDecrease hPackSpace
  · have hTime := hPack.2
    simp only [packSteps]
    omega

def preparedSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderExclusionPairPreparation.spanPolynomial bound
def rowInputSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial rowFields (preparedSpanPolynomial bound)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (preparedSpanPolynomial bound) (BuilderInitialRowLoop.spanPolynomial (rowInputSpanPolynomial bound))
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderExclusionPairPreparation.rawTimePolynomial bound)
    (.add (BuilderRegisterPack.rawTimePolynomial rowFields (preparedSpanPolynomial bound))
      (.add (BuilderInitialRowLoop.rawTimePolynomial (rowInputSpanPolynomial bound)) (.constant 36)))

/-- Full preparation-plus-lookup bounds, including the invalid branch, all joins and retained history. -/
theorem source_polynomial_bounds (count coordinate : Nat) (older : List Nat)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [count, coordinate])).length ≤ bound.eval inputLength) :
    (registerWord (resultValues count coordinate older)).length ≤ (spanPolynomial bound).eval inputLength ∧
      6 * workSteps count coordinate ≤ (rawTimePolynomial bound).eval inputLength := by
  have hPrep := BuilderExclusionPairPreparation.source_polynomial_bounds count coordinate older bound inputLength hSpan
  by_cases hValid : coordinate < pairCount count
  · have hPrepSpan :
        (registerWord (older ++ BuilderExclusionPairPreparation.history count coordinate)).length ≤
          (preparedSpanPolynomial bound).eval inputLength := by
      simpa only [preparedSpanPolynomial] using hPrep.1
    have hPack := pack_polynomial_bounds count coordinate older
      (preparedSpanPolynomial bound) inputLength hPrepSpan hValid
    have hRowSpan :
        (registerWord (older ++ BuilderExclusionPairPreparation.history count coordinate ++
          BuilderInitialRowLoop.frame 0 1 (reverseCoordinate count coordinate) (count - 1))).length ≤
            (rowInputSpanPolynomial bound).eval inputLength := by
      simpa only [rowInputSpanPolynomial] using hPack.1
    have hRow := BuilderInitialRowLoop.source_polynomial_bounds (count - 1) 0 1
      (reverseCoordinate count coordinate) (older ++ BuilderExclusionPairPreparation.history count coordinate)
      (rowInputSpanPolynomial bound) inputLength hRowSpan
    have hRowSpace :
        (registerWord (resultValues count coordinate older)).length ≤
          (BuilderInitialRowLoop.spanPolynomial (rowInputSpanPolynomial bound)).eval inputLength := by
      simpa only [resultValues, if_pos hValid, BuilderExclusionPairRow.resultValues] using hRow.1
    constructor
    · simp only [spanPolynomial, NatPolynomial.eval_add]
      omega
    · have hPrepTime := hPrep.2
      have hPackTime := hPack.2
      have hRowTime := hRow.2
      simp only [workSteps, if_pos hValid, BuilderExclusionPairRow.workSteps,
        rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
      omega
  · have hPrepSpace :
        (registerWord (resultValues count coordinate older)).length ≤ (preparedSpanPolynomial bound).eval inputLength := by
      simpa only [resultValues, if_neg hValid, preparedSpanPolynomial] using hPrep.1
    constructor
    · simp only [spanPolynomial, NatPolynomial.eval_add]
      omega
    · have hPrepTime := hPrep.2
      simp only [workSteps, if_neg hValid, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
      omega

theorem uniform_polynomial_lookup {width : Nat} (variables : List (Fin width)) (coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [variables.length, coordinate])).length ≤ bound.eval inputLength) :
    ∃ rawSteps, rawSteps ≤ (rawTimePolynomial bound).eval inputLength ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (initialConfiguration variables.length coordinate older inside)) =
        encodeWorkConfiguration (finalConfiguration variables.length coordinate older inside) ∧
      observePair variables (observedPair variables.length coordinate older inside) =
        (atMostOneBoundedClauses variables)[coordinate]? := by
  refine ⟨6 * workSteps variables.length coordinate,
    (source_polynomial_bounds variables.length coordinate older bound inputLength hSpan).2,
    run_compile_exact variables.length coordinate older inside, ?_⟩
  rw [observedPair_eq_selectedPair, BuilderExclusionPairSelection.selectedPair_observes_canonical]

end PNP.Concrete.CookLevin.BuilderExclusionPairLookup
