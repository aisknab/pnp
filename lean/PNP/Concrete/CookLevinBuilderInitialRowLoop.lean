/-
Copyright (c) 2026 PNP Labs.

One fixed physical loop selects among consecutive rows of widths W, W+1, ...
using the newest ordinary countdown register. Each continued attempt retains
its actual comparison history and installs a new four-register frame.
No row count, coordinate, branch answer or execution certificate generates
the machine. This is the initial-row cursor, not the complete formula builder.
-/

import PNP.Concrete.CookLevinBuilderRegisterCompareResidual
import PNP.Concrete.CookLevinBuilderUnaryTagMatch
import PNP.Concrete.CookLevinBuilderInitialLengthSelection

namespace PNP.Concrete.CookLevin.BuilderInitialRowLoop

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderArbitrarySlotHeaderRouter
open WorkMachineProgramGraph (Node Endpoint Graph NodeRef)
open WorkMachineProgramPath (AcceptPath)

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

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
    WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
    WorkMachineChain.noRuleAtAccept first
      {second with acceptState := second.rejectState} hSecond.2.2.1,
    WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2.2⟩

private theorem increment_good : Good BuilderConstraintRegionAssembly.Increment.machine := by
  refine ⟨BuilderConstraintRegionAssembly.Increment.rules_pairwise_query_distinct,
    BuilderConstraintRegionAssembly.Increment.noRuleAtAccept, ?_,
    BuilderConstraintRegionAssembly.Increment.acceptState_ne_rejectState⟩
  intro rule hMem
  decide +revert

namespace Advance

def lengthIndex : Fin 9 := ⟨0, by decide⟩
def widthIndex : Fin 9 := ⟨7, by decide⟩
def coordinateIndex : Fin 9 := ⟨8, by decide⟩
def remainingIndex : Fin 9 := ⟨3, by decide⟩
def argument (index : Fin 9) : BuilderRegisterExpression.Expr 9 := .argument index
def copyMachine (index : Fin 9) (afterCount : Nat) : WorkMachine :=
  BuilderRegisterExpression.machine (argument index) afterCount
def copySteps (index : Fin 9) (environment : Fin 9 → Nat) (after : List Nat) : Nat :=
  BuilderRegisterExpression.workSteps (argument index) environment after

def values (environment : Fin 9 → Nat) : List Nat :=
  [environment lengthIndex + 1, environment widthIndex + 1,
    environment coordinateIndex, environment remainingIndex]

/-- The four copy offsets are 8, 2, 2 and 8; only their first two outputs increment. -/
def machine : WorkMachine :=
  WorkMachineChain.machine (copyMachine lengthIndex 0)
    (WorkMachineChain.machine BuilderConstraintRegionAssembly.Increment.machine
      (WorkMachineChain.machine (copyMachine widthIndex 1)
        (WorkMachineChain.machine BuilderConstraintRegionAssembly.Increment.machine
          (WorkMachineChain.machine (copyMachine coordinateIndex 2) (copyMachine remainingIndex 3)))))

def workSteps (environment : Fin 9 → Nat) : Nat :=
  copySteps lengthIndex environment [] + 1 +
    (2 + 1 + (copySteps widthIndex environment [environment lengthIndex + 1] + 1 +
      (2 + 1 + (copySteps coordinateIndex environment
        [environment lengthIndex + 1, environment widthIndex + 1] + 1 +
          copySteps remainingIndex environment
            [environment lengthIndex + 1, environment widthIndex + 1, environment coordinateIndex]))))

private theorem copy_run (index : Fin 9) (afterCount : Nat) (older : List Nat)
    (environment : Fin 9 → Nat) (after : List Nat) (inside outside : List WorkSymbol)
    (hAfter : after.length = afterCount) :
    workRunExact? (copyMachine index afterCount) (copySteps index environment after)
      (workStartConfiguration (copyMachine index afterCount)
        (endTape (older ++ List.ofFn environment ++ after) inside outside)) =
      some {
        state := (copyMachine index afterCount).acceptState
        tape := endTape (older ++ List.ofFn environment ++ after ++ [environment index])
          inside (outside.drop (environment index + 1)) } := by
  have h := BuilderRegisterExpression.workRunExact (argument index) afterCount
    older environment after inside outside hAfter
  simpa only [copyMachine, copySteps, BuilderRegisterExpression.initialConfiguration,
    BuilderRegisterExpression.finalConfiguration, argument, BuilderRegisterExpression.values,
    registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, Nat.add_comm] using h

theorem workRunExact (older : List Nat) (environment : Fin 9 → Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps environment)
      (workStartConfiguration machine (endTape (older ++ List.ofFn environment) inside outside)) =
      some {
        state := machine.acceptState
        tape := endTape (older ++ List.ofFn environment ++ values environment)
          inside (outside.drop (registerWord (values environment)).length) } := by
  let a := environment lengthIndex
  let b := environment widthIndex
  let c := environment coordinateIndex
  let d := environment remainingIndex
  let outA := (outside.drop (a + 1)).drop 1
  let outB := (outA.drop (b + 1)).drop 1
  let outC := outB.drop (c + 1)
  have hA := copy_run lengthIndex 0 older environment [] inside outside rfl
  have hIA := BuilderConstraintRegionAssembly.Increment.workRunExact
    (older ++ List.ofFn environment) a inside (outside.drop (a + 1))
  have hB := copy_run widthIndex 1 older environment [a + 1] inside outA rfl
  have hIB := BuilderConstraintRegionAssembly.Increment.workRunExact
    (older ++ List.ofFn environment ++ [a + 1]) b inside (outA.drop (b + 1))
  have hC := copy_run coordinateIndex 2 older environment [a + 1, b + 1] inside outB rfl
  have hD := copy_run remainingIndex 3 older environment [a + 1, b + 1, c] inside outC rfl
  simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append] at hA hIA hIB hB hC hD
  have hCD := chain_run _ _ _ _ _ _ _ hC hD
  have hICD := chain_run _ _ _ _ _ _ _ hIB hCD
  have hBICD := chain_run _ _ _ _ _ _ _ hB hICD
  have hIBICD := chain_run _ _ _ _ _ _ _ hIA hBICD
  have hAll := chain_run _ _ _ _ _ _ _ hA hIBICD
  have hDrop : outC.drop (d + 1) = outside.drop (registerWord (values environment)).length := by
    simp only [outC, outB, outA, List.drop_drop, values, registerWord_length,
      List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    congr 1
    dsimp only [a, b, c, d]
    omega
  rw [hDrop] at hAll
  simpa only [machine, workSteps, values, a, b, c, d, List.append_assoc] using hAll

private theorem copy_good (index : Fin 9) (afterCount : Nat) : Good (copyMachine index afterCount) :=
  ⟨BuilderRegisterExpression.rules_pairwise_query_distinct (argument index) afterCount,
    BuilderRegisterExpression.noRuleAtAccept (argument index) afterCount,
    BuilderRegisterExpression.noRuleAtReject (argument index) afterCount,
    BuilderRegisterExpression.acceptState_ne_rejectState (argument index) afterCount⟩

private theorem good : Good machine :=
  chain_good _ _ (copy_good lengthIndex 0)
    (chain_good _ _ increment_good (chain_good _ _ (copy_good widthIndex 1)
      (chain_good _ _ increment_good
        (chain_good _ _ (copy_good coordinateIndex 2) (copy_good remainingIndex 3)))))

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := good.1
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := good.2.1
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := good.2.2.1
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := good.2.2.2

end Advance

def frame (length width coordinate remaining : Nat) : List Nat := [length, width, coordinate, remaining]
def prepareEnvironment (length width coordinate remaining : Nat) (index : Fin 4) : Nat :=
  match index.val with
  | 0 => length
  | 1 => width
  | 2 => coordinate
  | _ => remaining
def prepareFields : List (BuilderRegisterPack.Field 4) :=
  [.argument ⟨2, by decide⟩, .argument ⟨1, by decide⟩]
def prepareSteps (length width coordinate remaining : Nat) : Nat :=
  BuilderRegisterPack.workSteps prepareFields (prepareEnvironment length width coordinate remaining) []

theorem prepareEnvironment_ofFn (length width coordinate remaining : Nat) :
    List.ofFn (prepareEnvironment length width coordinate remaining) = frame length width coordinate remaining := rfl

def attemptValues (length width coordinate remaining : Nat) : List Nat :=
  frame length width coordinate remaining ++
    BuilderRegisterCompareResidual.outputValues (RawRouter.compareResult 0 coordinate width)
def attemptEnvironment (length width coordinate remaining : Nat) (index : Fin 9) : Nat :=
  let result := RawRouter.compareResult 0 coordinate width
  match index.val with
  | 0 => length
  | 1 => width
  | 2 => coordinate
  | 3 => remaining
  | 4 => BuilderRegisterCompareResidual.environment result ⟨0, by decide⟩
  | 5 => BuilderRegisterCompareResidual.environment result ⟨1, by decide⟩
  | 6 => BuilderRegisterCompareResidual.environment result ⟨2, by decide⟩
  | 7 => BuilderRegisterCompareResidual.resultBoundary result
  | _ => BuilderRegisterCompareResidual.resultCoordinate result

theorem attemptEnvironment_ofFn (length width coordinate remaining : Nat) :
    List.ofFn (attemptEnvironment length width coordinate remaining) =
      attemptValues length width coordinate remaining := by
  have hSplit : List.ofFn (attemptEnvironment length width coordinate remaining) =
      frame length width coordinate remaining ++
        List.ofFn (BuilderRegisterCompareResidual.environment (RawRouter.compareResult 0 coordinate width)) ++
          [BuilderRegisterCompareResidual.resultBoundary (RawRouter.compareResult 0 coordinate width),
            BuilderRegisterCompareResidual.resultCoordinate (RawRouter.compareResult 0 coordinate width)] := rfl
  rw [hSplit, BuilderRegisterCompareResidual.environment_ofFn]
  simp only [attemptValues, BuilderRegisterCompareResidual.outputValues, List.append_assoc]

theorem attemptValues_length (length width coordinate remaining : Nat) :
    (attemptValues length width coordinate remaining).length = 9 := by
  rw [attemptValues, List.length_append, BuilderRegisterCompareResidual.outputValues_length]
  rfl

theorem advance_values (length width coordinate remaining : Nat) (hNotLess : ¬ coordinate < width) :
    Advance.values (attemptEnvironment length width coordinate remaining) =
      frame (length + 1) (width + 1) (coordinate - width) remaining := by
  simp only [Advance.values, attemptEnvironment, Advance.lengthIndex, Advance.widthIndex,
    Advance.coordinateIndex, Advance.remainingIndex, BuilderRegisterCompareResidual.resultBoundary_eq,
    BuilderRegisterCompareResidual.resultCoordinate_eq, if_neg hNotLess, frame]

def zeroReference : NodeRef := {name := 0, startState := (BuilderUnaryTagMatch.machine 0).startState}
def advanceNode : Node :=
  {name := 4, program := Advance.machine, onAccept := .node zeroReference, onReject := .dead}
def compareNode : Node :=
  {name := 3, program := BuilderRegisterCompareResidual.machine,
   onAccept := .accept, onReject := .node advanceNode.reference}
def prepareNode : Node :=
  {name := 2, program := BuilderRegisterPack.machine prepareFields 0,
   onAccept := .node compareNode.reference, onReject := .dead}
def decrementNode : Node :=
  {name := 1, program := BuilderRegisterCountdownControl.decrement,
   onAccept := .node prepareNode.reference, onReject := .dead}
def zeroNode : Node :=
  {name := 0, program := BuilderUnaryTagMatch.machine 0,
   onAccept := .reject, onReject := .node decrementNode.reference}
def graph : Graph :=
  {nodes := [zeroNode, decrementNode, prepareNode, compareNode, advanceNode], entry := zeroNode.reference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph

theorem graph_nodes_length : graph.nodes.length = 5 := rfl

private theorem zero_mem : zeroNode ∈ graph.nodes := List.Mem.head _
private theorem decrement_mem : decrementNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)
private theorem prepare_mem : prepareNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem compare_mem : compareNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem advance_mem : advanceNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0, 1, 2, 3, 4] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl
    · exact ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct 0,
        BuilderUnaryTagMatch.noRuleAtAccept 0, BuilderUnaryTagMatch.noRuleAtReject 0,
        BuilderUnaryTagMatch.acceptState_ne_rejectState 0⟩
    · exact BuilderRegisterCountdownControl.decrement_control
    · exact ⟨BuilderRegisterPack.rules_pairwise_query_distinct prepareFields 0,
        BuilderRegisterPack.noRuleAtAccept prepareFields 0, BuilderRegisterPack.noRuleAtReject prepareFields 0,
        BuilderRegisterPack.acceptState_ne_rejectState prepareFields 0⟩
    · exact ⟨BuilderRegisterCompareResidual.rules_pairwise_query_distinct,
        BuilderRegisterCompareResidual.noRuleAtAccept, BuilderRegisterCompareResidual.noRuleAtReject,
        BuilderRegisterCompareResidual.acceptState_ne_rejectState⟩
    · exact ⟨Advance.rules_pairwise_query_distinct, Advance.noRuleAtAccept,
        Advance.noRuleAtReject, Advance.acceptState_ne_rejectState⟩
  · exact ⟨zeroNode, zero_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl
    · exact ⟨True.intro, ⟨decrementNode, decrement_mem, rfl, rfl⟩⟩
    · exact ⟨⟨prepareNode, prepare_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨compareNode, compare_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, ⟨advanceNode, advance_mem, rfl, rfl⟩⟩
    · exact ⟨⟨zeroNode, zero_mem, rfl, rfl⟩, True.intro⟩

def preparedOutside (width coordinate : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (WorkSymbol.blank :: outside).drop (registerWord [coordinate, width]).length
def attemptOutside (width coordinate : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (preparedOutside width coordinate outside).drop
    (BuilderRegisterCompareResidual.allocatedCells (RawRouter.compareResult 0 coordinate width))
def continuedOutside (length width coordinate remaining : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (attemptOutside width coordinate outside).drop
    (registerWord (frame (length + 1) (width + 1) (coordinate - width) remaining)).length

/-- Exact retained history, including every unsuccessful row and final frame. -/
def finishValues : Nat → Nat → Nat → Nat → List Nat
  | 0, length, width, coordinate => frame length width coordinate 0
  | remaining + 1, length, width, coordinate =>
      attemptValues length width coordinate remaining ++
        if coordinate < width then []
        else finishValues remaining (length + 1) (width + 1) (coordinate - width)

def finishOutside : Nat → Nat → Nat → Nat → List WorkSymbol → List WorkSymbol
  | 0, _, _, _, outside => outside
  | remaining + 1, length, width, coordinate, outside =>
      if coordinate < width then attemptOutside width coordinate outside
      else finishOutside remaining (length + 1) (width + 1) (coordinate - width)
        (continuedOutside length width coordinate remaining outside)

def endpoint : Nat → Nat → Nat → Endpoint
  | 0, _, _ => .reject
  | remaining + 1, width, coordinate =>
      if coordinate < width then .accept else endpoint remaining (width + 1) (coordinate - width)

def workSteps : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 4
  | remaining + 1, length, width, coordinate =>
      3 + 1 + (2 + 1 + (prepareSteps length width coordinate remaining + 1 +
        (BuilderRegisterCompareResidual.workSteps coordinate width + 1 +
          if coordinate < width then 0 else
            Advance.workSteps (attemptEnvironment length width coordinate remaining) + 1 +
              workSteps remaining (length + 1) (width + 1) (coordinate - width))))

def initialConfiguration (remaining length width coordinate : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ frame length width coordinate remaining) inside outside)
def finalConfiguration (remaining length width coordinate : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  WorkMachineProgramGraph.endpointConfiguration (endpoint remaining width coordinate)
    (endTape (older ++ finishValues remaining length width coordinate) inside
      (finishOutside remaining length width coordinate outside))

private theorem prepare_run (length width coordinate remaining : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? (BuilderRegisterPack.machine prepareFields 0)
      (prepareSteps length width coordinate remaining)
      (workStartConfiguration (BuilderRegisterPack.machine prepareFields 0)
        (endTape (older ++ frame length width coordinate remaining) inside (WorkSymbol.blank :: outside))) =
      some {
        state := (BuilderRegisterPack.machine prepareFields 0).acceptState
        tape := endTape (older ++ frame length width coordinate remaining ++ [coordinate, width])
          inside (preparedOutside width coordinate outside) } := by
  have h := BuilderRegisterPack.workRunExact prepareFields 0 older
    (prepareEnvironment length width coordinate remaining) [] inside (WorkSymbol.blank :: outside) rfl
  have hValues : BuilderRegisterPack.values prepareFields
      (prepareEnvironment length width coordinate remaining) = [coordinate, width] := rfl
  simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    prepareEnvironment_ofFn, hValues, List.append_nil, prepareSteps, preparedOutside] using h

private theorem configuration_eq_of_fields (config : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : config.state = state) (hTape : config.tape = tape) :
    config = {state := state, tape := tape} := by
  cases config with
  | mk currentState currentTape =>
      change currentState = state at hState
      change currentTape = tape at hTape
      subst currentState
      subst currentTape
      rfl

private theorem comparison_tape (length width coordinate remaining : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (BuilderRegisterCompareResidual.finalConfiguration coordinate width
      (older ++ frame length width coordinate remaining) inside
      (preparedOutside width coordinate outside)).tape =
      endTape (older ++ attemptValues length width coordinate remaining) inside
        (attemptOutside width coordinate outside) := by
  change endTape ((older ++ frame length width coordinate remaining) ++
    BuilderRegisterCompareResidual.outputValues (RawRouter.compareResult 0 coordinate width))
    inside (attemptOutside width coordinate outside) = _
  simp only [attemptValues, List.append_assoc]

/-- The induction follows the physically decremented counter; no path is supplied by a caller. -/
private theorem loop_path (remaining length width coordinate : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    AcceptPath graph (.node zeroNode.reference) (endpoint remaining width coordinate)
      (workSteps remaining length width coordinate)
      (endTape (older ++ frame length width coordinate remaining) inside outside)
      (endTape (older ++ finishValues remaining length width coordinate) inside
        (finishOutside remaining length width coordinate outside)) := by
  induction remaining generalizing length width coordinate older outside with
  | zero =>
      have hZero := BuilderUnaryTagMatch.accept_workRunExact 0
        (older ++ [length, width, coordinate]) inside outside
      simp only [BuilderUnaryTagMatch.workSteps, Nat.min_self, Nat.mul_zero, Nat.zero_add,
        List.append_assoc, List.cons_append, List.nil_append] at hZero
      have h := AcceptPath.step zeroNode .reject 3 0 _ _ _ zero_mem hZero (.terminal .reject _)
      exact h
  | succ remaining ih =>
      have hZero := BuilderUnaryTagMatch.reject_workRunExact 0 (remaining + 1)
        (older ++ [length, width, coordinate]) inside outside (by omega)
      simp only [BuilderUnaryTagMatch.workSteps, Nat.min_zero, Nat.mul_zero, Nat.zero_add,
        List.append_assoc, List.cons_append, List.nil_append] at hZero
      have hDec := BuilderRegisterLessThan.decrement_workRunExact remaining
        (older ++ [length, width, coordinate]) inside outside
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hDec
      have hPrep := prepare_run length width coordinate remaining older inside outside
      have hCompare := BuilderRegisterCompareResidual.workRunExact coordinate width
        (older ++ frame length width coordinate remaining) inside (preparedOutside width coordinate outside)
      have hTape := comparison_tape length width coordinate remaining older inside outside
      by_cases hLess : coordinate < width
      · have hState := (BuilderRegisterCompareResidual.final_accept_iff coordinate width
          (older ++ frame length width coordinate remaining) inside
          (preparedOutside width coordinate outside)).mpr hLess
        rw [configuration_eq_of_fields _ _ _ hState hTape] at hCompare
        have hC := AcceptPath.step compareNode .accept _ 0 _ _ _ compare_mem hCompare (.terminal .accept _)
        have hP := AcceptPath.step prepareNode .accept _ _ _ _ _ prepare_mem hPrep hC
        have hD := AcceptPath.step decrementNode .accept 2 _ _ _ _ decrement_mem hDec hP
        have hZ := AcceptPath.stepReject zeroNode .accept 3 _ _ _ _ zero_mem hZero hD
        simpa only [endpoint, workSteps, finishValues, finishOutside, if_pos hLess,
          List.append_nil, Nat.add_zero, frame] using hZ
      · have hState := (BuilderRegisterCompareResidual.final_reject_iff coordinate width
          (older ++ frame length width coordinate remaining) inside
          (preparedOutside width coordinate outside)).mpr (by omega)
        rw [configuration_eq_of_fields _ _ _ hState hTape] at hCompare
        have hAdvance := Advance.workRunExact older
          (attemptEnvironment length width coordinate remaining) inside (attemptOutside width coordinate outside)
        simp only [attemptEnvironment_ofFn, advance_values _ _ _ _ hLess] at hAdvance
        have hTail := ih (length + 1) (width + 1) (coordinate - width)
          (older ++ attemptValues length width coordinate remaining)
          (continuedOutside length width coordinate remaining outside)
        have hA := AcceptPath.step advanceNode _ _ _ _ _ _ advance_mem hAdvance hTail
        have hC := AcceptPath.stepReject compareNode _ _ _ _ _ _ compare_mem hCompare hA
        have hP := AcceptPath.step prepareNode _ _ _ _ _ _ prepare_mem hPrep hC
        have hD := AcceptPath.step decrementNode _ 2 _ _ _ _ decrement_mem hDec hP
        have hZ := AcceptPath.stepReject zeroNode _ 3 _ _ _ _ zero_mem hZero hD
        simpa only [endpoint, workSteps, finishValues, finishOutside, if_neg hLess,
          List.append_assoc, frame] using hZ

theorem workRunExact (remaining length width coordinate : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps remaining length width coordinate)
      (initialConfiguration remaining length width coordinate older inside outside) =
      some (finalConfiguration remaining length width coordinate older inside outside) := by
  have h := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed
    (loop_path remaining length width coordinate older inside outside)
  have hStart (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node zeroNode.reference) tape =
        workStartConfiguration machine tape := rfl
  rw [hStart] at h
  exact h

theorem run_compile_exact (remaining length width coordinate : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps remaining length width coordinate)
      (encodeWorkConfiguration (initialConfiguration remaining length width coordinate older inside outside)) =
      encodeWorkConfiguration (finalConfiguration remaining length width coordinate older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact remaining length width coordinate older inside outside)

theorem endpoint_eq_locate (remaining width coordinate : Nat) :
    endpoint remaining width coordinate =
      match BuilderInitialLengthSelection.locate remaining width coordinate with
      | none => .reject
      | some _ => .accept := by
  induction remaining generalizing width coordinate with
  | zero => rfl
  | succ remaining ih =>
      by_cases hLess : coordinate < width
      · simp only [endpoint, BuilderInitialLengthSelection.locate, if_pos hLess]
      · simp only [endpoint, BuilderInitialLengthSelection.locate, if_neg hLess]
        rw [ih]
        cases BuilderInitialLengthSelection.locate remaining (width + 1) (coordinate - width) <;> rfl

theorem final_accept_iff (remaining length width coordinate : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration remaining length width coordinate older inside outside).state = machine.acceptState ↔
      (BuilderInitialLengthSelection.locate remaining width coordinate).isSome = true := by
  change WorkMachineProgramGraph.endpointState (endpoint remaining width coordinate) = 0 ↔ _
  rw [endpoint_eq_locate]
  cases BuilderInitialLengthSelection.locate remaining width coordinate with
  | none =>
      change ((1 : Nat) = 0 ↔ false = true)
      decide
  | some found =>
      change ((0 : Nat) = 0 ↔ true = true)
      decide

theorem final_reject_iff (remaining length width coordinate : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration remaining length width coordinate older inside outside).state = machine.rejectState ↔
      BuilderInitialLengthSelection.locate remaining width coordinate = none := by
  change WorkMachineProgramGraph.endpointState (endpoint remaining width coordinate) = 1 ↔ _
  rw [endpoint_eq_locate]
  cases BuilderInitialLengthSelection.locate remaining width coordinate with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some found =>
      constructor
      · intro impossible
        change (0 : Nat) = 1 at impossible
        cases impossible
      · intro impossible
        cases impossible

theorem final_tape (remaining length width coordinate : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration remaining length width coordinate older inside outside).tape =
      endTape (older ++ finishValues remaining length width coordinate) inside
        (finishOutside remaining length width coordinate outside) := rfl

theorem source_final_accept_iff {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration (problem.certificateLimit + 1) 0
      (problem.dimensions.tapeWidth problem.tableauInputMode) coordinate older inside outside).state =
        machine.acceptState ↔ (BuilderInitialLengthSelection.selectedLength problem coordinate).isSome = true :=
  final_accept_iff _ _ _ _ _ _ _

theorem source_final_reject_iff {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) (coordinate : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration (problem.certificateLimit + 1) 0
      (problem.dimensions.tapeWidth problem.tableauInputMode) coordinate older inside outside).state =
        machine.rejectState ↔ problem.pairedCellsWidthDirect ≤ coordinate := by
  rw [final_reject_iff]
  exact BuilderInitialLengthSelection.selectedLength_none_iff problem hMode coordinate

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

/-- The selected length and offset occupy the first/last positions of the final nine-register suffix. -/
theorem found_suffix (remaining length width coordinate : Nat) (position : Fin remaining) (offset : Nat)
    (hFound : BuilderInitialLengthSelection.locate remaining width coordinate = some (position, offset)) :
    ∃ history middle : List Nat, middle.length = 7 ∧
      finishValues remaining length width coordinate = history ++ [length + position.val] ++ middle ++ [offset] := by
  induction remaining generalizing length width coordinate offset with
  | zero => cases position.isLt
  | succ remaining ih =>
      by_cases hLess : coordinate < width
      · simp only [BuilderInitialLengthSelection.locate, if_pos hLess] at hFound
        have hPair := Option.some.inj hFound
        have hPosition := congrArg Prod.fst hPair
        have hOffset := congrArg Prod.snd hPair
        dsimp only at hPosition hOffset
        subst position
        subst offset
        refine ⟨[], [width, coordinate, remaining] ++
          BuilderRegisterLessThan.resultValues (RawRouter.compareResult 0 coordinate width) ++ [width], ?_, ?_⟩
        · simp only [List.length_append, List.length_cons, List.length_nil,
            BuilderRegisterLessThan.resultValues_length]
        · simp only [finishValues, if_pos hLess, List.append_nil, attemptValues,
            BuilderRegisterCompareResidual.outputValues, BuilderRegisterCompareResidual.resultBoundary_eq,
            BuilderRegisterCompareResidual.resultCoordinate_eq, frame, Nat.add_zero,
            List.nil_append, List.append_assoc, List.cons_append]
      · cases hTail : BuilderInitialLengthSelection.locate remaining (width + 1) (coordinate - width) with
        | none =>
            simp only [BuilderInitialLengthSelection.locate, if_neg hLess, hTail, Option.map_none] at hFound
            cases hFound
        | some found =>
            rcases found with ⟨tailPosition, tailOffset⟩
            have hMap : some (tailPosition.succ, tailOffset) = some (position, offset) := by
              simpa only [BuilderInitialLengthSelection.locate, if_neg hLess, hTail, Option.map_some] using hFound
            have hPair := Option.some.inj hMap
            have hPosition := congrArg Prod.fst hPair
            have hOffset := congrArg Prod.snd hPair
            dsimp only at hPosition hOffset
            subst position
            subst offset
            rcases ih (length + 1) (width + 1) (coordinate - width) tailPosition tailOffset hTail with
              ⟨history, middle, hMiddle, hValues⟩
            refine ⟨attemptValues length width coordinate remaining ++ history, middle, hMiddle, ?_⟩
            have hLength : (length + 1) + tailPosition.val = length + tailPosition.succ.val := by
              change (length + 1) + tailPosition.val = length + (tailPosition.val + 1)
              omega
            simp only [finishValues, if_neg hLess, hValues, hLength, List.append_assoc]

private theorem frame_span (length width coordinate remaining : Nat) :
    (registerWord (frame length width coordinate remaining)).length =
      length + width + coordinate + remaining + 4 := by
  simp only [frame, registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  omega

private theorem pair_span (coordinate width : Nat) :
    (registerWord [coordinate, width]).length = coordinate + width + 2 := by
  simp only [registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  omega

private theorem next_le (coordinate width : Nat) :
    BuilderRegisterCompareResidual.resultCoordinate (RawRouter.compareResult 0 coordinate width) ≤ coordinate := by
  rw [BuilderRegisterCompareResidual.resultCoordinate_eq]
  split <;> omega

private theorem attempt_span (length width coordinate remaining : Nat) :
    (registerWord (attemptValues length width coordinate remaining)).length =
      length + 3 * width + 2 * coordinate + remaining +
        BuilderRegisterCompareResidual.resultCoordinate (RawRouter.compareResult 0 coordinate width) + 9 := by
  have hRestore : (registerWord (BuilderRegisterLessThan.resultValues
      (RawRouter.compareResult 0 coordinate width))).length = coordinate + width + 3 :=
    BuilderRegisterLessThan.clearedSpan_eq coordinate width
  simp only [attemptValues, BuilderRegisterCompareResidual.outputValues, registerWord_append,
    List.length_append, frame_span, pair_span, hRestore, BuilderRegisterCompareResidual.resultBoundary_eq]
  omega

private theorem attempt_span_le (length width coordinate remaining bound : Nat)
    (hLength : length ≤ bound) (hWidth : width ≤ bound)
    (hCoordinate : coordinate ≤ bound) (hRemaining : remaining ≤ bound) :
    (registerWord (attemptValues length width coordinate remaining)).length ≤ 9 * bound + 13 := by
  rw [attempt_span]
  have hNext := next_le coordinate width
  omega

/-- A linear allowance for each retained attempt, multiplied only by the physical countdown. -/
theorem finish_span_le (remaining length width coordinate bound : Nat)
    (hLength : length + remaining ≤ bound) (hWidth : width + remaining ≤ bound)
    (hCoordinate : coordinate ≤ bound) :
    (registerWord (finishValues remaining length width coordinate)).length ≤
      (remaining + 1) * (9 * bound + 13) := by
  induction remaining generalizing length width coordinate with
  | zero =>
      simp only [finishValues, frame_span, Nat.zero_add, Nat.one_mul]
      omega
  | succ remaining ih =>
      have hAttempt := attempt_span_le length width coordinate remaining bound
        (by omega) (by omega) hCoordinate (by omega)
      by_cases hLess : coordinate < width
      · simp only [finishValues, if_pos hLess, List.append_nil]
        have hNonneg : 0 ≤ (remaining + 1) * (9 * bound + 13) := Nat.zero_le _
        rw [Nat.succ_mul]
        omega
      · have hTail := ih (length + 1) (width + 1) (coordinate - width)
          (by omega) (by omega) (by omega)
        simp only [finishValues, if_neg hLess, registerWord_append, List.length_append]
        rw [Nat.succ_mul]
        omega

def carrierBound (bound : Nat) : Nat := 16 * bound + 32
def copyBound (bound : Nat) : Nat := 4 * (bound + 1) * (bound + 1) + 9 * (bound + 1) + 5

private theorem argument_time_le {arity : Nat} (index : Fin arity) (environment : Fin arity → Nat)
    (after : List Nat) (bound : Nat)
    (hSpan : (registerWord (List.ofFn environment ++ after)).length ≤ bound) :
    BuilderRegisterExpression.workSteps (.argument index) environment after ≤ copyBound bound := by
  have h := BuilderRegisterExpression.space_time_bounds (.argument index) [] environment after bound (by
    simpa only [List.nil_append] using hSpan)
  exact h.2

private theorem prepare_steps_le (length width coordinate remaining bound : Nat)
    (hLength : length ≤ bound) (hWidth : width ≤ bound)
    (hCoordinate : coordinate ≤ bound) (hRemaining : remaining ≤ bound) :
    prepareSteps length width coordinate remaining ≤ 2 * copyBound (carrierBound bound) + 2 := by
  have hFirst := argument_time_le (⟨2, by decide⟩ : Fin 4)
    (prepareEnvironment length width coordinate remaining) [] (carrierBound bound) (by
      rw [List.append_nil, prepareEnvironment_ofFn, frame_span]
      simp only [carrierBound]
      omega)
  have hSecond := argument_time_le (⟨1, by decide⟩ : Fin 4)
    (prepareEnvironment length width coordinate remaining) [coordinate] (carrierBound bound) (by
      rw [prepareEnvironment_ofFn, registerWord_append, List.length_append, frame_span]
      simp only [registerWord_length, List.length_cons, List.length_nil,
        List.sum_cons, List.sum_nil, carrierBound]
      omega)
  change BuilderRegisterExpression.workSteps (.argument ⟨2, by decide⟩)
      (prepareEnvironment length width coordinate remaining) [] + 1 +
    (BuilderRegisterExpression.workSteps (.argument ⟨1, by decide⟩)
      (prepareEnvironment length width coordinate remaining) [coordinate] + 1 + 0) ≤ _
  omega

private theorem advance_steps_le (length width coordinate remaining bound : Nat)
    (hLength : length ≤ bound) (hWidth : width ≤ bound)
    (hCoordinate : coordinate ≤ bound) (hRemaining : remaining ≤ bound) :
    Advance.workSteps (attemptEnvironment length width coordinate remaining) ≤
      4 * copyBound (carrierBound bound) + 9 := by
  let environment := attemptEnvironment length width coordinate remaining
  have hSpan : (registerWord (List.ofFn environment)).length ≤ 9 * bound + 13 := by
    rw [show List.ofFn environment = attemptValues length width coordinate remaining from
      attemptEnvironment_ofFn _ _ _ _]
    exact attempt_span_le _ _ _ _ _ hLength hWidth hCoordinate hRemaining
  have hSpanNumeric : (List.ofFn environment).length + (List.ofFn environment).sum ≤ 9 * bound + 13 := by
    simpa only [registerWord_length] using hSpan
  have hL : environment Advance.lengthIndex ≤ bound := hLength
  have hW : environment Advance.widthIndex ≤ bound := by
    change BuilderRegisterCompareResidual.resultBoundary (RawRouter.compareResult 0 coordinate width) ≤ bound
    rw [BuilderRegisterCompareResidual.resultBoundary_eq]
    exact hWidth
  have hC : environment Advance.coordinateIndex ≤ bound :=
    Nat.le_trans (next_le coordinate width) hCoordinate
  have h0 := argument_time_le Advance.lengthIndex environment [] (carrierBound bound) (by
    simp only [List.append_nil, carrierBound]
    omega)
  have h7 := argument_time_le Advance.widthIndex environment [environment Advance.lengthIndex + 1]
    (carrierBound bound) (by
      rw [registerWord_append, List.length_append]
      simp only [registerWord_length, List.length_cons, List.length_nil,
        List.sum_cons, List.sum_nil, carrierBound]
      omega)
  have h8 := argument_time_le Advance.coordinateIndex environment
    [environment Advance.lengthIndex + 1, environment Advance.widthIndex + 1] (carrierBound bound) (by
      rw [registerWord_append, List.length_append]
      simp only [registerWord_length, List.length_cons, List.length_nil,
        List.sum_cons, List.sum_nil, carrierBound]
      omega)
  have h3 := argument_time_le Advance.remainingIndex environment
    [environment Advance.lengthIndex + 1, environment Advance.widthIndex + 1, environment Advance.coordinateIndex]
    (carrierBound bound) (by
      rw [registerWord_append, List.length_append]
      simp only [registerWord_length, List.length_cons, List.length_nil,
        List.sum_cons, List.sum_nil, carrierBound]
      omega)
  change Advance.workSteps environment ≤ _
  simp only [Advance.workSteps, Advance.copySteps, Advance.argument]
  omega

def carrierPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 16) bound) (.constant 32)

/-- Six physical copies, the comparator/restorer, and all tests/increments/bridges. -/
def stepRawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add
    (.mul (.constant 36) (BuilderRegisterExpression.timePolynomial
      (Advance.argument Advance.lengthIndex) (carrierPolynomial bound)))
    (BuilderRegisterCompareResidual.rawTimePolynomial (carrierPolynomial bound))) (.constant 126)

private theorem step_time_le (length width coordinate remaining : Nat)
    (bound : NatPolynomial) (inputLength : Nat)
    (hLength : length ≤ bound.eval inputLength) (hWidth : width ≤ bound.eval inputLength)
    (hCoordinate : coordinate ≤ bound.eval inputLength) (hRemaining : remaining ≤ bound.eval inputLength) :
    6 * (3 + 1 + (2 + 1 + (prepareSteps length width coordinate remaining + 1 +
      (BuilderRegisterCompareResidual.workSteps coordinate width + 1 +
        (Advance.workSteps (attemptEnvironment length width coordinate remaining) + 1))))) ≤
      (stepRawTimePolynomial bound).eval inputLength := by
  have hPrep := prepare_steps_le _ _ _ _ _ hLength hWidth hCoordinate hRemaining
  have hAdvance := advance_steps_le _ _ _ _ _ hLength hWidth hCoordinate hRemaining
  have hCompare := (BuilderRegisterCompareResidual.source_polynomial_bounds coordinate width []
    (carrierPolynomial bound) inputLength (by
      rw [List.nil_append, pair_span]
      simp only [carrierPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
      omega)).2
  simp only [stepRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, BuilderRegisterExpression.timePolynomial_eval, Advance.argument,
    BuilderRegisterExpression.timeBound, carrierPolynomial, copyBound, carrierBound] at hPrep hAdvance hCompare ⊢
  omega

private theorem step_time_positive (bound : NatPolynomial) (inputLength : Nat) :
    24 ≤ (stepRawTimePolynomial bound).eval inputLength := by
  simp only [stepRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
  omega

theorem raw_time_le (remaining length width coordinate : Nat) (bound : NatPolynomial) (inputLength : Nat)
    (hLength : length + remaining ≤ bound.eval inputLength)
    (hWidth : width + remaining ≤ bound.eval inputLength)
    (hCoordinate : coordinate ≤ bound.eval inputLength) :
    6 * workSteps remaining length width coordinate ≤
      (remaining + 1) * (stepRawTimePolynomial bound).eval inputLength := by
  induction remaining generalizing length width coordinate with
  | zero =>
      simpa only [workSteps, Nat.zero_add, Nat.one_mul] using step_time_positive bound inputLength
  | succ remaining ih =>
      have hStep := step_time_le length width coordinate remaining bound inputLength
        (by omega) (by omega) hCoordinate (by omega)
      have hProduct : (remaining + 1 + 1) * (stepRawTimePolynomial bound).eval inputLength =
          (remaining + 1) * (stepRawTimePolynomial bound).eval inputLength +
            (stepRawTimePolynomial bound).eval inputLength :=
        Nat.succ_mul (remaining + 1) _
      by_cases hLess : coordinate < width
      · simp only [workSteps, if_pos hLess]
        rw [hProduct]
        omega
      · have hTail := ih (length + 1) (width + 1) (coordinate - width) (by omega) (by omega) (by omega)
        simp only [workSteps, if_neg hLess]
        rw [hProduct]
        omega

def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add bound (.mul (.add bound (.constant 1)) (.add (.mul (.constant 9) bound) (.constant 13)))
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.add bound (.constant 1)) (stepRawTimePolynomial bound)

/-- The complete loop and retained history are polynomial in the encoded input frame, not the row value alone. -/
theorem source_polynomial_bounds (remaining length width coordinate : Nat) (older : List Nat)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ frame length width coordinate remaining)).length ≤ bound.eval inputLength) :
    (registerWord (older ++ finishValues remaining length width coordinate)).length ≤
        (spanPolynomial bound).eval inputLength ∧
      6 * workSteps remaining length width coordinate ≤ (rawTimePolynomial bound).eval inputLength := by
  rw [registerWord_append, List.length_append, frame_span] at hSpan
  have hLength : length + remaining ≤ bound.eval inputLength := by omega
  have hWidth : width + remaining ≤ bound.eval inputLength := by omega
  have hCoordinate : coordinate ≤ bound.eval inputLength := by omega
  have hCount : remaining + 1 ≤ bound.eval inputLength + 1 := by omega
  have hSpace := finish_span_le remaining length width coordinate (bound.eval inputLength)
    hLength hWidth hCoordinate
  have hTime := raw_time_le remaining length width coordinate bound inputLength hLength hWidth hCoordinate
  have hSpaceProduct := Nat.mul_le_mul_right (9 * bound.eval inputLength + 13) hCount
  have hTimeProduct := Nat.mul_le_mul_right ((stepRawTimePolynomial bound).eval inputLength) hCount
  constructor
  · rw [registerWord_append, List.length_append]
    simp only [spanPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
    omega
  · simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderInitialRowLoop
