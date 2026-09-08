/-
Copyright (c) 2026 PNP Labs.

A fixed outer loop carries source input length and fuel through every row
attempt. It reuses the existing row machine with a physically packed
one-attempt budget, then copies a uniform metadata frame before continuing.
No runtime history length generates control or becomes a register address.
Preparing the initial source frame and complete formula emission remain due.
-/

import PNP.Concrete.CookLevinBuilderRegisterHalve

namespace PNP.Concrete.CookLevin.BuilderInitialRowCarry

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open WorkMachineProgramGraph (Node Endpoint Graph NodeRef)
open WorkMachineProgramPath (AcceptPath)

private def environment {arity : Nat} (data : List Nat) (index : Fin arity) : Nat :=
  data[index.val]?.getD 0
private theorem environment_ofFn {arity : Nat} (data : List Nat) (hLength : data.length = arity) :
    List.ofFn (environment data : Fin arity → Nat) = data := by
  subst arity
  have h : (environment data : Fin data.length → Nat) = fun index => data[index.val] := by
    funext index
    simp only [environment, List.getElem?_eq_getElem index.isLt, Option.getD_some]
  rw [h]
  exact List.ofFn_getElem

def frame (inputLength fuel length width coordinate remaining : Nat) : List Nat :=
  [inputLength, fuel, length, width, coordinate, remaining]
def foundStage (inputLength fuel length width coordinate remaining : Nat) : List Nat :=
  frame inputLength fuel length width coordinate remaining ++
    List.ofFn (BuilderInitialRowLoop.attemptEnvironment length width coordinate 0)
def advanceStage (inputLength fuel length width coordinate remaining : Nat) : List Nat :=
  foundStage inputLength fuel length width coordinate remaining ++
    BuilderInitialRowLoop.frame (length + 1) (width + 1) (coordinate - width) 0

theorem frame_length (inputLength fuel length width coordinate remaining : Nat) :
    (frame inputLength fuel length width coordinate remaining).length = 6 := rfl
theorem foundStage_length (inputLength fuel length width coordinate remaining : Nat) :
    (foundStage inputLength fuel length width coordinate remaining).length = 15 := rfl
theorem advanceStage_length (inputLength fuel length width coordinate remaining : Nat) :
    (advanceStage inputLength fuel length width coordinate remaining).length = 19 := rfl

def prepareFields : List (BuilderRegisterPack.Field 6) :=
  [.argument ⟨2, by decide⟩, .argument ⟨3, by decide⟩, .argument ⟨4, by decide⟩, .constant 1]
def foundFields : List (BuilderRegisterPack.Field 15) :=
  [.argument ⟨0, by decide⟩, .argument ⟨1, by decide⟩, .argument ⟨2, by decide⟩,
   .argument ⟨3, by decide⟩, .argument ⟨4, by decide⟩, .argument ⟨5, by decide⟩]
def advanceFields : List (BuilderRegisterPack.Field 19) :=
  [.argument ⟨0, by decide⟩, .argument ⟨1, by decide⟩, .argument ⟨15, by decide⟩,
   .argument ⟨16, by decide⟩, .argument ⟨17, by decide⟩, .argument ⟨5, by decide⟩]

private theorem prepare_values (inputLength fuel length width coordinate remaining : Nat) :
    BuilderRegisterPack.values prepareFields
        (environment (frame inputLength fuel length width coordinate remaining)) =
      BuilderInitialRowLoop.frame length width coordinate 1 := rfl
private theorem found_values (inputLength fuel length width coordinate remaining : Nat) :
    BuilderRegisterPack.values foundFields
        (environment (foundStage inputLength fuel length width coordinate remaining)) =
      frame inputLength fuel length width coordinate remaining := rfl
private theorem advance_values (inputLength fuel length width coordinate remaining : Nat) :
    BuilderRegisterPack.values advanceFields
        (environment (advanceStage inputLength fuel length width coordinate remaining)) =
      frame inputLength fuel (length + 1) (width + 1) (coordinate - width) remaining := rfl

private theorem stage_eq (inputLength fuel length width coordinate remaining : Nat) :
    frame inputLength fuel length width coordinate remaining ++
        BuilderInitialRowLoop.finishValues 1 length width coordinate =
      if coordinate < width then foundStage inputLength fuel length width coordinate remaining
      else advanceStage inputLength fuel length width coordinate remaining := by
  by_cases hLess : coordinate < width <;>
    simp only [BuilderInitialRowLoop.finishValues, hLess, ite_true, ite_false, foundStage,
      advanceStage, BuilderInitialRowLoop.attemptEnvironment_ofFn, List.append_nil, List.append_assoc]

def zeroReference : NodeRef := {name := 0, startState := (BuilderUnaryTagMatch.machine 0).startState}
def foundNode : Node :=
  {name := 4, program := BuilderRegisterPack.machine foundFields 0, onAccept := .accept, onReject := .dead}
def advanceNode : Node :=
  {name := 5, program := BuilderRegisterPack.machine advanceFields 0,
   onAccept := .node zeroReference, onReject := .dead}
def rowNode : Node :=
  {name := 3, program := BuilderInitialRowLoop.machine,
   onAccept := .node foundNode.reference, onReject := .node advanceNode.reference}
def prepareNode : Node :=
  {name := 2, program := BuilderRegisterPack.machine prepareFields 0,
   onAccept := .node rowNode.reference, onReject := .dead}
def decrementNode : Node :=
  {name := 1, program := BuilderRegisterCountdownControl.decrement,
   onAccept := .node prepareNode.reference, onReject := .dead}
def zeroNode : Node :=
  {name := 0, program := BuilderUnaryTagMatch.machine 0,
   onAccept := .reject, onReject := .node decrementNode.reference}
def graph : Graph :=
  {nodes := [zeroNode, decrementNode, prepareNode, rowNode, foundNode, advanceNode], entry := zeroNode.reference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph
theorem graph_nodes_length : graph.nodes.length = 6 := rfl

private theorem zeroNode_mem : zeroNode ∈ graph.nodes := List.Mem.head _

private theorem decrementNode_mem : decrementNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)

private theorem prepareNode_mem : prepareNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

private theorem rowNode_mem : rowNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

private theorem foundNode_mem : foundNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

private theorem advanceNode_mem : advanceNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

private theorem pack_good {arity : Nat} (fields : List (BuilderRegisterPack.Field arity)) :
    (BuilderRegisterPack.machine fields 0).rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
      WorkMachineProgramGraph.NoRuleAt (BuilderRegisterPack.machine fields 0)
        (BuilderRegisterPack.machine fields 0).acceptState ∧
      WorkMachineProgramGraph.NoRuleAt (BuilderRegisterPack.machine fields 0)
        (BuilderRegisterPack.machine fields 0).rejectState ∧
      (BuilderRegisterPack.machine fields 0).acceptState ≠ (BuilderRegisterPack.machine fields 0).rejectState :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct fields 0,
    BuilderRegisterPack.noRuleAtAccept fields 0, BuilderRegisterPack.noRuleAtReject fields 0,
    BuilderRegisterPack.acceptState_ne_rejectState fields 0⟩

theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0, 1, 2, 3, 4, 5] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct 0,
        BuilderUnaryTagMatch.noRuleAtAccept 0, BuilderUnaryTagMatch.noRuleAtReject 0,
        BuilderUnaryTagMatch.acceptState_ne_rejectState 0⟩
    · exact BuilderRegisterCountdownControl.decrement_control
    · exact pack_good prepareFields
    · exact ⟨BuilderInitialRowLoop.rules_pairwise_query_distinct,
        BuilderInitialRowLoop.noRuleAtAccept, BuilderInitialRowLoop.noRuleAtReject,
        BuilderInitialRowLoop.acceptState_ne_rejectState⟩
    · exact pack_good foundFields
    · exact pack_good advanceFields
  · exact ⟨zeroNode, zeroNode_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨True.intro, ⟨decrementNode, decrementNode_mem, rfl, rfl⟩⟩
    · exact ⟨⟨prepareNode, prepareNode_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨rowNode, rowNode_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨foundNode, foundNode_mem, rfl, rfl⟩, ⟨advanceNode, advanceNode_mem, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨zeroNode, zeroNode_mem, rfl, rfl⟩, True.intro⟩

def finishValues : Nat → Nat → Nat → Nat → Nat → Nat → List Nat
  | 0, inputLength, fuel, length, width, coordinate => frame inputLength fuel length width coordinate 0
  | remaining + 1, inputLength, fuel, length, width, coordinate =>
      if coordinate < width then foundStage inputLength fuel length width coordinate remaining ++
        frame inputLength fuel length width coordinate remaining
      else advanceStage inputLength fuel length width coordinate remaining ++
        finishValues remaining inputLength fuel (length + 1) (width + 1) (coordinate - width)

def prepareSteps (inputLength fuel length width coordinate remaining : Nat) : Nat :=
  BuilderRegisterPack.workSteps prepareFields
    (environment (frame inputLength fuel length width coordinate remaining)) []
def foundSteps (inputLength fuel length width coordinate remaining : Nat) : Nat :=
  BuilderRegisterPack.workSteps foundFields
    (environment (foundStage inputLength fuel length width coordinate remaining)) []
def advanceSteps (inputLength fuel length width coordinate remaining : Nat) : Nat :=
  BuilderRegisterPack.workSteps advanceFields
    (environment (advanceStage inputLength fuel length width coordinate remaining)) []
def workSteps : Nat → Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, _, _ => 4
  | remaining + 1, inputLength, fuel, length, width, coordinate =>
      3 + 1 + (2 + 1 + (prepareSteps inputLength fuel length width coordinate remaining + 1 +
        (BuilderInitialRowLoop.workSteps 1 length width coordinate + 1 +
          if coordinate < width then foundSteps inputLength fuel length width coordinate remaining + 1
          else advanceSteps inputLength fuel length width coordinate remaining + 1 +
            workSteps remaining inputLength fuel (length + 1) (width + 1) (coordinate - width))))

def initialConfiguration (remaining inputLength fuel length width coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ frame inputLength fuel length width coordinate remaining) inside [])
def finalConfiguration (remaining inputLength fuel length width coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  WorkMachineProgramGraph.endpointConfiguration (BuilderInitialRowLoop.endpoint remaining width coordinate)
    (endTape (older ++ finishValues remaining inputLength fuel length width coordinate) inside [])

private theorem pack_run {arity : Nat} (fields : List (BuilderRegisterPack.Field arity))
    (data older : List Nat) (inside outside : List WorkSymbol) (hLength : data.length = arity) :
    workRunExact? (BuilderRegisterPack.machine fields 0)
      (BuilderRegisterPack.workSteps fields (environment data) [])
      (workStartConfiguration (BuilderRegisterPack.machine fields 0) (endTape (older ++ data) inside outside)) =
      some {
        state := (BuilderRegisterPack.machine fields 0).acceptState
        tape := endTape (older ++ data ++ BuilderRegisterPack.values fields (environment data))
          inside (outside.drop (registerWord (BuilderRegisterPack.values fields (environment data))).length) } := by
  have h := BuilderRegisterPack.workRunExact fields 0 older (environment data) [] inside outside rfl
  simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    environment_ofFn data hLength, List.append_nil] using h

private theorem prepare_run (inputLength fuel length width coordinate remaining : Nat)
    (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? (BuilderRegisterPack.machine prepareFields 0)
      (prepareSteps inputLength fuel length width coordinate remaining)
      (workStartConfiguration (BuilderRegisterPack.machine prepareFields 0)
        (endTape (older ++ frame inputLength fuel length width coordinate remaining) inside [.blank])) =
      some {
        state := (BuilderRegisterPack.machine prepareFields 0).acceptState
        tape := endTape (older ++ frame inputLength fuel length width coordinate remaining ++
          BuilderInitialRowLoop.frame length width coordinate 1) inside [] } := by
  have h := pack_run prepareFields (frame inputLength fuel length width coordinate remaining)
    older inside [.blank] rfl
  rw [prepare_values] at h
  have hDrop : ([WorkSymbol.blank].drop (registerWord (BuilderInitialRowLoop.frame length width coordinate 1)).length) = [] := by
    apply List.drop_eq_nil_iff.mpr
    simp only [BuilderInitialRowLoop.frame, registerWord_length, List.length_cons, List.length_nil]
    omega
  simpa only [prepareSteps, hDrop] using h

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

private theorem row_run (inputLength fuel length width coordinate remaining : Nat)
    (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? BuilderInitialRowLoop.machine (BuilderInitialRowLoop.workSteps 1 length width coordinate)
      (workStartConfiguration BuilderInitialRowLoop.machine
        (endTape (older ++ frame inputLength fuel length width coordinate remaining ++
          BuilderInitialRowLoop.frame length width coordinate 1) inside [])) =
      some {
        state := if coordinate < width then BuilderInitialRowLoop.machine.acceptState else BuilderInitialRowLoop.machine.rejectState
        tape := endTape (older ++ (if coordinate < width then foundStage inputLength fuel length width coordinate remaining
          else advanceStage inputLength fuel length width coordinate remaining)) inside [] } := by
  have hState : (BuilderInitialRowLoop.finalConfiguration 1 length width coordinate
      (older ++ frame inputLength fuel length width coordinate remaining) inside []).state =
      if coordinate < width then BuilderInitialRowLoop.machine.acceptState else BuilderInitialRowLoop.machine.rejectState := by
    by_cases hLess : coordinate < width <;>
      simp only [BuilderInitialRowLoop.finalConfiguration, BuilderInitialRowLoop.endpoint,
        hLess, WorkMachineProgramGraph.endpointConfiguration,
        WorkMachineProgramGraph.endpointState] <;> rfl
  have hTape : (BuilderInitialRowLoop.finalConfiguration 1 length width coordinate
      (older ++ frame inputLength fuel length width coordinate remaining) inside []).tape =
      endTape (older ++ (if coordinate < width then foundStage inputLength fuel length width coordinate remaining
        else advanceStage inputLength fuel length width coordinate remaining)) inside [] := by
    simp only [BuilderInitialRowLoop.finalConfiguration, WorkMachineProgramGraph.endpointConfiguration,
      BuilderRegisterHalve.row_loop_frontier, List.append_assoc, stage_eq]
  have h := BuilderInitialRowLoop.workRunExact 1 length width coordinate
    (older ++ frame inputLength fuel length width coordinate remaining) inside []
  rw [configuration_eq_of_fields _ _ _ hState hTape] at h
  exact h

/-- Induction follows the actual outer counter, not a supplied row-selection trace. -/
private theorem loop_path (remaining inputLength fuel length width coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) :
    AcceptPath graph (.node zeroNode.reference) (BuilderInitialRowLoop.endpoint remaining width coordinate)
      (workSteps remaining inputLength fuel length width coordinate)
      (endTape (older ++ frame inputLength fuel length width coordinate remaining) inside [])
      (endTape (older ++ finishValues remaining inputLength fuel length width coordinate) inside []) := by
  induction remaining generalizing length width coordinate older with
  | zero =>
      have hZero := BuilderUnaryTagMatch.accept_workRunExact 0
        (older ++ [inputLength, fuel, length, width, coordinate]) inside []
      simp only [BuilderUnaryTagMatch.workSteps, Nat.min_self, Nat.mul_zero, Nat.zero_add,
        List.append_assoc, List.cons_append, List.nil_append] at hZero
      have h := AcceptPath.step zeroNode .reject 3 0 _ _ _ zeroNode_mem hZero (.terminal .reject _)
      exact h
  | succ remaining ih =>
      have hZero := BuilderUnaryTagMatch.reject_workRunExact 0 (remaining + 1)
        (older ++ [inputLength, fuel, length, width, coordinate]) inside [] (by omega)
      simp only [BuilderUnaryTagMatch.workSteps, Nat.min_zero, Nat.mul_zero, Nat.zero_add,
        List.append_assoc, List.cons_append, List.nil_append] at hZero
      have hDec := BuilderRegisterLessThan.decrement_workRunExact remaining
        (older ++ [inputLength, fuel, length, width, coordinate]) inside []
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hDec
      have hPrepare := prepare_run inputLength fuel length width coordinate remaining older inside
      have hRow := row_run inputLength fuel length width coordinate remaining older inside
      simp only [List.append_assoc] at hPrepare hRow
      have hR : AcceptPath graph (.node rowNode.reference)
          (BuilderInitialRowLoop.endpoint (remaining + 1) width coordinate)
          (BuilderInitialRowLoop.workSteps 1 length width coordinate + 1 +
            if coordinate < width then foundSteps inputLength fuel length width coordinate remaining + 1
            else advanceSteps inputLength fuel length width coordinate remaining + 1 +
              workSteps remaining inputLength fuel (length + 1) (width + 1) (coordinate - width))
          (endTape (older ++ (frame inputLength fuel length width coordinate remaining ++
            BuilderInitialRowLoop.frame length width coordinate 1)) inside [])
          (endTape (older ++ finishValues (remaining + 1) inputLength fuel length width coordinate) inside []) := by
        by_cases hLess : coordinate < width
        · simp only [if_pos hLess] at hRow
          have hFound := pack_run foundFields (foundStage inputLength fuel length width coordinate remaining)
            older inside [] rfl
          rw [found_values] at hFound
          simp only [List.drop_nil, List.append_assoc] at hFound
          have hF := AcceptPath.step foundNode .accept _ 0 _ _ _ foundNode_mem hFound (.terminal .accept _)
          have hA := AcceptPath.step rowNode .accept _ _ _ _ _ rowNode_mem hRow hF
          simpa only [BuilderInitialRowLoop.endpoint, if_pos hLess, finishValues, foundSteps,
            List.append_assoc, Nat.add_zero] using hA
        · simp only [if_neg hLess] at hRow
          have hAdvance := pack_run advanceFields (advanceStage inputLength fuel length width coordinate remaining)
            older inside [] rfl
          rw [advance_values] at hAdvance
          simp only [List.drop_nil, List.append_assoc] at hAdvance
          have hTail := ih (length + 1) (width + 1) (coordinate - width)
            (older ++ advanceStage inputLength fuel length width coordinate remaining)
          simp only [List.append_assoc] at hTail
          have hA := AcceptPath.step advanceNode _ _ _ _ _ _ advanceNode_mem hAdvance hTail
          have hR := AcceptPath.stepReject rowNode _ _ _ _ _ _ rowNode_mem hRow hA
          simpa only [BuilderInitialRowLoop.endpoint, if_neg hLess, finishValues, advanceSteps,
            List.append_assoc] using hR
      have hP := AcceptPath.step prepareNode _ _ _ _ _ _ prepareNode_mem hPrepare hR
      have hD := AcceptPath.step decrementNode _ 2 _ _ _ _ decrementNode_mem hDec hP
      have hZ := AcceptPath.stepReject zeroNode _ 3 _ _ _ _ zeroNode_mem hZero hD
      simpa only [workSteps, prepareSteps, frame] using hZ

theorem workRunExact (remaining inputLength fuel length width coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps remaining inputLength fuel length width coordinate)
      (initialConfiguration remaining inputLength fuel length width coordinate older inside) =
      some (finalConfiguration remaining inputLength fuel length width coordinate older inside) := by
  have h := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed
    (loop_path remaining inputLength fuel length width coordinate older inside)
  have hStart (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node zeroNode.reference) tape =
        workStartConfiguration machine tape := rfl
  have hMachine : WorkMachineProgramGraph.machine graph = machine := rfl
  rw [hStart, hMachine] at h
  simpa only [initialConfiguration, finalConfiguration] using h

theorem run_compile_exact (remaining inputLength fuel length width coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps remaining inputLength fuel length width coordinate)
      (encodeWorkConfiguration (initialConfiguration remaining inputLength fuel length width coordinate older inside)) =
      encodeWorkConfiguration (finalConfiguration remaining inputLength fuel length width coordinate older inside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExact remaining inputLength fuel length width coordinate older inside)

theorem final_tape (remaining inputLength fuel length width coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration remaining inputLength fuel length width coordinate older inside).tape =
      endTape (older ++ finishValues remaining inputLength fuel length width coordinate) inside [] := rfl
theorem final_frontier (remaining inputLength fuel length width coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration remaining inputLength fuel length width coordinate older inside).tape.left = [] := rfl

theorem final_accept_iff (remaining inputLength fuel length width coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration remaining inputLength fuel length width coordinate older inside).state = machine.acceptState ↔
      (BuilderInitialLengthSelection.locate remaining width coordinate).isSome = true := by
  have hState : (finalConfiguration remaining inputLength fuel length width coordinate older inside).state =
      (BuilderInitialRowLoop.finalConfiguration remaining length width coordinate older inside []).state := rfl
  have hAccept : machine.acceptState = BuilderInitialRowLoop.machine.acceptState := rfl
  rw [hState, hAccept]
  exact BuilderInitialRowLoop.final_accept_iff remaining length width coordinate older inside []

theorem final_reject_iff (remaining inputLength fuel length width coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration remaining inputLength fuel length width coordinate older inside).state = machine.rejectState ↔
      BuilderInitialLengthSelection.locate remaining width coordinate = none := by
  have hState : (finalConfiguration remaining inputLength fuel length width coordinate older inside).state =
      (BuilderInitialRowLoop.finalConfiguration remaining length width coordinate older inside []).state := rfl
  have hReject : machine.rejectState = BuilderInitialRowLoop.machine.rejectState := rfl
  rw [hState, hReject]
  exact BuilderInitialRowLoop.final_reject_iff remaining length width coordinate older inside []

/-- A uniform newest frame retains both actual source fields at every found row. -/
theorem found_suffix (remaining inputLength fuel length width coordinate : Nat)
    (position : Fin remaining) (offset : Nat)
    (hFound : BuilderInitialLengthSelection.locate remaining width coordinate = some (position, offset)) :
    ∃ history : List Nat, finishValues remaining inputLength fuel length width coordinate =
      history ++ frame inputLength fuel (length + position.val) (width + position.val) offset
        (remaining - (position.val + 1)) := by
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
        refine ⟨foundStage inputLength fuel length width coordinate remaining, ?_⟩
        simp only [finishValues, if_pos hLess, Nat.add_zero, Nat.zero_add, Nat.add_sub_cancel]
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
            rcases ih (length + 1) (width + 1) (coordinate - width) tailPosition tailOffset hTail with ⟨history, hValues⟩
            refine ⟨advanceStage inputLength fuel length width coordinate remaining ++ history, ?_⟩
            have hLength : (length + 1) + tailPosition.val = length + tailPosition.succ.val := by
              change (length + 1) + tailPosition.val = length + (tailPosition.val + 1)
              omega
            have hWidth : (width + 1) + tailPosition.val = width + tailPosition.succ.val := by
              change (width + 1) + tailPosition.val = width + (tailPosition.val + 1)
              omega
            have hRemaining : remaining - (tailPosition.val + 1) =
                remaining + 1 - (tailPosition.succ.val + 1) := by
              change remaining - (tailPosition.val + 1) = remaining + 1 - (tailPosition.val + 1 + 1)
              omega
            simp only [finishValues, if_neg hLess, hValues, hLength, hWidth, hRemaining, List.append_assoc]

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

private theorem frame_span (inputLength fuel length width coordinate remaining : Nat) :
    (registerWord (frame inputLength fuel length width coordinate remaining)).length =
      inputLength + fuel + length + width + coordinate + remaining + 6 := by
  simp only [frame, registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  omega

private theorem frame_span_le (inputLength fuel length width coordinate remaining bound : Nat)
    (hInput : inputLength ≤ bound) (hFuel : fuel ≤ bound) (hLength : length ≤ bound)
    (hWidth : width ≤ bound) (hCoordinate : coordinate ≤ bound) (hRemaining : remaining ≤ bound) :
    (registerWord (frame inputLength fuel length width coordinate remaining)).length ≤ 6 * bound + 6 := by
  rw [frame_span]
  omega

private theorem stage_span_le (inputLength fuel length width coordinate remaining bound : Nat)
    (hInput : inputLength ≤ bound) (hFuel : fuel ≤ bound) (hLength : length + 1 ≤ bound)
    (hWidth : width + 1 ≤ bound) (hCoordinate : coordinate ≤ bound) (hRemaining : remaining ≤ bound) :
    (registerWord (if coordinate < width then foundStage inputLength fuel length width coordinate remaining
      else advanceStage inputLength fuel length width coordinate remaining)).length ≤ 24 * bound + 32 := by
  have hFrame := frame_span_le inputLength fuel length width coordinate remaining bound
    hInput hFuel (by omega) (by omega) hCoordinate hRemaining
  have hRow := BuilderInitialRowLoop.finish_span_le 1 length width coordinate bound hLength hWidth hCoordinate
  rw [← stage_eq, registerWord_append, List.length_append]
  omega

theorem finish_span_le (remaining inputLength fuel length width coordinate bound : Nat)
    (hInput : inputLength ≤ bound) (hFuel : fuel ≤ bound) (hLength : length + remaining ≤ bound)
    (hWidth : width + remaining ≤ bound) (hCoordinate : coordinate ≤ bound) :
    (registerWord (finishValues remaining inputLength fuel length width coordinate)).length ≤
      (remaining + 1) * (30 * bound + 38) := by
  induction remaining generalizing length width coordinate with
  | zero =>
      simp only [finishValues, frame_span, Nat.zero_add, Nat.one_mul]
      omega
  | succ remaining ih =>
      have hStage := stage_span_le inputLength fuel length width coordinate remaining bound
        hInput hFuel (by omega) (by omega) hCoordinate (by omega)
      have hProduct : (remaining + 1 + 1) * (30 * bound + 38) =
          (remaining + 1) * (30 * bound + 38) + (30 * bound + 38) :=
        Nat.succ_mul (remaining + 1) _
      by_cases hLess : coordinate < width
      · have hFrame := frame_span_le inputLength fuel length width coordinate remaining bound
          hInput hFuel (by omega) (by omega) hCoordinate (by omega)
        simp only [if_pos hLess] at hStage
        simp only [finishValues, if_pos hLess, registerWord_append, List.length_append]
        rw [hProduct]
        omega
      · have hTail := ih (length + 1) (width + 1) (coordinate - width) (by omega) (by omega) (by omega)
        simp only [if_neg hLess] at hStage
        simp only [finishValues, if_neg hLess, registerWord_append, List.length_append]
        rw [hProduct]
        omega

private theorem pack_time {arity : Nat} (fields : List (BuilderRegisterPack.Field arity))
    (data : List Nat) (bound : NatPolynomial) (inputSize : Nat)
    (hLength : data.length = arity) (hSpan : (registerWord data).length ≤ bound.eval inputSize) :
    6 * BuilderRegisterPack.workSteps fields (environment data) [] ≤
      (BuilderRegisterPack.rawTimePolynomial fields bound).eval inputSize := by
  exact (BuilderRegisterPack.source_polynomial_bounds fields bound inputSize [] (environment data) [] (by
    simpa only [environment_ofFn data hLength, List.nil_append, List.append_nil] using hSpan)).2

def frameSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 6) bound) (.constant 6)
def rowSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 4) bound) (.constant 5)
def stageSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 24) bound) (.constant 32)
def stepRawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterPack.rawTimePolynomial prepareFields (frameSpanPolynomial bound))
    (.add (BuilderInitialRowLoop.rawTimePolynomial (rowSpanPolynomial bound))
      (.add (BuilderRegisterPack.rawTimePolynomial foundFields (stageSpanPolynomial bound))
        (.add (BuilderRegisterPack.rawTimePolynomial advanceFields (stageSpanPolynomial bound)) (.constant 60))))

theorem raw_time_le (remaining inputLength fuel length width coordinate : Nat)
    (bound : NatPolynomial) (inputSize : Nat)
    (hInput : inputLength ≤ bound.eval inputSize) (hFuel : fuel ≤ bound.eval inputSize)
    (hLength : length + remaining ≤ bound.eval inputSize)
    (hWidth : width + remaining ≤ bound.eval inputSize)
    (hCoordinate : coordinate ≤ bound.eval inputSize) :
    6 * workSteps remaining inputLength fuel length width coordinate ≤
      (remaining + 1) * (stepRawTimePolynomial bound).eval inputSize := by
  induction remaining generalizing length width coordinate with
  | zero =>
      simp only [workSteps, Nat.zero_add, Nat.one_mul, stepRawTimePolynomial,
        NatPolynomial.eval_add, NatPolynomial.eval_constant]
      omega
  | succ remaining ih =>
      have hFrame := frame_span_le inputLength fuel length width coordinate remaining (bound.eval inputSize)
        hInput hFuel (by omega) (by omega) hCoordinate (by omega)
      have hPrepare := pack_time prepareFields (frame inputLength fuel length width coordinate remaining)
        (frameSpanPolynomial bound) inputSize rfl (by
          simpa only [frameSpanPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul,
            NatPolynomial.eval_constant] using hFrame)
      have hRow := (BuilderInitialRowLoop.source_polynomial_bounds 1 length width coordinate []
        (rowSpanPolynomial bound) inputSize (by
          simp only [List.nil_append, BuilderInitialRowLoop.frame, registerWord_length,
            List.length_cons, List.length_nil, List.sum_cons, List.sum_nil, rowSpanPolynomial,
            NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
          omega)).2
      have hStage := stage_span_le inputLength fuel length width coordinate remaining (bound.eval inputSize)
        hInput hFuel (by omega) (by omega) hCoordinate (by omega)
      have hProduct : (remaining + 1 + 1) * (stepRawTimePolynomial bound).eval inputSize =
          (remaining + 1) * (stepRawTimePolynomial bound).eval inputSize +
            (stepRawTimePolynomial bound).eval inputSize :=
        Nat.succ_mul (remaining + 1) _
      by_cases hLess : coordinate < width
      · simp only [if_pos hLess] at hStage
        have hFound := pack_time foundFields (foundStage inputLength fuel length width coordinate remaining)
          (stageSpanPolynomial bound) inputSize rfl (by
            simpa only [stageSpanPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul,
              NatPolynomial.eval_constant] using hStage)
        rw [hProduct]
        simp only [workSteps, if_pos hLess, prepareSteps, foundSteps, stepRawTimePolynomial,
          NatPolynomial.eval_add, NatPolynomial.eval_constant]
        omega
      · simp only [if_neg hLess] at hStage
        have hAdvance := pack_time advanceFields (advanceStage inputLength fuel length width coordinate remaining)
          (stageSpanPolynomial bound) inputSize rfl (by
            simpa only [stageSpanPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul,
              NatPolynomial.eval_constant] using hStage)
        have hTail := ih (length + 1) (width + 1) (coordinate - width) (by omega) (by omega) (by omega)
        rw [hProduct]
        simp only [workSteps, if_neg hLess, prepareSteps, advanceSteps, stepRawTimePolynomial,
          NatPolynomial.eval_add, NatPolynomial.eval_constant] at hTail ⊢
        omega

def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add bound (.mul (.add bound (.constant 1)) (.add (.mul (.constant 30) bound) (.constant 38)))
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.add bound (.constant 1)) (stepRawTimePolynomial bound)

/-- The actual incoming frame bounds both the complete outer loop and retained history. -/
theorem source_polynomial_bounds (remaining inputLength fuel length width coordinate : Nat)
    (older : List Nat) (bound : NatPolynomial) (inputSize : Nat)
    (hSpan : (registerWord (older ++ frame inputLength fuel length width coordinate remaining)).length ≤
      bound.eval inputSize) :
    (registerWord (older ++ finishValues remaining inputLength fuel length width coordinate)).length ≤
        (spanPolynomial bound).eval inputSize ∧
      6 * workSteps remaining inputLength fuel length width coordinate ≤ (rawTimePolynomial bound).eval inputSize := by
  rw [registerWord_append, List.length_append, frame_span] at hSpan
  have hInput : inputLength ≤ bound.eval inputSize := by omega
  have hFuel : fuel ≤ bound.eval inputSize := by omega
  have hLength : length + remaining ≤ bound.eval inputSize := by omega
  have hWidth : width + remaining ≤ bound.eval inputSize := by omega
  have hCoordinate : coordinate ≤ bound.eval inputSize := by omega
  have hCount : remaining + 1 ≤ bound.eval inputSize + 1 := by omega
  have hSpace := finish_span_le remaining inputLength fuel length width coordinate (bound.eval inputSize)
    hInput hFuel hLength hWidth hCoordinate
  have hTime := raw_time_le remaining inputLength fuel length width coordinate bound inputSize
    hInput hFuel hLength hWidth hCoordinate
  have hSpaceProduct := Nat.mul_le_mul_right (30 * bound.eval inputSize + 38) hCount
  have hTimeProduct := Nat.mul_le_mul_right ((stepRawTimePolynomial bound).eval inputSize) hCount
  constructor
  · rw [registerWord_append, List.length_append]
    simp only [spanPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
    omega
  · simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderInitialRowCarry
