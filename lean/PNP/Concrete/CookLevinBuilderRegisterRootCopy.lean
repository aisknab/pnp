/-
Copyright (c) 2026 PNP Labs.

Preserved-register copying by a fixed ordinal from the stable inner boundary.
Newer register count and values may vary freely. A source-root locator marks
the actual register; the existing marked-counter loop copies and restores it.
No runtime value or growing-history length determines the finite program.
The exterior allocation is exact, including arbitrary pre-existing cells.
-/

import PNP.Concrete.CookLevinBuilderRegisterExactlyOnePayload
import PNP.Concrete.CookLevinBuilderRegisterAccess

namespace PNP.Concrete.CookLevin.BuilderRegisterRootCopy

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderRegisterCountdownControl (counterMarker markedTape restoredTape consume consumeSteps exhaustedSteps)
open WorkMachineProgramGraph (Node Graph)
open WorkMachineProgramPath (AcceptPath LocalAcceptRun LocalRejectRun)

private def rule (source target : Nat) (read write : WorkSymbol) (move : HeadMove) : WorkRule :=
  {sourceState := source, targetState := target, readSymbol := read, writeSymbol := write, move := move}

def seekMachine : WorkMachine :=
  {rules := [rule 0 1 scratchEndSymbol scratchEndSymbol .right,
    rule 1 1 unitSymbol unitSymbol .right, rule 1 1 separatorSymbol separatorSymbol .right,
    rule 1 2 leftMarker leftMarker .left], startState := 0, acceptState := 2, rejectState := 3}
def skipOneMachine : WorkMachine :=
  {rules := [rule 0 1 separatorSymbol separatorSymbol .left,
    rule 1 1 unitSymbol unitSymbol .left, rule 1 2 separatorSymbol separatorSymbol .stay], startState := 0, acceptState := 2, rejectState := 3}
def markMachine : WorkMachine :=
  {rules := [rule 0 1 separatorSymbol counterMarker .left,
    rule 1 1 unitSymbol unitSymbol .left, rule 1 1 separatorSymbol separatorSymbol .left,
    rule 1 2 scratchEndSymbol scratchEndSymbol .stay], startState := 0, acceptState := 2, rejectState := 3}
def doneMachine : WorkMachine := {rules := [], startState := 0, acceptState := 0, rejectState := 1}
def skipMachine : Nat → WorkMachine
  | 0 => doneMachine
  | count + 1 => WorkMachineChain.machine skipOneMachine (skipMachine count)
def markProgram (beforeCount : Nat) : WorkMachine :=
  WorkMachineChain.machine seekMachine (WorkMachineChain.machine (skipMachine beforeCount) markMachine)

private def leftFocus (left right : List WorkSymbol) : WorkTape :=
  match left with
  | [] => {left := [], head := .blank, right := right}
  | symbol :: rest => {left := rest, head := symbol, right := right}
private def rightFocus (left right : List WorkSymbol) : WorkTape :=
  match right with
  | [] => {left := left, head := .blank, right := []}
  | symbol :: rest => {left := left, head := symbol, right := rest}
private def prefixTape (before : List Nat) (tail inside : List WorkSymbol) : WorkTape :=
  leftFocus (registerWord before ++ separatorSymbol :: tail) inside

private theorem compose {program : WorkMachine} {n m : Nat} {a b c : WorkConfiguration}
    (first : workRunExact? program n a = some b) (second : workRunExact? program m b = some c) :
    workRunExact? program (n + m) a = some c :=
  PipelineMachineSimulation.workRunExact?_compose program n m a b c first second
private theorem one_step {program : WorkMachine} {a b : WorkConfiguration}
    (step : workStep? program a = some b) : workRunExact? program 1 a = some b := by
  simp only [workRunExact?, step]
private theorem chain_run (first second : WorkMachine) (n m : Nat) (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

private theorem scan_right (program : WorkMachine) (state : Nat) (scanned after before : List WorkSymbol)
    (hStep : ∀ symbol ∈ scanned, ∀ left right,
      workStep? program {state := state, tape := {left := left, head := symbol, right := right}} =
        some {state := state, tape := rightFocus (symbol :: left) right}) :
    workRunExact? program scanned.length {state := state, tape := rightFocus before (scanned ++ after)} =
      some {state := state, tape := rightFocus (scanned.reverse ++ before) after} := by
  induction scanned generalizing before with
  | nil => rfl
  | cons symbol rest ih =>
      have h := hStep symbol List.mem_cons_self before (rest ++ after)
      have hRest := ih (symbol :: before) (fun item hItem => hStep item (List.mem_cons_of_mem symbol hItem))
      simp only [List.length_cons, List.cons_append, rightFocus, workRunExact?]
      rw [h]
      simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append, rightFocus] using hRest

private theorem scan_left (program : WorkMachine) (state : Nat) (scanned after before : List WorkSymbol)
    (hStep : ∀ symbol ∈ scanned, ∀ left right,
      workStep? program {state := state, tape := {left := left, head := symbol, right := right}} =
        some {state := state, tape := leftFocus left (symbol :: right)}) :
    workRunExact? program scanned.length {state := state, tape := leftFocus (scanned ++ after) before} =
      some {state := state, tape := leftFocus after (scanned.reverse ++ before)} := by
  induction scanned generalizing before with
  | nil => rfl
  | cons symbol rest ih =>
      have h := hStep symbol List.mem_cons_self (rest ++ after) before
      have hRest := ih (symbol :: before) (fun item hItem => hStep item (List.mem_cons_of_mem symbol hItem))
      simp only [List.length_cons, List.cons_append, leftFocus, workRunExact?]
      rw [h]
      simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append, leftFocus] using hRest

private theorem seek_run (values : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? seekMachine ((registerWord values).length + 2)
      (workStartConfiguration seekMachine (endTape values (leftMarker :: inside) outside)) =
      some {state := seekMachine.acceptState, tape := leftFocus (registerWord values ++ scratchEndSymbol :: outside) (leftMarker :: inside)} := by
  have hStart : workStep? seekMachine
      (workStartConfiguration seekMachine (endTape values (leftMarker :: inside) outside)) =
      some {state := 1, tape := rightFocus (scratchEndSymbol :: outside) ((registerWord values).reverse ++ leftMarker :: inside)} := by
    simp only [workStartConfiguration, endTape]
    cases hWord : (registerWord values).reverse <;> rfl
  have hScan := scan_right seekMachine 1 (registerWord values).reverse (leftMarker :: inside)
    (scratchEndSymbol :: outside) (by
      intro symbol hSymbol left right
      have h := BuilderRegisterAccess.registerWord_symbols values symbol (List.mem_reverse.mp hSymbol)
      rcases h with rfl | rfl <;> rfl)
  have hFinish : workStep? seekMachine
      {state := 1, tape := {left := registerWord values ++ scratchEndSymbol :: outside, head := leftMarker, right := inside}} =
      some {state := seekMachine.acceptState, tape := leftFocus (registerWord values ++ scratchEndSymbol :: outside) (leftMarker :: inside)} := by
    cases hWord : registerWord values <;> rfl
  simp only [List.reverse_reverse, rightFocus] at hScan
  have h := compose (compose (one_step hStart) hScan) (one_step hFinish)
  have hClock : 1 + (registerWord values).reverse.length + 1 = (registerWord values).length + 2 := by
    simp only [List.length_reverse]
    omega
  rw [hClock] at h
  exact h

private theorem skip_one_run (value : Nat) (tail inside : List WorkSymbol) :
    workRunExact? skipOneMachine (value + 2)
      (workStartConfiguration skipOneMachine
        {left := List.replicate value unitSymbol ++ separatorSymbol :: tail, head := separatorSymbol, right := inside}) =
      some {state := skipOneMachine.acceptState, tape := {left := tail, head := separatorSymbol, right := List.replicate value unitSymbol ++ separatorSymbol :: inside}} := by
  have hStart : workStep? skipOneMachine
      (workStartConfiguration skipOneMachine
        {left := List.replicate value unitSymbol ++ separatorSymbol :: tail, head := separatorSymbol, right := inside}) =
      some {state := 1, tape := leftFocus (List.replicate value unitSymbol ++ separatorSymbol :: tail) (separatorSymbol :: inside)} := by cases value <;> rfl
  have hScan := scan_left skipOneMachine 1 (List.replicate value unitSymbol) (separatorSymbol :: tail)
    (separatorSymbol :: inside) (by
      intro symbol hSymbol left right
      have h := List.eq_of_mem_replicate hSymbol
      subst symbol
      rfl)
  simp only [List.reverse_replicate, leftFocus] at hScan
  have hFinish : workStep? skipOneMachine
      {state := 1, tape := {left := tail, head := separatorSymbol, right := List.replicate value unitSymbol ++ separatorSymbol :: inside}} =
      some {state := skipOneMachine.acceptState, tape := {left := tail, head := separatorSymbol, right := List.replicate value unitSymbol ++ separatorSymbol :: inside}} := rfl
  have h := compose (compose (one_step hStart) hScan) (one_step hFinish)
  have hClock : 1 + (List.replicate value unitSymbol).length + 1 = value + 2 := by
    simp only [List.length_replicate]
    omega
  rw [hClock] at h
  exact h

def skipSteps : List Nat → Nat
  | [] => 0
  | value :: rest => value + 2 + 1 + skipSteps rest

private theorem skip_run (before : List Nat) (tail inside : List WorkSymbol) :
    workRunExact? (skipMachine before.length) (skipSteps before)
      (workStartConfiguration (skipMachine before.length) (prefixTape before tail inside)) =
      some {state := (skipMachine before.length).acceptState, tape := {left := tail, head := separatorSymbol, right := (registerWord before).reverse ++ inside}} := by
  induction before generalizing inside with
  | nil => rfl
  | cons value rest ih =>
      obtain ⟨next, hNext⟩ : ∃ next, registerWord rest ++ separatorSymbol :: tail = separatorSymbol :: next := by
        cases rest with
        | nil => exact ⟨tail, rfl⟩
        | cons first following => exact ⟨List.replicate first unitSymbol ++ registerWord following ++ separatorSymbol :: tail,
            by simp only [registerWord, List.cons_append, List.append_assoc]⟩
      have hFirst := skip_one_run value next inside
      have hTail := ih (List.replicate value unitSymbol ++ separatorSymbol :: inside)
      have hMiddle : prefixTape rest tail (List.replicate value unitSymbol ++ separatorSymbol :: inside) =
          {left := next, head := separatorSymbol, right := List.replicate value unitSymbol ++ separatorSymbol :: inside} := by
        simp only [prefixTape, hNext, leftFocus]
      rw [hMiddle] at hTail
      have h := chain_run skipOneMachine (skipMachine rest.length) (value + 2) (skipSteps rest)
        _ _ _ hFirst hTail
      simpa only [skipMachine, skipSteps, List.length_cons, prefixTape, registerWord,
        List.cons_append, List.append_assoc, hNext, leftFocus, List.reverse_cons,
        List.reverse_append, List.reverse_replicate, List.append_nil, List.nil_append] using h

private theorem mark_run (value : Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? markMachine (value + (registerWord after).length + 2)
      (workStartConfiguration markMachine
        {left := List.replicate value unitSymbol ++ registerWord after ++ scratchEndSymbol :: outside, head := separatorSymbol, right := inside}) =
      some {state := markMachine.acceptState, tape := markedTape 0 value after inside outside} := by
  let scanned := List.replicate value unitSymbol ++ registerWord after
  have hStart : workStep? markMachine
      (workStartConfiguration markMachine
        {left := scanned ++ scratchEndSymbol :: outside, head := separatorSymbol, right := inside}) =
      some {state := 1, tape := leftFocus (scanned ++ scratchEndSymbol :: outside) (counterMarker :: inside)} := by
    cases hScan : scanned <;> rfl
  have hScan := scan_left markMachine 1 scanned (scratchEndSymbol :: outside) (counterMarker :: inside) (by
    intro symbol hSymbol left right
    simp only [scanned, List.mem_append] at hSymbol
    rcases hSymbol with hUnit | hWord
    · have h := List.eq_of_mem_replicate hUnit
      subst symbol
      rfl
    · have h := BuilderRegisterAccess.registerWord_symbols after symbol hWord
      rcases h with rfl | rfl <;> rfl)
  have hFinish : workStep? markMachine
      {state := 1, tape := {left := outside, head := scratchEndSymbol, right := scanned.reverse ++ counterMarker :: inside}} =
      some {state := markMachine.acceptState, tape := {left := outside, head := scratchEndSymbol, right := scanned.reverse ++ counterMarker :: inside}} := rfl
  simp only [leftFocus] at hScan
  have h := compose (compose (one_step hStart) hScan) (one_step hFinish)
  have hClock : 1 + scanned.length + 1 = value + (registerWord after).length + 2 := by
    simp only [scanned, List.length_append, List.length_replicate]
    omega
  rw [hClock] at h
  simpa only [scanned, markedTape, List.length_append, List.length_replicate,
    List.reverse_append, List.reverse_replicate, List.replicate_zero, List.append_nil,
    List.nil_append, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def markSteps (before : List Nat) (value : Nat) (after : List Nat) : Nat :=
  (registerWord (before ++ [value] ++ after)).length + 2 + 1 +
    (skipSteps before + 1 + (value + (registerWord after).length + 2))

private theorem mark_program_run (before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? (markProgram before.length) (markSteps before value after)
      (workStartConfiguration (markProgram before.length)
        (endTape (before ++ [value] ++ after) (leftMarker :: inside) outside)) =
      some {state := (markProgram before.length).acceptState, tape := markedTape 0 value after ((registerWord before).reverse ++ leftMarker :: inside) outside} := by
  have hSeek := seek_run (before ++ [value] ++ after) inside outside
  have hSkip := skip_run before (List.replicate value unitSymbol ++ registerWord after ++ scratchEndSymbol :: outside)
    (leftMarker :: inside)
  have hMark := mark_run value after ((registerWord before).reverse ++ leftMarker :: inside) outside
  have hTail := chain_run (skipMachine before.length) markMachine (skipSteps before)
    (value + (registerWord after).length + 2) _ _ _ hSkip hMark
  have h := chain_run seekMachine (WorkMachineChain.machine (skipMachine before.length) markMachine)
    ((registerWord (before ++ [value] ++ after)).length + 2) _ _ _ _ hSeek
    (by simpa only [prefixTape, registerWord_append, registerWord, List.append_nil, List.nil_append,
      List.cons_append, List.append_assoc] using hTail)
  simpa only [markProgram, markSteps] using h

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineChain.QueryDistinct ∧ WorkMachineChain.NoRuleAtAccept program ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧ program.acceptState ≠ program.rejectState
private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
   WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
   WorkMachineChain.noRuleAtAccept first {second with acceptState := second.rejectState} hSecond.2.2.1,
   WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2.2⟩
private theorem seek_good : Good seekMachine := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · unfold WorkMachineChain.QueryDistinct
    decide
  · intro item h
    decide +revert
  · intro item h
    decide +revert
private theorem skip_one_good : Good skipOneMachine := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · unfold WorkMachineChain.QueryDistinct
    decide
  · intro item h
    decide +revert
  · intro item h
    decide +revert
private theorem mark_good : Good markMachine := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · unfold WorkMachineChain.QueryDistinct
    decide
  · intro item h
    decide +revert
  · intro item h
    decide +revert
private theorem skip_good (count : Nat) : Good (skipMachine count) := by
  induction count with
  | zero =>
      refine ⟨List.Pairwise.nil, ?_, ?_, by decide⟩
      · intro item h
        cases h
      · intro item h
        cases h
  | succ count ih => exact chain_good _ _ skip_one_good ih
private theorem mark_program_good (count : Nat) : Good (markProgram count) :=
  chain_good _ _ seek_good (chain_good _ _ (skip_good count) mark_good)
private theorem constant_good (value : Nat) : Good (RegisterConstant.machine value) := by
  refine ⟨RegisterConstant.rules_pairwise_query_distinct value, ?_, ?_,
    RegisterConstant.machine_acceptState_ne_rejectState value⟩
  · intro item h
    exact Nat.ne_of_lt (RegisterConstant.rule_source_lt_acceptState value item h)
  · intro item h
    have hBound := RegisterConstant.rule_source_lt_acceptState value item h
    rw [RegisterConstant.machine_acceptState] at hBound
    rw [RegisterConstant.machine_rejectState]
    omega

def consumeReference : WorkMachineProgramGraph.NodeRef := {name := 1, startState := consume.startState}
def incrementNode : Node :=
  {name := 2, program := BuilderRegisterExactlyOnePayload.incrementMachine, onAccept := .node consumeReference, onReject := .reject}
def consumeNode : Node :=
  {name := 1, program := consume, onAccept := .node incrementNode.reference, onReject := .accept}
def zeroNode : Node :=
  {name := 0, program := RegisterConstant.machine 0, onAccept := .node consumeNode.reference, onReject := .reject}
def copyGraph : Graph := {nodes := [zeroNode, consumeNode, incrementNode], entry := zeroNode.reference}
def copyMachine : WorkMachine := WorkMachineProgramGraph.machine copyGraph

private theorem zero_mem : zeroNode ∈ copyGraph.nodes := List.Mem.head _
private theorem consume_mem : consumeNode ∈ copyGraph.nodes := List.Mem.tail _ (List.Mem.head _)
private theorem increment_mem : incrementNode ∈ copyGraph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem copy_graph_wellFormed : copyGraph.WellFormed := by
  have hNames : (copyGraph.nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0,1,2] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [copyGraph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact constant_good 0
    · exact BuilderRegisterCountdownControl.consume_control
    · exact BuilderRegisterExactlyOnePayload.increment_control
  · exact ⟨zeroNode, zero_mem, rfl, rfl⟩
  · intro node hMem
    simp only [copyGraph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact ⟨⟨consumeNode, consume_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨incrementNode, increment_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨consumeNode, consume_mem, rfl, rfl⟩, True.intro⟩

def loopSteps : Nat → Nat → List Nat → Nat → Nat
  | spent, 0, after, value => exhaustedSteps spent (after ++ [value]) + 1
  | spent, remaining + 1, after, value =>
      consumeSteps spent (remaining + 1) (after ++ [value]) + 1 +
        (2 + 1 + loopSteps (spent + 1) remaining after (value + 1))
def copySteps (value : Nat) (after : List Nat) : Nat :=
  RegisterConstant.steps 0 + 1 + loopSteps 0 value after 0

private theorem constant_run (value : Nat) (existing : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (RegisterConstant.machine value) (RegisterConstant.steps value)
      (workStartConfiguration (RegisterConstant.machine value) (endTape existing inside outside)) =
      some {state := (RegisterConstant.machine value).acceptState, tape := endTape (existing ++ [value]) inside (outside.drop (value + 1))} := by
  rw [RegisterConstant.machine_acceptState]
  exact RegisterConstant.workRunExact value existing inside outside

private theorem zero_trace (count : Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    LocalAcceptRun zeroNode (RegisterConstant.steps 0)
      (markedTape 0 count after inside outside)
      (markedTape 0 count (after ++ [0]) inside (outside.drop 1)) := by
  have h := constant_run 0 [] ((registerWord after).reverse ++ List.replicate count unitSymbol ++ counterMarker :: inside) outside
  simpa only [LocalAcceptRun, zeroNode, workStartConfiguration, markedTape, endTape, List.replicate_zero,
    registerWord_append, registerWord, List.reverse_nil, List.reverse_cons, List.reverse_append,
    List.nil_append, List.append_nil, List.cons_append, List.append_assoc, Nat.zero_add] using h

private theorem increment_trace (spent remaining value : Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    LocalAcceptRun incrementNode 2 (markedTape spent remaining (after ++ [value]) inside outside)
      (markedTape spent remaining (after ++ [value + 1]) inside (outside.drop 1)) := by
  have h := BuilderRegisterExactlyOnePayload.increment_workRunExact
    (List.replicate value unitSymbol ++ separatorSymbol ::
      ((registerWord after).reverse ++ List.replicate remaining unitSymbol ++
        List.replicate spent BuilderRegisterCountdownControl.spentSymbol ++ counterMarker :: inside)) outside
  simp only [LocalAcceptRun, incrementNode, workStartConfiguration, markedTape, registerWord_append, registerWord,
    List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
    List.append_nil, List.nil_append, List.cons_append, List.append_assoc] at h ⊢
  simpa only [List.replicate_succ, List.cons_append] using h

private def loopFinalTape (spent remaining value : Nat) (after : List Nat) (inside outside : List WorkSymbol) : WorkTape :=
  restoredTape (spent + remaining) (after ++ [value + remaining]) inside (outside.drop remaining)

private theorem loop_path (spent remaining value : Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    AcceptPath copyGraph (.node consumeNode.reference) .accept (loopSteps spent remaining after value)
      (markedTape spent remaining (after ++ [value]) inside outside)
      (loopFinalTape spent remaining value after inside outside) := by
  induction remaining generalizing spent value outside with
  | zero =>
      have hExit : LocalRejectRun consumeNode (exhaustedSteps spent (after ++ [value]))
          (markedTape spent 0 (after ++ [value]) inside outside)
          (loopFinalTape spent 0 value after inside outside) := by
        simpa only [LocalRejectRun, consumeNode, workStartConfiguration, loopFinalTape, Nat.add_zero, List.drop_zero] using
          BuilderRegisterCountdownControl.exhausted_workRunExact spent (after ++ [value]) inside outside
      have h := AcceptPath.stepReject consumeNode .accept _ 0 _ _ _ consume_mem hExit
        (AcceptPath.terminal .accept (loopFinalTape spent 0 value after inside outside))
      simpa only [loopSteps, Nat.add_zero] using h
  | succ remaining ih =>
      have hTake : LocalAcceptRun consumeNode (consumeSteps spent (remaining + 1) (after ++ [value]))
          (markedTape spent (remaining + 1) (after ++ [value]) inside outside)
          (markedTape (spent + 1) remaining (after ++ [value]) inside outside) :=
        BuilderRegisterCountdownControl.consume_workRunExact spent remaining (after ++ [value]) inside outside
      have hInc := increment_trace (spent + 1) remaining value after inside outside
      have hTail := ih (spent + 1) (value + 1) (outside.drop 1)
      have hIncPath := AcceptPath.step incrementNode .accept _ _ _ _ _ increment_mem hInc hTail
      have hPath := AcceptPath.step consumeNode .accept _ _ _ _ _ consume_mem hTake hIncPath
      have hCounter : spent + 1 + remaining = spent + (remaining + 1) := by omega
      have hValue : value + 1 + remaining = value + (remaining + 1) := by omega
      have hDrop : (outside.drop 1).drop remaining = outside.drop (remaining + 1) := by
        rw [List.drop_drop, Nat.add_comm]
      simpa only [loopSteps, loopFinalTape, hCounter, hValue, hDrop] using hPath

private theorem copy_run (value : Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? copyMachine (copySteps value after)
      (workStartConfiguration copyMachine (markedTape 0 value after inside outside)) =
      some {state := copyMachine.acceptState, tape := restoredTape value (after ++ [value]) inside (outside.drop (value + 1))} := by
  have hZero := zero_trace value after inside outside
  have hLoop := loop_path 0 value 0 after inside (outside.drop 1)
  have hPath := AcceptPath.step zeroNode .accept _ _ _ _ _ zero_mem hZero hLoop
  have hRun := WorkMachineProgramPath.runExact copyGraph _ _ _ _ _ copy_graph_wellFormed hPath
  have hInitial (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node zeroNode.reference) tape =
        workStartConfiguration copyMachine tape := rfl
  have hFinal (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration .accept tape =
        {state := copyMachine.acceptState, tape := tape} := rfl
  rw [hInitial, hFinal] at hRun
  simpa only [copyMachine, copySteps, loopFinalTape, Nat.zero_add, Nat.add_zero, List.drop_drop, Nat.add_comm] using hRun

def machine (beforeCount : Nat) : WorkMachine := WorkMachineChain.machine (markProgram beforeCount) copyMachine
def workSteps (before : List Nat) (value : Nat) (after : List Nat) : Nat :=
  markSteps before value after + 1 + copySteps value after
def initialConfiguration (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine beforeCount) (endTape (before ++ [value] ++ after) (leftMarker :: inside) outside)
def finalConfiguration (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  {state := (machine beforeCount).acceptState, tape := endTape (before ++ [value] ++ after ++ [value]) (leftMarker :: inside) (outside.drop (value + 1))}

theorem workRunExact (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) (hBefore : before.length = beforeCount) :
    workRunExact? (machine beforeCount) (workSteps before value after)
      (initialConfiguration beforeCount before value after inside outside) =
      some (finalConfiguration beforeCount before value after inside outside) := by
  subst beforeCount
  have hMark := mark_program_run before value after inside outside
  have hCopy := copy_run value after ((registerWord before).reverse ++ leftMarker :: inside) outside
  rw [BuilderRegisterCountdownControl.restoredTape_eq_endTape] at hCopy
  have h := chain_run (markProgram before.length) copyMachine (markSteps before value after) (copySteps value after)
    _ _ _ hMark hCopy
  simpa only [machine, workSteps, initialConfiguration, finalConfiguration,
    List.append_assoc, List.cons_append, List.nil_append] using h

theorem run_compile_exact (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) (hBefore : before.length = beforeCount) :
    run (compileWorkMachine (machine beforeCount)) (6 * workSteps before value after)
      (encodeWorkConfiguration (initialConfiguration beforeCount before value after inside outside)) =
      encodeWorkConfiguration (finalConfiguration beforeCount before value after inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact beforeCount before value after inside outside hBefore)

theorem final_tape (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration beforeCount before value after inside outside).tape =
      endTape (before ++ [value] ++ after ++ [value]) (leftMarker :: inside) (outside.drop (value + 1)) := rfl

private theorem good (beforeCount : Nat) : Good (machine beforeCount) :=
  chain_good _ _ (mark_program_good beforeCount)
    ⟨WorkMachineProgramGraph.rules_pairwise copyGraph copy_graph_wellFormed,
     WorkMachineProgramGraph.noRuleAt_globalAccept copyGraph, WorkMachineProgramGraph.noRuleAt_globalReject copyGraph,
     by change (0 : Nat) ≠ 1; decide⟩

theorem rules_pairwise_query_distinct (beforeCount : Nat) :
    (machine beforeCount).rules.Pairwise WorkMachineChain.QueryDistinct := (good beforeCount).1
theorem noRuleAtAccept (beforeCount : Nat) : WorkMachineChain.NoRuleAtAccept (machine beforeCount) := (good beforeCount).2.1
theorem noRuleAtReject (beforeCount : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine beforeCount) (machine beforeCount).rejectState := (good beforeCount).2.2.1
theorem acceptState_ne_rejectState (beforeCount : Nat) :
    (machine beforeCount).acceptState ≠ (machine beforeCount).rejectState := (good beforeCount).2.2.2

theorem skipSteps_closed (before : List Nat) : skipSteps before = before.sum + 3 * before.length := by
  induction before with
  | nil => rfl
  | cons value rest ih =>
      simp only [skipSteps, List.sum_cons, List.length_cons, ih, Nat.mul_succ]
      omega

private theorem append_span (values : List Nat) (value : Nat) :
    (registerWord (values ++ [value])).length = (registerWord values).length + value + 1 := by
  rw [registerWord_append, List.length_append]
  simp only [registerWord, List.length_cons, List.length_append, List.length_replicate, List.length_nil]
  omega

private theorem loopSteps_le (spent remaining value : Nat) (after : List Nat) (bound : Nat)
    (hCounter : spent + remaining ≤ bound) (hValue : value + remaining ≤ bound)
    (hAfter : (registerWord after).length ≤ bound) :
    loopSteps spent remaining after value ≤ remaining * (6 * bound + 9) + 8 * bound + 8 := by
  induction remaining generalizing spent value with
  | zero =>
      simp only [loopSteps, exhaustedSteps, append_span]
      omega
  | succ remaining ih =>
      have hNextCounter : spent + 1 + remaining ≤ bound := by omega
      have hNextValue : value + 1 + remaining ≤ bound := by omega
      have hTail := ih (spent + 1) (value + 1) hNextCounter hNextValue
      have hStep : consumeSteps spent (remaining + 1) (after ++ [value]) + 4 ≤ 6 * bound + 9 := by
        simp only [consumeSteps, append_span]
        omega
      simp only [loopSteps, Nat.add_mul, Nat.one_mul]
      omega

def workBound (bound : Nat) : Nat := bound * (6 * bound + 9) + 13 * bound + 18

theorem workSteps_le (before : List Nat) (value : Nat) (after : List Nat) (bound : Nat)
    (hSpan : (registerWord (before ++ [value] ++ after)).length ≤ bound) :
    workSteps before value after ≤ workBound bound := by
  have hSplit : (registerWord (before ++ [value] ++ after)).length =
      (registerWord before).length + value + 1 + (registerWord after).length := by
    rw [registerWord_append, List.length_append, append_span]
  have hBefore : (registerWord before).length ≤ bound := by omega
  have hValue : value ≤ bound := by omega
  have hAfter : (registerWord after).length ≤ bound := by omega
  have hTogether : value + (registerWord after).length ≤ bound := by omega
  have hSkip : skipSteps before ≤ 3 * bound := by
    rw [skipSteps_closed]
    rw [registerWord_length] at hBefore
    omega
  have hMark : markSteps before value after ≤ 5 * bound + 6 := by
    unfold markSteps
    omega
  have hLoop := loopSteps_le 0 value 0 after bound (by omega) (by omega) hAfter
  have hMul := Nat.mul_le_mul_right (6 * bound + 9) hValue
  have hZero : RegisterConstant.steps 0 = 2 := rfl
  simp only [workSteps, copySteps, hZero, workBound]
  omega

theorem final_span_le (before : List Nat) (value : Nat) (after : List Nat) (outside : List WorkSymbol) (bound : Nat)
    (hSpan : (registerWord (before ++ [value] ++ after)).length + outside.length ≤ bound) :
    (registerWord (before ++ [value] ++ after ++ [value])).length + (outside.drop (value + 1)).length ≤ 2 * bound + 1 := by
  have hValue : value ≤ bound := by
    have h := hSpan
    rw [registerWord_append, List.length_append, append_span] at h
    omega
  rw [append_span]
  simp only [List.length_drop]
  omega

def spanPolynomial (bound : NatPolynomial) : NatPolynomial := .add (.mul (.constant 2) bound) (.constant 1)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.constant 6) (.add (.add (.mul bound (.add (.mul (.constant 6) bound) (.constant 9)))
    (.mul (.constant 13) bound)) (.constant 18))

theorem source_polynomial_bounds (before : List Nat) (value : Nat) (after : List Nat) (outside : List WorkSymbol)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (before ++ [value] ++ after)).length + outside.length ≤ bound.eval inputLength) :
    (registerWord (before ++ [value] ++ after ++ [value])).length + (outside.drop (value + 1)).length ≤
        (spanPolynomial bound).eval inputLength ∧
      6 * workSteps before value after ≤ (rawTimePolynomial bound).eval inputLength := by
  have hTime := workSteps_le before value after (bound.eval inputLength) (by omega)
  constructor
  · exact final_span_le before value after outside (bound.eval inputLength) hSpan
  · simp only [rawTimePolynomial, NatPolynomial.eval_mul, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    exact Nat.mul_le_mul_left 6 hTime

end PNP.Concrete.CookLevin.BuilderRegisterRootCopy
