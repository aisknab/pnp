/-
Copyright (c) 2026 PNP Labs.

One fixed graph constructs a descending range and its exactly-one count/tag
metadata from the two actual written input registers. A retained counter marker
allows a second physical pass without an input-sized register offset or program.
Every loop bridge, scratch erasure, restoration and metadata write is charged.

Actual shape-source fields and canonical symbol/head/state list linkage remain
separate obligations. This is not a complete Cook-Levin builder claim.
-/
import PNP.Concrete.CookLevinBuilderRegisterDescendingRange

namespace PNP.Concrete.CookLevin.BuilderRegisterExactlyOnePayload

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderRegisterCountdownControl
  (consume markedTape counterMarker consumeSteps exhaustedSteps)
open WorkMachineProgramGraph (Node NodeRef Graph)
open WorkMachineProgramPath (LocalAcceptRun LocalRejectRun AcceptPath)

/-- One new unary unit and a new end marker, independent of the register value. -/
def incrementMachine : WorkMachine :=
  { rules :=
      { sourceState := 0, targetState := 1, readSymbol := scratchEndSymbol,
        writeSymbol := unitSymbol, move := .left } ::
      PipelineMachineSimulation.allWorkSymbols.map (fun symbol =>
        { sourceState := 1, targetState := 2, readSymbol := symbol,
          writeSymbol := scratchEndSymbol, move := .stay })
    startState := 0
    acceptState := 2
    rejectState := 3 }

theorem increment_workRunExact (inside outside : List WorkSymbol) :
    workRunExact? incrementMachine 2
      (workStartConfiguration incrementMachine
        { left := outside, head := scratchEndSymbol, right := inside }) =
      some {
        state := incrementMachine.acceptState
        tape := { left := outside.drop 1, head := scratchEndSymbol, right := unitSymbol :: inside } } := by
  cases outside with
  | nil => rfl
  | cons symbol rest =>
      rcases symbol with ⟨first, second⟩
      cases first <;> cases second <;> rfl

theorem increment_control :
    incrementMachine.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt incrementMachine incrementMachine.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt incrementMachine incrementMachine.rejectState ∧
    incrementMachine.acceptState ≠ incrementMachine.rejectState := by
  constructor
  · unfold WorkMachineChain.QueryDistinct
    decide
  constructor
  · intro item h
    decide +revert
  constructor
  · intro item h
    decide +revert
  · decide

def consumeReference : NodeRef := { name := 2, startState := consume.startState }

def tagNode : Node :=
  { name := 4
    program := RegisterConstant.machine 4
    onAccept := .accept
    onReject := .dead }

def incrementNode : Node :=
  { name := 3
    program := incrementMachine
    onAccept := .node consumeReference
    onReject := .dead }

def consumeNode : Node :=
  { name := 2
    program := consume
    onAccept := .node incrementNode.reference
    onReject := .node tagNode.reference }

def zeroNode : Node :=
  { name := 1
    program := RegisterConstant.machine 0
    onAccept := .node consumeNode.reference
    onReject := .dead }

def rangeNode : Node :=
  { name := 0
    program := BuilderRegisterDescendingRange.machineWith counterMarker
    onAccept := .node zeroNode.reference
    onReject := .dead }

def graph : Graph :=
  { nodes := [rangeNode, zeroNode, consumeNode, incrementNode, tagNode]
    entry := rangeNode.reference }

def machine : WorkMachine := WorkMachineProgramGraph.machine graph

private theorem range_mem : rangeNode ∈ graph.nodes := List.Mem.head _
private theorem zero_mem : zeroNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)
private theorem consume_mem : consumeNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem increment_mem : incrementNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem tag_mem : tagNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

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

theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun left right : Nat => left ≠ right) := by
    change ([0, 1, 2, 3, 4] : List Nat).Pairwise (fun left right => left ≠ right)
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl
    · exact ⟨BuilderRegisterDescendingRange.rulesWith_pairwise_query_distinct counterMarker,
        BuilderRegisterDescendingRange.noRuleWithAtAccept counterMarker,
        BuilderRegisterDescendingRange.noRuleWithAtReject counterMarker,
        BuilderRegisterDescendingRange.acceptWith_ne_rejectState counterMarker⟩
    · exact constant_good 0
    · exact BuilderRegisterCountdownControl.consume_control
    · exact increment_control
    · exact constant_good 4
  · exact ⟨rangeNode, range_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨zeroNode, zero_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨consumeNode, consume_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨incrementNode, increment_mem, rfl, rfl⟩, ⟨tagNode, tag_mem, rfl, rfl⟩⟩
    · exact ⟨⟨consumeNode, consume_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

/-- Semantic output specification, not data supplied to the finite machine. -/
def payloadValues (count upper : Nat) : List Nat :=
  BuilderRegisterDescendingRange.values upper count ++ [count, 4]

def loopSteps : Nat → Nat → List Nat → Nat → Nat
  | spent, 0, emitted, value =>
      exhaustedSteps spent (emitted ++ [value]) + 1 + (RegisterConstant.steps 4 + 1)
  | spent, remaining + 1, emitted, value =>
      consumeSteps spent (remaining + 1) (emitted ++ [value]) + 1 +
        (2 + 1 + loopSteps (spent + 1) remaining emitted (value + 1))

def workSteps (count upper : Nat) : Nat :=
  BuilderRegisterDescendingRange.workSteps count upper + 1 +
    (RegisterConstant.steps 0 + 1 + loopSteps 0 count (BuilderRegisterDescendingRange.values upper count) 0)

def initialConfiguration (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ [count, upper]) inside [])

def finalTape (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) : WorkTape :=
  endTape (older ++ [count] ++ payloadValues count upper) inside
    ((List.replicate (upper - count + 1) .blank).drop (count + 6))

def exteriorFrom (count upper : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (BuilderRegisterDescendingRange.exteriorFrom count upper outside).drop (count + 6)

def finalTapeWithOutside (count upper : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkTape :=
  endTape (older ++ [count] ++ payloadValues count upper) inside (exteriorFrom count upper outside)

theorem finalTapeWithOutside_nil (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    finalTapeWithOutside count upper older inside [] = finalTape count upper older inside := by
  simp only [finalTapeWithOutside, exteriorFrom, BuilderRegisterDescendingRange.exteriorFrom,
    List.drop_nil, List.append_nil, finalTape]

def finalConfiguration (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  { state := machine.acceptState
    tape := finalTape count upper older inside }

private theorem constant_run (value : Nat) (existing : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (RegisterConstant.machine value) (RegisterConstant.steps value)
      (workStartConfiguration (RegisterConstant.machine value) (endTape existing inside outside)) =
      some {
        state := (RegisterConstant.machine value).acceptState
        tape := endTape (existing ++ [value]) inside (outside.drop (value + 1)) } := by
  rw [RegisterConstant.machine_acceptState]
  exact RegisterConstant.workRunExact value existing inside outside

private theorem zero_trace (count : Nat) (emitted : List Nat) (inside outside : List WorkSymbol) :
    LocalAcceptRun zeroNode (RegisterConstant.steps 0)
      (markedTape 0 count emitted inside outside)
      (markedTape 0 count (emitted ++ [0]) inside (outside.drop 1)) := by
  have h := constant_run 0 [] ((registerWord emitted).reverse ++ List.replicate count unitSymbol ++ counterMarker :: inside) outside
  simpa only [LocalAcceptRun, zeroNode, workStartConfiguration, markedTape, endTape, List.replicate_zero,
    registerWord_append, registerWord, List.reverse_nil, List.reverse_cons, List.reverse_append,
    List.nil_append, List.append_nil, List.cons_append, List.append_assoc, Nat.zero_add] using h

private theorem increment_trace (spent remaining value : Nat) (emitted : List Nat)
    (inside outside : List WorkSymbol) :
    LocalAcceptRun incrementNode 2
      (markedTape spent remaining (emitted ++ [value]) inside outside)
      (markedTape spent remaining (emitted ++ [value + 1]) inside (outside.drop 1)) := by
  have h := increment_workRunExact
    (List.replicate value unitSymbol ++ separatorSymbol ::
      ((registerWord emitted).reverse ++ List.replicate remaining unitSymbol ++
        List.replicate spent BuilderRegisterCountdownControl.spentSymbol ++ counterMarker :: inside)) outside
  simp only [LocalAcceptRun, incrementNode, workStartConfiguration, markedTape, registerWord_append, registerWord,
    List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
    List.append_nil, List.nil_append, List.cons_append, List.append_assoc] at h ⊢
  simpa only [List.replicate_succ, List.cons_append] using h

private def loopFinalTape (spent remaining value : Nat) (emitted older : List Nat)
    (inside outside : List WorkSymbol) : WorkTape :=
  endTape (older ++ [spent + remaining] ++ emitted ++ [value + remaining, 4]) inside
    (outside.drop (remaining + 5))

private theorem loop_path (spent remaining value : Nat) (emitted older : List Nat)
    (inside outside : List WorkSymbol) :
    AcceptPath graph (.node consumeNode.reference) .accept (loopSteps spent remaining emitted value)
      (markedTape spent remaining (emitted ++ [value]) ((registerWord older).reverse ++ inside) outside)
      (loopFinalTape spent remaining value emitted older inside outside) := by
  induction remaining generalizing spent value outside with
  | zero =>
      have hExit : LocalRejectRun consumeNode (exhaustedSteps spent (emitted ++ [value]))
          (markedTape spent 0 (emitted ++ [value]) ((registerWord older).reverse ++ inside) outside)
          (endTape (older ++ [spent] ++ emitted ++ [value]) inside outside) := by
        have h := BuilderRegisterCountdownControl.exhausted_workRunExact spent (emitted ++ [value])
          ((registerWord older).reverse ++ inside) outside
        simpa only [LocalRejectRun, consumeNode, workStartConfiguration,
          BuilderRegisterCountdownControl.restoredTape_eq_endTape, List.append_assoc,
          List.cons_append, List.nil_append] using h
      have hTag : LocalAcceptRun tagNode (RegisterConstant.steps 4)
          (endTape (older ++ [spent] ++ emitted ++ [value]) inside outside)
          (loopFinalTape spent 0 value emitted older inside outside) := by
        have h := constant_run 4 (older ++ [spent] ++ emitted ++ [value]) inside outside
        simpa only [LocalAcceptRun, tagNode, workStartConfiguration, loopFinalTape, Nat.add_zero, Nat.zero_add,
          List.append_assoc, List.cons_append, List.nil_append] using h
      have hFinish := AcceptPath.step tagNode .accept _ 0 _ _ _ tag_mem hTag
        (AcceptPath.terminal .accept (loopFinalTape spent 0 value emitted older inside outside))
      simpa only [loopSteps, Nat.add_zero] using
        AcceptPath.stepReject consumeNode .accept _ _ _ _ _ consume_mem hExit hFinish
  | succ remaining ih =>
      have hTake : LocalAcceptRun consumeNode (consumeSteps spent (remaining + 1) (emitted ++ [value]))
          (markedTape spent (remaining + 1) (emitted ++ [value]) ((registerWord older).reverse ++ inside) outside)
          (markedTape (spent + 1) remaining (emitted ++ [value]) ((registerWord older).reverse ++ inside) outside) :=
        BuilderRegisterCountdownControl.consume_workRunExact spent remaining (emitted ++ [value])
          ((registerWord older).reverse ++ inside) outside
      have hInc := increment_trace (spent + 1) remaining value emitted ((registerWord older).reverse ++ inside) outside
      have hTail := ih (spent + 1) (value + 1) (outside.drop 1)
      have hIncPath := AcceptPath.step incrementNode .accept _ _ _ _ _ increment_mem hInc hTail
      have hTakePath := AcceptPath.step consumeNode .accept _ _ _ _ _ consume_mem hTake hIncPath
      have hCounter : spent + 1 + remaining = spent + (remaining + 1) := by omega
      have hValue : value + 1 + remaining = value + (remaining + 1) := by omega
      have hDrop : (outside.drop 1).drop (remaining + 5) = outside.drop ((remaining + 1) + 5) := by
        rw [List.drop_drop]
        congr 1
        omega
      simpa only [loopSteps, loopFinalTape, hCounter, hValue, hDrop] using hTakePath

/-- Full range and metadata preserve arbitrary exterior after exactly charged allocation. -/
theorem workRunExactWithOutside (count upper : Nat) (older : List Nat) (inside outside : List WorkSymbol)
    (hCount : count ≤ upper) :
    workRunExact? machine (workSteps count upper)
      (workStartConfiguration machine (endTape (older ++ [count, upper]) inside outside)) =
      some {
        state := machine.acceptState
        tape := finalTapeWithOutside count upper older inside outside } := by
  let emitted := BuilderRegisterDescendingRange.values upper count
  let rangeOutside := BuilderRegisterDescendingRange.exteriorFrom count upper outside
  have hRange : LocalAcceptRun rangeNode (BuilderRegisterDescendingRange.workSteps count upper)
      (endTape (older ++ [count, upper]) inside outside)
      (markedTape 0 count emitted ((registerWord older).reverse ++ inside) rangeOutside) := by
    have h := BuilderRegisterDescendingRange.workRunExactWithOutside counterMarker count upper older inside outside hCount
    simpa only [LocalAcceptRun, rangeNode, workStartConfiguration,
      BuilderRegisterDescendingRange.finalTapeWithOutside_marker, emitted, rangeOutside] using h
  have hZero := zero_trace count emitted ((registerWord older).reverse ++ inside) rangeOutside
  have hLoop := loop_path 0 count 0 emitted older inside (rangeOutside.drop 1)
  have hZeroPath := AcceptPath.step zeroNode .accept _ _ _ _ _ zero_mem hZero hLoop
  have hPath := AcceptPath.step rangeNode .accept _ _ _ _ _ range_mem hRange hZeroPath
  have hRun := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hPath
  have hInitial (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node rangeNode.reference) tape =
        workStartConfiguration machine tape := by rfl
  have hFinal (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration .accept tape =
        { state := machine.acceptState, tape := tape } := by rfl
  have hDrop : (rangeOutside.drop 1).drop (count + 5) = rangeOutside.drop (count + 6) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [hInitial, hFinal] at hRun
  simpa only [machine, workSteps, finalTapeWithOutside, exteriorFrom,
    payloadValues, loopFinalTape, Nat.zero_add, hDrop, emitted, rangeOutside, List.append_assoc] using hRun

/-- The original empty-exterior contract is retained unchanged. -/
theorem workRunExact (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) (hCount : count ≤ upper) :
    workRunExact? machine (workSteps count upper) (initialConfiguration count upper older inside) =
      some (finalConfiguration count upper older inside) := by
  simpa only [initialConfiguration, finalConfiguration, finalTapeWithOutside_nil] using
    workRunExactWithOutside count upper older inside [] hCount

theorem run_compile_exactWithOutside (count upper : Nat) (older : List Nat) (inside outside : List WorkSymbol)
    (hCount : count ≤ upper) :
    run (compileWorkMachine machine) (6 * workSteps count upper)
      (encodeWorkConfiguration
        (workStartConfiguration machine (endTape (older ++ [count, upper]) inside outside))) =
      encodeWorkConfiguration {
        state := machine.acceptState
        tape := finalTapeWithOutside count upper older inside outside } :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExactWithOutside count upper older inside outside hCount)

theorem run_compile_exact (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) (hCount : count ≤ upper) :
    run (compileWorkMachine machine) (6 * workSteps count upper)
      (encodeWorkConfiguration (initialConfiguration count upper older inside)) =
      encodeWorkConfiguration (finalConfiguration count upper older inside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact count upper older inside hCount)

theorem payload_length (count upper : Nat) : (payloadValues count upper).length = count + 2 := by
  simp only [payloadValues, List.length_append, BuilderRegisterDescendingRange.values_length,
    List.length_cons, List.length_nil]

theorem final_inside_preserved (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count upper older inside).tape.right =
      (registerWord (payloadValues count upper)).reverse ++
        ((registerWord (older ++ [count])).reverse ++ inside) := by
  simp only [finalConfiguration, finalTape, endTape, registerWord_append, List.reverse_append, List.append_assoc]

theorem final_exterior (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count upper older inside).tape.left =
      (List.replicate (upper - count + 1) WorkSymbol.blank).drop (count + 6) := rfl

private theorem sum_le (items : List Nat) (bound : Nat) (h : ∀ value ∈ items, value ≤ bound) :
    items.sum ≤ items.length * bound := by
  induction items with
  | nil =>
      simp only [List.sum_nil, List.length_nil, Nat.zero_mul]
      exact Nat.le_refl 0
  | cons value rest ih =>
      have hv := h value List.mem_cons_self
      have hr := ih (fun item hItem => h item (List.mem_cons_of_mem value hItem))
      simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

private theorem newer_span_le (emitted : List Nat) (value bound : Nat)
    (hLength : emitted.length ≤ bound) (hValues : ∀ item ∈ emitted, item ≤ bound) (hValue : value ≤ bound) :
    (registerWord (emitted ++ [value])).length ≤ (bound + 1) * (bound + 1) := by
  have hSum := sum_le emitted bound hValues
  have hProduct := Nat.mul_le_mul_right bound hLength
  simp only [registerWord_length, List.length_append, List.length_cons, List.length_nil,
    List.sum_append, List.sum_cons, List.sum_nil]
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

/-- Complete second-pass cost, including the terminating tag and every bridge. -/
theorem loopSteps_le (spent remaining value bound : Nat) (emitted : List Nat)
    (hCounter : spent + remaining ≤ bound) (hValue : value + remaining ≤ bound)
    (hLength : emitted.length ≤ bound) (hValues : ∀ item ∈ emitted, item ≤ bound) :
    loopSteps spent remaining emitted value ≤ (remaining + 1) * (24 * ((bound + 1) * (bound + 1))) := by
  induction remaining generalizing spent value with
  | zero =>
      have hSpan := newer_span_le emitted value bound hLength hValues (by omega)
      simp only [loopSteps, exhaustedSteps, RegisterConstant.steps, Nat.zero_add, Nat.one_mul]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at hSpan ⊢
      omega
  | succ remaining ih =>
      have hSpan := newer_span_le emitted value bound hLength hValues (by omega)
      have hTail := ih (spent := spent + 1) (value := value + 1) (by omega) (by omega)
      have hOne : consumeSteps spent (remaining + 1) (emitted ++ [value]) + 1 + (2 + 1) ≤
          24 * ((bound + 1) * (bound + 1)) := by
        simp only [consumeSteps, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at hSpan ⊢
        omega
      have hTotal := Nat.add_le_add hOne hTail
      simpa only [loopSteps, Nat.add_assoc, Nat.add_mul, Nat.one_mul, Nat.add_comm, Nat.add_left_comm] using hTotal

theorem workSteps_le (count upper bound : Nat) (hCount : count ≤ bound) (hUpper : upper ≤ bound) :
    workSteps count upper ≤ 60 * ((bound + 1) * (bound + 1) * (bound + 1)) := by
  have hRange := BuilderRegisterDescendingRange.workSteps_le count upper bound hCount hUpper
  have hLoop := loopSteps_le 0 count 0 bound (BuilderRegisterDescendingRange.values upper count)
    (by omega) (by omega)
    (by simpa only [BuilderRegisterDescendingRange.values_length] using hCount)
    (fun value h => Nat.le_trans (BuilderRegisterDescendingRange.values_le upper count value h) hUpper)
  have hScale := Nat.mul_le_mul_right (24 * ((bound + 1) * (bound + 1))) (Nat.add_le_add_right hCount 1)
  have hPositive : 0 < (bound + 1) * (bound + 1) * (bound + 1) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hReorder : (bound + 1) * (24 * ((bound + 1) * (bound + 1))) =
      24 * ((bound + 1) * (bound + 1) * (bound + 1)) := by
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hReorder] at hScale
  unfold workSteps RegisterConstant.steps
  omega

theorem output_span_le (count upper bound : Nat) (older : List Nat) (inside : List WorkSymbol)
    (hCount : count ≤ bound) (hUpper : upper ≤ bound) (hOlder : (registerWord older).length ≤ bound) :
    (registerWord (older ++ [count] ++ payloadValues count upper)).length +
      (finalConfiguration count upper older inside).tape.left.length ≤ 10 * ((bound + 1) * (bound + 1)) := by
  have hRange := BuilderRegisterDescendingRange.output_span_le count upper bound older inside hCount hUpper hOlder
  have hOutside :
      (finalConfiguration count upper older inside).tape.left.length ≤
        (BuilderRegisterDescendingRange.finalConfiguration count upper older inside).tape.left.length := by
    simp only [final_exterior, BuilderRegisterDescendingRange.final_exterior, List.length_drop]
    exact Nat.sub_le _ _
  have hLength : (registerWord (older ++ [count] ++ payloadValues count upper)).length =
      (registerWord (older ++ [count] ++ BuilderRegisterDescendingRange.values upper count)).length + (count + 6) := by
    simp only [payloadValues, registerWord_append, List.length_append, registerWord_length,
      List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    omega
  have hExtra : count + 6 ≤ 6 * ((bound + 1) * (bound + 1)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  rw [hLength]
  omega

def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.constant 10) (.mul (.add bound (.constant 1)) (.add bound (.constant 1)))

def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.constant 360) (.mul (.mul (.add bound (.constant 1)) (.add bound (.constant 1))) (.add bound (.constant 1)))

theorem source_polynomial_bounds (bound : NatPolynomial) (inputLength count upper : Nat)
    (older : List Nat) (inside : List WorkSymbol)
    (hCount : count ≤ bound.eval inputLength) (hUpper : upper ≤ bound.eval inputLength)
    (hOlder : (registerWord older).length ≤ bound.eval inputLength) :
    (registerWord (older ++ [count] ++ payloadValues count upper)).length +
        (finalConfiguration count upper older inside).tape.left.length ≤ (spanPolynomial bound).eval inputLength ∧
      6 * workSteps count upper ≤ (rawTimePolynomial bound).eval inputLength := by
  have hSpan := output_span_le count upper (bound.eval inputLength) older inside hCount hUpper hOlder
  have hTime := Nat.mul_le_mul_left 6 (workSteps_le count upper (bound.eval inputLength) hCount hUpper)
  constructor
  · simpa only [spanPolynomial, NatPolynomial.eval_mul, NatPolynomial.eval_constant, NatPolynomial.eval_add] using hSpan
  · simpa only [rawTimePolynomial, NatPolynomial.eval_mul, NatPolynomial.eval_constant, NatPolynomial.eval_add,
      ← Nat.mul_assoc] using hTime

theorem exteriorFrom_length_le (count upper : Nat) (outside : List WorkSymbol) :
    (exteriorFrom count upper outside).length ≤
      ((List.replicate (upper - count + 1) WorkSymbol.blank).drop (count + 6)).length + outside.length := by
  simp only [exteriorFrom, BuilderRegisterDescendingRange.exteriorFrom, List.length_drop,
    List.length_append, List.length_replicate]
  omega

theorem output_span_withOutside_le (count upper bound : Nat) (older : List Nat)
    (inside outside : List WorkSymbol)
    (hCount : count ≤ bound) (hUpper : upper ≤ bound) (hOlder : (registerWord older).length ≤ bound) :
    (registerWord (older ++ [count] ++ payloadValues count upper)).length +
        (finalTapeWithOutside count upper older inside outside).left.length ≤
      10 * ((bound + 1) * (bound + 1)) + outside.length := by
  have hOld := output_span_le count upper bound older inside hCount hUpper hOlder
  have hOutside := exteriorFrom_length_le count upper outside
  rw [final_exterior] at hOld
  change (registerWord (older ++ [count] ++ payloadValues count upper)).length +
    (exteriorFrom count upper outside).length ≤ _
  omega

theorem source_polynomial_boundsWithOutside (bound outsideBound : NatPolynomial)
    (inputLength count upper : Nat) (older : List Nat) (inside outside : List WorkSymbol)
    (hCount : count ≤ bound.eval inputLength) (hUpper : upper ≤ bound.eval inputLength)
    (hOlder : (registerWord older).length ≤ bound.eval inputLength)
    (hOutside : outside.length ≤ outsideBound.eval inputLength) :
    (registerWord (older ++ [count] ++ payloadValues count upper)).length +
        (finalTapeWithOutside count upper older inside outside).left.length ≤
      (NatPolynomial.add (spanPolynomial bound) outsideBound).eval inputLength ∧
    6 * workSteps count upper ≤ (rawTimePolynomial bound).eval inputLength := by
  have hSpace := output_span_withOutside_le count upper (bound.eval inputLength)
    older inside outside hCount hUpper hOlder
  have hTime := (source_polynomial_bounds bound inputLength count upper older inside hCount hUpper hOlder).2
  constructor
  · simp only [NatPolynomial.eval_add, spanPolynomial, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
    omega
  · exact hTime

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph

theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

end PNP.Concrete.CookLevin.BuilderRegisterExactlyOnePayload
