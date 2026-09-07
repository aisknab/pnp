/-
Copyright (c) 2026 PNP Labs.

One fixed finite machine constructs every descending consecutive register list
from an actual written count and exclusive upper bound. Its control graph does
not depend on those values. All back-edges, counter restoration and final
duplicate erasure occur on tape and are charged in the exact execution theorem.

The shape-source binding, final payload metadata and complete formula builder
remain separate obligations; this is not a complete-builder progress claim.
-/
import PNP.Concrete.CookLevinBuilderRegisterCountdownControl

namespace PNP.Concrete.CookLevin.BuilderRegisterDescendingRange

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderRegisterCountdownControl
  (markCounterMachine consume decrement markedTape restoredTape counterMarker spentSymbol
    initializeSteps consumeSteps exhaustedSteps consumeWith restoredTapeWith)
open WorkMachineProgramGraph (Node NodeRef Graph)
open WorkMachineProgramPath (LocalAcceptRun LocalRejectRun AcceptPath)

/-- Mathematical endpoint specification, never executable control data. -/
def values : Nat → Nat → List Nat
  | _, 0 => []
  | upper, count + 1 => (upper - 1) :: values (upper - 1) count

theorem values_length (upper count : Nat) : (values upper count).length = count := by
  induction count generalizing upper with
  | zero => rfl
  | succ count ih => simp only [values, List.length_cons, ih]

theorem values_index (upper count : Nat) (index : Fin count) :
    (values upper count)[index.val]'(by rw [values_length]; exact index.isLt) =
      upper - (index.val + 1) := by
  induction count generalizing upper with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      cases index with
      | mk index hIndex =>
          cases index with
          | zero => rfl
          | succ next =>
              have hNext : next < count := by omega
              have h := ih (upper - 1) ⟨next, hNext⟩
              change (values (upper - 1) count)[next]'(by rw [values_length]; exact hNext) =
                upper - (next + 1 + 1)
              rw [h]
              change upper - 1 - (next + 1) = upper - (next + 1 + 1)
              omega

theorem values_le (upper count : Nat) : ∀ value ∈ values upper count, value ≤ upper := by
  induction count generalizing upper with
  | zero => intro value h; contradiction
  | succ count ih =>
      intro value h
      simp only [values, List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.sub_le _ _
      · exact Nat.le_trans (ih (upper - 1) value h) (Nat.sub_le _ _)

def consumeReference : NodeRef := { name := 1, startState := consume.startState }

def eraseNode : Node :=
  { name := 4
    program := BuilderRegisterErase.oneMachine
    onAccept := .accept
    onReject := .dead }

def copyNode : Node :=
  { name := 3
    program := RegisterCopy.machine 0
    onAccept := .node consumeReference
    onReject := .dead }

def decrementNode : Node :=
  { name := 2
    program := decrement
    onAccept := .node copyNode.reference
    onReject := .dead }

def consumeNodeWith (delimiter : WorkSymbol) : Node :=
  { name := 1
    program := consumeWith delimiter
    onAccept := .node decrementNode.reference
    onReject := .node eraseNode.reference }

def consumeNode : Node := consumeNodeWith separatorSymbol

def markNode : Node :=
  { name := 0
    program := markCounterMachine
    onAccept := .node consumeNode.reference
    onReject := .dead }

def graphWith (delimiter : WorkSymbol) : Graph :=
  { nodes := [markNode, consumeNodeWith delimiter, decrementNode, copyNode, eraseNode]
    entry := markNode.reference }

def graph : Graph := graphWith separatorSymbol

def machineWith (delimiter : WorkSymbol) : WorkMachine := WorkMachineProgramGraph.machine (graphWith delimiter)
def machine : WorkMachine := machineWith separatorSymbol

private theorem mark_mem (delimiter : WorkSymbol) : markNode ∈ (graphWith delimiter).nodes := List.Mem.head _
private theorem consume_mem (delimiter : WorkSymbol) : consumeNodeWith delimiter ∈ (graphWith delimiter).nodes := List.Mem.tail _ (List.Mem.head _)
private theorem decrement_mem (delimiter : WorkSymbol) : decrementNode ∈ (graphWith delimiter).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem copy_mem (delimiter : WorkSymbol) : copyNode ∈ (graphWith delimiter).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem erase_mem (delimiter : WorkSymbol) : eraseNode ∈ (graphWith delimiter).nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem copy_good : Good (RegisterCopy.machine 0) := by
  refine ⟨RegisterCopy.rules_pairwise_query_distinct 0, ?_, ?_, RegisterCopy.machine_acceptState_ne_rejectState 0⟩
  · intro item h
    exact Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState 0 item h)
  · intro item h
    have hBound := RegisterCopy.rule_source_lt_acceptState 0 item h
    rw [RegisterCopy.machine_acceptState] at hBound
    rw [RegisterCopy.machine_rejectState]
    unfold RegisterCopy.stateCount at hBound ⊢
    omega

private theorem erase_good : Good BuilderRegisterErase.oneMachine :=
  ⟨BuilderRegisterErase.one_rules_pairwise_query_distinct, BuilderRegisterErase.one_noRuleAtAccept,
    BuilderRegisterErase.one_noRuleAtReject, BuilderRegisterErase.one_acceptState_ne_rejectState⟩

theorem graphWith_wellFormed (delimiter : WorkSymbol) : (graphWith delimiter).WellFormed := by
  have hNames : ((graphWith delimiter).nodes.map Node.name).Pairwise (fun left right : Nat => left ≠ right) := by
    change ([0, 1, 2, 3, 4] : List Nat).Pairwise (fun left right => left ≠ right)
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graphWith, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl
    · exact BuilderRegisterCountdownControl.initialize_control
    · exact BuilderRegisterCountdownControl.consumeWith_control delimiter
    · exact BuilderRegisterCountdownControl.decrement_control
    · exact copy_good
    · exact erase_good
  · exact ⟨markNode, mark_mem delimiter, rfl, rfl⟩
  · intro node hMem
    simp only [graphWith, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨consumeNodeWith delimiter, consume_mem delimiter, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨decrementNode, decrement_mem delimiter, rfl, rfl⟩, ⟨eraseNode, erase_mem delimiter, rfl, rfl⟩⟩
    · exact ⟨⟨copyNode, copy_mem delimiter, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨consumeNodeWith delimiter, consume_mem delimiter, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

theorem graph_wellFormed : graph.WellFormed := graphWith_wellFormed separatorSymbol

/-- Every transition between local kernels, including the loop back-edge, is charged. -/
def loopSteps : Nat → Nat → List Nat → Nat → Nat
  | spent, 0, emitted, value =>
      exhaustedSteps spent (emitted ++ [value]) + 1 + (value + 2 + 1)
  | spent, remaining + 1, emitted, value =>
      consumeSteps spent (remaining + 1) (emitted ++ [value]) + 1 +
        (2 + 1 + (RegisterCopy.steps [] (value - 1) + 1 +
          loopSteps (spent + 1) remaining (emitted ++ [value - 1]) (value - 1)))

def workSteps (count upper : Nat) : Nat :=
  initializeSteps count upper + 1 + loopSteps 0 count [] upper

def initialConfiguration (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ [count, upper]) inside [])

def finalTape (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) : WorkTape :=
  endTape (older ++ [count] ++ values upper count) inside
    (List.replicate (upper - count + 1) .blank)

def finalTapeWith (delimiter : WorkSymbol) (count upper : Nat) (older : List Nat)
    (inside : List WorkSymbol) : WorkTape :=
  restoredTapeWith delimiter count (values upper count) ((registerWord older).reverse ++ inside)
    (List.replicate (upper - count + 1) .blank)

theorem finalTapeWith_separator (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    finalTapeWith separatorSymbol count upper older inside = finalTape count upper older inside := by
  simpa only [finalTapeWith, BuilderRegisterCountdownControl.restoredTapeWith_separator,
    BuilderRegisterCountdownControl.restoredTape_eq_endTape, finalTape, List.append_assoc,
    List.cons_append, List.nil_append]

theorem finalTapeWith_marker (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    finalTapeWith counterMarker count upper older inside =
      markedTape 0 count (values upper count) ((registerWord older).reverse ++ inside)
        (List.replicate (upper - count + 1) .blank) :=
  BuilderRegisterCountdownControl.restoredTapeWith_marker _ _ _ _

/-- Cleared working register followed by exactly the unallocated original exterior. -/
def exteriorFrom (count upper : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  List.replicate (upper - count + 1) .blank ++ outside.drop (values upper count).sum

def finalTapeWithOutside (delimiter : WorkSymbol) (count upper : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkTape :=
  restoredTapeWith delimiter count (values upper count) ((registerWord older).reverse ++ inside)
    (exteriorFrom count upper outside)

theorem finalTapeWithOutside_nil (delimiter : WorkSymbol) (count upper : Nat) (older : List Nat)
    (inside : List WorkSymbol) :
    finalTapeWithOutside delimiter count upper older inside [] = finalTapeWith delimiter count upper older inside := by
  simp only [finalTapeWithOutside, finalTapeWith, exteriorFrom, List.drop_nil, List.append_nil]

theorem finalTapeWithOutside_separator (count upper : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    finalTapeWithOutside separatorSymbol count upper older inside outside =
      endTape (older ++ [count] ++ values upper count) inside (exteriorFrom count upper outside) := by
  simpa only [finalTapeWithOutside, BuilderRegisterCountdownControl.restoredTapeWith_separator,
    BuilderRegisterCountdownControl.restoredTape_eq_endTape, List.append_assoc,
    List.cons_append, List.nil_append]

theorem finalTapeWithOutside_marker (count upper : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    finalTapeWithOutside counterMarker count upper older inside outside =
      markedTape 0 count (values upper count) ((registerWord older).reverse ++ inside)
        (exteriorFrom count upper outside) :=
  BuilderRegisterCountdownControl.restoredTapeWith_marker _ _ _ _

def finalConfiguration (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  { state := machine.acceptState
    tape := finalTape count upper older inside }

private def counterWord (spent remaining : Nat) : List WorkSymbol :=
  counterMarker :: (List.replicate spent spentSymbol ++ List.replicate remaining unitSymbol)

private theorem decrement_trace (spent remaining value : Nat) (emitted : List Nat)
    (inside outside : List WorkSymbol) :
    LocalAcceptRun decrementNode 2
      (markedTape spent remaining (emitted ++ [value + 1]) inside outside)
      (markedTape spent remaining (emitted ++ [value]) inside (.blank :: outside)) := by
  have h := BuilderRegisterCountdownControl.decrement_workRunExact value
    (counterWord spent remaining ++ registerWord emitted) inside outside
  simpa only [LocalAcceptRun, decrementNode, workStartConfiguration, markedTape,
    counterWord, registerWord_append, registerWord, List.append_nil, List.reverse_append,
    List.reverse_cons, List.reverse_replicate, List.reverse_nil, List.cons_append,
    List.nil_append, List.append_assoc] using h

private theorem copy_trace (spent remaining value : Nat) (emitted : List Nat) (inside outside : List WorkSymbol) :
    LocalAcceptRun copyNode (RegisterCopy.steps [] value)
      (markedTape spent remaining (emitted ++ [value]) inside (.blank :: outside))
      (markedTape spent remaining ((emitted ++ [value]) ++ [value]) inside (outside.drop value)) := by
  let oldWord := counterWord spent remaining ++ registerWord emitted
  have h := RegisterCopy.workRunExact oldWord inside (.blank :: outside) value []
  change workRunExact? (RegisterCopy.machine 0) (RegisterCopy.steps [] value)
    {
      state := 0
      tape := {
        left := WorkSymbol.blank :: outside
        head := scratchEndSymbol
        right := (oldWord ++ registerWord [value]).reverse ++ inside } } =
    some {
      state := RegisterCopy.stateCount 0
      tape := {
        left := (WorkSymbol.blank :: outside).drop (value + 1)
        head := scratchEndSymbol
        right := (oldWord ++ registerWord [value, value]).reverse ++ inside } } at h
  have hOutside : (WorkSymbol.blank :: outside).drop (value + 1) = outside.drop value := rfl
  simpa only [LocalAcceptRun, copyNode, workStartConfiguration,
    RegisterCopy.machine_startState, RegisterCopy.machine_acceptState,
    markedTape, oldWord, counterWord, hOutside, registerWord_append,
    registerWord, List.append_nil, List.nil_append, List.reverse_append, List.reverse_cons,
    List.reverse_replicate, List.reverse_nil, List.cons_append, List.append_assoc] using h

private def loopFinalTape (delimiter : WorkSymbol) (spent remaining value : Nat)
    (emitted older : List Nat) (inside outside : List WorkSymbol) : WorkTape :=
  restoredTapeWith delimiter (spent + remaining) (emitted ++ values value remaining)
    ((registerWord older).reverse ++ inside)
    (List.replicate (value - remaining + 1) .blank ++ outside.drop (values value remaining).sum)

private theorem loop_path (delimiter : WorkSymbol) (spent remaining value : Nat) (emitted older : List Nat) (inside outside : List WorkSymbol)
    (hRemaining : remaining ≤ value) :
    AcceptPath (graphWith delimiter) (.node (consumeNodeWith delimiter).reference) .accept (loopSteps spent remaining emitted value)
      (markedTape spent remaining (emitted ++ [value]) ((registerWord older).reverse ++ inside) outside)
      (loopFinalTape delimiter spent remaining value emitted older inside outside) := by
  induction remaining generalizing spent value emitted outside with
  | zero =>
      have hExit : LocalRejectRun (consumeNodeWith delimiter) (exhaustedSteps spent (emitted ++ [value]))
          (markedTape spent 0 (emitted ++ [value]) ((registerWord older).reverse ++ inside) outside)
          (restoredTapeWith delimiter spent (emitted ++ [value]) ((registerWord older).reverse ++ inside) outside) :=
        BuilderRegisterCountdownControl.exhaustedWith_workRunExact delimiter spent (emitted ++ [value])
          ((registerWord older).reverse ++ inside) outside
      have hErase : LocalAcceptRun eraseNode (value + 2)
          (restoredTapeWith delimiter spent (emitted ++ [value]) ((registerWord older).reverse ++ inside) outside)
          (loopFinalTape delimiter spent 0 value emitted older inside outside) := by
        have h := BuilderRegisterErase.one_workRunExact emitted value
          (List.replicate spent unitSymbol ++ delimiter :: ((registerWord older).reverse ++ inside)) outside
        simpa only [LocalAcceptRun, eraseNode, workStartConfiguration, loopFinalTape,
          restoredTapeWith, endTape, values, Nat.add_zero, Nat.sub_zero, List.append_nil,
          List.append_assoc, List.sum_nil, List.drop_zero] using h
      have hFinish := AcceptPath.step eraseNode .accept (value + 2) 0 _ _ _ (erase_mem delimiter) hErase
        (AcceptPath.terminal .accept (loopFinalTape delimiter spent 0 value emitted older inside outside))
      simpa only [loopSteps, Nat.add_zero] using
        AcceptPath.stepReject (consumeNodeWith delimiter) .accept _ _ _ _ _ (consume_mem delimiter) hExit hFinish
  | succ remaining ih =>
      cases value with
      | zero => exact False.elim (by omega)
      | succ value =>
          have hTake : LocalAcceptRun (consumeNodeWith delimiter) (consumeSteps spent (remaining + 1) (emitted ++ [value + 1]))
              (markedTape spent (remaining + 1) (emitted ++ [value + 1]) ((registerWord older).reverse ++ inside) outside)
              (markedTape (spent + 1) remaining (emitted ++ [value + 1]) ((registerWord older).reverse ++ inside) outside) := by
            exact BuilderRegisterCountdownControl.consumeWith_workRunExact delimiter spent remaining (emitted ++ [value + 1])
              ((registerWord older).reverse ++ inside) outside
          have hDec := decrement_trace (spent + 1) remaining value emitted ((registerWord older).reverse ++ inside) outside
          have hCopy := copy_trace (spent + 1) remaining value emitted ((registerWord older).reverse ++ inside) outside
          have hTail := ih (spent := spent + 1) (value := value) (emitted := emitted ++ [value]) (outside := outside.drop value) (by omega)
          have hCopyPath := AcceptPath.step copyNode .accept _ _ _ _ _ (copy_mem delimiter) hCopy hTail
          have hDecPath := AcceptPath.step decrementNode .accept _ _ _ _ _ (decrement_mem delimiter) hDec hCopyPath
          have hTakePath := AcceptPath.step (consumeNodeWith delimiter) .accept _ _ _ _ _ (consume_mem delimiter) hTake hDecPath
          have hCounter : spent + 1 + remaining = spent + (remaining + 1) := by omega
          have hResidual : value + 1 - (remaining + 1) = value - remaining := by omega
          have hDrop : (outside.drop value).drop (values value remaining).sum =
              outside.drop (values (value + 1) (remaining + 1)).sum := by
            simp only [List.drop_drop, values, Nat.add_sub_cancel, List.sum_cons, Nat.add_comm]
          simpa only [loopSteps, loopFinalTape, hDrop, values, Nat.add_sub_cancel, hCounter, hResidual,
            List.append_assoc, List.cons_append, List.nil_append] using hTakePath

/-- One fixed finite program, every count and upper bound, exact list and cleanup. -/
theorem workRunExactWithOutside (delimiter : WorkSymbol) (count upper : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) (hCount : count ≤ upper) :
    workRunExact? (machineWith delimiter) (workSteps count upper)
      (workStartConfiguration (machineWith delimiter) (endTape (older ++ [count, upper]) inside outside)) =
      some {
        state := (machineWith delimiter).acceptState
        tape := finalTapeWithOutside delimiter count upper older inside outside } := by
  have hMark : LocalAcceptRun markNode (initializeSteps count upper)
      (endTape (older ++ [count, upper]) inside outside)
      (markedTape 0 count [upper] ((registerWord older).reverse ++ inside) outside) := by
    have h := BuilderRegisterCountdownControl.initialize_workRunExact count upper ((registerWord older).reverse ++ inside) outside
    simpa only [LocalAcceptRun, markNode, workStartConfiguration,
      BuilderRegisterCountdownControl.restoredTape_eq_endTape] using h
  have hTail := loop_path delimiter 0 count upper [] older inside outside hCount
  have hPath := AcceptPath.step markNode .accept _ _ _ _ _ (mark_mem delimiter) hMark hTail
  have hRun := WorkMachineProgramPath.runExact (graphWith delimiter) _ _ _ _ _ (graphWith_wellFormed delimiter) hPath
  have hInitial (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node markNode.reference) tape =
        workStartConfiguration (machineWith delimiter) tape := by rfl
  have hFinal (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration .accept tape =
        { state := (machineWith delimiter).acceptState, tape := tape } := by rfl
  rw [hInitial, hFinal] at hRun
  simpa only [machineWith, workSteps, finalTapeWithOutside, exteriorFrom, loopFinalTape,
    Nat.zero_add, List.nil_append, List.append_nil] using hRun

theorem workRunExactWith (delimiter : WorkSymbol) (count upper : Nat) (older : List Nat)
    (inside : List WorkSymbol) (hCount : count ≤ upper) :
    workRunExact? (machineWith delimiter) (workSteps count upper)
      (workStartConfiguration (machineWith delimiter) (endTape (older ++ [count, upper]) inside [])) =
      some {
        state := (machineWith delimiter).acceptState
        tape := finalTapeWith delimiter count upper older inside } := by
  simpa only [finalTapeWithOutside_nil] using
    workRunExactWithOutside delimiter count upper older inside [] hCount

theorem run_compile_exactWithOutside (delimiter : WorkSymbol) (count upper : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) (hCount : count ≤ upper) :
    run (compileWorkMachine (machineWith delimiter)) (6 * workSteps count upper)
      (encodeWorkConfiguration
        (workStartConfiguration (machineWith delimiter) (endTape (older ++ [count, upper]) inside outside))) =
      encodeWorkConfiguration {
        state := (machineWith delimiter).acceptState
        tape := finalTapeWithOutside delimiter count upper older inside outside } :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExactWithOutside delimiter count upper older inside outside hCount)

theorem workRunExact (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) (hCount : count ≤ upper) :
    workRunExact? machine (workSteps count upper) (initialConfiguration count upper older inside) =
      some (finalConfiguration count upper older inside) := by
  simpa only [machine, initialConfiguration, finalConfiguration, finalTapeWith_separator] using
    workRunExactWith separatorSymbol count upper older inside hCount

theorem run_compile_exactWith (delimiter : WorkSymbol) (count upper : Nat) (older : List Nat)
    (inside : List WorkSymbol) (hCount : count ≤ upper) :
    run (compileWorkMachine (machineWith delimiter)) (6 * workSteps count upper)
      (encodeWorkConfiguration
        (workStartConfiguration (machineWith delimiter) (endTape (older ++ [count, upper]) inside []))) =
      encodeWorkConfiguration {
        state := (machineWith delimiter).acceptState
        tape := finalTapeWith delimiter count upper older inside } :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExactWith delimiter count upper older inside hCount)

theorem run_compile_exact (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) (hCount : count ≤ upper) :
    run (compileWorkMachine machine) (6 * workSteps count upper)
      (encodeWorkConfiguration (initialConfiguration count upper older inside)) =
      encodeWorkConfiguration (finalConfiguration count upper older inside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact count upper older inside hCount)

theorem final_register_count (count upper : Nat) (older : List Nat) :
    (older ++ [count] ++ values upper count).length = older.length + 1 + count := by
  simp only [List.length_append, List.length_cons, List.length_nil, values_length]

theorem final_inside_preserved (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count upper older inside).tape.right =
      (registerWord (values upper count)).reverse ++
        ((registerWord (older ++ [count])).reverse ++ inside) := by
  simp only [finalConfiguration, finalTape, endTape, registerWord_append, List.reverse_append, List.append_assoc]

theorem final_exterior (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count upper older inside).tape.left = List.replicate (upper - count + 1) .blank := rfl

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

/-- Bounds the entire loop, not just a supplied step or finite prefix. -/
theorem loopSteps_le (spent remaining value bound : Nat) (emitted : List Nat)
    (hCounter : spent + remaining ≤ bound) (hBudget : emitted.length + remaining ≤ bound)
    (hValues : ∀ item ∈ emitted, item ≤ bound) (hValue : value ≤ bound) :
    loopSteps spent remaining emitted value ≤ (remaining + 1) * (20 * ((bound + 1) * (bound + 1))) := by
  induction remaining generalizing spent emitted value with
  | zero =>
      have hSpan := newer_span_le emitted value bound (by omega) hValues hValue
      simp only [loopSteps, exhaustedSteps]
      simp only [Nat.zero_add, Nat.one_mul]
      have hBound : bound ≤ bound * bound + 2 * bound + 1 := by omega
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at hSpan ⊢
      omega
  | succ remaining ih =>
      have hSpan := newer_span_le emitted value bound (by omega) hValues hValue
      have hNextValues : ∀ item ∈ emitted ++ [value - 1], item ≤ bound := by
        intro item h
        rcases List.mem_append.mp h with h | h
        · exact hValues item h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          subst item
          omega
      have hTail := ih (spent := spent + 1) (emitted := emitted ++ [value - 1]) (value := value - 1)
        (by omega) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        hNextValues (by omega)
      have hSquare := Nat.mul_le_mul (show value - 1 ≤ bound by omega) (show value - 1 ≤ bound by omega)
      have hCopy := RegisterCopy.steps_closed [] (value - 1)
      simp only [List.length_nil, List.sum_nil, Nat.zero_add, Nat.add_zero, Nat.one_mul] at hCopy
      have hOne : consumeSteps spent (remaining + 1) (emitted ++ [value]) + 1 +
          (2 + 1 + (RegisterCopy.steps [] (value - 1) + 1)) ≤
          20 * ((bound + 1) * (bound + 1)) := by
        simp only [consumeSteps, hCopy, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one,
          Nat.mul_assoc] at hSpan ⊢
        omega
      have hTotal := Nat.add_le_add hOne hTail
      simpa only [loopSteps, Nat.add_assoc, Nat.add_mul, Nat.one_mul, Nat.add_comm, Nat.add_left_comm] using hTotal

theorem workSteps_le (count upper bound : Nat) (hCount : count ≤ bound) (hUpper : upper ≤ bound) :
    workSteps count upper ≤ 30 * ((bound + 1) * (bound + 1) * (bound + 1)) := by
  have hLoop := loopSteps_le 0 count upper bound [] (by omega) (by simpa only [List.length_nil, Nat.zero_add] using hCount) (by intro item h; contradiction) hUpper
  have hScale := Nat.mul_le_mul_right (20 * ((bound + 1) * (bound + 1))) (Nat.add_le_add_right hCount 1)
  have hQuadratic : bound ≤ (bound + 1) * (bound + 1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  have hCubic : (bound + 1) * (bound + 1) ≤ (bound + 1) * (bound + 1) * (bound + 1) := by
    calc
      (bound + 1) * (bound + 1) = ((bound + 1) * (bound + 1)) * 1 := by rw [Nat.mul_one]
      _ ≤ ((bound + 1) * (bound + 1)) * (bound + 1) := Nat.mul_le_mul_left _ (by omega)
  have hPositive : 0 < (bound + 1) * (bound + 1) := Nat.mul_pos (by omega) (by omega)
  unfold workSteps initializeSteps
  have hReorder : (bound + 1) * (20 * ((bound + 1) * (bound + 1))) =
      20 * ((bound + 1) * (bound + 1) * (bound + 1)) := by
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hReorder] at hScale
  omega

theorem output_span_le (count upper bound : Nat) (older : List Nat) (inside : List WorkSymbol)
    (hCount : count ≤ bound) (hUpper : upper ≤ bound) (hOlder : (registerWord older).length ≤ bound) :
    (registerWord (older ++ [count] ++ values upper count)).length +
      (finalConfiguration count upper older inside).tape.left.length ≤ 4 * ((bound + 1) * (bound + 1)) := by
  have hValues := sum_le (values upper count) bound
    (fun value h => Nat.le_trans (values_le upper count value h) hUpper)
  have hProd := Nat.mul_le_mul_right bound hCount
  simp only [values_length] at hValues
  simp only [registerWord_append, List.length_append, registerWord_length, values_length,
    List.length_cons, List.length_nil, List.sum_cons, List.sum_nil,
    final_exterior, List.length_replicate] at hOlder ⊢
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.constant 4) (.mul (.add bound (.constant 1)) (.add bound (.constant 1)))

def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.constant 180) (.mul (.mul (.add bound (.constant 1)) (.add bound (.constant 1))) (.add bound (.constant 1)))

theorem source_polynomial_bounds (bound : NatPolynomial) (inputLength count upper : Nat)
    (older : List Nat) (inside : List WorkSymbol)
    (hCount : count ≤ bound.eval inputLength) (hUpper : upper ≤ bound.eval inputLength)
    (hOlder : (registerWord older).length ≤ bound.eval inputLength) :
    (registerWord (older ++ [count] ++ values upper count)).length +
        (finalConfiguration count upper older inside).tape.left.length ≤ (spanPolynomial bound).eval inputLength ∧
      6 * workSteps count upper ≤ (rawTimePolynomial bound).eval inputLength := by
  have hSpan := output_span_le count upper (bound.eval inputLength) older inside hCount hUpper hOlder
  have hTime := Nat.mul_le_mul_left 6 (workSteps_le count upper (bound.eval inputLength) hCount hUpper)
  constructor
  · simpa only [spanPolynomial, NatPolynomial.eval_mul, NatPolynomial.eval_constant, NatPolynomial.eval_add] using hSpan
  · simpa only [rawTimePolynomial, NatPolynomial.eval_mul, NatPolynomial.eval_constant, NatPolynomial.eval_add,
      ← Nat.mul_assoc] using hTime

theorem exteriorFrom_length_le (count upper : Nat) (outside : List WorkSymbol) :
    (exteriorFrom count upper outside).length ≤ upper - count + 1 + outside.length := by
  simp only [exteriorFrom, List.length_append, List.length_replicate, List.length_drop]
  omega

theorem output_span_withOutside_le (delimiter : WorkSymbol) (count upper bound : Nat)
    (older : List Nat) (inside outside : List WorkSymbol)
    (hCount : count ≤ bound) (hUpper : upper ≤ bound) (hOlder : (registerWord older).length ≤ bound) :
    (registerWord (older ++ [count] ++ values upper count)).length +
        (finalTapeWithOutside delimiter count upper older inside outside).left.length ≤
      4 * ((bound + 1) * (bound + 1)) + outside.length := by
  have hOld := output_span_le count upper bound older inside hCount hUpper hOlder
  have hOutside := exteriorFrom_length_le count upper outside
  simp only [final_exterior, List.length_replicate] at hOld
  change (registerWord (older ++ [count] ++ values upper count)).length +
    (exteriorFrom count upper outside).length ≤ _
  omega

theorem source_polynomial_boundsWithOutside (delimiter : WorkSymbol) (bound outsideBound : NatPolynomial)
    (inputLength count upper : Nat) (older : List Nat) (inside outside : List WorkSymbol)
    (hCount : count ≤ bound.eval inputLength) (hUpper : upper ≤ bound.eval inputLength)
    (hOlder : (registerWord older).length ≤ bound.eval inputLength)
    (hOutside : outside.length ≤ outsideBound.eval inputLength) :
    (registerWord (older ++ [count] ++ values upper count)).length +
        (finalTapeWithOutside delimiter count upper older inside outside).left.length ≤
      (NatPolynomial.add (spanPolynomial bound) outsideBound).eval inputLength ∧
    6 * workSteps count upper ≤ (rawTimePolynomial bound).eval inputLength := by
  have hSpace := output_span_withOutside_le delimiter count upper (bound.eval inputLength)
    older inside outside hCount hUpper hOlder
  have hTime := (source_polynomial_bounds bound inputLength count upper older inside hCount hUpper hOlder).2
  constructor
  · simp only [NatPolynomial.eval_add, spanPolynomial, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
    omega
  · exact hTime

theorem rulesWith_pairwise_query_distinct (delimiter : WorkSymbol) :
    (machineWith delimiter).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise (graphWith delimiter) (graphWith_wellFormed delimiter)

theorem noRuleWithAtAccept (delimiter : WorkSymbol) : WorkMachineChain.NoRuleAtAccept (machineWith delimiter) :=
  WorkMachineProgramGraph.noRuleAt_globalAccept (graphWith delimiter)

theorem noRuleWithAtReject (delimiter : WorkSymbol) :
    WorkMachineProgramGraph.NoRuleAt (machineWith delimiter) (machineWith delimiter).rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject (graphWith delimiter)

theorem acceptWith_ne_rejectState (delimiter : WorkSymbol) :
    (machineWith delimiter).acceptState ≠ (machineWith delimiter).rejectState := by
  change (0 : Nat) ≠ 1
  decide

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph

theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

end PNP.Concrete.CookLevin.BuilderRegisterDescendingRange
