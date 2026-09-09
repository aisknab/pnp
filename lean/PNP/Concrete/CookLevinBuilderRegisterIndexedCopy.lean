/-
Copyright (c) 2026 PNP Labs.

Runtime-ordinal access to an arbitrary reader-ordered register list.
One fixed finite program consumes the written ordinal, advances a physical
candidate marker, restores the original list and ordinal, and copies the
selected value. The valid-index data domain is explicit. This primitive does
not classify invalid ordinals or supply the source selector's indexing proof.
-/
import PNP.Concrete.CookLevinBuilderRegisterRootCopy

namespace PNP.Concrete.CookLevin.BuilderRegisterIndexedCopy

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderRegisterCountdownControl (counterMarker spentSymbol markedTape consumeSteps exhaustedSteps)
open WorkMachineProgramGraph (Node Graph)
open WorkMachineProgramPath (AcceptPath LocalAcceptRun LocalRejectRun)

/-- A temporary delimiter inside the register region, distinct from its alphabet. -/
def candidateMarker : WorkSymbol := ⟨.zero, .blank⟩

/-- Physical reader order, beginning at the newest listed register. -/
def readerWord : List Nat → List WorkSymbol
  | [] => []
  | value :: rest => List.replicate value unitSymbol ++ separatorSymbol :: readerWord rest

theorem readerWord_append (left right : List Nat) :
    readerWord (left ++ right) = readerWord left ++ readerWord right := by
  induction left with
  | nil => rfl
  | cons value rest ih =>
      simp only [readerWord, List.cons_append, ih, List.append_assoc]

theorem readerWord_eq_reverse (values : List Nat) :
    readerWord values = (registerWord values.reverse).reverse := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [readerWord, List.reverse_cons, registerWord_append, List.reverse_append,
        registerWord, List.reverse_cons, List.reverse_append, List.reverse_replicate,
        List.reverse_nil, List.nil_append, List.append_nil, List.cons_append, List.append_assoc, ← ih]

theorem readerWord_length (values : List Nat) :
    (readerWord values).length = values.sum + values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [readerWord, List.length_append, List.length_replicate, List.length_cons,
        List.sum_cons, ih]
      omega

private theorem readerWord_symbols (values : List Nat) (symbol : WorkSymbol)
    (h : symbol ∈ readerWord values) : symbol = unitSymbol ∨ symbol = separatorSymbol := by
  rw [readerWord_eq_reverse] at h
  exact BuilderRegisterAccess.registerWord_symbols values.reverse symbol (List.mem_reverse.mp h)

private def rule (source target : Nat) (read write : WorkSymbol) (move : HeadMove) : WorkRule :=
  {sourceState := source, targetState := target, readSymbol := read, writeSymbol := write, move := move}

def initializeMachine : WorkMachine :=
  {rules := [rule 0 1 scratchEndSymbol scratchEndSymbol .right,
    rule 1 1 unitSymbol unitSymbol .right, rule 1 2 separatorSymbol counterMarker .right,
    rule 2 2 unitSymbol unitSymbol .right, rule 2 3 separatorSymbol candidateMarker .left,
    rule 3 3 unitSymbol unitSymbol .left, rule 3 3 counterMarker counterMarker .left,
    rule 3 4 scratchEndSymbol scratchEndSymbol .stay],
   startState := 0, acceptState := 4, rejectState := 5}

def advance : WorkMachine :=
  {rules := [rule 0 1 scratchEndSymbol scratchEndSymbol .right,
    rule 1 1 unitSymbol unitSymbol .right, rule 1 1 separatorSymbol separatorSymbol .right,
    rule 1 1 spentSymbol spentSymbol .right, rule 1 1 counterMarker counterMarker .right,
    rule 1 2 candidateMarker separatorSymbol .right,
    rule 2 2 unitSymbol unitSymbol .right, rule 2 3 separatorSymbol candidateMarker .left,
    rule 3 3 unitSymbol unitSymbol .left, rule 3 3 separatorSymbol separatorSymbol .left,
    rule 3 3 spentSymbol spentSymbol .left, rule 3 3 counterMarker counterMarker .left,
    rule 3 4 scratchEndSymbol scratchEndSymbol .stay],
   startState := 0, acceptState := 4, rejectState := 5}

def finalize : WorkMachine :=
  {rules := [rule 0 1 scratchEndSymbol scratchEndSymbol .right,
    rule 1 1 unitSymbol unitSymbol .right, rule 1 2 counterMarker separatorSymbol .right,
    rule 2 2 unitSymbol unitSymbol .right, rule 2 2 separatorSymbol separatorSymbol .right,
    rule 2 3 candidateMarker counterMarker .left,
    rule 3 3 unitSymbol unitSymbol .left, rule 3 3 separatorSymbol separatorSymbol .left,
    rule 3 4 scratchEndSymbol scratchEndSymbol .stay],
   startState := 0, acceptState := 4, rejectState := 5}

private def rightFocus (left right : List WorkSymbol) : WorkTape :=
  match right with
  | [] => {left := left, head := .blank, right := []}
  | symbol :: rest => {left := left, head := symbol, right := rest}
private def leftFocus (left right : List WorkSymbol) : WorkTape :=
  match left with
  | [] => {left := [], head := .blank, right := right}
  | symbol :: rest => {left := rest, head := symbol, right := right}
private theorem compose {program : WorkMachine} {n m : Nat} {a b c : WorkConfiguration}
    (first : workRunExact? program n a = some b) (second : workRunExact? program m b = some c) :
    workRunExact? program (n + m) a = some c :=
  PipelineMachineSimulation.workRunExact?_compose program n m a b c first second
private theorem one_step {program : WorkMachine} {a b : WorkConfiguration}
    (step : workStep? program a = some b) : workRunExact? program 1 a = some b := by
  simp only [workRunExact?, step]

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

private theorem two_markers_run (program : WorkMachine) (front middle inside outside : List WorkSymbol)
    (first second firstWrite secondWrite : WorkSymbol)
    (hStart : ∀ left right, workStep? program
      {state := program.startState, tape := {left := left, head := scratchEndSymbol, right := right}} =
      some {state := 1, tape := rightFocus (scratchEndSymbol :: left) right})
    (hFront : ∀ symbol ∈ front, ∀ left right, workStep? program
      {state := 1, tape := {left := left, head := symbol, right := right}} =
      some {state := 1, tape := rightFocus (symbol :: left) right})
    (hFirst : ∀ left right, workStep? program
      {state := 1, tape := {left := left, head := first, right := right}} =
      some {state := 2, tape := rightFocus (firstWrite :: left) right})
    (hMiddle : ∀ symbol ∈ middle, ∀ left right, workStep? program
      {state := 2, tape := {left := left, head := symbol, right := right}} =
      some {state := 2, tape := rightFocus (symbol :: left) right})
    (hSecond : ∀ left right, workStep? program
      {state := 2, tape := {left := left, head := second, right := right}} =
      some {state := 3, tape := leftFocus left (secondWrite :: right)})
    (hBack : ∀ symbol ∈ middle.reverse ++ firstWrite :: front.reverse, ∀ left right,
      workStep? program {state := 3, tape := {left := left, head := symbol, right := right}} =
      some {state := 3, tape := leftFocus left (symbol :: right)})
    (hEnd : ∀ left right, workStep? program
      {state := 3, tape := {left := left, head := scratchEndSymbol, right := right}} =
      some {state := program.acceptState, tape := {left := left, head := scratchEndSymbol, right := right}}) :
    workRunExact? program (2 * (front.length + middle.length) + 5)
      (workStartConfiguration program
        {left := outside, head := scratchEndSymbol, right := front ++ first :: middle ++ second :: inside}) =
      some {state := program.acceptState,
            tape := {left := outside, head := scratchEndSymbol,
                     right := front ++ firstWrite :: middle ++ secondWrite :: inside}} := by
  have h0 := one_step (hStart outside (front ++ first :: middle ++ second :: inside))
  have h1 := scan_right program 1 front (first :: middle ++ second :: inside) (scratchEndSymbol :: outside) hFront
  simp only [rightFocus] at h1
  have h2 := one_step (hFirst (front.reverse ++ scratchEndSymbol :: outside) (middle ++ second :: inside))
  have h3 := scan_right program 2 middle (second :: inside)
    (firstWrite :: (front.reverse ++ scratchEndSymbol :: outside)) hMiddle
  simp only [rightFocus] at h3
  have h4 := one_step (hSecond (middle.reverse ++ firstWrite :: (front.reverse ++ scratchEndSymbol :: outside)) inside)
  have h5 := scan_left program 3 (middle.reverse ++ firstWrite :: front.reverse)
    (scratchEndSymbol :: outside) (secondWrite :: inside) hBack
  simp only [List.cons_append, List.append_assoc, leftFocus] at h5
  have h6 := one_step (hEnd outside ((middle.reverse ++ firstWrite :: front.reverse).reverse ++ secondWrite :: inside))
  simp only [List.cons_append, List.append_assoc, rightFocus, leftFocus] at h0 h1 h2 h3 h4 h5 h6
  have h := compose (compose (compose (compose (compose (compose h0 h1) h2) h3) h4) h5) h6
  have hClock : 1 + front.length + 1 + middle.length + 1 +
      (middle.reverse ++ firstWrite :: front.reverse).length + 1 =
      2 * (front.length + middle.length) + 5 := by
    simp only [List.length_append, List.length_reverse, List.length_cons]
    omega
  rw [hClock] at h
  simpa only [workStartConfiguration, List.reverse_append, List.reverse_cons, List.reverse_reverse,
    List.cons_append, List.nil_append, List.append_assoc] using h

def candidateTape (spent remaining : Nat) (before : List Nat) (value : Nat)
    (inside outside : List WorkSymbol) : WorkTape :=
  {left := outside, head := scratchEndSymbol,
   right := List.replicate remaining unitSymbol ++ List.replicate spent spentSymbol ++
     counterMarker :: readerWord before ++ List.replicate value unitSymbol ++ candidateMarker :: inside}

def initializeSteps (count value : Nat) : Nat := 2 * (count + value) + 5
def advanceSteps (count : Nat) (before : List Nat) (value next : Nat) : Nat :=
  2 * (count + (readerWord before).length + value + next) + 7
def finalizeSteps (count : Nat) (before : List Nat) (value : Nat) : Nat :=
  2 * (count + (readerWord before).length + value) + 5

theorem initialize_workRunExact (count value : Nat) (inside outside : List WorkSymbol) :
    workRunExact? initializeMachine (initializeSteps count value)
      (workStartConfiguration initializeMachine (endTape [value, count] inside outside)) =
      some {state := initializeMachine.acceptState, tape := candidateTape 0 count [] value inside outside} := by
  have h := two_markers_run initializeMachine (List.replicate count unitSymbol) (List.replicate value unitSymbol)
    inside outside separatorSymbol separatorSymbol counterMarker candidateMarker
    (by intro left right; cases right <;> rfl)
    (by intro symbol hSymbol left right; have hs := List.eq_of_mem_replicate hSymbol; subst symbol; cases right <;> rfl)
    (by intro left right; cases right <;> rfl)
    (by intro symbol hSymbol left right; have hs := List.eq_of_mem_replicate hSymbol; subst symbol; cases right <;> rfl)
    (by intro left right; cases left <;> rfl)
    (by
      intro symbol hSymbol left right
      simp only [List.reverse_replicate, List.mem_append, List.mem_cons] at hSymbol
      rcases hSymbol with hUnit | rfl | hUnit
      · have hs := List.eq_of_mem_replicate hUnit; subst symbol; cases left <;> rfl
      · cases left <;> rfl
      · have hs := List.eq_of_mem_replicate hUnit; subst symbol; cases left <;> rfl)
    (by intro left right; rfl)
  simpa only [initializeSteps, List.length_replicate, endTape, registerWord,
    List.reverse_cons, List.reverse_append, List.reverse_replicate, List.reverse_nil,
    List.append_nil, List.nil_append, List.cons_append, List.append_assoc,
    candidateTape, readerWord, List.replicate_zero] using h

private theorem front_symbols (spent remaining : Nat) (before : List Nat) (value : Nat) (symbol : WorkSymbol)
    (h : symbol ∈ List.replicate remaining unitSymbol ++ List.replicate spent spentSymbol ++
      counterMarker :: readerWord before ++ List.replicate value unitSymbol) :
    symbol = unitSymbol ∨ symbol = separatorSymbol ∨ symbol = spentSymbol ∨ symbol = counterMarker := by
  simp only [List.append_assoc, List.cons_append, List.mem_append, List.mem_cons] at h
  rcases h with hUnit | hSpent | hCounter | hBefore | hUnit
  · exact Or.inl (List.eq_of_mem_replicate hUnit)
  · exact Or.inr (Or.inr (Or.inl (List.eq_of_mem_replicate hSpent)))
  · exact Or.inr (Or.inr (Or.inr hCounter))
  · rcases readerWord_symbols before symbol hBefore with hUnit | hSep
    · exact Or.inl hUnit
    · exact Or.inr (Or.inl hSep)
  · exact Or.inl (List.eq_of_mem_replicate hUnit)

theorem advance_workRunExact (spent remaining : Nat) (before : List Nat) (value next : Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? advance (advanceSteps (spent + remaining) before value next)
      (workStartConfiguration advance
        (candidateTape spent remaining before value (List.replicate next unitSymbol ++ separatorSymbol :: inside) outside)) =
      some {state := advance.acceptState,
            tape := candidateTape spent remaining (before ++ [value]) next inside outside} := by
  let front := List.replicate remaining unitSymbol ++ List.replicate spent spentSymbol ++
      counterMarker :: readerWord before ++ List.replicate value unitSymbol
  have h := two_markers_run advance front (List.replicate next unitSymbol)
    inside outside candidateMarker separatorSymbol separatorSymbol candidateMarker
    (by intro left right; cases right <;> rfl)
    (by
      intro symbol hSymbol left right
      rcases front_symbols spent remaining before value symbol hSymbol with rfl | rfl | rfl | rfl <;>
        cases right <;> rfl)
    (by intro left right; cases right <;> rfl)
    (by intro symbol hSymbol left right; have hs := List.eq_of_mem_replicate hSymbol; subst symbol; cases right <;> rfl)
    (by intro left right; cases left <;> rfl)
    (by
      intro symbol hSymbol left right
      simp only [List.mem_append, List.mem_reverse, List.mem_cons] at hSymbol
      rcases hSymbol with hUnit | rfl | hFront
      · have hs := List.eq_of_mem_replicate hUnit; subst symbol; cases left <;> rfl
      · cases left <;> rfl
      · rcases front_symbols spent remaining before value symbol hFront with rfl | rfl | rfl | rfl <;>
          cases left <;> rfl)
    (by intro left right; rfl)
  have hClock : 2 * (front.length + (List.replicate next unitSymbol).length) + 5 =
      advanceSteps (spent + remaining) before value next := by
    simp only [front, advanceSteps, List.length_append, List.length_replicate, List.length_cons]
    omega
  rw [hClock] at h
  simpa only [candidateTape, front, readerWord_append, readerWord, List.append_nil,
    List.cons_append, List.nil_append, List.append_assoc] using h

theorem finalize_workRunExact (count : Nat) (before : List Nat) (value : Nat) (inside outside : List WorkSymbol) :
    workRunExact? finalize (finalizeSteps count before value)
      (workStartConfiguration finalize (candidateTape 0 count before value inside outside)) =
      some {state := finalize.acceptState,
            tape := markedTape 0 value (before.reverse ++ [count]) inside outside} := by
  let middle := readerWord before ++ List.replicate value unitSymbol
  have hMiddle : ∀ symbol ∈ middle, symbol = unitSymbol ∨ symbol = separatorSymbol := by
    intro symbol hSymbol
    rcases List.mem_append.mp hSymbol with hBefore | hUnit
    · exact readerWord_symbols before symbol hBefore
    · exact Or.inl (List.eq_of_mem_replicate hUnit)
  have h := two_markers_run finalize (List.replicate count unitSymbol) middle
    inside outside counterMarker candidateMarker separatorSymbol counterMarker
    (by intro left right; cases right <;> rfl)
    (by intro symbol hSymbol left right; have hs := List.eq_of_mem_replicate hSymbol; subst symbol; cases right <;> rfl)
    (by intro left right; cases right <;> rfl)
    (by intro symbol hSymbol left right; rcases hMiddle symbol hSymbol with rfl | rfl <;> cases right <;> rfl)
    (by intro left right; cases left <;> rfl)
    (by
      intro symbol hSymbol left right
      simp only [List.mem_append, List.mem_reverse, List.mem_cons] at hSymbol
      rcases hSymbol with hMid | rfl | hUnit
      · rcases hMiddle symbol hMid with rfl | rfl <;> cases left <;> rfl
      · cases left <;> rfl
      · have hs := List.eq_of_mem_replicate hUnit; subst symbol; cases left <;> rfl)
    (by intro left right; rfl)
  have hClock : 2 * ((List.replicate count unitSymbol).length + middle.length) + 5 =
      finalizeSteps count before value := by
    simp only [middle, finalizeSteps, List.length_append, List.length_replicate]
    omega
  rw [hClock] at h
  simpa only [candidateTape, middle, markedTape, List.replicate_zero, List.append_nil,
    registerWord_append, registerWord, List.reverse_append, List.reverse_cons,
    List.reverse_replicate, List.reverse_nil, List.nil_append, List.cons_append,
    List.append_assoc, ← readerWord_eq_reverse] using h

theorem initialize_control :
    initializeMachine.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineChain.NoRuleAtAccept initializeMachine ∧ WorkMachineProgramGraph.NoRuleAt initializeMachine initializeMachine.rejectState ∧
    initializeMachine.acceptState ≠ initializeMachine.rejectState := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · unfold WorkMachineChain.QueryDistinct
    decide
  · intro item h
    decide +revert
  · intro item h
    decide +revert

theorem advance_control :
    advance.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineChain.NoRuleAtAccept advance ∧ WorkMachineProgramGraph.NoRuleAt advance advance.rejectState ∧
    advance.acceptState ≠ advance.rejectState := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · unfold WorkMachineChain.QueryDistinct
    decide
  · intro item h
    decide +revert
  · intro item h
    decide +revert

theorem finalize_control :
    finalize.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineChain.NoRuleAtAccept finalize ∧ WorkMachineProgramGraph.NoRuleAt finalize finalize.rejectState ∧
    finalize.acceptState ≠ finalize.rejectState := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · unfold WorkMachineChain.QueryDistinct
    decide
  · intro item h
    decide +revert
  · intro item h
    decide +revert

def consumeReference : WorkMachineProgramGraph.NodeRef :=
  {name := 1, startState := (BuilderRegisterCountdownControl.consumeWith counterMarker).startState}
def copyNode : Node :=
  {name := 4, program := BuilderRegisterRootCopy.copyMachine, onAccept := .accept, onReject := .reject}
def finalizeNode : Node :=
  {name := 3, program := finalize, onAccept := .node copyNode.reference, onReject := .reject}
def advanceNode : Node :=
  {name := 2, program := advance, onAccept := .node consumeReference, onReject := .reject}
def consumeNode : Node :=
  {name := 1, program := BuilderRegisterCountdownControl.consumeWith counterMarker,
   onAccept := .node advanceNode.reference, onReject := .node finalizeNode.reference}
def initializeNode : Node :=
  {name := 0, program := initializeMachine, onAccept := .node consumeNode.reference, onReject := .reject}
def graph : Graph :=
  {nodes := [initializeNode, consumeNode, advanceNode, finalizeNode, copyNode], entry := initializeNode.reference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph

private theorem initialize_mem : initializeNode ∈ graph.nodes := List.Mem.head _
private theorem consume_mem : consumeNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)
private theorem advance_mem : advanceNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem finalize_mem : finalizeNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem copy_mem : copyNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem graph_nodes_length : graph.nodes.length = 5 := rfl
theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun left right : Nat => left ≠ right) := by
    change ([0, 1, 2, 3, 4] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl
    · exact initialize_control
    · exact BuilderRegisterCountdownControl.consumeWith_control counterMarker
    · exact advance_control
    · exact finalize_control
    · exact BuilderRegisterRootCopy.copy_control
  · exact ⟨initializeNode, initialize_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨consumeNode, consume_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨advanceNode, advance_mem, rfl, rfl⟩, ⟨finalizeNode, finalize_mem, rfl, rfl⟩⟩
    · exact ⟨⟨consumeNode, consume_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨copyNode, copy_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def firstValue : List Nat → Nat → Nat
  | [], value => value
  | first :: _, _ => first
def remainingValues : List Nat → Nat → List Nat → List Nat
  | [], _, after => after
  | _ :: rest, value, after => rest ++ [value] ++ after

theorem readerWord_first (before : List Nat) (value : Nat) (after : List Nat) :
    readerWord (before ++ [value] ++ after) =
      List.replicate (firstValue before value) unitSymbol ++
        separatorSymbol :: readerWord (remainingValues before value after) := by
  cases before <;> simp only [List.nil_append, List.cons_append, readerWord, firstValue,
    remainingValues, List.nil_append]

def loopTape (spent : Nat) (scanned before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) : WorkTape :=
  candidateTape spent before.length scanned (firstValue before value)
    (readerWord (remainingValues before value after) ++ inside) outside
def loopFinalTape (spent : Nat) (scanned before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) : WorkTape :=
  BuilderRegisterCountdownControl.restoredTape value
    ((scanned ++ before).reverse ++ [spent + before.length, value])
    (readerWord after ++ inside) (outside.drop (value + 1))
def loopSteps : Nat → List Nat → List Nat → Nat → Nat
  | spent, scanned, [], value =>
      exhaustedSteps spent [] + 1 +
        (finalizeSteps spent scanned value + 1 +
          (BuilderRegisterRootCopy.copySteps value (scanned.reverse ++ [spent]) + 1))
  | spent, scanned, first :: rest, value =>
      consumeSteps spent (rest.length + 1) [] + 1 +
        (advanceSteps (spent + 1 + rest.length) scanned first (firstValue rest value) + 1 +
          loopSteps (spent + 1) (scanned ++ [first]) rest value)

private theorem consume_trace (spent remaining : Nat) (scanned : List Nat) (value : Nat)
    (inside outside : List WorkSymbol) :
    LocalAcceptRun consumeNode (consumeSteps spent (remaining + 1) [])
      (candidateTape spent (remaining + 1) scanned value inside outside)
      (candidateTape (spent + 1) remaining scanned value inside outside) := by
  have h := BuilderRegisterCountdownControl.consumeWith_workRunExact counterMarker spent remaining []
    (readerWord scanned ++ List.replicate value unitSymbol ++ candidateMarker :: inside) outside
  simpa only [LocalAcceptRun, consumeNode, workStartConfiguration, markedTape,
    candidateTape, registerWord, List.reverse_nil, List.nil_append,
    List.cons_append, List.append_assoc] using h

private theorem exhausted_trace (spent : Nat) (scanned : List Nat) (value : Nat)
    (inside outside : List WorkSymbol) :
    LocalRejectRun consumeNode (exhaustedSteps spent [])
      (candidateTape spent 0 scanned value inside outside)
      (candidateTape 0 spent scanned value inside outside) := by
  have h := BuilderRegisterCountdownControl.exhaustedWith_workRunExact counterMarker spent []
    (readerWord scanned ++ List.replicate value unitSymbol ++ candidateMarker :: inside) outside
  simpa only [LocalRejectRun, consumeNode, workStartConfiguration, markedTape,
    BuilderRegisterCountdownControl.restoredTapeWith, candidateTape, registerWord,
    List.reverse_nil, List.nil_append, List.replicate_zero, List.append_nil,
    List.cons_append, List.append_assoc] using h

private theorem loop_path (spent : Nat) (scanned before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) :
    AcceptPath graph (.node consumeNode.reference) .accept (loopSteps spent scanned before value)
      (loopTape spent scanned before value after inside outside)
      (loopFinalTape spent scanned before value after inside outside) := by
  induction before generalizing spent scanned with
  | nil =>
      have hExhaust := exhausted_trace spent scanned value (readerWord after ++ inside) outside
      have hFinalize : LocalAcceptRun finalizeNode (finalizeSteps spent scanned value)
          (candidateTape 0 spent scanned value (readerWord after ++ inside) outside)
          (markedTape 0 value (scanned.reverse ++ [spent]) (readerWord after ++ inside) outside) :=
        finalize_workRunExact spent scanned value (readerWord after ++ inside) outside
      have hCopy : LocalAcceptRun copyNode (BuilderRegisterRootCopy.copySteps value (scanned.reverse ++ [spent]))
          (markedTape 0 value (scanned.reverse ++ [spent]) (readerWord after ++ inside) outside)
          (loopFinalTape spent scanned [] value after inside outside) := by
        simpa only [LocalAcceptRun, copyNode, workStartConfiguration, loopFinalTape, List.append_nil,
          List.length_nil, Nat.add_zero, List.append_assoc, List.cons_append, List.nil_append] using
          BuilderRegisterRootCopy.copy_workRunExact value (scanned.reverse ++ [spent]) (readerWord after ++ inside) outside
      have hCopyPath := AcceptPath.step copyNode .accept _ 0 _ _ _ copy_mem hCopy
        (AcceptPath.terminal .accept (loopFinalTape spent scanned [] value after inside outside))
      have hFinishPath := AcceptPath.step finalizeNode .accept _ _ _ _ _ finalize_mem hFinalize hCopyPath
      have hPath := AcceptPath.stepReject consumeNode .accept _ _ _ _ _ consume_mem hExhaust hFinishPath
      simpa only [loopTape, loopSteps, List.length_nil, firstValue, remainingValues, Nat.add_zero] using hPath
  | cons first rest ih =>
      have hTake := consume_trace spent rest.length scanned first
        (readerWord (rest ++ [value] ++ after) ++ inside) outside
      have hAdvance : LocalAcceptRun advanceNode
          (advanceSteps (spent + 1 + rest.length) scanned first (firstValue rest value))
          (candidateTape (spent + 1) rest.length scanned first
            (readerWord (rest ++ [value] ++ after) ++ inside) outside)
          (loopTape (spent + 1) (scanned ++ [first]) rest value after inside outside) := by
        have h := advance_workRunExact (spent + 1) rest.length scanned first (firstValue rest value)
          (readerWord (remainingValues rest value after) ++ inside) outside
        simp only [LocalAcceptRun, advanceNode, workStartConfiguration, loopTape]
        rw [readerWord_first rest value after]
        simpa only [workStartConfiguration, List.append_assoc, List.cons_append] using h
      have hTail := ih (spent + 1) (scanned ++ [first])
      have hAdvancePath := AcceptPath.step advanceNode .accept _ _ _ _ _ advance_mem hAdvance hTail
      have hPath := AcceptPath.step consumeNode .accept _ _ _ _ _ consume_mem hTake hAdvancePath
      have hCount : spent + 1 + rest.length = spent + (first :: rest).length := by
        simp only [List.length_cons]
        omega
      simpa only [loopSteps, loopTape, firstValue, remainingValues, List.length_cons,
        loopFinalTape, List.append_assoc, List.cons_append, List.nil_append, hCount] using hPath

def inputValues (before : List Nat) (value : Nat) (after older : List Nat) : List Nat :=
  older ++ (before ++ [value] ++ after).reverse ++ [before.length]
def workSteps (before : List Nat) (value : Nat) : Nat :=
  initializeSteps before.length (firstValue before value) + 1 + loopSteps 0 [] before value
def initialConfiguration (before : List Nat) (value : Nat) (after older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (inputValues before value after older) inside outside)
def finalConfiguration (before : List Nat) (value : Nat) (after older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  {state := machine.acceptState,
   tape := endTape (inputValues before value after older ++ [value]) inside (outside.drop (value + 1))}

theorem workRunExact (before : List Nat) (value : Nat) (after older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps before value)
      (initialConfiguration before value after older inside outside) =
      some (finalConfiguration before value after older inside outside) := by
  let frame := (registerWord older).reverse ++ inside
  have hInit : LocalAcceptRun initializeNode (initializeSteps before.length (firstValue before value))
      (endTape (inputValues before value after older) inside outside)
      (loopTape 0 [] before value after frame outside) := by
    have h := initialize_workRunExact before.length (firstValue before value)
      (readerWord (remainingValues before value after) ++ frame) outside
    simp only [LocalAcceptRun, initializeNode, workStartConfiguration, endTape,
      inputValues, registerWord_append, List.reverse_append, registerWord, List.reverse_cons,
      List.reverse_replicate, List.reverse_nil, List.append_nil, List.nil_append,
      List.cons_append, List.append_assoc, ← readerWord_eq_reverse, readerWord_first before value after,
      loopTape, candidateTape, readerWord, List.replicate_zero, frame] at h ⊢
    cases before <;>
      simpa only [firstValue, remainingValues, readerWord, readerWord_append, List.cons_append,
        List.nil_append, List.append_nil, List.append_assoc] using h
  have hLoop := loop_path 0 [] before value after frame outside
  have hPath := AcceptPath.step initializeNode .accept _ _ _ _ _ initialize_mem hInit hLoop
  have h := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hPath
  have hMachine : WorkMachineProgramGraph.machine graph = machine := rfl
  rw [hMachine] at h
  have hInitial (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node initializeNode.reference) tape =
        workStartConfiguration machine tape := rfl
  have hFinal (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration .accept tape = {state := machine.acceptState, tape := tape} := rfl
  rw [hInitial, hFinal] at h
  simpa only [workSteps, initialConfiguration, finalConfiguration, loopFinalTape,
    inputValues, endTape, BuilderRegisterCountdownControl.restoredTape,
    BuilderRegisterCountdownControl.restoredTapeWith, registerWord_append,
    List.reverse_append, registerWord, List.reverse_cons, List.reverse_replicate,
    List.reverse_nil, List.append_nil, List.nil_append, List.cons_append,
    List.append_assoc, readerWord_append, readerWord, readerWord_eq_reverse,
    frame, List.length_nil, Nat.zero_add] using h

theorem run_compile_exact (before : List Nat) (value : Nat) (after older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps before value)
      (encodeWorkConfiguration (initialConfiguration before value after older inside outside)) =
      encodeWorkConfiguration (finalConfiguration before value after older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact before value after older inside outside)

theorem final_tape (before : List Nat) (value : Nat) (after older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration before value after older inside outside).tape =
      endTape (inputValues before value after older ++ [value]) inside (outside.drop (value + 1)) := rfl

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

theorem input_word_length (before : List Nat) (value : Nat) (after older : List Nat) :
    (registerWord (inputValues before value after older)).length =
      (registerWord older).length + (readerWord before).length + value + 1 +
        (readerWord after).length + before.length + 1 := by
  simp only [inputValues, registerWord_length, readerWord_length, List.sum_append,
    List.sum_reverse, List.length_append, List.length_reverse, List.sum_cons,
    List.sum_nil, List.length_cons, List.length_nil]
  omega

theorem firstValue_le (before : List Nat) (value : Nat) :
    firstValue before value ≤ (readerWord before).length + value := by
  cases before with
  | nil => simp only [firstValue, readerWord, List.length_nil]; omega
  | cons first rest =>
      simp only [firstValue, readerWord, List.length_append, List.length_replicate, List.length_cons]
      omega

private theorem loopSteps_le (spent : Nat) (scanned before : List Nat) (value bound : Nat)
    (hSpan : (readerWord (scanned ++ before)).length + value + spent + before.length + 2 ≤ bound) :
    loopSteps spent scanned before value ≤
      before.length * (4 * bound + 12) + bound * (6 * bound + 9) + 14 * bound + 24 := by
  induction before generalizing spent scanned with
  | nil =>
      have hNewer : (registerWord (scanned.reverse ++ [spent])).length ≤ bound := by
        simp only [List.append_nil, List.length_nil, Nat.add_zero, readerWord_length] at hSpan
        simp only [registerWord_length, List.sum_append, List.sum_reverse, List.length_append,
          List.length_reverse, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
        omega
      have hValue : value ≤ bound := by omega
      have hCopy := BuilderRegisterRootCopy.copySteps_le value (scanned.reverse ++ [spent]) bound hValue hNewer
      simp only [List.append_nil, List.length_nil, Nat.add_zero] at hSpan
      simp only [loopSteps, exhaustedSteps, finalizeSteps, registerWord, List.length_nil, Nat.zero_mul]
      omega
  | cons first rest ih =>
      have hSpan' := hSpan
      simp only [readerWord_append, readerWord, List.length_append, List.length_replicate,
        List.length_cons] at hSpan'
      have hNextSpan : (readerWord ((scanned ++ [first]) ++ rest)).length +
          value + (spent + 1) + rest.length + 2 ≤ bound := by
        simp only [readerWord_append, readerWord, List.length_append, List.length_replicate,
          List.length_cons, List.length_nil]
        omega
      have hTail := ih (spent + 1) (scanned ++ [first]) hNextSpan
      have hFirst := firstValue_le rest value
      have hConsume : consumeSteps spent (rest.length + 1) [] ≤ 2 * bound + 3 := by
        simp only [consumeSteps, registerWord, List.length_nil]
        omega
      have hAdvance : advanceSteps (spent + 1 + rest.length) scanned first (firstValue rest value) ≤
          2 * bound + 7 := by
        simp only [advanceSteps]
        omega
      simp only [loopSteps, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

def workBound (bound : Nat) : Nat :=
  bound * (4 * bound + 12) + bound * (6 * bound + 9) + 16 * bound + 30

theorem workSteps_le (before : List Nat) (value : Nat) (after older : List Nat) (bound : Nat)
    (hSpan : (registerWord (inputValues before value after older)).length ≤ bound) :
    workSteps before value ≤ workBound bound := by
  have hSpan' := hSpan
  rw [input_word_length] at hSpan'
  have hLoop := loopSteps_le 0 [] before value bound (by simp only [List.nil_append]; omega)
  have hFirst := firstValue_le before value
  have hInit : initializeSteps before.length (firstValue before value) ≤ 2 * bound + 5 := by
    simp only [initializeSteps]
    omega
  have hCount : before.length ≤ bound := by omega
  have hMul := Nat.mul_le_mul_right (4 * bound + 12) hCount
  simp only [workSteps, workBound]
  omega

theorem final_span_le (before : List Nat) (value : Nat) (after older : List Nat) (outside : List WorkSymbol)
    (bound : Nat) (hSpan : (registerWord (inputValues before value after older)).length + outside.length ≤ bound) :
    (registerWord (inputValues before value after older ++ [value])).length +
      (outside.drop (value + 1)).length ≤ 2 * bound + 1 := by
  have hInput := input_word_length before value after older
  have hValue : value ≤ bound := by omega
  simp only [registerWord_append, List.length_append, registerWord, List.length_cons,
    List.length_replicate, List.length_nil, List.length_append, List.length_drop]
  omega

def spanPolynomial (bound : NatPolynomial) : NatPolynomial := .add (.mul (.constant 2) bound) (.constant 1)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.constant 6)
    (.add
      (.add (.mul bound (.add (.mul (.constant 4) bound) (.constant 12)))
        (.mul bound (.add (.mul (.constant 6) bound) (.constant 9))))
      (.add (.mul (.constant 16) bound) (.constant 30)))

theorem rawTimePolynomial_eval (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) := by
  simp only [rawTimePolynomial, workBound, NatPolynomial.eval_mul, NatPolynomial.eval_add,
    NatPolynomial.eval_constant]
  omega

theorem source_polynomial_bounds (before : List Nat) (value : Nat) (after older : List Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (inputValues before value after older)).length + outside.length ≤ bound.eval input) :
    (registerWord (inputValues before value after older ++ [value])).length +
        (outside.drop (value + 1)).length ≤ (spanPolynomial bound).eval input ∧
      6 * workSteps before value ≤ (rawTimePolynomial bound).eval input := by
  constructor
  · simpa only [spanPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant] using
      final_span_le before value after older outside (bound.eval input) hSpan
  · rw [rawTimePolynomial_eval]
    exact Nat.mul_le_mul_left 6 (workSteps_le before value after older (bound.eval input) (by omega))

private theorem list_split (values : List Nat) (index : Fin values.length) :
    values.take index.val ++ [values[index.val]] ++ values.drop (index.val + 1) = values := by
  calc
    _ = values.take index.val ++ values.drop index.val := by
      rw [List.drop_eq_getElem_cons index.isLt]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    _ = values := List.take_append_drop index.val values

private theorem take_length (values : List Nat) (index : Fin values.length) :
    (values.take index.val).length = index.val := by
  rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt index.isLt)]

/-- The ordinal is read from the tape. The finite index describes its valid data domain. -/
theorem workRun_select_getElem (values older : List Nat) (index : Fin values.length) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps (values.take index.val) values[index.val])
      (workStartConfiguration machine (endTape (older ++ values.reverse ++ [index.val]) inside outside)) =
      some {state := machine.acceptState,
            tape := endTape (older ++ values.reverse ++ [index.val, values[index.val]])
              inside (outside.drop (values[index.val] + 1))} := by
  have h := workRunExact (values.take index.val) values[index.val] (values.drop (index.val + 1)) older inside outside
  simpa only [initialConfiguration, finalConfiguration, inputValues, list_split values index,
    take_length values index, List.append_assoc, List.cons_append, List.nil_append] using h

theorem run_compile_select_getElem (values older : List Nat) (index : Fin values.length)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps (values.take index.val) values[index.val])
      (encodeWorkConfiguration (workStartConfiguration machine
        (endTape (older ++ values.reverse ++ [index.val]) inside outside))) =
      encodeWorkConfiguration
        {state := machine.acceptState,
         tape := endTape (older ++ values.reverse ++ [index.val, values[index.val]])
          inside (outside.drop (values[index.val] + 1))} :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRun_select_getElem values older index inside outside)

theorem selected_source_polynomial_bounds (values older : List Nat) (index : Fin values.length)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (older ++ values.reverse ++ [index.val])).length + outside.length ≤ bound.eval input) :
    (registerWord (older ++ values.reverse ++ [index.val, values[index.val]])).length +
        (outside.drop (values[index.val] + 1)).length ≤ (spanPolynomial bound).eval input ∧
      6 * workSteps (values.take index.val) values[index.val] ≤ (rawTimePolynomial bound).eval input := by
  have hSource : (registerWord (inputValues (values.take index.val) values[index.val]
      (values.drop (index.val + 1)) older)).length + outside.length ≤ bound.eval input := by
    simpa only [inputValues, list_split values index, take_length values index] using hSpan
  simpa only [inputValues, list_split values index, take_length values index,
    List.append_assoc, List.cons_append, List.nil_append] using
    source_polynomial_bounds (values.take index.val) values[index.val] (values.drop (index.val + 1)) older outside bound input hSource

end PNP.Concrete.CookLevin.BuilderRegisterIndexedCopy
