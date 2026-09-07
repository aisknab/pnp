/-
Copyright (c) 2026 PNP Labs.

Fixed finite control for the input-dependent descending-register loop.
A marked unary counter is consumed one unit at a time without moving its
boundary; exhaustion restores its original cells and delimiter exactly.
The payload word may grow arbitrarily. It never changes the control table.
These kernels do not by themselves construct the full shape payload.
-/

import PNP.Concrete.CookLevinBuilderRegisterErase

namespace PNP.Concrete.CookLevin.BuilderRegisterCountdownControl

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

def counterMarker : WorkSymbol := .oneZero
def spentSymbol : WorkSymbol := .zeroZero

private def rule (source target : Nat) (read write : WorkSymbol) (move : HeadMove) : WorkRule :=
  { sourceState := source, targetState := target, readSymbol := read, writeSymbol := write, move := move }

/-- Mark the counter immediately before the newest working register. -/
def markCounterMachine : WorkMachine :=
  { rules :=
      [rule 0 1 scratchEndSymbol scratchEndSymbol .right,
       rule 1 1 unitSymbol unitSymbol .right,
       rule 1 2 separatorSymbol separatorSymbol .right,
       rule 2 2 unitSymbol unitSymbol .right,
       rule 2 3 separatorSymbol counterMarker .left,
       rule 3 3 unitSymbol unitSymbol .left,
       rule 3 3 separatorSymbol separatorSymbol .left,
       rule 3 4 scratchEndSymbol scratchEndSymbol .stay]
    startState := 0
    acceptState := 4
    rejectState := 5 }

/-- Accept consumes one unit; reject restores the exhausted counter. -/
def consume : WorkMachine :=
  { rules :=
      [rule 0 1 scratchEndSymbol scratchEndSymbol .right,
       rule 1 1 unitSymbol unitSymbol .right,
       rule 1 1 separatorSymbol separatorSymbol .right,
       rule 1 1 spentSymbol spentSymbol .right,
       rule 1 2 counterMarker counterMarker .left,
       rule 2 2 spentSymbol spentSymbol .left,
       rule 2 3 unitSymbol spentSymbol .left,
       rule 2 4 separatorSymbol separatorSymbol .right,
       rule 2 4 scratchEndSymbol scratchEndSymbol .right,
       rule 3 3 unitSymbol unitSymbol .left,
       rule 3 3 separatorSymbol separatorSymbol .left,
       rule 3 6 scratchEndSymbol scratchEndSymbol .stay,
       rule 4 4 spentSymbol unitSymbol .right,
       rule 4 5 counterMarker separatorSymbol .left,
       rule 5 5 unitSymbol unitSymbol .left,
       rule 5 5 separatorSymbol separatorSymbol .left,
       rule 5 7 scratchEndSymbol scratchEndSymbol .stay]
    startState := 0
    acceptState := 6
    rejectState := 7 }

/-- Remove one physically present unary unit, leaving its cell explicitly blank. -/
def decrement : WorkMachine :=
  { rules :=
      [rule 0 1 scratchEndSymbol .blank .right,
       rule 1 2 unitSymbol scratchEndSymbol .stay]
    startState := 0
    acceptState := 2
    rejectState := 3 }

/-- The interior suffix is arbitrary and is never scanned past the counter marker. -/
def markedTape (spent remaining : Nat) (newer : List Nat) (inside outside : List WorkSymbol) : WorkTape :=
  { left := outside
    head := scratchEndSymbol
    right := (registerWord newer).reverse ++ List.replicate remaining unitSymbol ++
      List.replicate spent spentSymbol ++ counterMarker :: inside }

def restoredTape (count : Nat) (newer : List Nat) (inside outside : List WorkSymbol) : WorkTape :=
  { left := outside
    head := scratchEndSymbol
    right := (registerWord newer).reverse ++ List.replicate count unitSymbol ++ separatorSymbol :: inside }

def initializeSteps (count value : Nat) : Nat := 2 * (count + value) + 5
def consumeSteps (spent remaining : Nat) (newer : List Nat) : Nat :=
  2 * ((registerWord newer).length + spent + remaining) + 3
def exhaustedSteps (spent : Nat) (newer : List Nat) : Nat :=
  2 * (registerWord newer).length + 4 * spent + 5

private def rightFocus (left right : List WorkSymbol) : WorkTape :=
  match right with
  | [] => { left := left, head := .blank, right := [] }
  | symbol :: rest => { left := left, head := symbol, right := rest }

private def leftFocus (left right : List WorkSymbol) : WorkTape :=
  match left with
  | [] => { left := [], head := .blank, right := right }
  | symbol :: rest => { left := rest, head := symbol, right := right }

private theorem compose {program : WorkMachine} {n m : Nat} {a b c : WorkConfiguration}
    (first : workRunExact? program n a = some b)
    (second : workRunExact? program m b = some c) :
    workRunExact? program (n + m) a = some c :=
  PipelineMachineSimulation.workRunExact?_compose program n m a b c first second

private theorem one_step {program : WorkMachine} {a b : WorkConfiguration}
    (step : workStep? program a = some b) : workRunExact? program 1 a = some b := by
  simp only [workRunExact?, step]

private theorem scan_right (program : WorkMachine) (state : Nat) (changeSymbol : WorkSymbol → WorkSymbol)
    (scanned after before : List WorkSymbol)
    (hStep : ∀ symbol ∈ scanned, ∀ left right,
      workStep? program {
      state := state
      tape := { left := left, head := symbol, right := right } } =
        some {
        state := state
        tape := rightFocus (changeSymbol symbol :: left) right }) :
    workRunExact? program scanned.length
      {
      state := state
      tape := rightFocus before (scanned ++ after) } =
      some {
      state := state
      tape := rightFocus ((scanned.map changeSymbol).reverse ++ before) after } := by
  induction scanned generalizing before with
  | nil => rfl
  | cons symbol rest ih =>
      have h := hStep symbol List.mem_cons_self before (rest ++ after)
      have hRest := ih (changeSymbol symbol :: before)
        (fun item hItem => hStep item (List.mem_cons_of_mem symbol hItem))
      simp only [List.length_cons, List.cons_append, rightFocus, workRunExact?]
      rw [h]
      simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append, rightFocus] using hRest

private theorem scan_left (program : WorkMachine) (state : Nat) (changeSymbol : WorkSymbol → WorkSymbol)
    (scanned after before : List WorkSymbol)
    (hStep : ∀ symbol ∈ scanned, ∀ left right,
      workStep? program {
      state := state
      tape := { left := left, head := symbol, right := right } } =
        some {
        state := state
        tape := leftFocus left (changeSymbol symbol :: right) }) :
    workRunExact? program scanned.length
      {
      state := state
      tape := leftFocus (scanned ++ after) before } =
      some {
      state := state
      tape := leftFocus after ((scanned.map changeSymbol).reverse ++ before) } := by
  induction scanned generalizing before with
  | nil => rfl
  | cons symbol rest ih =>
      have h := hStep symbol List.mem_cons_self (rest ++ after) before
      have hRest := ih (changeSymbol symbol :: before)
        (fun item hItem => hStep item (List.mem_cons_of_mem symbol hItem))
      simp only [List.length_cons, List.cons_append, leftFocus, workRunExact?]
      rw [h]
      simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append, leftFocus] using hRest

private theorem word_symbols (newer : List Nat) (symbol : WorkSymbol)
    (h : symbol ∈ registerWord newer) : symbol = unitSymbol ∨ symbol = separatorSymbol := by
  induction newer with
  | nil => contradiction
  | cons value rest ih =>
      simp only [registerWord, List.mem_cons, List.mem_append] at h
      rcases h with h | h | h
      · exact Or.inr h
      · exact Or.inl (List.eq_of_mem_replicate h)
      · exact ih h

private theorem unit_word_symbols (count : Nat) (newer : List Nat) (symbol : WorkSymbol)
    (h : symbol ∈ List.replicate count unitSymbol ++ registerWord newer) :
    symbol = unitSymbol ∨ symbol = separatorSymbol := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl (List.eq_of_mem_replicate h)
  · exact word_symbols newer symbol h

theorem initialize_workRunExact (count value : Nat) (inside outside : List WorkSymbol) :
    workRunExact? markCounterMachine (initializeSteps count value)
      (workStartConfiguration markCounterMachine (restoredTape count [value] inside outside)) =
      some {
      state := markCounterMachine.acceptState
      tape := markedTape 0 count [value] inside outside } := by
  let upper := List.replicate value unitSymbol
  let counter := List.replicate count unitSymbol
  let tail := counter ++ separatorSymbol :: inside
  have hStart : workRunExact? markCounterMachine 1
      (workStartConfiguration markCounterMachine (restoredTape count [value] inside outside)) =
      some {
      state := 1
      tape := rightFocus (scratchEndSymbol :: outside) (upper ++ separatorSymbol :: tail) } := by
    apply one_step
    simp only [restoredTape, registerWord, List.append_nil, List.reverse_cons,
      List.reverse_append, List.reverse_replicate, List.reverse_nil, List.nil_append,
      List.cons_append, upper, counter, tail, List.append_assoc]
    cases value <;> rfl
  have hUpper := scan_right markCounterMachine 1 id upper (separatorSymbol :: tail) (scratchEndSymbol :: outside)
    (by
      intro symbol h left right
      have hSymbol := List.eq_of_mem_replicate h
      subst symbol
      cases right <;> rfl)
  have hDelimiter : workRunExact? markCounterMachine 1
      {
      state := 1
      tape := rightFocus ((upper.map id).reverse ++ scratchEndSymbol :: outside) (separatorSymbol :: tail) } =
      some {
      state := 2
      tape := rightFocus (separatorSymbol :: (upper.reverse ++ scratchEndSymbol :: outside)) tail } := by
    apply one_step
    simp only [List.map_id]
    cases count <;> rfl
  have hCounter := scan_right markCounterMachine 2 id counter (separatorSymbol :: inside)
    (separatorSymbol :: (upper.reverse ++ scratchEndSymbol :: outside))
    (by
      intro symbol h left right
      have hSymbol := List.eq_of_mem_replicate h
      subst symbol
      cases right <;> rfl)
  have hMark : workRunExact? markCounterMachine 1
      {
      state := 2
      tape := rightFocus ((counter.map id).reverse ++
          separatorSymbol :: (upper.reverse ++ scratchEndSymbol :: outside)) (separatorSymbol :: inside) } =
      some {
      state := 3
      tape := leftFocus
        ((counter ++ separatorSymbol :: upper) ++ scratchEndSymbol :: outside) (counterMarker :: inside) } := by
    apply one_step
    simp only [List.map_id, upper, counter, List.reverse_replicate, List.append_assoc, List.cons_append]
    cases count <;> rfl
  have hSeek := scan_left markCounterMachine 3 id (counter ++ separatorSymbol :: upper)
    (scratchEndSymbol :: outside) (counterMarker :: inside) (by
      intro symbol h left right
      simp only [List.mem_append, List.mem_cons] at h
      rcases h with h | h | h
      · have hSymbol := List.eq_of_mem_replicate h
        subst symbol
        cases left <;> rfl
      · subst symbol
        cases left <;> rfl
      · have hSymbol := List.eq_of_mem_replicate h
        subst symbol
        cases left <;> rfl)
  have hStop : workRunExact? markCounterMachine 1
      {
      state := 3
      tape := leftFocus (scratchEndSymbol :: outside)
        (((counter ++ separatorSymbol :: upper).map id).reverse ++ counterMarker :: inside) } =
      some {
      state := markCounterMachine.acceptState
      tape := markedTape 0 count [value] inside outside } := by
    apply one_step
    simp only [List.map_id, List.reverse_append, List.reverse_cons, upper, counter,
      List.reverse_replicate, List.cons_append, List.append_assoc, List.nil_append,
      List.replicate_zero, List.append_nil, markedTape, registerWord, List.reverse_nil, leftFocus]
    rfl
  have hAll := compose (compose (compose (compose (compose hStart hUpper) hDelimiter) hCounter) hMark)
    (compose hSeek hStop)
  have hLength : 1 + upper.length + 1 + counter.length + 1 +
      ((counter ++ separatorSymbol :: upper).length + 1) = initializeSteps count value := by
    simp only [initializeSteps, upper, counter, List.length_replicate, List.length_append, List.length_cons]
    omega
  rw [hLength] at hAll
  exact hAll

theorem consume_workRunExact (spent remaining : Nat) (newer : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? consume (consumeSteps spent (remaining + 1) newer)
      (workStartConfiguration consume (markedTape spent (remaining + 1) newer inside outside)) =
      some {
      state := consume.acceptState
      tape := markedTape (spent + 1) remaining newer inside outside } := by
  let word := registerWord newer
  let scanned := word.reverse ++ List.replicate (remaining + 1) unitSymbol ++ List.replicate spent spentSymbol
  let back := List.replicate remaining unitSymbol ++ word
  have hStart : workRunExact? consume 1
      (workStartConfiguration consume (markedTape spent (remaining + 1) newer inside outside)) =
      some {
      state := 1
      tape := rightFocus (scratchEndSymbol :: outside) (scanned ++ counterMarker :: inside) } := by
    apply one_step
    change workStep? consume
      {
      state := 0
      tape := {
          left := outside
          head := scratchEndSymbol
          right := scanned ++ counterMarker :: inside } } = _
    cases scanned ++ counterMarker :: inside <;> rfl
  have hScan := scan_right consume 1 id scanned (counterMarker :: inside) (scratchEndSymbol :: outside) (by
    intro symbol h left right
    simp only [scanned, List.mem_append, List.mem_reverse] at h
    rcases h with (h | h) | h
    · rcases word_symbols newer symbol h with hSymbol | hSymbol <;> subst symbol <;> cases right <;> rfl
    · have hSymbol := List.eq_of_mem_replicate h
      subst symbol
      cases right <;> rfl
    · have hSymbol := List.eq_of_mem_replicate h
      subst symbol
      cases right <;> rfl)
  have hMarker : workRunExact? consume 1
      {
      state := 1
      tape := rightFocus ((scanned.map id).reverse ++ scratchEndSymbol :: outside) (counterMarker :: inside) } =
      some {
      state := 2
      tape := leftFocus
        (List.replicate spent spentSymbol ++ unitSymbol :: (back ++ scratchEndSymbol :: outside)) (counterMarker :: inside) } := by
    apply one_step
    simp only [List.map_id, scanned, back, List.reverse_append, List.reverse_replicate,
      List.reverse_reverse, List.append_assoc, List.cons_append]
    cases spent <;> rfl
  have hSpent := scan_left consume 2 id (List.replicate spent spentSymbol)
    (unitSymbol :: (back ++ scratchEndSymbol :: outside)) (counterMarker :: inside) (by
      intro symbol h left right
      have hSymbol := List.eq_of_mem_replicate h
      subst symbol
      cases left <;> rfl)
  have hTake : workRunExact? consume 1
      {
      state := 2
      tape := leftFocus (unitSymbol :: (back ++ scratchEndSymbol :: outside))
        (((List.replicate spent spentSymbol).map id).reverse ++ counterMarker :: inside) } =
      some {
      state := 3
      tape := leftFocus (back ++ scratchEndSymbol :: outside)
        (List.replicate (spent + 1) spentSymbol ++ counterMarker :: inside) } := by
    apply one_step
    simp only [List.map_id, List.reverse_replicate, List.replicate_succ, List.cons_append]
    cases back ++ scratchEndSymbol :: outside <;> rfl
  have hBack := scan_left consume 3 id back (scratchEndSymbol :: outside)
    (List.replicate (spent + 1) spentSymbol ++ counterMarker :: inside) (by
      intro symbol h left right
      rcases unit_word_symbols remaining newer symbol h with hSymbol | hSymbol <;>
        subst symbol <;> cases left <;> rfl)
  have hStop : workRunExact? consume 1
      {
      state := 3
      tape := leftFocus (scratchEndSymbol :: outside)
        ((back.map id).reverse ++ (List.replicate (spent + 1) spentSymbol ++ counterMarker :: inside)) } =
      some {
      state := consume.acceptState
      tape := markedTape (spent + 1) remaining newer inside outside } := by
    apply one_step
    simp only [List.map_id, back, word, List.reverse_append, List.reverse_replicate, markedTape, List.append_assoc]
    rfl
  have hAll := compose (compose (compose (compose (compose hStart hScan) hMarker) hSpent) hTake)
    (compose hBack hStop)
  have hLength : 1 + scanned.length + 1 + (List.replicate spent spentSymbol).length + 1 +
      (back.length + 1) = consumeSteps spent (remaining + 1) newer := by
    simp only [scanned, back, word, consumeSteps, List.length_append, List.length_reverse, List.length_replicate]
    omega
  rw [hLength] at hAll
  exact hAll

theorem exhausted_workRunExact (spent : Nat) (newer : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? consume (exhaustedSteps spent newer)
      (workStartConfiguration consume (markedTape spent 0 newer inside outside)) =
      some {
      state := consume.rejectState
      tape := restoredTape spent newer inside outside } := by
  let word := registerWord newer
  let scanned := word.reverse ++ List.replicate spent spentSymbol
  let after := word ++ scratchEndSymbol :: outside
  have hStart : workRunExact? consume 1
      (workStartConfiguration consume (markedTape spent 0 newer inside outside)) =
      some {
      state := 1
      tape := rightFocus (scratchEndSymbol :: outside) (scanned ++ counterMarker :: inside) } := by
    apply one_step
    simp only [markedTape, List.replicate_zero, List.nil_append, List.append_nil]
    change workStep? consume
      {
      state := 0
      tape := {
          left := outside
          head := scratchEndSymbol
          right := scanned ++ counterMarker :: inside } } = _
    cases scanned ++ counterMarker :: inside <;> rfl
  have hScan := scan_right consume 1 id scanned (counterMarker :: inside) (scratchEndSymbol :: outside) (by
    intro symbol h left right
    simp only [scanned, List.mem_append, List.mem_reverse] at h
    rcases h with h | h
    · rcases word_symbols newer symbol h with hSymbol | hSymbol <;> subst symbol <;> cases right <;> rfl
    · have hSymbol := List.eq_of_mem_replicate h
      subst symbol
      cases right <;> rfl)
  have hMarker : workRunExact? consume 1
      {
      state := 1
      tape := rightFocus ((scanned.map id).reverse ++ scratchEndSymbol :: outside) (counterMarker :: inside) } =
      some {
      state := 2
      tape := leftFocus (List.replicate spent spentSymbol ++ after) (counterMarker :: inside) } := by
    apply one_step
    simp only [List.map_id, scanned, after, List.reverse_append, List.reverse_replicate,
      List.reverse_reverse, List.append_assoc]
    cases List.replicate spent spentSymbol ++ after <;> rfl
  have hSpent := scan_left consume 2 id (List.replicate spent spentSymbol) after (counterMarker :: inside) (by
    intro symbol h left right
    have hSymbol := List.eq_of_mem_replicate h
    subst symbol
    cases left <;> rfl)
  have hEmpty : workRunExact? consume 1
      {
      state := 2
      tape := leftFocus after
        (((List.replicate spent spentSymbol).map id).reverse ++ counterMarker :: inside) } =
      some {
      state := 4
      tape := rightFocus after (List.replicate spent spentSymbol ++ counterMarker :: inside) } := by
    apply one_step
    simp only [List.map_id, List.reverse_replicate]
    cases newer <;> cases spent <;> rfl
  have hRestore := scan_right consume 4 (fun _ => unitSymbol) (List.replicate spent spentSymbol)
    (counterMarker :: inside) after (by
      intro symbol h left right
      have hSymbol := List.eq_of_mem_replicate h
      subst symbol
      cases right <;> rfl)
  have hUnmark : workRunExact? consume 1
      {
      state := 4
      tape := rightFocus
        (((List.replicate spent spentSymbol).map (fun _ => unitSymbol)).reverse ++ after) (counterMarker :: inside) } =
      some {
      state := 5
      tape := leftFocus
        ((List.replicate spent unitSymbol ++ word) ++ scratchEndSymbol :: outside) (separatorSymbol :: inside) } := by
    apply one_step
    simp only [List.map_replicate, List.reverse_replicate, after, List.append_assoc]
    cases List.replicate spent unitSymbol ++ (word ++ scratchEndSymbol :: outside) <;> rfl
  have hBack := scan_left consume 5 id (List.replicate spent unitSymbol ++ word)
    (scratchEndSymbol :: outside) (separatorSymbol :: inside) (by
      intro symbol h left right
      rcases unit_word_symbols spent newer symbol h with hSymbol | hSymbol <;>
        subst symbol <;> cases left <;> rfl)
  have hStop : workRunExact? consume 1
      {
      state := 5
      tape := leftFocus (scratchEndSymbol :: outside)
        (((List.replicate spent unitSymbol ++ word).map id).reverse ++ separatorSymbol :: inside) } =
      some {
      state := consume.rejectState
      tape := restoredTape spent newer inside outside } := by
    apply one_step
    simp only [List.map_id, List.reverse_append, List.reverse_replicate, word, restoredTape, List.append_assoc]
    rfl
  have hAll := compose (compose (compose (compose (compose (compose hStart hScan) hMarker) hSpent) hEmpty) hRestore)
    (compose hUnmark (compose hBack hStop))
  have hLength : 1 + scanned.length + 1 + (List.replicate spent spentSymbol).length + 1 +
      (List.replicate spent spentSymbol).length +
      (1 + ((List.replicate spent unitSymbol ++ word).length + 1)) = exhaustedSteps spent newer := by
    simp only [scanned, word, exhaustedSteps, List.length_append, List.length_reverse, List.length_replicate]
    omega
  rw [hLength] at hAll
  exact hAll

theorem decrement_workRunExact (value : Nat) (older inside outside : List WorkSymbol) :
    workRunExact? decrement 2
      (workStartConfiguration decrement
        {
          left := outside
          head := scratchEndSymbol
          right := List.replicate (value + 1) unitSymbol ++ separatorSymbol :: (older.reverse ++ inside) }) =
      some { state := decrement.acceptState, tape :=
        {
          left := WorkSymbol.blank :: outside
          head := scratchEndSymbol
          right := List.replicate value unitSymbol ++ separatorSymbol :: (older.reverse ++ inside) } } := by
  rfl

theorem initialize_run_compile_exact (count value : Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine markCounterMachine) (6 * initializeSteps count value)
      (encodeWorkConfiguration (workStartConfiguration markCounterMachine (restoredTape count [value] inside outside))) =
      encodeWorkConfiguration {
      state := markCounterMachine.acceptState
      tape := markedTape 0 count [value] inside outside } :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (initialize_workRunExact count value inside outside)

theorem consume_run_compile_exact (spent remaining : Nat) (newer : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine consume) (6 * consumeSteps spent (remaining + 1) newer)
      (encodeWorkConfiguration (workStartConfiguration consume (markedTape spent (remaining + 1) newer inside outside))) =
      encodeWorkConfiguration {
      state := consume.acceptState
      tape := markedTape (spent + 1) remaining newer inside outside } :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (consume_workRunExact spent remaining newer inside outside)

theorem exhausted_run_compile_exact (spent : Nat) (newer : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine consume) (6 * exhaustedSteps spent newer)
      (encodeWorkConfiguration (workStartConfiguration consume (markedTape spent 0 newer inside outside))) =
      encodeWorkConfiguration {
      state := consume.rejectState
      tape := restoredTape spent newer inside outside } :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (exhausted_workRunExact spent newer inside outside)

theorem restoredTape_eq_endTape (count : Nat) (newer older : List Nat) (inside outside : List WorkSymbol) :
    restoredTape count newer ((registerWord older).reverse ++ inside) outside =
      endTape (older ++ count :: newer) inside outside := by
  simp only [restoredTape, endTape, registerWord_append, registerWord, List.reverse_cons,
    List.reverse_append, List.reverse_replicate, List.cons_append, List.append_assoc, List.nil_append]

theorem markedTape_span (spent remaining : Nat) (newer : List Nat) (inside outside : List WorkSymbol) :
    (markedTape spent remaining newer inside outside).right.length =
      (registerWord newer).length + remaining + spent + 1 + inside.length := by
  simp only [markedTape, List.length_append, List.length_reverse, List.length_replicate, List.length_cons]
  omega

theorem consumeSteps_le (spent remaining bound : Nat) (newer : List Nat)
    (hCounter : spent + remaining ≤ bound) (hWord : (registerWord newer).length ≤ bound) :
    consumeSteps spent remaining newer ≤ 4 * bound + 3 := by
  unfold consumeSteps
  omega

theorem exhaustedSteps_le (spent bound : Nat) (newer : List Nat)
    (hCounter : spent ≤ bound) (hWord : (registerWord newer).length ≤ bound) :
    exhaustedSteps spent newer ≤ 6 * bound + 5 := by
  unfold exhaustedSteps
  omega

theorem initialize_rules_length : markCounterMachine.rules.length = 8 := rfl
theorem consume_rules_length : consume.rules.length = 17 := rfl
theorem decrement_rules_length : decrement.rules.length = 2 := rfl

theorem initialize_control :
    markCounterMachine.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt markCounterMachine markCounterMachine.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt markCounterMachine markCounterMachine.rejectState ∧
    markCounterMachine.acceptState ≠ markCounterMachine.rejectState := by
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

theorem consume_control :
    consume.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt consume consume.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt consume consume.rejectState ∧
    consume.acceptState ≠ consume.rejectState := by
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

theorem decrement_control :
    decrement.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt decrement decrement.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt decrement decrement.rejectState ∧
    decrement.acceptState ≠ decrement.rejectState := by
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

end PNP.Concrete.CookLevin.BuilderRegisterCountdownControl
