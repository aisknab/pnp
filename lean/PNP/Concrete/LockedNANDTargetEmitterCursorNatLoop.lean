/-
Copyright (c) 2026 PNP Labs.

A literal cursor-aware finite natural-token loop for the grammar-only
locked-NAND target emitter.

The loop starts on the first retained source cell.  The retained source has
one contextual `oneBlank` cursor cell between two packed words.  Every source
scan passes over that cursor without changing it.  Immediately behind the
source-left boundary the loop receives a unary scratch counter.  It consumes
the counter by changing one `zeroBlank` unit at a time to a context-local
mark, appends one literal `.unit` token for each unit, then appends one literal
`.natEnd` token.  A final cleanup pass restores every scratch unit before the
machine accepts.  The retained source, pre-existing target prefix, and
workspace outside the scratch record are not used as host-side advice.

The executable table is fixed finite data.  Its two token append copies have
different done states, so the controller never depends on a shared accept-state
rule or rule shadowing.  No rule calls a decoder, `targetBytes`, the raw
builder, or any semantic source-to-target function.
-/

import PNP.Concrete.LockedNANDTargetEmitterCursorAppender

namespace PNP.Concrete.LockedNAND.TargetEmitterCursorNatLoop

open PNP.Concrete

/-! ### Disjoint controller states and scratch layout -/

def startState : Nat := 100
def inspectBoundaryState : Nat := 101
def inspectCounterState : Nat := 102
def returnUnitState : Nat := 103
def returnEndState : Nat := 104
def unitDoneState : Nat := 105
def natEndDoneState : Nat := 106
def cleanupBoundaryState : Nat := 107
def cleanupCounterState : Nat := 108
def cleanupReturnState : Nat := 109
def acceptState : Nat := 110
def rejectState : Nat := 111
def deadState : Nat := TargetEmitter.deadState

/-- Consumed unary units use the target-boundary symbol in the disjoint
left-scratch context. -/
def counterMark : WorkSymbol := WorkSymbol.blankOne

def unaryUnit : WorkSymbol := TargetEmitter.unaryUnit
def unarySeparator : WorkSymbol := TargetEmitter.unarySeparator
def cursorMarker : WorkSymbol := TargetEmitterCursorAppender.cursorMarker
def sourceLeftBoundary : WorkSymbol :=
  TargetEmitterCursorAppender.sourceLeftBoundary
def sourceTargetBoundary : WorkSymbol :=
  TargetEmitterCursorAppender.sourceTargetBoundary

abbrev SourceSymbol : WorkSymbol → Prop :=
  TargetEmitterCursorAppender.SourceSymbol

/-- The left scratch separator and retained-source cursor deliberately share
one symbol; the source-left boundary keeps their contexts disjoint. -/
theorem cursorMarker_eq_unarySeparator :
    cursorMarker = unarySeparator := by
  rfl

theorem cursor_ne_sourceLeftBoundary :
    cursorMarker ≠ sourceLeftBoundary :=
  TargetEmitterCursorAppender.cursor_ne_sourceLeftBoundary

theorem cursor_ne_sourceTargetBoundary :
    cursorMarker ≠ sourceTargetBoundary :=
  TargetEmitterCursorAppender.cursor_ne_sourceTargetBoundary

def initialCounterWord (count : Nat) : List WorkSymbol :=
  List.replicate count unaryUnit ++ [unarySeparator]

def loopCounterWord (used remaining : Nat) : List WorkSymbol :=
  List.replicate used counterMark ++
    List.replicate remaining unaryUnit ++ [unarySeparator]

theorem initialCounterWord_eq_loop (count : Nat) :
    initialCounterWord count = loopCounterWord 0 count := by
  simp [initialCounterWord, loopCounterWord]

private theorem replicate_succ_append {α : Type}
    (count : Nat) (item : α) :
    List.replicate (count + 1) item =
      List.replicate count item ++ [item] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change
        item :: List.replicate (count + 1) item =
          item :: (List.replicate count item ++ [item])
      rw [ih]

/-! ### Fixed 180-rule table -/

def allWorkSymbols : List WorkSymbol :=
  TargetEmitter.allWorkSymbols

structure StateProgram where
  state : Nat
  action : WorkSymbol → Nat × WorkSymbol × HeadMove

def deadAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  (deadState, symbol, .stay)

def sourceAction (target : Nat) (move : HeadMove)
    (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.zeroZero ∨ symbol = WorkSymbol.zeroOne ∨
      symbol = WorkSymbol.oneZero ∨ symbol = WorkSymbol.oneOne ∨
      symbol = cursorMarker then
    (target, symbol, move)
  else
    deadAction symbol

def expectKeep (expected : WorkSymbol) (target : Nat)
    (move : HeadMove) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = expected then
    (target, symbol, move)
  else
    deadAction symbol

/-- The only append-row changed from the primitive: a successful return over
the source-left boundary enters the token-specific done state. -/
def appendRewindSourceAction (token : Token) (done : Nat)
    (symbol : WorkSymbol) : Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.zeroZero ∨ symbol = WorkSymbol.zeroOne ∨
      symbol = WorkSymbol.oneZero ∨ symbol = WorkSymbol.oneOne ∨
      symbol = cursorMarker then
    (TargetEmitter.rewindSourceState token, symbol, .left)
  else if symbol = sourceLeftBoundary then
    (done, symbol, .right)
  else
    deadAction symbol

def appendPrograms (token : Token) (done : Nat) : List StateProgram :=
  [{ state := TargetEmitter.seekSourceState token,
      action := TargetEmitterCursorAppender.seekSourceAction token },
   { state := TargetEmitter.seekTargetState token,
      action := TargetEmitter.seekTargetAction token },
   { state := TargetEmitter.writeSecondState token,
      action := TargetEmitter.writeSecondAction token },
   { state := TargetEmitter.rewindTargetState token,
      action := TargetEmitter.rewindTargetAction token },
   { state := TargetEmitter.rewindSourceState token,
      action := appendRewindSourceAction token done }]

def inspectCounterAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = counterMark then
    (inspectCounterState, symbol, .left)
  else if symbol = unaryUnit then
    (returnUnitState, counterMark, .right)
  else if symbol = unarySeparator then
    (returnEndState, symbol, .right)
  else
    deadAction symbol

def returnUnitAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = counterMark then
    (returnUnitState, symbol, .right)
  else if symbol = sourceLeftBoundary then
    (TargetEmitter.seekSourceState .unit, symbol, .right)
  else
    deadAction symbol

def returnEndAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = counterMark then
    (returnEndState, symbol, .right)
  else if symbol = sourceLeftBoundary then
    (TargetEmitter.seekSourceState .natEnd, symbol, .right)
  else
    deadAction symbol

def cleanupCounterAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = counterMark then
    (cleanupCounterState, unaryUnit, .left)
  else if symbol = unarySeparator then
    (cleanupReturnState, symbol, .right)
  else
    deadAction symbol

def cleanupReturnAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (cleanupReturnState, symbol, .right)
  else if symbol = sourceLeftBoundary then
    (acceptState, symbol, .right)
  else
    deadAction symbol

def controllerPrograms : List StateProgram :=
  [{ state := startState,
      action := sourceAction inspectBoundaryState .left },
   { state := inspectBoundaryState,
      action := expectKeep sourceLeftBoundary inspectCounterState .left },
   { state := inspectCounterState,
      action := inspectCounterAction },
   { state := returnUnitState,
      action := returnUnitAction },
   { state := returnEndState,
      action := returnEndAction },
   { state := unitDoneState,
      action := sourceAction inspectBoundaryState .left },
   { state := natEndDoneState,
      action := sourceAction cleanupBoundaryState .left },
   { state := cleanupBoundaryState,
      action := expectKeep sourceLeftBoundary cleanupCounterState .left },
   { state := cleanupCounterState,
      action := cleanupCounterAction },
   { state := cleanupReturnState,
      action := cleanupReturnAction }]

def statePrograms : List StateProgram :=
  appendPrograms .unit unitDoneState ++
    appendPrograms .natEnd natEndDoneState ++
      controllerPrograms

def rulesAt (program : StateProgram) : List WorkRule :=
  allWorkSymbols.map fun symbol =>
    let action := program.action symbol
    { sourceState := program.state
      readSymbol := symbol
      targetState := action.1
      writeSymbol := action.2.1
      move := action.2.2 }

def rules : List WorkRule :=
  statePrograms.flatMap rulesAt

def machine : WorkMachine :=
  { rules := rules
    startState := startState
    acceptState := acceptState
    rejectState := rejectState }

def compiledMachine : Machine :=
  compileWorkMachine machine

theorem statePrograms_length :
    statePrograms.length = 20 := by
  rfl

theorem rulesAt_length (program : StateProgram) :
    (rulesAt program).length = 9 := by
  simp [rulesAt, allWorkSymbols, TargetEmitter.allWorkSymbols_length]

theorem rules_length :
    rules.length = 180 := by
  change (statePrograms.flatMap rulesAt).length = 180
  have materializedLength :
      ∀ programs : List StateProgram,
        (programs.flatMap rulesAt).length = 9 * programs.length := by
    intro programs
    induction programs with
    | nil => rfl
    | cons first rest ih =>
        simp only [List.flatMap_cons, List.length_append,
          rulesAt_length, ih, List.length_cons, Nat.mul_succ]
        omega
  rw [materializedLength, statePrograms_length]

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

private theorem rulesAt_pairwise_query_distinct
    (program : StateProgram) :
    (rulesAt program).Pairwise QueryDistinct := by
  unfold rulesAt allWorkSymbols TargetEmitter.allWorkSymbols
  simp [QueryDistinct, WorkSymbol.blank,
    WorkSymbol.blankZero, WorkSymbol.blankOne,
    WorkSymbol.zeroBlank, WorkSymbol.zeroZero, WorkSymbol.zeroOne,
    WorkSymbol.oneBlank, WorkSymbol.oneZero, WorkSymbol.oneOne]

private theorem rulesAt_source_eq {program : StateProgram}
    {rule : WorkRule} (member : rule ∈ rulesAt program) :
    rule.sourceState = program.state := by
  rcases List.mem_map.mp member with ⟨symbol, _symbolMember, hRule⟩
  rw [← hRule]

private theorem materializedPrograms_pairwise_query_distinct
    (programs : List StateProgram)
    (stateDistinct : programs.Pairwise fun left right =>
      left.state ≠ right.state) :
    (programs.flatMap rulesAt).Pairwise QueryDistinct := by
  induction programs with
  | nil => exact List.Pairwise.nil
  | cons first rest ih =>
      cases stateDistinct with
      | cons firstDistinct restDistinct =>
          change
            (rulesAt first ++ rest.flatMap rulesAt).Pairwise
              QueryDistinct
          rw [List.pairwise_append]
          refine
            ⟨rulesAt_pairwise_query_distinct first,
             ih restDistinct, ?_⟩
          intro left leftMember right rightMember queryEq
          rcases List.mem_flatMap.mp rightMember with
            ⟨rightProgram, rightProgramMember, rightRuleMember⟩
          have sourceNe :=
            firstDistinct rightProgram rightProgramMember
          have leftSource := rulesAt_source_eq leftMember
          have rightSource := rulesAt_source_eq rightRuleMember
          have sourceEq := congrArg Prod.fst queryEq
          exact sourceNe
            (leftSource.symm.trans (sourceEq.trans rightSource))

private theorem statePrograms_pairwise_state_distinct :
    statePrograms.Pairwise fun left right => left.state ≠ right.state := by
  set_option maxRecDepth 100000 in
    decide

theorem rules_pairwise :
    rules.Pairwise QueryDistinct := by
  exact materializedPrograms_pairwise_query_distinct statePrograms
    statePrograms_pairwise_state_distinct

theorem machine_start_ne_accept :
    machine.startState ≠ machine.acceptState := by
  decide

theorem machine_start_ne_reject :
    machine.startState ≠ machine.rejectState := by
  decide

theorem machine_accept_ne_reject :
    machine.acceptState ≠ machine.rejectState := by
  decide

set_option maxRecDepth 100000 in
theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule rules acceptState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 100000 in
theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules rejectState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 100000 in
theorem no_rule_at_dead (symbol : WorkSymbol) :
    findWorkRule rules deadState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

/-! ### Exact token-specific append subroutines -/

inductive AppendKind where
  | unit
  | natEnd
deriving BEq, DecidableEq, Repr

def AppendKind.token : AppendKind → Token
  | .unit => .unit
  | .natEnd => .natEnd

def AppendKind.doneState : AppendKind → Nat
  | .unit => unitDoneState
  | .natEnd => natEndDoneState

private theorem appendTokenFirstPacked (kind : AppendKind) :
    TargetEmitter.PackedSymbol
      (TargetEmitter.tokenFirstSymbol kind.token) := by
  cases kind <;> constructor

private def pushLeft : List WorkSymbol → List WorkSymbol → List WorkSymbol
  | [], farSide => farSide
  | head :: rest, farSide => pushLeft rest (head :: farSide)

private theorem pushLeft_eq_reverse_append
    (word farSide : List WorkSymbol) :
    pushLeft word farSide = word.reverse ++ farSide := by
  induction word generalizing farSide with
  | nil => rfl
  | cons head rest ih =>
      simp only [pushLeft, ih, List.reverse_cons, List.append_assoc]
      rfl

private theorem workRunExact_compose (first second : Nat)
    (start middle final : WorkConfiguration)
    (hFirst : workRunExact? machine first start = some middle)
    (hSecond : workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) start = some final := by
  induction first generalizing start with
  | zero =>
      change some start = some middle at hFirst
      have hStart : start = middle := Option.some.inj hFirst
      rw [Nat.zero_add, hStart]
      exact hSecond
  | succ first ih =>
      cases hStep : workStep? machine start with
      | none =>
          change
            (match workStep? machine start with
             | none => none
             | some next => workRunExact? machine first next) =
              some middle at hFirst
          rw [hStep] at hFirst
          contradiction
      | some next =>
          have hTail : workRunExact? machine first next = some middle := by
            change
              (match workStep? machine start with
               | none => none
               | some next => workRunExact? machine first next) =
                some middle at hFirst
            rw [hStep] at hFirst
            exact hFirst
          rw [Nat.succ_add]
          change
            (match workStep? machine start with
             | none => none
             | some next => workRunExact? machine (first + second) next) =
              some final
          rw [hStep]
          exact ih next hTail

private theorem workRunExact_one
    (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change (match workStep? machine start with
    | none => none
    | some result => some result) = some next
  rw [hStep]

private theorem scanRightExact (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ leftSide head suffix,
      Allowed head →
      workStep? machine
          (TargetEmitter.configAtWord state leftSide (head :: suffix)) =
        some (TargetEmitter.configAtWord state
          (head :: leftSide) suffix))
    (word suffix leftSide : List WorkSymbol)
    (hAllowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? machine word.length
        (TargetEmitter.configAtWord state leftSide (word ++ suffix)) =
      some (TargetEmitter.configAtWord state
        (pushLeft word leftSide) suffix) := by
  induction word generalizing leftSide with
  | nil => rfl
  | cons head rest ih =>
      have hHead : Allowed head := hAllowed head (List.Mem.head rest)
      have hRest : ∀ symbol, symbol ∈ rest → Allowed symbol := by
        intro symbol found
        exact hAllowed symbol (List.Mem.tail head found)
      change
        (match workStep? machine
          (TargetEmitter.configAtWord state leftSide
            (head :: (rest ++ suffix))) with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep leftSide head (rest ++ suffix) hHead]
      exact ih (head :: leftSide) hRest

private theorem scanLeftExact (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ head leftTail rightSide,
      Allowed head →
      workStep? machine
          (TargetEmitter.configAtLeftWord state
            (head :: leftTail) rightSide) =
        some (TargetEmitter.configAtLeftWord state
          leftTail (head :: rightSide)))
    (word leftSuffix rightSide : List WorkSymbol)
    (hAllowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? machine word.length
        (TargetEmitter.configAtLeftWord state
          (word ++ leftSuffix) rightSide) =
      some (TargetEmitter.configAtLeftWord state
        leftSuffix (pushLeft word rightSide)) := by
  induction word generalizing rightSide with
  | nil => rfl
  | cons head rest ih =>
      have hHead : Allowed head := hAllowed head (List.Mem.head rest)
      have hRest : ∀ symbol, symbol ∈ rest → Allowed symbol := by
        intro symbol found
        exact hAllowed symbol (List.Mem.tail head found)
      change
        (match workStep? machine
          (TargetEmitter.configAtLeftWord state
            (head :: (rest ++ leftSuffix)) rightSide) with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep head (rest ++ leftSuffix) rightSide hHead]
      exact ih (head :: rightSide) hRest

private def literalRule (source : Nat) (read : WorkSymbol)
    (target : Nat) (write : WorkSymbol) (move : HeadMove) : WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := write
    move := move }

set_option maxRecDepth 100000 in
private theorem find_append_seekSource_packed (kind : AppendKind)
    (symbol : WorkSymbol) (ordinary : SourceSymbol symbol) :
    findWorkRule rules (TargetEmitter.seekSourceState kind.token) symbol =
      some (literalRule (TargetEmitter.seekSourceState kind.token) symbol
        (TargetEmitter.seekSourceState kind.token) symbol .right) := by
  cases kind <;> cases ordinary with
    | packed packed => cases packed <;> decide
    | cursor => decide

set_option maxRecDepth 100000 in
private theorem find_append_seekSource_boundary (kind : AppendKind) :
    findWorkRule rules (TargetEmitter.seekSourceState kind.token)
        sourceTargetBoundary =
      some (literalRule (TargetEmitter.seekSourceState kind.token)
        sourceTargetBoundary
        (TargetEmitter.seekTargetState kind.token)
        sourceTargetBoundary .right) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_append_seekTarget_packed (kind : AppendKind)
    (symbol : WorkSymbol) (ordinary : TargetEmitter.PackedSymbol symbol) :
    findWorkRule rules (TargetEmitter.seekTargetState kind.token) symbol =
      some (literalRule (TargetEmitter.seekTargetState kind.token) symbol
        (TargetEmitter.seekTargetState kind.token) symbol .right) := by
  cases kind <;> cases ordinary <;> decide

set_option maxRecDepth 100000 in
private theorem find_append_seekTarget_blank (kind : AppendKind) :
    findWorkRule rules (TargetEmitter.seekTargetState kind.token)
        WorkSymbol.blank =
      some (literalRule (TargetEmitter.seekTargetState kind.token)
        WorkSymbol.blank
        (TargetEmitter.writeSecondState kind.token)
        (TargetEmitter.tokenFirstSymbol kind.token) .right) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_append_writeSecond_blank (kind : AppendKind) :
    findWorkRule rules (TargetEmitter.writeSecondState kind.token)
        WorkSymbol.blank =
      some (literalRule (TargetEmitter.writeSecondState kind.token)
        WorkSymbol.blank
        (TargetEmitter.rewindTargetState kind.token)
        (TargetEmitter.tokenSecondSymbol kind.token) .left) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_append_rewindTarget_packed (kind : AppendKind)
    (symbol : WorkSymbol) (ordinary : TargetEmitter.PackedSymbol symbol) :
    findWorkRule rules (TargetEmitter.rewindTargetState kind.token) symbol =
      some (literalRule (TargetEmitter.rewindTargetState kind.token) symbol
        (TargetEmitter.rewindTargetState kind.token) symbol .left) := by
  cases kind <;> cases ordinary <;> decide

set_option maxRecDepth 100000 in
private theorem find_append_rewindTarget_boundary (kind : AppendKind) :
    findWorkRule rules (TargetEmitter.rewindTargetState kind.token)
        sourceTargetBoundary =
      some (literalRule (TargetEmitter.rewindTargetState kind.token)
        sourceTargetBoundary
        (TargetEmitter.rewindSourceState kind.token)
        sourceTargetBoundary .left) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_append_rewindSource_packed (kind : AppendKind)
    (symbol : WorkSymbol) (ordinary : SourceSymbol symbol) :
    findWorkRule rules (TargetEmitter.rewindSourceState kind.token) symbol =
      some (literalRule (TargetEmitter.rewindSourceState kind.token) symbol
        (TargetEmitter.rewindSourceState kind.token) symbol .left) := by
  cases kind <;> cases ordinary with
    | packed packed => cases packed <;> decide
    | cursor => decide

set_option maxRecDepth 100000 in
private theorem find_append_rewindSource_boundary (kind : AppendKind) :
    findWorkRule rules (TargetEmitter.rewindSourceState kind.token)
        sourceLeftBoundary =
      some (literalRule (TargetEmitter.rewindSourceState kind.token)
        sourceLeftBoundary kind.doneState sourceLeftBoundary .right) := by
  cases kind <;> decide

private theorem appendState_not_halted (kind : AppendKind)
    (state : Nat)
    (stateCases :
      state = TargetEmitter.seekSourceState kind.token ∨
      state = TargetEmitter.seekTargetState kind.token ∨
      state = TargetEmitter.writeSecondState kind.token ∨
      state = TargetEmitter.rewindTargetState kind.token ∨
      state = TargetEmitter.rewindSourceState kind.token)
    (tape : WorkTape) :
    machine.isHalted { state := state, tape := tape } = false := by
  rcases stateCases with first | second | third | fourth | fifth
  · subst state
    cases kind <;> rfl
  · subst state
    cases kind <;> rfl
  · subst state
    cases kind <;> rfl
  · subst state
    cases kind <;> rfl
  · subst state
    cases kind <;> rfl

private theorem append_seekSource_packed_step (kind : AppendKind)
    (leftSide suffix : List WorkSymbol) (symbol : WorkSymbol)
    (ordinary : SourceSymbol symbol) :
    workStep? machine
        (TargetEmitter.configAtWord
          (TargetEmitter.seekSourceState kind.token)
          leftSide (symbol :: suffix)) =
      some (TargetEmitter.configAtWord
        (TargetEmitter.seekSourceState kind.token)
        (symbol :: leftSide) suffix) := by
  let config := TargetEmitter.configAtWord
    (TargetEmitter.seekSourceState kind.token)
    leftSide (symbol :: suffix)
  have hHalted : machine.isHalted config = false :=
    appendState_not_halted kind _ (Or.inl rfl) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule (TargetEmitter.seekSourceState kind.token) symbol
          (TargetEmitter.seekSourceState kind.token) symbol .right)
        config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_append_seekSource_packed kind symbol ordinary)
    _ = some (TargetEmitter.configAtWord
        (TargetEmitter.seekSourceState kind.token)
        (symbol :: leftSide) suffix) := by
      cases suffix <;> rfl

private theorem append_seekSource_boundary_step (kind : AppendKind)
    (leftSide suffix : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtWord
          (TargetEmitter.seekSourceState kind.token)
          leftSide (sourceTargetBoundary :: suffix)) =
      some (TargetEmitter.configAtWord
        (TargetEmitter.seekTargetState kind.token)
        (sourceTargetBoundary :: leftSide) suffix) := by
  let config := TargetEmitter.configAtWord
    (TargetEmitter.seekSourceState kind.token)
    leftSide (sourceTargetBoundary :: suffix)
  have hHalted : machine.isHalted config = false :=
    appendState_not_halted kind _ (Or.inl rfl) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule (TargetEmitter.seekSourceState kind.token)
          sourceTargetBoundary
          (TargetEmitter.seekTargetState kind.token)
          sourceTargetBoundary .right) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_append_seekSource_boundary kind)
    _ = some (TargetEmitter.configAtWord
        (TargetEmitter.seekTargetState kind.token)
        (sourceTargetBoundary :: leftSide) suffix) := by
      cases suffix <;> rfl

private theorem append_seekTarget_packed_step (kind : AppendKind)
    (leftSide suffix : List WorkSymbol) (symbol : WorkSymbol)
    (ordinary : TargetEmitter.PackedSymbol symbol) :
    workStep? machine
        (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState kind.token)
          leftSide (symbol :: suffix)) =
      some (TargetEmitter.configAtWord
        (TargetEmitter.seekTargetState kind.token)
        (symbol :: leftSide) suffix) := by
  let config := TargetEmitter.configAtWord
    (TargetEmitter.seekTargetState kind.token)
    leftSide (symbol :: suffix)
  have hHalted : machine.isHalted config = false :=
    appendState_not_halted kind _ (Or.inr (Or.inl rfl)) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule (TargetEmitter.seekTargetState kind.token) symbol
          (TargetEmitter.seekTargetState kind.token) symbol .right)
        config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_append_seekTarget_packed kind symbol ordinary)
    _ = some (TargetEmitter.configAtWord
        (TargetEmitter.seekTargetState kind.token)
        (symbol :: leftSide) suffix) := by
      cases suffix <;> rfl

private theorem append_writeFirst_step (kind : AppendKind)
    (leftSide suffix : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState kind.token) leftSide
          (WorkSymbol.blank :: WorkSymbol.blank :: suffix)) =
      some (TargetEmitter.configAtWord
        (TargetEmitter.writeSecondState kind.token)
        (TargetEmitter.tokenFirstSymbol kind.token :: leftSide)
        (WorkSymbol.blank :: suffix)) := by
  let config := TargetEmitter.configAtWord
    (TargetEmitter.seekTargetState kind.token) leftSide
    (WorkSymbol.blank :: WorkSymbol.blank :: suffix)
  have hHalted : machine.isHalted config = false :=
    appendState_not_halted kind _ (Or.inr (Or.inl rfl)) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule (TargetEmitter.seekTargetState kind.token)
          WorkSymbol.blank
          (TargetEmitter.writeSecondState kind.token)
          (TargetEmitter.tokenFirstSymbol kind.token) .right)
        config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_append_seekTarget_blank kind)
    _ = some (TargetEmitter.configAtWord
        (TargetEmitter.writeSecondState kind.token)
        (TargetEmitter.tokenFirstSymbol kind.token :: leftSide)
        (WorkSymbol.blank :: suffix)) := by
      rfl

private theorem append_writeSecond_step (kind : AppendKind)
    (leftSide suffix : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtWord
          (TargetEmitter.writeSecondState kind.token)
          (TargetEmitter.tokenFirstSymbol kind.token :: leftSide)
          (WorkSymbol.blank :: suffix)) =
      some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindTargetState kind.token)
        (TargetEmitter.tokenFirstSymbol kind.token :: leftSide)
        (TargetEmitter.tokenSecondSymbol kind.token :: suffix)) := by
  let config := TargetEmitter.configAtWord
    (TargetEmitter.writeSecondState kind.token)
    (TargetEmitter.tokenFirstSymbol kind.token :: leftSide)
    (WorkSymbol.blank :: suffix)
  have hHalted : machine.isHalted config = false :=
    appendState_not_halted kind _
      (Or.inr (Or.inr (Or.inl rfl))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule (TargetEmitter.writeSecondState kind.token)
          WorkSymbol.blank
          (TargetEmitter.rewindTargetState kind.token)
          (TargetEmitter.tokenSecondSymbol kind.token) .left)
        config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_append_writeSecond_blank kind)
    _ = some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindTargetState kind.token)
        (TargetEmitter.tokenFirstSymbol kind.token :: leftSide)
        (TargetEmitter.tokenSecondSymbol kind.token :: suffix)) := by
      rfl

private theorem append_rewindTarget_packed_step (kind : AppendKind)
    (leftTail rightSide : List WorkSymbol) (symbol : WorkSymbol)
    (ordinary : TargetEmitter.PackedSymbol symbol) :
    workStep? machine
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindTargetState kind.token)
          (symbol :: leftTail) rightSide) =
      some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindTargetState kind.token)
        leftTail (symbol :: rightSide)) := by
  let config := TargetEmitter.configAtLeftWord
    (TargetEmitter.rewindTargetState kind.token)
    (symbol :: leftTail) rightSide
  have hHalted : machine.isHalted config = false :=
    appendState_not_halted kind _
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule (TargetEmitter.rewindTargetState kind.token) symbol
          (TargetEmitter.rewindTargetState kind.token) symbol .left)
        config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_append_rewindTarget_packed kind symbol ordinary)
    _ = some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindTargetState kind.token)
        leftTail (symbol :: rightSide)) := by
      cases leftTail <;> rfl

private theorem append_rewindTarget_boundary_step (kind : AppendKind)
    (leftTail rightSide : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindTargetState kind.token)
          (sourceTargetBoundary :: leftTail) rightSide) =
      some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindSourceState kind.token)
        leftTail (sourceTargetBoundary :: rightSide)) := by
  let config := TargetEmitter.configAtLeftWord
    (TargetEmitter.rewindTargetState kind.token)
    (sourceTargetBoundary :: leftTail) rightSide
  have hHalted : machine.isHalted config = false :=
    appendState_not_halted kind _
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule (TargetEmitter.rewindTargetState kind.token)
          sourceTargetBoundary
          (TargetEmitter.rewindSourceState kind.token)
          sourceTargetBoundary .left) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_append_rewindTarget_boundary kind)
    _ = some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindSourceState kind.token)
        leftTail (sourceTargetBoundary :: rightSide)) := by
      cases leftTail <;> rfl

private theorem append_rewindSource_packed_step (kind : AppendKind)
    (leftTail rightSide : List WorkSymbol) (symbol : WorkSymbol)
    (ordinary : SourceSymbol symbol) :
    workStep? machine
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindSourceState kind.token)
          (symbol :: leftTail) rightSide) =
      some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindSourceState kind.token)
        leftTail (symbol :: rightSide)) := by
  let config := TargetEmitter.configAtLeftWord
    (TargetEmitter.rewindSourceState kind.token)
    (symbol :: leftTail) rightSide
  have hHalted : machine.isHalted config = false :=
    appendState_not_halted kind _
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule (TargetEmitter.rewindSourceState kind.token) symbol
          (TargetEmitter.rewindSourceState kind.token) symbol .left)
        config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_append_rewindSource_packed kind symbol ordinary)
    _ = some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindSourceState kind.token)
        leftTail (symbol :: rightSide)) := by
      cases leftTail <;> rfl

private theorem append_rewindSource_boundary_step (kind : AppendKind)
    (leftTail rightSide : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindSourceState kind.token)
          (sourceLeftBoundary :: leftTail) rightSide) =
      some (TargetEmitter.configAtWord kind.doneState
        (sourceLeftBoundary :: leftTail) rightSide) := by
  let config := TargetEmitter.configAtLeftWord
    (TargetEmitter.rewindSourceState kind.token)
    (sourceLeftBoundary :: leftTail) rightSide
  have hHalted : machine.isHalted config = false :=
    appendState_not_halted kind _
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule (TargetEmitter.rewindSourceState kind.token)
          sourceLeftBoundary kind.doneState sourceLeftBoundary .right)
        config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_append_rewindSource_boundary kind)
    _ = some (TargetEmitter.configAtWord kind.doneState
        (sourceLeftBoundary :: leftTail) rightSide) := by
      cases rightSide <;> rfl

def appendEntry (kind : AppendKind)
    (source target controllerOutside outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  TargetEmitter.configAtWord
    (TargetEmitter.seekSourceState kind.token)
    (sourceLeftBoundary :: controllerOutside)
    (source ++
      (sourceTargetBoundary ::
        (target ++
          (WorkSymbol.blank :: WorkSymbol.blank ::
            WorkSymbol.blank :: outsideRight))))

def appendFinal (kind : AppendKind)
    (source target controllerOutside outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  TargetEmitter.configAtWord kind.doneState
    (sourceLeftBoundary :: controllerOutside)
    (source ++
      (sourceTargetBoundary ::
        (target ++ TargetEmitter.tokenSymbols kind.token ++
          (WorkSymbol.blank :: outsideRight))))

def appendWorkSteps (source target : List WorkSymbol) : Nat :=
  2 * source.length + 2 * target.length + 6

theorem append_exact (kind : AppendKind)
    (source target controllerOutside outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol, symbol ∈ source → SourceSymbol symbol)
    (targetPacked :
      ∀ symbol, symbol ∈ target → TargetEmitter.PackedSymbol symbol) :
    workRunExact? machine (appendWorkSteps source target)
        (appendEntry kind source target controllerOutside outsideRight) =
      some (appendFinal kind source target
        controllerOutside outsideRight) := by
  let baseLeft := sourceLeftBoundary :: controllerOutside
  let afterSourceLeft := pushLeft source baseLeft
  let afterBoundaryLeft := sourceTargetBoundary :: afterSourceLeft
  let afterTargetLeft := pushLeft target afterBoundaryLeft
  let targetAndTokenRight :=
    target ++ TargetEmitter.tokenSymbols kind.token ++
      (WorkSymbol.blank :: outsideRight)
  have hSource :
      workRunExact? machine source.length
          (TargetEmitter.configAtWord
            (TargetEmitter.seekSourceState kind.token) baseLeft
            (source ++
              (sourceTargetBoundary ::
                (target ++
                  (WorkSymbol.blank :: WorkSymbol.blank ::
                    WorkSymbol.blank :: outsideRight))))) =
        some (TargetEmitter.configAtWord
          (TargetEmitter.seekSourceState kind.token) afterSourceLeft
          (sourceTargetBoundary ::
            (target ++
              (WorkSymbol.blank :: WorkSymbol.blank ::
                WorkSymbol.blank :: outsideRight)))) := by
    exact scanRightExact
      (TargetEmitter.seekSourceState kind.token)
      SourceSymbol
      (fun left head suffix ordinary =>
        append_seekSource_packed_step kind left suffix head ordinary)
      source
      (sourceTargetBoundary ::
        (target ++
          (WorkSymbol.blank :: WorkSymbol.blank ::
            WorkSymbol.blank :: outsideRight)))
      baseLeft sourcePacked
  have hSourceBoundary :
      workRunExact? machine 1
          (TargetEmitter.configAtWord
            (TargetEmitter.seekSourceState kind.token) afterSourceLeft
            (sourceTargetBoundary ::
              (target ++
                (WorkSymbol.blank :: WorkSymbol.blank ::
                  WorkSymbol.blank :: outsideRight)))) =
        some (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState kind.token) afterBoundaryLeft
          (target ++
            (WorkSymbol.blank :: WorkSymbol.blank ::
              WorkSymbol.blank :: outsideRight))) := by
    apply workRunExact_one
    exact append_seekSource_boundary_step kind afterSourceLeft
      (target ++
        (WorkSymbol.blank :: WorkSymbol.blank ::
          WorkSymbol.blank :: outsideRight))
  have hTarget :
      workRunExact? machine target.length
          (TargetEmitter.configAtWord
            (TargetEmitter.seekTargetState kind.token) afterBoundaryLeft
            (target ++
              (WorkSymbol.blank :: WorkSymbol.blank ::
                WorkSymbol.blank :: outsideRight))) =
        some (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState kind.token) afterTargetLeft
          (WorkSymbol.blank :: WorkSymbol.blank ::
            WorkSymbol.blank :: outsideRight)) := by
    exact scanRightExact
      (TargetEmitter.seekTargetState kind.token)
      TargetEmitter.PackedSymbol
      (fun left head suffix ordinary =>
        append_seekTarget_packed_step kind left suffix head ordinary)
      target
      (WorkSymbol.blank :: WorkSymbol.blank ::
        WorkSymbol.blank :: outsideRight)
      afterBoundaryLeft targetPacked
  have hFirst :
      workRunExact? machine 1
          (TargetEmitter.configAtWord
            (TargetEmitter.seekTargetState kind.token) afterTargetLeft
            (WorkSymbol.blank :: WorkSymbol.blank ::
              WorkSymbol.blank :: outsideRight)) =
        some (TargetEmitter.configAtWord
          (TargetEmitter.writeSecondState kind.token)
          (TargetEmitter.tokenFirstSymbol kind.token :: afterTargetLeft)
          (WorkSymbol.blank :: WorkSymbol.blank :: outsideRight)) := by
    apply workRunExact_one
    exact append_writeFirst_step kind afterTargetLeft
      (WorkSymbol.blank :: outsideRight)
  have hSecond :
      workRunExact? machine 1
          (TargetEmitter.configAtWord
            (TargetEmitter.writeSecondState kind.token)
            (TargetEmitter.tokenFirstSymbol kind.token :: afterTargetLeft)
            (WorkSymbol.blank :: WorkSymbol.blank :: outsideRight)) =
        some (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindTargetState kind.token)
          (TargetEmitter.tokenFirstSymbol kind.token :: afterTargetLeft)
          (TargetEmitter.tokenSecondSymbol kind.token ::
            WorkSymbol.blank :: outsideRight)) := by
    apply workRunExact_one
    exact append_writeSecond_step kind afterTargetLeft
      (WorkSymbol.blank :: outsideRight)
  have rewindTargetPacked :
      ∀ symbol,
        symbol ∈ TargetEmitter.tokenFirstSymbol kind.token :: target.reverse →
          TargetEmitter.PackedSymbol symbol := by
    intro symbol found
    cases found with
    | head =>
        exact appendTokenFirstPacked kind
    | tail _ tailMember =>
        exact targetPacked symbol (List.mem_reverse.mp tailMember)
  have hRewindTarget :
      workRunExact? machine (target.length + 1)
          (TargetEmitter.configAtLeftWord
            (TargetEmitter.rewindTargetState kind.token)
            (TargetEmitter.tokenFirstSymbol kind.token :: afterTargetLeft)
            (TargetEmitter.tokenSecondSymbol kind.token ::
              WorkSymbol.blank :: outsideRight)) =
        some (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindTargetState kind.token)
          afterBoundaryLeft targetAndTokenRight) := by
    have scanned := scanLeftExact
      (TargetEmitter.rewindTargetState kind.token)
      TargetEmitter.PackedSymbol
      (fun head left right ordinary =>
        append_rewindTarget_packed_step kind left right head ordinary)
      (TargetEmitter.tokenFirstSymbol kind.token :: target.reverse)
      afterBoundaryLeft
      (TargetEmitter.tokenSecondSymbol kind.token ::
        WorkSymbol.blank :: outsideRight)
      rewindTargetPacked
    simpa [afterTargetLeft, pushLeft_eq_reverse_append,
      targetAndTokenRight, TargetEmitter.tokenSymbols,
      List.append_assoc] using scanned
  have hTargetBoundary :
      workRunExact? machine 1
          (TargetEmitter.configAtLeftWord
            (TargetEmitter.rewindTargetState kind.token)
            afterBoundaryLeft targetAndTokenRight) =
        some (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindSourceState kind.token)
          afterSourceLeft
          (sourceTargetBoundary :: targetAndTokenRight)) := by
    apply workRunExact_one
    exact append_rewindTarget_boundary_step kind afterSourceLeft
      targetAndTokenRight
  have rewindSourcePacked :
    ∀ symbol, symbol ∈ source.reverse →
        SourceSymbol symbol := by
    intro symbol found
    exact sourcePacked symbol (List.mem_reverse.mp found)
  have hRewindSource :
      workRunExact? machine source.length
          (TargetEmitter.configAtLeftWord
            (TargetEmitter.rewindSourceState kind.token)
            afterSourceLeft
            (sourceTargetBoundary :: targetAndTokenRight)) =
        some (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindSourceState kind.token)
          baseLeft
          (source ++
            (sourceTargetBoundary :: targetAndTokenRight))) := by
    have scanned := scanLeftExact
      (TargetEmitter.rewindSourceState kind.token)
      SourceSymbol
      (fun head left right ordinary =>
        append_rewindSource_packed_step kind left right head ordinary)
      source.reverse baseLeft
      (sourceTargetBoundary :: targetAndTokenRight)
      rewindSourcePacked
    simpa [afterSourceLeft, pushLeft_eq_reverse_append,
      List.append_assoc] using scanned
  have hLeftBoundary :
      workRunExact? machine 1
          (TargetEmitter.configAtLeftWord
            (TargetEmitter.rewindSourceState kind.token)
            baseLeft
            (source ++
              (sourceTargetBoundary :: targetAndTokenRight))) =
        some (TargetEmitter.configAtWord kind.doneState baseLeft
          (source ++
            (sourceTargetBoundary :: targetAndTokenRight))) := by
    apply workRunExact_one
    exact append_rewindSource_boundary_step kind controllerOutside
      (source ++
        (sourceTargetBoundary :: targetAndTokenRight))
  have h01 := workRunExact_compose
    source.length 1 _ _ _ hSource hSourceBoundary
  have h02 := workRunExact_compose
    (source.length + 1) target.length _ _ _ h01 hTarget
  have h03 := workRunExact_compose
    (source.length + 1 + target.length) 1 _ _ _ h02 hFirst
  have h04 := workRunExact_compose
    (source.length + 1 + target.length + 1) 1 _ _ _ h03 hSecond
  have h05 := workRunExact_compose
    (source.length + 1 + target.length + 1 + 1)
    (target.length + 1) _ _ _ h04 hRewindTarget
  have h06 := workRunExact_compose
    (source.length + 1 + target.length + 1 + 1 +
      (target.length + 1))
    1 _ _ _ h05 hTargetBoundary
  have h07 := workRunExact_compose
    (source.length + 1 + target.length + 1 + 1 +
      (target.length + 1) + 1)
    source.length _ _ _ h06 hRewindSource
  have complete := workRunExact_compose
    (source.length + 1 + target.length + 1 + 1 +
      (target.length + 1) + 1 + source.length)
    1 _ _ _ h07 hLeftBoundary
  have stepCount :
      source.length + 1 + target.length + 1 + 1 +
          (target.length + 1) + 1 + source.length + 1 =
        appendWorkSteps source target := by
    unfold appendWorkSteps
    omega
  rw [stepCount] at complete
  simpa [appendEntry, appendFinal,
    baseLeft, targetAndTokenRight,
    TargetEmitter.tokenSymbols, List.append_assoc] using complete

/-- The forward source scan passes the contextual cursor unchanged. -/
theorem seekSource_cursor_step (kind : AppendKind)
    (leftSide suffix : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtWord
          (TargetEmitter.seekSourceState kind.token)
          leftSide (cursorMarker :: suffix)) =
      some (TargetEmitter.configAtWord
        (TargetEmitter.seekSourceState kind.token)
        (cursorMarker :: leftSide) suffix) :=
  append_seekSource_packed_step kind leftSide suffix cursorMarker
    TargetEmitterCursorAppender.SourceSymbol.cursor

/-- The backward source scan passes the same cursor unchanged. -/
theorem rewindSource_cursor_step (kind : AppendKind)
    (leftTail rightSide : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindSourceState kind.token)
          (cursorMarker :: leftTail) rightSide) =
      some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindSourceState kind.token)
        leftTail (cursorMarker :: rightSide)) :=
  append_rewindSource_packed_step kind leftTail rightSide cursorMarker
    TargetEmitterCursorAppender.SourceSymbol.cursor

/-! ### Dynamic unary-counter controller -/

def readyState : Nat → Nat
  | 0 => startState
  | _ + 1 => unitDoneState

def blankReserve (count : Nat) : List WorkSymbol :=
  List.replicate (2 * (count + 1) + 1) WorkSymbol.blank

def naturalTokens (count : Nat) : List Token :=
  List.replicate count .unit ++ [.natEnd]

def phaseConfiguration (state : Nat)
    (counter source target reserve outsideLeft outsideRight :
      List WorkSymbol) : WorkConfiguration :=
  TargetEmitter.configAtWord state
    (sourceLeftBoundary :: (counter ++ outsideLeft))
    (source ++
      (sourceTargetBoundary ::
        (target ++ (reserve ++ outsideRight))))

def loopConfiguration (used remaining : Nat)
    (source target outsideLeft outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  phaseConfiguration (readyState used)
    (loopCounterWord used remaining) source target
    (blankReserve remaining) outsideLeft outsideRight

def unitLaunchConfiguration (used remaining : Nat)
    (source target outsideLeft outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  phaseConfiguration (TargetEmitter.seekSourceState .unit)
    (loopCounterWord (used + 1) remaining) source target
    (blankReserve (remaining + 1)) outsideLeft outsideRight

def endLaunchConfiguration (used : Nat)
    (source target outsideLeft outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  phaseConfiguration (TargetEmitter.seekSourceState .natEnd)
    (loopCounterWord used 0) source target
    (blankReserve 0) outsideLeft outsideRight

def cleanedConfiguration (total : Nat)
    (source target outsideLeft outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  phaseConfiguration acceptState
    (initialCounterWord total) source target
    [WorkSymbol.blank] outsideLeft outsideRight

def unitControllerSteps (used : Nat) : Nat :=
  2 * used + 4

def cleanupSteps (used : Nat) : Nat :=
  2 * used + 4

set_option maxRecDepth 100000 in
private theorem find_ready_packed (used : Nat) (symbol : WorkSymbol)
    (ordinary : SourceSymbol symbol) :
    findWorkRule rules (readyState used) symbol =
      some (literalRule (readyState used) symbol
        inspectBoundaryState symbol .left) := by
  cases used with
  | zero =>
      cases ordinary with
      | packed packed => cases packed <;> decide
      | cursor => decide
  | succ used =>
      change
        findWorkRule rules unitDoneState symbol =
          some (literalRule unitDoneState symbol
            inspectBoundaryState symbol .left)
      cases ordinary with
      | packed packed => cases packed <;> decide
      | cursor => decide

set_option maxRecDepth 100000 in
private theorem find_inspect_boundary :
    findWorkRule rules inspectBoundaryState sourceLeftBoundary =
      some (literalRule inspectBoundaryState sourceLeftBoundary
        inspectCounterState sourceLeftBoundary .left) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_inspect_mark :
    findWorkRule rules inspectCounterState counterMark =
      some (literalRule inspectCounterState counterMark
        inspectCounterState counterMark .left) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_inspect_unit :
    findWorkRule rules inspectCounterState unaryUnit =
      some (literalRule inspectCounterState unaryUnit
        returnUnitState counterMark .right) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_inspect_separator :
    findWorkRule rules inspectCounterState unarySeparator =
      some (literalRule inspectCounterState unarySeparator
        returnEndState unarySeparator .right) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_returnUnit_mark :
    findWorkRule rules returnUnitState counterMark =
      some (literalRule returnUnitState counterMark
        returnUnitState counterMark .right) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_returnUnit_boundary :
    findWorkRule rules returnUnitState sourceLeftBoundary =
      some (literalRule returnUnitState sourceLeftBoundary
        (TargetEmitter.seekSourceState .unit)
        sourceLeftBoundary .right) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_returnEnd_mark :
    findWorkRule rules returnEndState counterMark =
      some (literalRule returnEndState counterMark
        returnEndState counterMark .right) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_returnEnd_boundary :
    findWorkRule rules returnEndState sourceLeftBoundary =
      some (literalRule returnEndState sourceLeftBoundary
        (TargetEmitter.seekSourceState .natEnd)
        sourceLeftBoundary .right) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_natEndDone_packed (symbol : WorkSymbol)
    (ordinary : SourceSymbol symbol) :
    findWorkRule rules natEndDoneState symbol =
      some (literalRule natEndDoneState symbol
        cleanupBoundaryState symbol .left) := by
  cases ordinary with
  | packed packed => cases packed <;> decide
  | cursor => decide

set_option maxRecDepth 100000 in
private theorem find_cleanup_boundary :
    findWorkRule rules cleanupBoundaryState sourceLeftBoundary =
      some (literalRule cleanupBoundaryState sourceLeftBoundary
        cleanupCounterState sourceLeftBoundary .left) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_cleanup_mark :
    findWorkRule rules cleanupCounterState counterMark =
      some (literalRule cleanupCounterState counterMark
        cleanupCounterState unaryUnit .left) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_cleanup_separator :
    findWorkRule rules cleanupCounterState unarySeparator =
      some (literalRule cleanupCounterState unarySeparator
        cleanupReturnState unarySeparator .right) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_cleanupReturn_unit :
    findWorkRule rules cleanupReturnState unaryUnit =
      some (literalRule cleanupReturnState unaryUnit
        cleanupReturnState unaryUnit .right) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_cleanupReturn_boundary :
    findWorkRule rules cleanupReturnState sourceLeftBoundary =
      some (literalRule cleanupReturnState sourceLeftBoundary
        acceptState sourceLeftBoundary .right) := by
  decide

private theorem controller_not_halted (state : Nat)
    (stateCases :
      state = startState ∨ state = inspectBoundaryState ∨
      state = inspectCounterState ∨ state = returnUnitState ∨
      state = returnEndState ∨ state = unitDoneState ∨
      state = natEndDoneState ∨ state = cleanupBoundaryState ∨
      state = cleanupCounterState ∨ state = cleanupReturnState)
    (tape : WorkTape) :
    machine.isHalted { state := state, tape := tape } = false := by
  rcases stateCases with first | second | third | fourth | fifth |
      sixth | seventh | eighth | ninth | tenth
  all_goals subst state
  all_goals rfl

private theorem ready_step (used : Nat)
    (counter : List WorkSymbol) (sourceHead : WorkSymbol)
    (sourceTail : List WorkSymbol)
    (ordinary : SourceSymbol sourceHead) :
    workStep? machine
        (TargetEmitter.configAtWord (readyState used)
          (sourceLeftBoundary :: counter)
          (sourceHead :: sourceTail)) =
      some (TargetEmitter.configAtLeftWord inspectBoundaryState
        (sourceLeftBoundary :: counter)
        (sourceHead :: sourceTail)) := by
  let config := TargetEmitter.configAtWord (readyState used)
    (sourceLeftBoundary :: counter) (sourceHead :: sourceTail)
  have hHalted : machine.isHalted config = false := by
    cases used with
    | zero =>
        exact controller_not_halted _ (Or.inl rfl) config.tape
    | succ used =>
        exact controller_not_halted _
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
          config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule (readyState used) sourceHead
          inspectBoundaryState sourceHead .left) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_ready_packed used sourceHead ordinary)
    _ = some (TargetEmitter.configAtLeftWord inspectBoundaryState
        (sourceLeftBoundary :: counter)
        (sourceHead :: sourceTail)) := by
      rfl

private theorem inspect_boundary_step
    (counter sourceWord : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtLeftWord inspectBoundaryState
          (sourceLeftBoundary :: counter) sourceWord) =
      some (TargetEmitter.configAtLeftWord inspectCounterState
        counter (sourceLeftBoundary :: sourceWord)) := by
  let config := TargetEmitter.configAtLeftWord inspectBoundaryState
    (sourceLeftBoundary :: counter) sourceWord
  have hHalted : machine.isHalted config = false :=
    controller_not_halted _ (Or.inr (Or.inl rfl)) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule inspectBoundaryState sourceLeftBoundary
          inspectCounterState sourceLeftBoundary .left) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted find_inspect_boundary
    _ = some (TargetEmitter.configAtLeftWord inspectCounterState
        counter (sourceLeftBoundary :: sourceWord)) := by
      cases counter <;> rfl

private theorem inspect_mark_step
    (leftTail rightSide : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtLeftWord inspectCounterState
          (counterMark :: leftTail) rightSide) =
      some (TargetEmitter.configAtLeftWord inspectCounterState
        leftTail (counterMark :: rightSide)) := by
  let config := TargetEmitter.configAtLeftWord inspectCounterState
    (counterMark :: leftTail) rightSide
  have hHalted : machine.isHalted config = false :=
    controller_not_halted _
      (Or.inr (Or.inr (Or.inl rfl))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule inspectCounterState counterMark
          inspectCounterState counterMark .left) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted find_inspect_mark
    _ = some (TargetEmitter.configAtLeftWord inspectCounterState
        leftTail (counterMark :: rightSide)) := by
      cases leftTail <;> rfl

private theorem inspect_unit_step
    (leftTail rightSide : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtLeftWord inspectCounterState
          (unaryUnit :: leftTail) rightSide) =
      some (TargetEmitter.configAtWord returnUnitState
        (counterMark :: leftTail) rightSide) := by
  let config := TargetEmitter.configAtLeftWord inspectCounterState
    (unaryUnit :: leftTail) rightSide
  have hHalted : machine.isHalted config = false :=
    controller_not_halted _
      (Or.inr (Or.inr (Or.inl rfl))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule inspectCounterState unaryUnit
          returnUnitState counterMark .right) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted find_inspect_unit
    _ = some (TargetEmitter.configAtWord returnUnitState
        (counterMark :: leftTail) rightSide) := by
      cases rightSide <;> rfl

private theorem inspect_separator_step
    (leftTail rightSide : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtLeftWord inspectCounterState
          (unarySeparator :: leftTail) rightSide) =
      some (TargetEmitter.configAtWord returnEndState
        (unarySeparator :: leftTail) rightSide) := by
  let config := TargetEmitter.configAtLeftWord inspectCounterState
    (unarySeparator :: leftTail) rightSide
  have hHalted : machine.isHalted config = false :=
    controller_not_halted _
      (Or.inr (Or.inr (Or.inl rfl))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule inspectCounterState unarySeparator
          returnEndState unarySeparator .right) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted find_inspect_separator
    _ = some (TargetEmitter.configAtWord returnEndState
        (unarySeparator :: leftTail) rightSide) := by
      cases rightSide <;> rfl

private theorem returnUnit_mark_step
    (leftSide suffix : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtWord returnUnitState leftSide
          (counterMark :: suffix)) =
      some (TargetEmitter.configAtWord returnUnitState
        (counterMark :: leftSide) suffix) := by
  let config := TargetEmitter.configAtWord returnUnitState
    leftSide (counterMark :: suffix)
  have hHalted : machine.isHalted config = false :=
    controller_not_halted _
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule returnUnitState counterMark
          returnUnitState counterMark .right) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted find_returnUnit_mark
    _ = some (TargetEmitter.configAtWord returnUnitState
        (counterMark :: leftSide) suffix) := by
      cases suffix <;> rfl

private theorem returnUnit_boundary_step
    (leftSide sourceWord : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtWord returnUnitState leftSide
          (sourceLeftBoundary :: sourceWord)) =
      some (TargetEmitter.configAtWord
        (TargetEmitter.seekSourceState .unit)
        (sourceLeftBoundary :: leftSide) sourceWord) := by
  let config := TargetEmitter.configAtWord returnUnitState
    leftSide (sourceLeftBoundary :: sourceWord)
  have hHalted : machine.isHalted config = false :=
    controller_not_halted _
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule returnUnitState sourceLeftBoundary
          (TargetEmitter.seekSourceState .unit)
          sourceLeftBoundary .right) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        find_returnUnit_boundary
    _ = some (TargetEmitter.configAtWord
        (TargetEmitter.seekSourceState .unit)
        (sourceLeftBoundary :: leftSide) sourceWord) := by
      cases sourceWord <;> rfl

private theorem returnEnd_mark_step
    (leftSide suffix : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtWord returnEndState leftSide
          (counterMark :: suffix)) =
      some (TargetEmitter.configAtWord returnEndState
        (counterMark :: leftSide) suffix) := by
  let config := TargetEmitter.configAtWord returnEndState
    leftSide (counterMark :: suffix)
  have hHalted : machine.isHalted config = false :=
    controller_not_halted _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule returnEndState counterMark
          returnEndState counterMark .right) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted find_returnEnd_mark
    _ = some (TargetEmitter.configAtWord returnEndState
        (counterMark :: leftSide) suffix) := by
      cases suffix <;> rfl

private theorem returnEnd_boundary_step
    (leftSide sourceWord : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtWord returnEndState leftSide
          (sourceLeftBoundary :: sourceWord)) =
      some (TargetEmitter.configAtWord
        (TargetEmitter.seekSourceState .natEnd)
        (sourceLeftBoundary :: leftSide) sourceWord) := by
  let config := TargetEmitter.configAtWord returnEndState
    leftSide (sourceLeftBoundary :: sourceWord)
  have hHalted : machine.isHalted config = false :=
    controller_not_halted _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule returnEndState sourceLeftBoundary
          (TargetEmitter.seekSourceState .natEnd)
          sourceLeftBoundary .right) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        find_returnEnd_boundary
    _ = some (TargetEmitter.configAtWord
        (TargetEmitter.seekSourceState .natEnd)
        (sourceLeftBoundary :: leftSide) sourceWord) := by
      cases sourceWord <;> rfl

private theorem natEndDone_step
    (counter : List WorkSymbol) (sourceHead : WorkSymbol)
    (sourceTail : List WorkSymbol)
    (ordinary : SourceSymbol sourceHead) :
    workStep? machine
        (TargetEmitter.configAtWord natEndDoneState
          (sourceLeftBoundary :: counter)
          (sourceHead :: sourceTail)) =
      some (TargetEmitter.configAtLeftWord cleanupBoundaryState
        (sourceLeftBoundary :: counter)
        (sourceHead :: sourceTail)) := by
  let config := TargetEmitter.configAtWord natEndDoneState
    (sourceLeftBoundary :: counter) (sourceHead :: sourceTail)
  have hHalted : machine.isHalted config = false :=
    controller_not_halted _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl rfl))))))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule natEndDoneState sourceHead
          cleanupBoundaryState sourceHead .left) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_natEndDone_packed sourceHead ordinary)
    _ = some (TargetEmitter.configAtLeftWord cleanupBoundaryState
        (sourceLeftBoundary :: counter)
        (sourceHead :: sourceTail)) := by
      rfl

private theorem cleanup_boundary_step
    (counter sourceWord : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtLeftWord cleanupBoundaryState
          (sourceLeftBoundary :: counter) sourceWord) =
      some (TargetEmitter.configAtLeftWord cleanupCounterState
        counter (sourceLeftBoundary :: sourceWord)) := by
  let config := TargetEmitter.configAtLeftWord cleanupBoundaryState
    (sourceLeftBoundary :: counter) sourceWord
  have hHalted : machine.isHalted config = false :=
    controller_not_halted _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl rfl)))))))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule cleanupBoundaryState sourceLeftBoundary
          cleanupCounterState sourceLeftBoundary .left) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted find_cleanup_boundary
    _ = some (TargetEmitter.configAtLeftWord cleanupCounterState
        counter (sourceLeftBoundary :: sourceWord)) := by
      cases counter <;> rfl

private theorem cleanup_mark_step
    (leftTail rightSide : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtLeftWord cleanupCounterState
          (counterMark :: leftTail) rightSide) =
      some (TargetEmitter.configAtLeftWord cleanupCounterState
        leftTail (unaryUnit :: rightSide)) := by
  let config := TargetEmitter.configAtLeftWord cleanupCounterState
    (counterMark :: leftTail) rightSide
  have hHalted : machine.isHalted config = false :=
    controller_not_halted _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule cleanupCounterState counterMark
          cleanupCounterState unaryUnit .left) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted find_cleanup_mark
    _ = some (TargetEmitter.configAtLeftWord cleanupCounterState
        leftTail (unaryUnit :: rightSide)) := by
      cases leftTail <;> rfl

private theorem cleanup_separator_step
    (leftTail rightSide : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtLeftWord cleanupCounterState
          (unarySeparator :: leftTail) rightSide) =
      some (TargetEmitter.configAtWord cleanupReturnState
        (unarySeparator :: leftTail) rightSide) := by
  let config := TargetEmitter.configAtLeftWord cleanupCounterState
    (unarySeparator :: leftTail) rightSide
  have hHalted : machine.isHalted config = false :=
    controller_not_halted _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule cleanupCounterState unarySeparator
          cleanupReturnState unarySeparator .right) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted find_cleanup_separator
    _ = some (TargetEmitter.configAtWord cleanupReturnState
        (unarySeparator :: leftTail) rightSide) := by
      cases rightSide <;> rfl

private theorem cleanupReturn_unit_step
    (leftSide suffix : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtWord cleanupReturnState leftSide
          (unaryUnit :: suffix)) =
      some (TargetEmitter.configAtWord cleanupReturnState
        (unaryUnit :: leftSide) suffix) := by
  let config := TargetEmitter.configAtWord cleanupReturnState
    leftSide (unaryUnit :: suffix)
  have hHalted : machine.isHalted config = false :=
    controller_not_halted _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule cleanupReturnState unaryUnit
          cleanupReturnState unaryUnit .right) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted find_cleanupReturn_unit
    _ = some (TargetEmitter.configAtWord cleanupReturnState
        (unaryUnit :: leftSide) suffix) := by
      cases suffix <;> rfl

private theorem cleanupReturn_boundary_step
    (leftSide sourceWord : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtWord cleanupReturnState leftSide
          (sourceLeftBoundary :: sourceWord)) =
      some (TargetEmitter.configAtWord acceptState
        (sourceLeftBoundary :: leftSide) sourceWord) := by
  let config := TargetEmitter.configAtWord cleanupReturnState
    leftSide (sourceLeftBoundary :: sourceWord)
  have hHalted : machine.isHalted config = false :=
    controller_not_halted _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule cleanupReturnState sourceLeftBoundary
          acceptState sourceLeftBoundary .right) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        find_cleanupReturn_boundary
    _ = some (TargetEmitter.configAtWord acceptState
        (sourceLeftBoundary :: leftSide) sourceWord) := by
      cases sourceWord <;> rfl

theorem unit_launch_exact (used remaining : Nat)
    (sourceHead : WorkSymbol) (sourceTail target : List WorkSymbol)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourceHeadPacked : SourceSymbol sourceHead) :
    workRunExact? machine (unitControllerSteps used)
        (loopConfiguration used (remaining + 1)
          (sourceHead :: sourceTail) target outsideLeft outsideRight) =
      some (unitLaunchConfiguration used remaining
        (sourceHead :: sourceTail) target outsideLeft outsideRight) := by
  let sourceWord :=
    sourceHead :: sourceTail ++
      (sourceTargetBoundary ::
        (target ++
          (blankReserve (remaining + 1) ++ outsideRight)))
  let counterTail :=
    List.replicate remaining unaryUnit ++
      unarySeparator :: outsideLeft
  let marks := List.replicate used counterMark
  have hReady :
      workRunExact? machine 1
          (TargetEmitter.configAtWord (readyState used)
            (sourceLeftBoundary ::
              (marks ++ unaryUnit :: counterTail))
            sourceWord) =
        some (TargetEmitter.configAtLeftWord inspectBoundaryState
          (sourceLeftBoundary ::
            (marks ++ unaryUnit :: counterTail))
          sourceWord) := by
    apply workRunExact_one
    exact ready_step used (marks ++ unaryUnit :: counterTail)
      sourceHead
      (sourceTail ++
        (sourceTargetBoundary ::
          (target ++
            (blankReserve (remaining + 1) ++ outsideRight))))
      sourceHeadPacked
  have hBoundary :
      workRunExact? machine 1
          (TargetEmitter.configAtLeftWord inspectBoundaryState
            (sourceLeftBoundary ::
              (marks ++ unaryUnit :: counterTail))
            sourceWord) =
        some (TargetEmitter.configAtLeftWord inspectCounterState
          (marks ++ unaryUnit :: counterTail)
          (sourceLeftBoundary :: sourceWord)) := by
    apply workRunExact_one
    exact inspect_boundary_step
      (marks ++ unaryUnit :: counterTail) sourceWord
  have marksAllowed :
      ∀ symbol, symbol ∈ marks → symbol = counterMark := by
    intro symbol found
    have parts : used ≠ 0 ∧ symbol = counterMark := by
      simpa [marks] using found
    exact parts.2
  have hInspectMarks :
      workRunExact? machine used
          (TargetEmitter.configAtLeftWord inspectCounterState
            (marks ++ unaryUnit :: counterTail)
            (sourceLeftBoundary :: sourceWord)) =
        some (TargetEmitter.configAtLeftWord inspectCounterState
          (unaryUnit :: counterTail)
          (marks ++ sourceLeftBoundary :: sourceWord)) := by
    have scanned := scanLeftExact inspectCounterState
      (fun symbol => symbol = counterMark)
      (fun head left right equal => by
        subst head
        exact inspect_mark_step left right)
      marks (unaryUnit :: counterTail)
      (sourceLeftBoundary :: sourceWord) marksAllowed
    simpa [marks, pushLeft_eq_reverse_append] using scanned
  have hMarkUnit :
      workRunExact? machine 1
          (TargetEmitter.configAtLeftWord inspectCounterState
            (unaryUnit :: counterTail)
            (marks ++ sourceLeftBoundary :: sourceWord)) =
        some (TargetEmitter.configAtWord returnUnitState
          (counterMark :: counterTail)
          (marks ++ sourceLeftBoundary :: sourceWord)) := by
    apply workRunExact_one
    exact inspect_unit_step counterTail
      (marks ++ sourceLeftBoundary :: sourceWord)
  have hReturnMarks :
      workRunExact? machine used
          (TargetEmitter.configAtWord returnUnitState
            (counterMark :: counterTail)
            (marks ++ sourceLeftBoundary :: sourceWord)) =
        some (TargetEmitter.configAtWord returnUnitState
          (marks ++ counterMark :: counterTail)
          (sourceLeftBoundary :: sourceWord)) := by
    have scanned := scanRightExact returnUnitState
      (fun symbol => symbol = counterMark)
      (fun left head suffix equal => by
        subst head
        exact returnUnit_mark_step left suffix)
      marks (sourceLeftBoundary :: sourceWord)
      (counterMark :: counterTail) marksAllowed
    simpa [marks, pushLeft_eq_reverse_append,
      List.append_assoc] using scanned
  have hReturnBoundary :
      workRunExact? machine 1
          (TargetEmitter.configAtWord returnUnitState
            (marks ++ counterMark :: counterTail)
            (sourceLeftBoundary :: sourceWord)) =
        some (TargetEmitter.configAtWord
          (TargetEmitter.seekSourceState .unit)
          (sourceLeftBoundary :: marks ++ counterMark :: counterTail)
          sourceWord) := by
    apply workRunExact_one
    exact returnUnit_boundary_step
      (marks ++ counterMark :: counterTail) sourceWord
  have h01 := workRunExact_compose 1 1 _ _ _ hReady hBoundary
  have h02 := workRunExact_compose 2 used _ _ _ h01 hInspectMarks
  have h03 := workRunExact_compose (2 + used) 1 _ _ _ h02 hMarkUnit
  have h04 := workRunExact_compose (2 + used + 1) used
    _ _ _ h03 hReturnMarks
  have complete := workRunExact_compose
    (2 + used + 1 + used) 1 _ _ _ h04 hReturnBoundary
  have stepCount :
      2 + used + 1 + used + 1 = unitControllerSteps used := by
    unfold unitControllerSteps
    omega
  rw [stepCount] at complete
  have entryEq :
      loopConfiguration used (remaining + 1)
          (sourceHead :: sourceTail) target outsideLeft outsideRight =
        TargetEmitter.configAtWord (readyState used)
          (sourceLeftBoundary ::
            (marks ++ unaryUnit :: counterTail))
          sourceWord := by
    simp [loopConfiguration, phaseConfiguration, loopCounterWord,
      sourceWord, counterTail, marks, List.replicate_succ,
      List.append_assoc]
  have finalEq :
      unitLaunchConfiguration used remaining
          (sourceHead :: sourceTail) target outsideLeft outsideRight =
        TargetEmitter.configAtWord
          (TargetEmitter.seekSourceState .unit)
          (sourceLeftBoundary :: marks ++ counterMark :: counterTail)
          sourceWord := by
    simp [unitLaunchConfiguration, phaseConfiguration,
      loopCounterWord, sourceWord, counterTail, marks,
      replicate_succ_append, List.append_assoc]
  rw [entryEq, finalEq]
  exact complete

theorem end_launch_exact (used : Nat)
    (sourceHead : WorkSymbol) (sourceTail target : List WorkSymbol)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourceHeadPacked : SourceSymbol sourceHead) :
    workRunExact? machine (unitControllerSteps used)
        (loopConfiguration used 0
          (sourceHead :: sourceTail) target outsideLeft outsideRight) =
      some (endLaunchConfiguration used
        (sourceHead :: sourceTail) target outsideLeft outsideRight) := by
  let sourceWord :=
    sourceHead :: sourceTail ++
      (sourceTargetBoundary ::
        (target ++ (blankReserve 0 ++ outsideRight)))
  let counterTail := unarySeparator :: outsideLeft
  let marks := List.replicate used counterMark
  have hReady :
      workRunExact? machine 1
          (TargetEmitter.configAtWord (readyState used)
            (sourceLeftBoundary :: (marks ++ counterTail))
            sourceWord) =
        some (TargetEmitter.configAtLeftWord inspectBoundaryState
          (sourceLeftBoundary :: (marks ++ counterTail))
          sourceWord) := by
    apply workRunExact_one
    exact ready_step used (marks ++ counterTail) sourceHead
      (sourceTail ++
        (sourceTargetBoundary ::
          (target ++ (blankReserve 0 ++ outsideRight))))
      sourceHeadPacked
  have hBoundary :
      workRunExact? machine 1
          (TargetEmitter.configAtLeftWord inspectBoundaryState
            (sourceLeftBoundary :: (marks ++ counterTail))
            sourceWord) =
        some (TargetEmitter.configAtLeftWord inspectCounterState
          (marks ++ counterTail)
          (sourceLeftBoundary :: sourceWord)) := by
    apply workRunExact_one
    exact inspect_boundary_step (marks ++ counterTail) sourceWord
  have marksAllowed :
      ∀ symbol, symbol ∈ marks → symbol = counterMark := by
    intro symbol found
    have parts : used ≠ 0 ∧ symbol = counterMark := by
      simpa [marks] using found
    exact parts.2
  have hInspectMarks :
      workRunExact? machine used
          (TargetEmitter.configAtLeftWord inspectCounterState
            (marks ++ counterTail)
            (sourceLeftBoundary :: sourceWord)) =
        some (TargetEmitter.configAtLeftWord inspectCounterState
          counterTail
          (marks ++ sourceLeftBoundary :: sourceWord)) := by
    have scanned := scanLeftExact inspectCounterState
      (fun symbol => symbol = counterMark)
      (fun head left right equal => by
        subst head
        exact inspect_mark_step left right)
      marks counterTail (sourceLeftBoundary :: sourceWord) marksAllowed
    simpa [marks, pushLeft_eq_reverse_append] using scanned
  have hSeparator :
      workRunExact? machine 1
          (TargetEmitter.configAtLeftWord inspectCounterState
            counterTail
            (marks ++ sourceLeftBoundary :: sourceWord)) =
        some (TargetEmitter.configAtWord returnEndState
          counterTail
          (marks ++ sourceLeftBoundary :: sourceWord)) := by
    apply workRunExact_one
    exact inspect_separator_step outsideLeft
      (marks ++ sourceLeftBoundary :: sourceWord)
  have hReturnMarks :
      workRunExact? machine used
          (TargetEmitter.configAtWord returnEndState
            counterTail
            (marks ++ sourceLeftBoundary :: sourceWord)) =
        some (TargetEmitter.configAtWord returnEndState
          (marks ++ counterTail)
          (sourceLeftBoundary :: sourceWord)) := by
    have scanned := scanRightExact returnEndState
      (fun symbol => symbol = counterMark)
      (fun left head suffix equal => by
        subst head
        exact returnEnd_mark_step left suffix)
      marks (sourceLeftBoundary :: sourceWord)
      counterTail marksAllowed
    simpa [marks, pushLeft_eq_reverse_append,
      List.append_assoc] using scanned
  have hReturnBoundary :
      workRunExact? machine 1
          (TargetEmitter.configAtWord returnEndState
            (marks ++ counterTail)
            (sourceLeftBoundary :: sourceWord)) =
        some (TargetEmitter.configAtWord
          (TargetEmitter.seekSourceState .natEnd)
          (sourceLeftBoundary :: marks ++ counterTail)
          sourceWord) := by
    apply workRunExact_one
    exact returnEnd_boundary_step (marks ++ counterTail) sourceWord
  have h01 := workRunExact_compose 1 1 _ _ _ hReady hBoundary
  have h02 := workRunExact_compose 2 used _ _ _ h01 hInspectMarks
  have h03 := workRunExact_compose (2 + used) 1 _ _ _ h02 hSeparator
  have h04 := workRunExact_compose (2 + used + 1) used
    _ _ _ h03 hReturnMarks
  have complete := workRunExact_compose
    (2 + used + 1 + used) 1 _ _ _ h04 hReturnBoundary
  have stepCount :
      2 + used + 1 + used + 1 = unitControllerSteps used := by
    unfold unitControllerSteps
    omega
  rw [stepCount] at complete
  simpa [loopConfiguration, endLaunchConfiguration,
    phaseConfiguration, loopCounterWord, sourceWord, counterTail, marks,
    blankReserve, List.append_assoc] using complete

private theorem cleanup_marks_exact (used : Nat)
    (leftSuffix rightSide : List WorkSymbol) :
    workRunExact? machine used
        (TargetEmitter.configAtLeftWord cleanupCounterState
          (List.replicate used counterMark ++ leftSuffix) rightSide) =
      some (TargetEmitter.configAtLeftWord cleanupCounterState
        leftSuffix
        (List.replicate used unaryUnit ++ rightSide)) := by
  induction used generalizing rightSide with
  | zero => rfl
  | succ used ih =>
      change
        (match workStep? machine
          (TargetEmitter.configAtLeftWord cleanupCounterState
            (counterMark ::
              (List.replicate used counterMark ++ leftSuffix))
            rightSide) with
         | none => none
         | some next => workRunExact? machine used next) = _
      rw [cleanup_mark_step
        (List.replicate used counterMark ++ leftSuffix) rightSide]
      simpa [replicate_succ_append, List.replicate_succ,
        List.append_assoc] using
        ih (unaryUnit :: rightSide)

theorem cleanup_exact (used : Nat)
    (sourceHead : WorkSymbol) (sourceTail target : List WorkSymbol)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourceHeadPacked : SourceSymbol sourceHead) :
    workRunExact? machine (cleanupSteps used)
        (phaseConfiguration natEndDoneState
          (loopCounterWord used 0)
          (sourceHead :: sourceTail) target [WorkSymbol.blank]
          outsideLeft outsideRight) =
      some (cleanedConfiguration used
        (sourceHead :: sourceTail) target outsideLeft outsideRight) := by
  let sourceWord :=
    sourceHead :: sourceTail ++
      (sourceTargetBoundary ::
        (target ++ (WorkSymbol.blank :: outsideRight)))
  let counterTail := unarySeparator :: outsideLeft
  let marks := List.replicate used counterMark
  let units := List.replicate used unaryUnit
  have hDone :
      workRunExact? machine 1
          (TargetEmitter.configAtWord natEndDoneState
            (sourceLeftBoundary :: marks ++ counterTail)
            sourceWord) =
        some (TargetEmitter.configAtLeftWord cleanupBoundaryState
          (sourceLeftBoundary :: marks ++ counterTail)
          sourceWord) := by
    apply workRunExact_one
    exact natEndDone_step (marks ++ counterTail) sourceHead
      (sourceTail ++
        (sourceTargetBoundary ::
          (target ++ (WorkSymbol.blank :: outsideRight))))
      sourceHeadPacked
  have hBoundary :
      workRunExact? machine 1
          (TargetEmitter.configAtLeftWord cleanupBoundaryState
            (sourceLeftBoundary :: marks ++ counterTail)
            sourceWord) =
        some (TargetEmitter.configAtLeftWord cleanupCounterState
          (marks ++ counterTail)
          (sourceLeftBoundary :: sourceWord)) := by
    apply workRunExact_one
    exact cleanup_boundary_step (marks ++ counterTail) sourceWord
  have hMarks :
      workRunExact? machine used
          (TargetEmitter.configAtLeftWord cleanupCounterState
            (marks ++ counterTail)
            (sourceLeftBoundary :: sourceWord)) =
        some (TargetEmitter.configAtLeftWord cleanupCounterState
          counterTail
          (units ++ sourceLeftBoundary :: sourceWord)) := by
    simpa [marks, units] using cleanup_marks_exact used counterTail
      (sourceLeftBoundary :: sourceWord)
  have hSeparator :
      workRunExact? machine 1
          (TargetEmitter.configAtLeftWord cleanupCounterState
            counterTail
            (units ++ sourceLeftBoundary :: sourceWord)) =
        some (TargetEmitter.configAtWord cleanupReturnState
          counterTail
          (units ++ sourceLeftBoundary :: sourceWord)) := by
    apply workRunExact_one
    exact cleanup_separator_step outsideLeft
      (units ++ sourceLeftBoundary :: sourceWord)
  have unitsAllowed :
      ∀ symbol, symbol ∈ units → symbol = unaryUnit := by
    intro symbol found
    have parts : used ≠ 0 ∧ symbol = unaryUnit := by
      simpa [units] using found
    exact parts.2
  have hUnits :
      workRunExact? machine used
          (TargetEmitter.configAtWord cleanupReturnState
            counterTail
            (units ++ sourceLeftBoundary :: sourceWord)) =
        some (TargetEmitter.configAtWord cleanupReturnState
          (units ++ counterTail)
          (sourceLeftBoundary :: sourceWord)) := by
    have scanned := scanRightExact cleanupReturnState
      (fun symbol => symbol = unaryUnit)
      (fun left head suffix equal => by
        subst head
        exact cleanupReturn_unit_step left suffix)
      units (sourceLeftBoundary :: sourceWord)
      counterTail unitsAllowed
    simpa [units, pushLeft_eq_reverse_append,
      List.append_assoc] using scanned
  have hFinalBoundary :
      workRunExact? machine 1
          (TargetEmitter.configAtWord cleanupReturnState
            (units ++ counterTail)
            (sourceLeftBoundary :: sourceWord)) =
        some (TargetEmitter.configAtWord acceptState
          (sourceLeftBoundary :: units ++ counterTail)
          sourceWord) := by
    apply workRunExact_one
    exact cleanupReturn_boundary_step
      (units ++ counterTail) sourceWord
  have h01 := workRunExact_compose 1 1 _ _ _ hDone hBoundary
  have h02 := workRunExact_compose 2 used _ _ _ h01 hMarks
  have h03 := workRunExact_compose (2 + used) 1 _ _ _ h02 hSeparator
  have h04 := workRunExact_compose (2 + used + 1) used
    _ _ _ h03 hUnits
  have complete := workRunExact_compose
    (2 + used + 1 + used) 1 _ _ _ h04 hFinalBoundary
  have stepCount :
      2 + used + 1 + used + 1 = cleanupSteps used := by
    unfold cleanupSteps
    omega
  rw [stepCount] at complete
  simpa [phaseConfiguration, cleanedConfiguration,
    loopCounterWord, initialCounterWord, sourceWord,
    counterTail, marks, units, List.append_assoc] using complete

private theorem replicateBlank_append (first second : Nat) :
    List.replicate first WorkSymbol.blank ++
        List.replicate second WorkSymbol.blank =
      List.replicate (first + second) WorkSymbol.blank := by
  induction first with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ first ih =>
      rw [Nat.succ_add]
      exact congrArg (List.cons WorkSymbol.blank) ih

private theorem blankReserve_succ_split (remaining : Nat) :
    blankReserve (remaining + 1) =
      [WorkSymbol.blank, WorkSymbol.blank, WorkSymbol.blank] ++
        List.replicate (2 * (remaining + 1)) WorkSymbol.blank := by
  unfold blankReserve
  change
    List.replicate (2 * ((remaining + 1) + 1) + 1)
        WorkSymbol.blank =
      List.replicate 3 WorkSymbol.blank ++
        List.replicate (2 * (remaining + 1)) WorkSymbol.blank
  rw [replicateBlank_append]
  apply congrArg (fun count =>
    List.replicate count WorkSymbol.blank)
  omega

private theorem blankReserve_after_append (remaining : Nat) :
    WorkSymbol.blank ::
        List.replicate (2 * (remaining + 1)) WorkSymbol.blank =
      blankReserve remaining := by
  unfold blankReserve
  change
    List.replicate 1 WorkSymbol.blank ++
        List.replicate (2 * (remaining + 1)) WorkSymbol.blank =
      List.replicate (2 * (remaining + 1) + 1) WorkSymbol.blank
  rw [replicateBlank_append]
  apply congrArg (fun count =>
    List.replicate count WorkSymbol.blank)
  omega

def unitIterationSteps (used : Nat)
    (source target : List WorkSymbol) : Nat :=
  unitControllerSteps used + appendWorkSteps source target

theorem unit_iteration_exact (used remaining : Nat)
    (sourceHead : WorkSymbol) (sourceTail target : List WorkSymbol)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol, symbol ∈ sourceHead :: sourceTail →
        SourceSymbol symbol)
    (targetPacked :
      ∀ symbol, symbol ∈ target →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? machine
        (unitIterationSteps used (sourceHead :: sourceTail) target)
        (loopConfiguration used (remaining + 1)
          (sourceHead :: sourceTail) target outsideLeft outsideRight) =
      some (loopConfiguration (used + 1) remaining
        (sourceHead :: sourceTail)
        (target ++ TargetEmitter.tokenSymbols .unit)
        outsideLeft outsideRight) := by
  let controllerOutside :=
    loopCounterWord (used + 1) remaining ++ outsideLeft
  let appendOutside :=
    List.replicate (2 * (remaining + 1)) WorkSymbol.blank ++ outsideRight
  have hLaunch := unit_launch_exact used remaining
    sourceHead sourceTail target outsideLeft outsideRight
    (sourcePacked sourceHead (List.Mem.head sourceTail))
  have hAppend := append_exact .unit
    (sourceHead :: sourceTail) target controllerOutside appendOutside
    sourcePacked targetPacked
  have hEntry :
      unitLaunchConfiguration used remaining
          (sourceHead :: sourceTail) target outsideLeft outsideRight =
        appendEntry .unit (sourceHead :: sourceTail) target
          controllerOutside appendOutside := by
    unfold unitLaunchConfiguration phaseConfiguration appendEntry
    rw [blankReserve_succ_split]
    simp [AppendKind.token, controllerOutside, appendOutside]
  have hFinal :
      appendFinal .unit (sourceHead :: sourceTail) target
          controllerOutside appendOutside =
        loopConfiguration (used + 1) remaining
          (sourceHead :: sourceTail)
          (target ++ TargetEmitter.tokenSymbols .unit)
          outsideLeft outsideRight := by
    unfold appendFinal loopConfiguration phaseConfiguration
    rw [← blankReserve_after_append remaining]
    simp [AppendKind.token, AppendKind.doneState, readyState,
      controllerOutside, appendOutside, loopCounterWord,
      TargetEmitter.tokenSymbols, List.append_assoc]
  rw [← hEntry] at hAppend
  rw [hFinal] at hAppend
  exact workRunExact_compose _ _ _ _ _ hLaunch hAppend

def endIterationSteps (used : Nat)
    (source target : List WorkSymbol) : Nat :=
  unitControllerSteps used + appendWorkSteps source target +
    cleanupSteps used

theorem end_iteration_exact (used : Nat)
    (sourceHead : WorkSymbol) (sourceTail target : List WorkSymbol)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol, symbol ∈ sourceHead :: sourceTail →
        SourceSymbol symbol)
    (targetPacked :
      ∀ symbol, symbol ∈ target →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? machine
        (endIterationSteps used (sourceHead :: sourceTail) target)
        (loopConfiguration used 0
          (sourceHead :: sourceTail) target outsideLeft outsideRight) =
      some (cleanedConfiguration used
        (sourceHead :: sourceTail)
        (target ++ TargetEmitter.tokenSymbols .natEnd)
        outsideLeft outsideRight) := by
  let controllerOutside :=
    loopCounterWord used 0 ++ outsideLeft
  have hLaunch := end_launch_exact used sourceHead sourceTail target
    outsideLeft outsideRight
    (sourcePacked sourceHead (List.Mem.head sourceTail))
  have hAppend := append_exact .natEnd
    (sourceHead :: sourceTail) target controllerOutside outsideRight
    sourcePacked targetPacked
  have hEntry :
      endLaunchConfiguration used
          (sourceHead :: sourceTail) target outsideLeft outsideRight =
        appendEntry .natEnd (sourceHead :: sourceTail) target
          controllerOutside outsideRight := by
    simp [endLaunchConfiguration, phaseConfiguration, appendEntry,
      AppendKind.token, controllerOutside, blankReserve, loopCounterWord,
      List.append_assoc]
  have hAfterAppend :
      appendFinal .natEnd (sourceHead :: sourceTail) target
          controllerOutside outsideRight =
        phaseConfiguration natEndDoneState
          (loopCounterWord used 0)
          (sourceHead :: sourceTail)
          (target ++ TargetEmitter.tokenSymbols .natEnd)
          [WorkSymbol.blank] outsideLeft outsideRight := by
    simp [appendFinal, phaseConfiguration, controllerOutside,
      AppendKind.token, AppendKind.doneState,
      loopCounterWord, TargetEmitter.tokenSymbols,
      List.append_assoc]
  have hCleanup := cleanup_exact used sourceHead sourceTail
    (target ++ TargetEmitter.tokenSymbols .natEnd)
    outsideLeft outsideRight
    (sourcePacked sourceHead (List.Mem.head sourceTail))
  rw [← hEntry] at hAppend
  rw [hAfterAppend] at hAppend
  have hFirst := workRunExact_compose _ _ _ _ _ hLaunch hAppend
  exact workRunExact_compose _ _ _ _ _ hFirst hCleanup

private theorem packedTokenCells_append (first second : List Token) :
    SourceParser.packedTokenCells (first ++ second) =
      SourceParser.packedTokenCells first ++
        SourceParser.packedTokenCells second := by
  induction first with
  | nil => rfl
  | cons token rest ih =>
      simp [SourceParser.packedTokenCells, ih, List.append_assoc]

private theorem naturalTokenCells_zero :
    SourceParser.packedTokenCells (naturalTokens 0) =
      TargetEmitter.tokenSymbols .natEnd := by
  rw [TargetEmitter.tokenSymbols_eq_parser_cells]
  rfl

private theorem naturalTokenCells_succ (remaining : Nat) :
    SourceParser.packedTokenCells (naturalTokens (remaining + 1)) =
      TargetEmitter.tokenSymbols .unit ++
        SourceParser.packedTokenCells (naturalTokens remaining) := by
  rw [TargetEmitter.tokenSymbols_eq_parser_cells]
  simp [naturalTokens, List.replicate_succ,
    SourceParser.packedTokenCells]

def triangular : Nat → Nat
  | 0 => 0
  | count + 1 => triangular count + count

def loopWorkSteps (source target : List WorkSymbol)
    (used remaining : Nat) : Nat :=
  remaining *
      (2 * source.length + 2 * target.length + 2 * used + 10) +
    6 * triangular remaining +
    (2 * source.length + 2 * target.length +
      4 * used + 8 * remaining + 14)

theorem loopWorkSteps_zero (source target : List WorkSymbol)
    (used : Nat) :
    loopWorkSteps source target used 0 =
      endIterationSteps used source target := by
  simp [loopWorkSteps, endIterationSteps, unitControllerSteps,
    cleanupSteps, appendWorkSteps, triangular]
  omega

theorem loopWorkSteps_succ (source target : List WorkSymbol)
    (used remaining : Nat) :
    loopWorkSteps source target used (remaining + 1) =
      unitIterationSteps used source target +
        loopWorkSteps source
          (target ++ TargetEmitter.tokenSymbols .unit)
          (used + 1) remaining := by
  simp [loopWorkSteps, unitIterationSteps, unitControllerSteps,
    appendWorkSteps, triangular, TargetEmitter.tokenSymbols]
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
  omega

/-- Exact all-count execution from a partially consumed unary counter.  This
strengthened induction statement makes the tape-driven loop explicit: `used`
units are marked, `remaining` units are live, and only the latter schedule
future `.unit` emissions. -/
theorem loop_exact (used remaining : Nat)
    (sourceHead : WorkSymbol) (sourceTail target : List WorkSymbol)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol, symbol ∈ sourceHead :: sourceTail →
        SourceSymbol symbol)
    (targetPacked :
      ∀ symbol, symbol ∈ target →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? machine
        (loopWorkSteps (sourceHead :: sourceTail) target used remaining)
        (loopConfiguration used remaining
          (sourceHead :: sourceTail) target outsideLeft outsideRight) =
      some (cleanedConfiguration (used + remaining)
        (sourceHead :: sourceTail)
        (target ++
          SourceParser.packedTokenCells (naturalTokens remaining))
        outsideLeft outsideRight) := by
  induction remaining generalizing used target with
  | zero =>
      have exactEnd := end_iteration_exact used sourceHead sourceTail
        target outsideLeft outsideRight sourcePacked targetPacked
      rw [loopWorkSteps_zero]
      simpa [naturalTokenCells_zero] using exactEnd
  | succ remaining ih =>
      let nextTarget :=
        target ++ TargetEmitter.tokenSymbols .unit
      have nextTargetPacked :
          ∀ symbol, symbol ∈ nextTarget →
            TargetEmitter.PackedSymbol symbol := by
        intro symbol found
        rw [List.mem_append] at found
        cases found with
        | inl inTarget =>
            exact targetPacked symbol inTarget
        | inr inUnit =>
            rw [TargetEmitter.tokenSymbols_eq_parser_cells] at inUnit
            exact TargetEmitter.packedTokenCells_packed [.unit]
              symbol inUnit
      have first := unit_iteration_exact used remaining
        sourceHead sourceTail target outsideLeft outsideRight
        sourcePacked targetPacked
      have rest := ih (used + 1) nextTarget nextTargetPacked
      have complete := workRunExact_compose
        (unitIterationSteps used (sourceHead :: sourceTail) target)
        (loopWorkSteps (sourceHead :: sourceTail)
          nextTarget (used + 1) remaining)
        _ _ _ first rest
      rw [← loopWorkSteps_succ] at complete
      have countEq :
          used + (remaining + 1) = used + 1 + remaining := by
        omega
      have targetEq :
          target ++
              SourceParser.packedTokenCells
                (naturalTokens (remaining + 1)) =
            nextTarget ++
              SourceParser.packedTokenCells
                (naturalTokens remaining) := by
        rw [naturalTokenCells_succ]
        simp [nextTarget, List.append_assoc]
      rw [countEq, targetEq]
      exact complete


/-! ### Exact marked-source workspace endpoints -/

/-- The unique contextual cursor remains between the same two packed source
words for the entire loop. -/
def markedSource (before after : List WorkSymbol) : List WorkSymbol :=
  before ++ cursorMarker :: after

theorem markedSource_unique_context
    (before after : List WorkSymbol)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (afterPacked :
      ∀ symbol, symbol ∈ after →
        TargetEmitter.PackedSymbol symbol) :
    cursorMarker ∉ before ∧ cursorMarker ∉ after :=
  TargetEmitterCursorAppender.sourceWithCursor_unique_context
    before after beforePacked afterPacked

/-- The retained source contains exactly one contextual cursor. -/
theorem markedSource_cursor_count
    (before after : List WorkSymbol)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (afterPacked :
      ∀ symbol, symbol ∈ after →
        TargetEmitter.PackedSymbol symbol) :
    (markedSource before after).count cursorMarker = 1 := by
  have context :=
    markedSource_unique_context before after beforePacked afterPacked
  have beforeCount : before.count cursorMarker = 0 :=
    List.count_eq_zero.mpr context.1
  have afterCount : after.count cursorMarker = 0 :=
    List.count_eq_zero.mpr context.2
  rw [markedSource, List.count_append, beforeCount, List.count_cons,
    afterCount]
  decide

theorem markedSource_allowed
    (before after : List WorkSymbol)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (afterPacked :
      ∀ symbol, symbol ∈ after →
        TargetEmitter.PackedSymbol symbol) :
    ∀ symbol, symbol ∈ markedSource before after →
      SourceSymbol symbol := by
  intro symbol found
  rw [markedSource, List.mem_append] at found
  rcases found with inBefore | inRest
  · exact TargetEmitterCursorAppender.SourceSymbol.packed
      (beforePacked symbol inBefore)
  · cases inRest with
    | head => exact TargetEmitterCursorAppender.SourceSymbol.cursor
    | tail _ inAfter =>
        exact TargetEmitterCursorAppender.SourceSymbol.packed
          (afterPacked symbol inAfter)

theorem naturalTokens_eq_encodeNatTokens (count : Nat) :
    naturalTokens count = encodeNatTokens count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change
        List.replicate (count + 1) .unit ++ [.natEnd] =
          .unit :: encodeNatTokens count
      rw [List.replicate_succ]
      change
        .unit :: (List.replicate count .unit ++ [.natEnd]) =
          .unit :: encodeNatTokens count
      exact congrArg (List.cons Token.unit) ih

def entryConfiguration (before after : List WorkSymbol)
    (count : Nat) (targetPrefix : List Token)
    (outsideLeft outsideRight : List WorkSymbol) : WorkConfiguration :=
  loopConfiguration 0 count (markedSource before after)
    (SourceParser.packedTokenCells targetPrefix)
    outsideLeft outsideRight

def entryTape (before after : List WorkSymbol)
    (count : Nat) (targetPrefix : List Token)
    (outsideLeft outsideRight : List WorkSymbol) : WorkTape :=
  (entryConfiguration before after count targetPrefix
    outsideLeft outsideRight).tape

def finalConfiguration (before after : List WorkSymbol)
    (count : Nat) (targetPrefix : List Token)
    (outsideLeft outsideRight : List WorkSymbol) : WorkConfiguration :=
  cleanedConfiguration count (markedSource before after)
    (SourceParser.packedTokenCells
      (targetPrefix ++ encodeNatTokens count))
    outsideLeft outsideRight

def finalTape (before after : List WorkSymbol)
    (count : Nat) (targetPrefix : List Token)
    (outsideLeft outsideRight : List WorkSymbol) : WorkTape :=
  (finalConfiguration before after count targetPrefix
    outsideLeft outsideRight).tape

theorem finalConfiguration_halted (before after : List WorkSymbol)
    (count : Nat) (targetPrefix : List Token)
    (outsideLeft outsideRight : List WorkSymbol) :
    machine.isHalted
      (finalConfiguration before after count targetPrefix
        outsideLeft outsideRight) = true := by
  cases before <;>
    rfl

def workSteps (before after : List WorkSymbol)
    (targetPrefix : List Token) (count : Nat) : Nat :=
  loopWorkSteps (markedSource before after)
    (SourceParser.packedTokenCells targetPrefix) 0 count

/-- Exact all-count emission of the canonical natural-token encoding while
preserving the marked source split byte-for-byte. -/
theorem exact (before after : List WorkSymbol) (count : Nat)
    (targetPrefix : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (afterPacked :
      ∀ symbol, symbol ∈ after →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? machine
        (workSteps before after targetPrefix count)
        (entryConfiguration before after count targetPrefix
          outsideLeft outsideRight) =
      some (finalConfiguration before after count targetPrefix
        outsideLeft outsideRight) := by
  let source := markedSource before after
  let target := SourceParser.packedTokenCells targetPrefix
  have sourceAllowed :
      ∀ symbol, symbol ∈ source → SourceSymbol symbol := by
    simpa [source] using
      markedSource_allowed before after beforePacked afterPacked
  have targetPacked :
      ∀ symbol, symbol ∈ target →
        TargetEmitter.PackedSymbol symbol :=
    TargetEmitter.packedTokenCells_packed targetPrefix
  cases sourceEq : source with
  | nil =>
      have impossible : source ≠ [] := by
        simp [source, markedSource]
      exact (impossible sourceEq).elim
  | cons sourceHead sourceTail =>
      have complete := loop_exact 0 count sourceHead sourceTail target
        outsideLeft outsideRight
        (by simpa [sourceEq] using sourceAllowed) targetPacked
      have finalTarget :
          target ++
              SourceParser.packedTokenCells (naturalTokens count) =
            SourceParser.packedTokenCells
              (targetPrefix ++ encodeNatTokens count) := by
        rw [packedTokenCells_append, naturalTokens_eq_encodeNatTokens]
      simpa [workSteps, entryConfiguration, finalConfiguration,
        source, target, sourceEq, finalTarget] using complete

/-- The accepting endpoint still begins with exactly
`before ++ cursorMarker :: after`; only the target suffix was extended. -/
theorem finalConfiguration_source_preserved
    (before after : List WorkSymbol) (count : Nat)
    (targetPrefix : List Token)
    (outsideLeft outsideRight : List WorkSymbol) :
    let final :=
      finalConfiguration before after count targetPrefix
        outsideLeft outsideRight
    final.tape.head :: final.tape.right =
      markedSource before after ++
        (sourceTargetBoundary ::
          (SourceParser.packedTokenCells
            (targetPrefix ++ encodeNatTokens count) ++
              (WorkSymbol.blank :: outsideRight))) := by
  cases before <;>
    simp [finalConfiguration, cleanedConfiguration, phaseConfiguration,
      markedSource, TargetEmitter.configAtWord,
      List.append_assoc]

theorem finalConfiguration_left_workspace
    (before after : List WorkSymbol) (count : Nat)
    (targetPrefix : List Token)
    (outsideLeft outsideRight : List WorkSymbol) :
    (finalConfiguration before after count targetPrefix
      outsideLeft outsideRight).tape.left =
        sourceLeftBoundary ::
          (initialCounterWord count ++ outsideLeft) := by
  cases before <;>
    simp [finalConfiguration, cleanedConfiguration, phaseConfiguration,
      markedSource, TargetEmitter.configAtWord, List.append_assoc]

theorem workSteps_evaluated (before after : List WorkSymbol)
    (targetPrefix : List Token) (count : Nat) :
    workSteps before after targetPrefix count =
      count *
          (2 * before.length + 2 * after.length +
            4 * targetPrefix.length + 12) +
        6 * triangular count +
        (2 * before.length + 2 * after.length +
          4 * targetPrefix.length + 8 * count + 16) := by
  have sourceLength :
      (markedSource before after).length =
        before.length + 1 + after.length := by
    simp [markedSource]
    omega
  have targetLength :
      (SourceParser.packedTokenCells targetPrefix).length =
        2 * targetPrefix.length :=
    SourceParser.packedTokenCells_length targetPrefix
  unfold workSteps loopWorkSteps
  rw [sourceLength, targetLength]
  have mainFactor :
      2 * (before.length + 1 + after.length) +
            2 * (2 * targetPrefix.length) + 2 * 0 + 10 =
        2 * before.length + 2 * after.length +
          4 * targetPrefix.length + 12 := by
    omega
  have finalFactor :
      2 * (before.length + 1 + after.length) +
            2 * (2 * targetPrefix.length) +
            4 * 0 + 8 * count + 14 =
        2 * before.length + 2 * after.length +
          4 * targetPrefix.length + 8 * count + 16 := by
    omega
  rw [mainFactor, finalFactor]

theorem triangular_le_square (count : Nat) :
    triangular count ≤ count * count := by
  induction count with
  | zero => exact Nat.le_refl _
  | succ count ih =>
      rw [triangular]
      have first :
          triangular count + count ≤ count * count + count :=
        Nat.add_le_add_right ih count
      have expansion :
          (count + 1) * (count + 1) =
            count * count + count + count + 1 := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
        omega
      rw [expansion]
      omega

def polynomialWorkBound (before after : List WorkSymbol)
    (targetPrefix : List Token) (count : Nat) : Nat :=
  count *
      (2 * before.length + 2 * after.length +
        4 * targetPrefix.length + 12) +
    6 * (count * count) +
    (2 * before.length + 2 * after.length +
      4 * targetPrefix.length + 8 * count + 16)

theorem workSteps_le_polynomialWorkBound (before after : List WorkSymbol)
    (targetPrefix : List Token) (count : Nat) :
    workSteps before after targetPrefix count ≤
      polynomialWorkBound before after targetPrefix count := by
  rw [workSteps_evaluated]
  unfold polynomialWorkBound
  have scaled :=
    Nat.mul_le_mul_left 6 (triangular_le_square count)
  omega

/-! ### Fail-closed malformed-workspace behavior -/

set_option maxRecDepth 100000 in
private theorem find_seekTarget_cursor (kind : AppendKind) :
    findWorkRule rules (TargetEmitter.seekTargetState kind.token)
        cursorMarker =
      some (literalRule (TargetEmitter.seekTargetState kind.token)
        cursorMarker deadState cursorMarker .stay) := by
  cases kind <;> decide

/-- The contextual cursor is valid only in the retained-source region.  If a
malformed target places it under a target scan, the machine enters the
ruleless, non-halting dead state immediately. -/
theorem target_cursor_enters_dead (kind : AppendKind)
    (leftSide suffix : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState kind.token)
          leftSide (cursorMarker :: suffix)) =
      some (TargetEmitter.configAtWord deadState
        leftSide (cursorMarker :: suffix)) := by
  let config := TargetEmitter.configAtWord
    (TargetEmitter.seekTargetState kind.token)
    leftSide (cursorMarker :: suffix)
  have hHalted : machine.isHalted config = false :=
    appendState_not_halted kind _
      (Or.inr (Or.inl rfl)) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule (TargetEmitter.seekTargetState kind.token)
          cursorMarker deadState cursorMarker .stay) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_seekTarget_cursor kind)
    _ = some (TargetEmitter.configAtWord deadState
        leftSide (cursorMarker :: suffix)) := by
      rfl

set_option maxRecDepth 100000 in
private theorem find_inspect_blank :
    findWorkRule rules inspectCounterState WorkSymbol.blank =
      some (literalRule inspectCounterState WorkSymbol.blank
        deadState WorkSymbol.blank .stay) := by
  decide

theorem malformed_counter_enters_dead
    (leftTail rightSide : List WorkSymbol) :
    workStep? machine
        (TargetEmitter.configAtLeftWord inspectCounterState
          (WorkSymbol.blank :: leftTail) rightSide) =
      some (TargetEmitter.configAtLeftWord deadState
        (WorkSymbol.blank :: leftTail) rightSide) := by
  let config := TargetEmitter.configAtLeftWord inspectCounterState
    (WorkSymbol.blank :: leftTail) rightSide
  have hHalted : machine.isHalted config = false :=
    controller_not_halted _
      (Or.inr (Or.inr (Or.inl rfl))) config.tape
  calc
    workStep? machine config =
      some (applyWorkRule
        (literalRule inspectCounterState WorkSymbol.blank
          deadState WorkSymbol.blank .stay) config) :=
      workStep?_eq_apply_of_find _ _ _ hHalted find_inspect_blank
    _ = some (TargetEmitter.configAtLeftWord deadState
        (WorkSymbol.blank :: leftTail) rightSide) := by
      rfl

theorem dead_configuration_not_halted (tape : WorkTape) :
    machine.isHalted { state := deadState, tape := tape } = false := by
  rfl

theorem dead_configuration_stuck (tape : WorkTape) :
    workStep? machine { state := deadState, tape := tape } = none := by
  have hHalted :
      machine.isHalted { state := deadState, tape := tape } = false := by
    rfl
  unfold workStep?
  rw [show machine.isHalted
      { state := deadState, tape := tape } = false from hHalted]
  rw [show machine.rules = rules from rfl]
  rw [no_rule_at_dead]
  rfl

end PNP.Concrete.LockedNAND.TargetEmitterCursorNatLoop
