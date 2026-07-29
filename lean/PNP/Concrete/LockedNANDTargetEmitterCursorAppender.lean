/-
Copyright (c) 2026 PNP Labs.

Literal cursor-preserving token append primitive for the locked-NAND target
emitter.

The retained packed source may contain one contextual cursor marker in place
of one packed source cell.  This fixed table differs from the base
`TargetEmitter` token appender only in its two source scans: `oneBlank` is
passed through unchanged there, while it remains invalid in the target scan
and token-write states.  The source-left and source/target boundary symbols
remain distinct from the cursor.

Each of the twelve literal token requests has its own halting continuation
endpoint.  No transition relies on adding a rule at the base appender's shared
accept state.  The executable rules inspect only literal work symbols and
literal token control blocks; they do not call a decoder, raw builder, or
source-to-target function.
-/

import PNP.Concrete.LockedNANDTargetEmitterMachine

namespace PNP.Concrete.LockedNAND.TargetEmitterCursorAppender

open PNP.Concrete

/-! ### Context-local cursor and token-specific endpoints -/

def cursorMarker : WorkSymbol := WorkSymbol.oneBlank

def sourceLeftBoundary : WorkSymbol :=
  TargetEmitter.sourceLeftBoundary

def sourceTargetBoundary : WorkSymbol :=
  TargetEmitter.sourceTargetBoundary

theorem cursor_ne_sourceLeftBoundary :
    cursorMarker ≠ sourceLeftBoundary := by
  decide

theorem cursor_ne_sourceTargetBoundary :
    cursorMarker ≠ sourceTargetBoundary := by
  decide

theorem sourceLeftBoundary_ne_sourceTargetBoundary :
    sourceLeftBoundary ≠ sourceTargetBoundary := by
  decide

theorem cursor_not_packed :
    ¬ TargetEmitter.PackedSymbol cursorMarker := by
  intro packed
  cases packed

/-- The future controller may bridge this endpoint to a phase-specific
continuation.  In this bounded standalone machine it is the halting done
state. -/
def continuationState (token : Token) : Nat :=
  63 + TargetEmitter.tokenCode token

def doneState (token : Token) : Nat :=
  continuationState token

def rejectState : Nat := TargetEmitter.rejectState
def deadState : Nat := TargetEmitter.deadState

theorem doneState_injective :
    Function.Injective doneState := by
  intro left right equality
  cases left <;> cases right <;>
    simp [doneState, continuationState, TargetEmitter.tokenCode] at equality ⊢

theorem continuationState_eq_doneState (token : Token) :
    continuationState token = doneState token := by
  rfl

/-! ### Literal 540-rule table -/

def allWorkSymbols : List WorkSymbol :=
  TargetEmitter.allWorkSymbols

structure StateProgram where
  state : Nat
  action : WorkSymbol → Nat × WorkSymbol × HeadMove

def deadAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  (deadState, symbol, .stay)

def seekSourceAction (token : Token) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.zeroZero ∨ symbol = WorkSymbol.zeroOne ∨
      symbol = WorkSymbol.oneZero ∨ symbol = WorkSymbol.oneOne ∨
      symbol = cursorMarker then
    (TargetEmitter.seekSourceState token, symbol, .right)
  else if symbol = sourceTargetBoundary then
    (TargetEmitter.seekTargetState token, symbol, .right)
  else
    deadAction symbol

def rewindSourceAction (token : Token) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.zeroZero ∨ symbol = WorkSymbol.zeroOne ∨
      symbol = WorkSymbol.oneZero ∨ symbol = WorkSymbol.oneOne ∨
      symbol = cursorMarker then
    (TargetEmitter.rewindSourceState token, symbol, .left)
  else if symbol = sourceLeftBoundary then
    (doneState token, symbol, .right)
  else
    deadAction symbol

def tokenPrograms (token : Token) : List StateProgram :=
  [{ state := TargetEmitter.seekSourceState token,
      action := seekSourceAction token },
   { state := TargetEmitter.seekTargetState token,
      action := TargetEmitter.seekTargetAction token },
   { state := TargetEmitter.writeSecondState token,
      action := TargetEmitter.writeSecondAction token },
   { state := TargetEmitter.rewindTargetState token,
      action := TargetEmitter.rewindTargetAction token },
   { state := TargetEmitter.rewindSourceState token,
      action := rewindSourceAction token }]

def statePrograms : List StateProgram :=
  TargetEmitter.allTokens.flatMap tokenPrograms

def rulesAt (program : StateProgram) : List WorkRule :=
  allWorkSymbols.map fun symbol =>
    let action := program.action symbol
    { sourceState := program.state
      readSymbol := symbol
      targetState := action.1
      writeSymbol := action.2.1
      move := action.2.2 }

/-- One closed table contains all twelve literal token-request blocks. -/
def rules : List WorkRule :=
  statePrograms.flatMap rulesAt

def machineFor (token : Token) : WorkMachine :=
  { rules := rules
    startState := TargetEmitter.seekSourceState token
    acceptState := doneState token
    rejectState := rejectState }

def compiledMachineFor (token : Token) : Machine :=
  compileWorkMachine (machineFor token)

theorem tokenPrograms_length (token : Token) :
    (tokenPrograms token).length = 5 := by
  rfl

theorem statePrograms_length :
    statePrograms.length = 60 := by
  rfl

theorem rulesAt_length (program : StateProgram) :
    (rulesAt program).length = 9 := by
  simp [rulesAt, allWorkSymbols, TargetEmitter.allWorkSymbols_length]

theorem rules_length :
    rules.length = 540 := by
  change (statePrograms.flatMap rulesAt).length = 540
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
  rcases List.mem_map.mp member with
    ⟨symbol, _symbolMember, ruleEq⟩
  rw [← ruleEq]

private theorem materializedPrograms_pairwise_query_distinct
    (programs : List StateProgram)
    (stateDistinct : programs.Pairwise fun left right =>
      left.state ≠ right.state) :
    (programs.flatMap rulesAt).Pairwise QueryDistinct := by
  induction programs with
  | nil =>
      exact List.Pairwise.nil
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

/-- Every query in the literal table is unique. -/
theorem rules_pairwise :
    rules.Pairwise QueryDistinct := by
  exact materializedPrograms_pairwise_query_distinct statePrograms
    statePrograms_pairwise_state_distinct

theorem machine_start_ne_accept (token : Token) :
    (machineFor token).startState ≠
      (machineFor token).acceptState := by
  cases token <;> decide

theorem machine_start_ne_reject (token : Token) :
    (machineFor token).startState ≠
      (machineFor token).rejectState := by
  cases token <;> decide

theorem machine_accept_ne_reject (token : Token) :
    (machineFor token).acceptState ≠
      (machineFor token).rejectState := by
  cases token <;> decide

set_option maxRecDepth 200000 in
theorem no_rule_at_done (token : Token) (symbol : WorkSymbol) :
    findWorkRule rules (doneState token) symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases token <;> cases first <;> cases second <;> decide

set_option maxRecDepth 200000 in
theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules rejectState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 200000 in
theorem no_rule_at_dead (symbol : WorkSymbol) :
    findWorkRule rules deadState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem done_configuration_halted (token : Token) (tape : WorkTape) :
    (machineFor token).isHalted
      { state := doneState token, tape := tape } = true := by
  cases token <;> rfl

theorem reject_configuration_halted (token : Token) (tape : WorkTape) :
    (machineFor token).isHalted
      { state := rejectState, tape := tape } = true := by
  cases token <;> rfl

theorem dead_configuration_not_halted
    (token : Token) (tape : WorkTape) :
    (machineFor token).isHalted
      { state := deadState, tape := tape } = false := by
  cases token <;> rfl

/-! ### Exact single-token mechanics -/

inductive SourceSymbol : WorkSymbol → Prop where
  | packed {symbol : WorkSymbol} :
      TargetEmitter.PackedSymbol symbol → SourceSymbol symbol
  | cursor : SourceSymbol cursorMarker

private def pushLeft :
    List WorkSymbol → List WorkSymbol → List WorkSymbol
  | [], farSide => farSide
  | head :: rest, farSide => pushLeft rest (head :: farSide)

private theorem pushLeft_eq_reverse_append
    (word farSide : List WorkSymbol) :
    pushLeft word farSide = word.reverse ++ farSide := by
  induction word generalizing farSide with
  | nil =>
      rfl
  | cons head rest ih =>
      simp only [pushLeft, ih, List.reverse_cons, List.append_assoc]
      rfl

private theorem workRunExact_compose (token : Token)
    (first second : Nat) (start middle final : WorkConfiguration)
    (hFirst :
      workRunExact? (machineFor token) first start = some middle)
    (hSecond :
      workRunExact? (machineFor token) second middle = some final) :
    workRunExact? (machineFor token) (first + second) start =
      some final := by
  induction first generalizing start with
  | zero =>
      change some start = some middle at hFirst
      have startEq : start = middle := Option.some.inj hFirst
      rw [Nat.zero_add, startEq]
      exact hSecond
  | succ first ih =>
      cases hStep : workStep? (machineFor token) start with
      | none =>
          change
            (match workStep? (machineFor token) start with
             | none => none
             | some next =>
                 workRunExact? (machineFor token) first next) =
              some middle at hFirst
          rw [hStep] at hFirst
          contradiction
      | some next =>
          have hTail :
              workRunExact? (machineFor token) first next =
                some middle := by
            change
              (match workStep? (machineFor token) start with
               | none => none
               | some next =>
                   workRunExact? (machineFor token) first next) =
                some middle at hFirst
            rw [hStep] at hFirst
            exact hFirst
          rw [Nat.succ_add]
          change
            (match workStep? (machineFor token) start with
             | none => none
             | some next =>
                 workRunExact? (machineFor token)
                   (first + second) next) =
              some final
          rw [hStep]
          exact ih next hTail

private theorem workRunExact_one (token : Token)
    (start next : WorkConfiguration)
    (hStep : workStep? (machineFor token) start = some next) :
    workRunExact? (machineFor token) 1 start = some next := by
  change
    (match workStep? (machineFor token) start with
     | none => none
     | some result => some result) = some next
  rw [hStep]

private theorem scanRightExact (token : Token) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ leftSide head suffix,
      Allowed head →
      workStep? (machineFor token)
          (TargetEmitter.configAtWord state
            leftSide (head :: suffix)) =
        some (TargetEmitter.configAtWord state
          (head :: leftSide) suffix))
    (word suffix leftSide : List WorkSymbol)
    (hAllowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? (machineFor token) word.length
        (TargetEmitter.configAtWord state
          leftSide (word ++ suffix)) =
      some (TargetEmitter.configAtWord state
        (pushLeft word leftSide) suffix) := by
  induction word generalizing leftSide with
  | nil =>
      rfl
  | cons head rest ih =>
      have headAllowed : Allowed head :=
        hAllowed head (List.Mem.head rest)
      have restAllowed :
          ∀ symbol, symbol ∈ rest → Allowed symbol := by
        intro symbol found
        exact hAllowed symbol (List.Mem.tail head found)
      change
        (match workStep? (machineFor token)
            (TargetEmitter.configAtWord state leftSide
              (head :: (rest ++ suffix))) with
         | none => none
         | some next =>
             workRunExact? (machineFor token) rest.length next) = _
      rw [hStep leftSide head (rest ++ suffix) headAllowed]
      exact ih (head :: leftSide) restAllowed

private theorem scanLeftExact (token : Token) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ head leftTail rightSide,
      Allowed head →
      workStep? (machineFor token)
          (TargetEmitter.configAtLeftWord state
            (head :: leftTail) rightSide) =
        some (TargetEmitter.configAtLeftWord state
          leftTail (head :: rightSide)))
    (word leftSuffix rightSide : List WorkSymbol)
    (hAllowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? (machineFor token) word.length
        (TargetEmitter.configAtLeftWord state
          (word ++ leftSuffix) rightSide) =
      some (TargetEmitter.configAtLeftWord state
        leftSuffix (pushLeft word rightSide)) := by
  induction word generalizing rightSide with
  | nil =>
      rfl
  | cons head rest ih =>
      have headAllowed : Allowed head :=
        hAllowed head (List.Mem.head rest)
      have restAllowed :
          ∀ symbol, symbol ∈ rest → Allowed symbol := by
        intro symbol found
        exact hAllowed symbol (List.Mem.tail head found)
      change
        (match workStep? (machineFor token)
            (TargetEmitter.configAtLeftWord state
              (head :: (rest ++ leftSuffix)) rightSide) with
         | none => none
         | some next =>
             workRunExact? (machineFor token) rest.length next) = _
      rw [hStep head (rest ++ leftSuffix) rightSide headAllowed]
      exact ih (head :: rightSide) restAllowed

private def literalRule (source : Nat) (read : WorkSymbol)
    (target : Nat) (write : WorkSymbol) (move : HeadMove) :
    WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := write
    move := move }

set_option maxRecDepth 200000 in
private theorem find_seekSource_packed (token : Token)
    (symbol : WorkSymbol)
    (ordinary : TargetEmitter.PackedSymbol symbol) :
    findWorkRule rules (TargetEmitter.seekSourceState token) symbol =
      some (literalRule (TargetEmitter.seekSourceState token) symbol
        (TargetEmitter.seekSourceState token) symbol .right) := by
  cases ordinary <;> cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_seekSource_cursor (token : Token) :
    findWorkRule rules (TargetEmitter.seekSourceState token)
        cursorMarker =
      some (literalRule (TargetEmitter.seekSourceState token)
        cursorMarker (TargetEmitter.seekSourceState token)
        cursorMarker .right) := by
  cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_seekSource_boundary (token : Token) :
    findWorkRule rules (TargetEmitter.seekSourceState token)
        sourceTargetBoundary =
      some (literalRule (TargetEmitter.seekSourceState token)
        sourceTargetBoundary (TargetEmitter.seekTargetState token)
        sourceTargetBoundary .right) := by
  cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_seekTarget_packed (token : Token)
    (symbol : WorkSymbol)
    (ordinary : TargetEmitter.PackedSymbol symbol) :
    findWorkRule rules (TargetEmitter.seekTargetState token) symbol =
      some (literalRule (TargetEmitter.seekTargetState token) symbol
        (TargetEmitter.seekTargetState token) symbol .right) := by
  cases ordinary <;> cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_seekTarget_blank (token : Token) :
    findWorkRule rules (TargetEmitter.seekTargetState token)
        WorkSymbol.blank =
      some (literalRule (TargetEmitter.seekTargetState token)
        WorkSymbol.blank (TargetEmitter.writeSecondState token)
        (TargetEmitter.tokenFirstSymbol token) .right) := by
  cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_writeSecond_blank (token : Token) :
    findWorkRule rules (TargetEmitter.writeSecondState token)
        WorkSymbol.blank =
      some (literalRule (TargetEmitter.writeSecondState token)
        WorkSymbol.blank (TargetEmitter.rewindTargetState token)
        (TargetEmitter.tokenSecondSymbol token) .left) := by
  cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_rewindTarget_packed (token : Token)
    (symbol : WorkSymbol)
    (ordinary : TargetEmitter.PackedSymbol symbol) :
    findWorkRule rules (TargetEmitter.rewindTargetState token) symbol =
      some (literalRule (TargetEmitter.rewindTargetState token) symbol
        (TargetEmitter.rewindTargetState token) symbol .left) := by
  cases ordinary <;> cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_rewindTarget_boundary (token : Token) :
    findWorkRule rules (TargetEmitter.rewindTargetState token)
        sourceTargetBoundary =
      some (literalRule (TargetEmitter.rewindTargetState token)
        sourceTargetBoundary (TargetEmitter.rewindSourceState token)
        sourceTargetBoundary .left) := by
  cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_rewindSource_packed (token : Token)
    (symbol : WorkSymbol)
    (ordinary : TargetEmitter.PackedSymbol symbol) :
    findWorkRule rules (TargetEmitter.rewindSourceState token) symbol =
      some (literalRule (TargetEmitter.rewindSourceState token) symbol
        (TargetEmitter.rewindSourceState token) symbol .left) := by
  cases ordinary <;> cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_rewindSource_cursor (token : Token) :
    findWorkRule rules (TargetEmitter.rewindSourceState token)
        cursorMarker =
      some (literalRule (TargetEmitter.rewindSourceState token)
        cursorMarker (TargetEmitter.rewindSourceState token)
        cursorMarker .left) := by
  cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_rewindSource_boundary (token : Token) :
    findWorkRule rules (TargetEmitter.rewindSourceState token)
        sourceLeftBoundary =
      some (literalRule (TargetEmitter.rewindSourceState token)
        sourceLeftBoundary (doneState token)
        sourceLeftBoundary .right) := by
  cases token <;> decide

set_option maxRecDepth 200000 in
private theorem seekSource_symbol_step (token : Token)
    (leftSide suffix : List WorkSymbol) (symbol : WorkSymbol)
    (allowed : SourceSymbol symbol) :
    workStep? (machineFor token)
        (TargetEmitter.configAtWord
          (TargetEmitter.seekSourceState token)
          leftSide (symbol :: suffix)) =
      some (TargetEmitter.configAtWord
        (TargetEmitter.seekSourceState token)
        (symbol :: leftSide) suffix) := by
  have found :
      findWorkRule rules (TargetEmitter.seekSourceState token) symbol =
        some (literalRule (TargetEmitter.seekSourceState token) symbol
          (TargetEmitter.seekSourceState token) symbol .right) := by
    cases allowed with
    | packed ordinary =>
        exact find_seekSource_packed token symbol ordinary
    | cursor =>
        exact find_seekSource_cursor token
  have notHalted :
      (machineFor token).isHalted
        (TargetEmitter.configAtWord
          (TargetEmitter.seekSourceState token)
          leftSide (symbol :: suffix)) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (TargetEmitter.configAtWord
          (TargetEmitter.seekSourceState token)
          leftSide (symbol :: suffix)) =
      some (applyWorkRule
        (literalRule (TargetEmitter.seekSourceState token) symbol
          (TargetEmitter.seekSourceState token) symbol .right)
        (TargetEmitter.configAtWord
          (TargetEmitter.seekSourceState token)
          leftSide (symbol :: suffix))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some (TargetEmitter.configAtWord
        (TargetEmitter.seekSourceState token)
        (symbol :: leftSide) suffix) := by
      cases suffix <;> rfl

set_option maxRecDepth 200000 in
private theorem seekSource_boundary_step (token : Token)
    (leftSide suffix : List WorkSymbol) :
    workStep? (machineFor token)
        (TargetEmitter.configAtWord
          (TargetEmitter.seekSourceState token) leftSide
          (sourceTargetBoundary :: suffix)) =
      some (TargetEmitter.configAtWord
        (TargetEmitter.seekTargetState token)
        (sourceTargetBoundary :: leftSide) suffix) := by
  have notHalted :
      (machineFor token).isHalted
        (TargetEmitter.configAtWord
          (TargetEmitter.seekSourceState token) leftSide
          (sourceTargetBoundary :: suffix)) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (TargetEmitter.configAtWord
          (TargetEmitter.seekSourceState token) leftSide
          (sourceTargetBoundary :: suffix)) =
      some (applyWorkRule
        (literalRule (TargetEmitter.seekSourceState token)
          sourceTargetBoundary (TargetEmitter.seekTargetState token)
          sourceTargetBoundary .right)
        (TargetEmitter.configAtWord
          (TargetEmitter.seekSourceState token) leftSide
          (sourceTargetBoundary :: suffix))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_seekSource_boundary token)
    _ = some (TargetEmitter.configAtWord
        (TargetEmitter.seekTargetState token)
        (sourceTargetBoundary :: leftSide) suffix) := by
      cases suffix <;> rfl

set_option maxRecDepth 200000 in
private theorem seekTarget_packed_step (token : Token)
    (leftSide suffix : List WorkSymbol) (symbol : WorkSymbol)
    (ordinary : TargetEmitter.PackedSymbol symbol) :
    workStep? (machineFor token)
        (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState token)
          leftSide (symbol :: suffix)) =
      some (TargetEmitter.configAtWord
        (TargetEmitter.seekTargetState token)
        (symbol :: leftSide) suffix) := by
  have notHalted :
      (machineFor token).isHalted
        (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState token)
          leftSide (symbol :: suffix)) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState token)
          leftSide (symbol :: suffix)) =
      some (applyWorkRule
        (literalRule (TargetEmitter.seekTargetState token) symbol
          (TargetEmitter.seekTargetState token) symbol .right)
        (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState token)
          leftSide (symbol :: suffix))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_seekTarget_packed token symbol ordinary)
    _ = some (TargetEmitter.configAtWord
        (TargetEmitter.seekTargetState token)
        (symbol :: leftSide) suffix) := by
      cases suffix <;> rfl

set_option maxRecDepth 200000 in
private theorem writeFirst_step (token : Token)
    (leftSide suffix : List WorkSymbol) :
    workStep? (machineFor token)
        (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState token) leftSide
          (WorkSymbol.blank :: WorkSymbol.blank :: suffix)) =
      some (TargetEmitter.configAtWord
        (TargetEmitter.writeSecondState token)
        (TargetEmitter.tokenFirstSymbol token :: leftSide)
        (WorkSymbol.blank :: suffix)) := by
  have notHalted :
      (machineFor token).isHalted
        (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState token) leftSide
          (WorkSymbol.blank :: WorkSymbol.blank :: suffix)) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState token) leftSide
          (WorkSymbol.blank :: WorkSymbol.blank :: suffix)) =
      some (applyWorkRule
        (literalRule (TargetEmitter.seekTargetState token)
          WorkSymbol.blank (TargetEmitter.writeSecondState token)
          (TargetEmitter.tokenFirstSymbol token) .right)
        (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState token) leftSide
          (WorkSymbol.blank :: WorkSymbol.blank :: suffix))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_seekTarget_blank token)
    _ = some (TargetEmitter.configAtWord
        (TargetEmitter.writeSecondState token)
        (TargetEmitter.tokenFirstSymbol token :: leftSide)
        (WorkSymbol.blank :: suffix)) := by
      rfl

set_option maxRecDepth 200000 in
private theorem writeSecond_step (token : Token)
    (leftSide suffix : List WorkSymbol) :
    workStep? (machineFor token)
        (TargetEmitter.configAtWord
          (TargetEmitter.writeSecondState token)
          (TargetEmitter.tokenFirstSymbol token :: leftSide)
          (WorkSymbol.blank :: suffix)) =
      some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindTargetState token)
        (TargetEmitter.tokenFirstSymbol token :: leftSide)
        (TargetEmitter.tokenSecondSymbol token :: suffix)) := by
  have notHalted :
      (machineFor token).isHalted
        (TargetEmitter.configAtWord
          (TargetEmitter.writeSecondState token)
          (TargetEmitter.tokenFirstSymbol token :: leftSide)
          (WorkSymbol.blank :: suffix)) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (TargetEmitter.configAtWord
          (TargetEmitter.writeSecondState token)
          (TargetEmitter.tokenFirstSymbol token :: leftSide)
          (WorkSymbol.blank :: suffix)) =
      some (applyWorkRule
        (literalRule (TargetEmitter.writeSecondState token)
          WorkSymbol.blank (TargetEmitter.rewindTargetState token)
          (TargetEmitter.tokenSecondSymbol token) .left)
        (TargetEmitter.configAtWord
          (TargetEmitter.writeSecondState token)
          (TargetEmitter.tokenFirstSymbol token :: leftSide)
          (WorkSymbol.blank :: suffix))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_writeSecond_blank token)
    _ = some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindTargetState token)
        (TargetEmitter.tokenFirstSymbol token :: leftSide)
        (TargetEmitter.tokenSecondSymbol token :: suffix)) := by
      rfl

set_option maxRecDepth 200000 in
private theorem rewindTarget_packed_step (token : Token)
    (leftTail rightSide : List WorkSymbol) (symbol : WorkSymbol)
    (ordinary : TargetEmitter.PackedSymbol symbol) :
    workStep? (machineFor token)
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindTargetState token)
          (symbol :: leftTail) rightSide) =
      some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindTargetState token)
        leftTail (symbol :: rightSide)) := by
  have notHalted :
      (machineFor token).isHalted
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindTargetState token)
          (symbol :: leftTail) rightSide) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindTargetState token)
          (symbol :: leftTail) rightSide) =
      some (applyWorkRule
        (literalRule (TargetEmitter.rewindTargetState token) symbol
          (TargetEmitter.rewindTargetState token) symbol .left)
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindTargetState token)
          (symbol :: leftTail) rightSide)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_rewindTarget_packed token symbol ordinary)
    _ = some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindTargetState token)
        leftTail (symbol :: rightSide)) := by
      cases leftTail <;> rfl

set_option maxRecDepth 200000 in
private theorem rewindTarget_boundary_step (token : Token)
    (leftTail rightSide : List WorkSymbol) :
    workStep? (machineFor token)
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindTargetState token)
          (sourceTargetBoundary :: leftTail) rightSide) =
      some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindSourceState token)
        leftTail (sourceTargetBoundary :: rightSide)) := by
  have notHalted :
      (machineFor token).isHalted
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindTargetState token)
          (sourceTargetBoundary :: leftTail) rightSide) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindTargetState token)
          (sourceTargetBoundary :: leftTail) rightSide) =
      some (applyWorkRule
        (literalRule (TargetEmitter.rewindTargetState token)
          sourceTargetBoundary (TargetEmitter.rewindSourceState token)
          sourceTargetBoundary .left)
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindTargetState token)
          (sourceTargetBoundary :: leftTail) rightSide)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_rewindTarget_boundary token)
    _ = some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindSourceState token)
        leftTail (sourceTargetBoundary :: rightSide)) := by
      cases leftTail <;> rfl

set_option maxRecDepth 200000 in
private theorem rewindSource_symbol_step (token : Token)
    (leftTail rightSide : List WorkSymbol) (symbol : WorkSymbol)
    (allowed : SourceSymbol symbol) :
    workStep? (machineFor token)
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindSourceState token)
          (symbol :: leftTail) rightSide) =
      some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindSourceState token)
        leftTail (symbol :: rightSide)) := by
  have found :
      findWorkRule rules (TargetEmitter.rewindSourceState token) symbol =
        some (literalRule (TargetEmitter.rewindSourceState token) symbol
          (TargetEmitter.rewindSourceState token) symbol .left) := by
    cases allowed with
    | packed ordinary =>
        exact find_rewindSource_packed token symbol ordinary
    | cursor =>
        exact find_rewindSource_cursor token
  have notHalted :
      (machineFor token).isHalted
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindSourceState token)
          (symbol :: leftTail) rightSide) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindSourceState token)
          (symbol :: leftTail) rightSide) =
      some (applyWorkRule
        (literalRule (TargetEmitter.rewindSourceState token) symbol
          (TargetEmitter.rewindSourceState token) symbol .left)
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindSourceState token)
          (symbol :: leftTail) rightSide)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindSourceState token)
        leftTail (symbol :: rightSide)) := by
      cases leftTail <;> rfl

set_option maxRecDepth 200000 in
private theorem rewindSource_boundary_step (token : Token)
    (leftTail rightSide : List WorkSymbol) :
    workStep? (machineFor token)
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindSourceState token)
          (sourceLeftBoundary :: leftTail) rightSide) =
      some (TargetEmitter.configAtWord (doneState token)
        (sourceLeftBoundary :: leftTail) rightSide) := by
  have notHalted :
      (machineFor token).isHalted
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindSourceState token)
          (sourceLeftBoundary :: leftTail) rightSide) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindSourceState token)
          (sourceLeftBoundary :: leftTail) rightSide) =
      some (applyWorkRule
        (literalRule (TargetEmitter.rewindSourceState token)
          sourceLeftBoundary (doneState token)
          sourceLeftBoundary .right)
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindSourceState token)
          (sourceLeftBoundary :: leftTail) rightSide)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_rewindSource_boundary token)
    _ = some (TargetEmitter.configAtWord (doneState token)
        (sourceLeftBoundary :: leftTail) rightSide) := by
      cases rightSide <;> rfl

private theorem tokenFirst_packed (token : Token) :
    TargetEmitter.PackedSymbol
      (TargetEmitter.tokenFirstSymbol token) := by
  cases token <;> constructor

def appendEntry (token : Token)
    (source target controllerOutside outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  TargetEmitter.configAtWord
    (TargetEmitter.seekSourceState token)
    (sourceLeftBoundary :: controllerOutside)
    (source ++
      (sourceTargetBoundary ::
        (target ++
          (WorkSymbol.blank :: WorkSymbol.blank ::
            WorkSymbol.blank :: outsideRight))))

def appendFinal (token : Token)
    (source target controllerOutside outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  TargetEmitter.configAtWord (doneState token)
    (sourceLeftBoundary :: controllerOutside)
    (source ++
      (sourceTargetBoundary ::
        (target ++ TargetEmitter.tokenSymbols token ++
          (WorkSymbol.blank :: outsideRight))))

def appendWorkSteps
    (source target : List WorkSymbol) : Nat :=
  2 * source.length + 2 * target.length + 6

/-- Exact cursor-aware append for an arbitrary source word consisting only of
packed cells and contextual cursor cells. -/
theorem append_exact (token : Token)
    (source target controllerOutside outsideRight : List WorkSymbol)
    (sourceAllowed :
      ∀ symbol, symbol ∈ source → SourceSymbol symbol)
    (targetPacked :
      ∀ symbol, symbol ∈ target →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? (machineFor token)
        (appendWorkSteps source target)
        (appendEntry token source target
          controllerOutside outsideRight) =
      some (appendFinal token source target
        controllerOutside outsideRight) := by
  let baseLeft := sourceLeftBoundary :: controllerOutside
  let afterSourceLeft := pushLeft source baseLeft
  let afterBoundaryLeft := sourceTargetBoundary :: afterSourceLeft
  let afterTargetLeft := pushLeft target afterBoundaryLeft
  let targetAndTokenRight :=
    target ++ TargetEmitter.tokenSymbols token ++
      (WorkSymbol.blank :: outsideRight)
  have hSource :
      workRunExact? (machineFor token) source.length
          (TargetEmitter.configAtWord
            (TargetEmitter.seekSourceState token) baseLeft
            (source ++
              (sourceTargetBoundary ::
                (target ++
                  (WorkSymbol.blank :: WorkSymbol.blank ::
                    WorkSymbol.blank :: outsideRight))))) =
        some (TargetEmitter.configAtWord
          (TargetEmitter.seekSourceState token) afterSourceLeft
          (sourceTargetBoundary ::
            (target ++
              (WorkSymbol.blank :: WorkSymbol.blank ::
                WorkSymbol.blank :: outsideRight)))) := by
    exact scanRightExact token
      (TargetEmitter.seekSourceState token) SourceSymbol
      (fun left head suffix allowed =>
        seekSource_symbol_step token left suffix head allowed)
      source
      (sourceTargetBoundary ::
        (target ++
          (WorkSymbol.blank :: WorkSymbol.blank ::
            WorkSymbol.blank :: outsideRight)))
      baseLeft sourceAllowed
  have hSourceBoundary :
      workRunExact? (machineFor token) 1
          (TargetEmitter.configAtWord
            (TargetEmitter.seekSourceState token) afterSourceLeft
            (sourceTargetBoundary ::
              (target ++
                (WorkSymbol.blank :: WorkSymbol.blank ::
                  WorkSymbol.blank :: outsideRight)))) =
        some (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState token) afterBoundaryLeft
          (target ++
            (WorkSymbol.blank :: WorkSymbol.blank ::
              WorkSymbol.blank :: outsideRight))) := by
    apply workRunExact_one token
    exact seekSource_boundary_step token afterSourceLeft
      (target ++
        (WorkSymbol.blank :: WorkSymbol.blank ::
          WorkSymbol.blank :: outsideRight))
  have hTarget :
      workRunExact? (machineFor token) target.length
          (TargetEmitter.configAtWord
            (TargetEmitter.seekTargetState token) afterBoundaryLeft
            (target ++
              (WorkSymbol.blank :: WorkSymbol.blank ::
                WorkSymbol.blank :: outsideRight))) =
        some (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState token) afterTargetLeft
          (WorkSymbol.blank :: WorkSymbol.blank ::
            WorkSymbol.blank :: outsideRight)) := by
    exact scanRightExact token
      (TargetEmitter.seekTargetState token)
      TargetEmitter.PackedSymbol
      (fun left head suffix ordinary =>
        seekTarget_packed_step token left suffix head ordinary)
      target
      (WorkSymbol.blank :: WorkSymbol.blank ::
        WorkSymbol.blank :: outsideRight)
      afterBoundaryLeft targetPacked
  have hFirst :
      workRunExact? (machineFor token) 1
          (TargetEmitter.configAtWord
            (TargetEmitter.seekTargetState token) afterTargetLeft
            (WorkSymbol.blank :: WorkSymbol.blank ::
              WorkSymbol.blank :: outsideRight)) =
        some (TargetEmitter.configAtWord
          (TargetEmitter.writeSecondState token)
          (TargetEmitter.tokenFirstSymbol token :: afterTargetLeft)
          (WorkSymbol.blank :: WorkSymbol.blank :: outsideRight)) := by
    apply workRunExact_one token
    exact writeFirst_step token afterTargetLeft
      (WorkSymbol.blank :: outsideRight)
  have hSecond :
      workRunExact? (machineFor token) 1
          (TargetEmitter.configAtWord
            (TargetEmitter.writeSecondState token)
            (TargetEmitter.tokenFirstSymbol token :: afterTargetLeft)
            (WorkSymbol.blank :: WorkSymbol.blank :: outsideRight)) =
        some (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindTargetState token)
          (TargetEmitter.tokenFirstSymbol token :: afterTargetLeft)
          (TargetEmitter.tokenSecondSymbol token ::
            WorkSymbol.blank :: outsideRight)) := by
    apply workRunExact_one token
    exact writeSecond_step token afterTargetLeft
      (WorkSymbol.blank :: outsideRight)
  have rewindTargetPacked :
      ∀ symbol,
        symbol ∈ TargetEmitter.tokenFirstSymbol token :: target.reverse →
          TargetEmitter.PackedSymbol symbol := by
    intro symbol found
    cases found with
    | head =>
        exact tokenFirst_packed token
    | tail _ tailMember =>
        exact targetPacked symbol (List.mem_reverse.mp tailMember)
  have hRewindTarget :
      workRunExact? (machineFor token) (target.length + 1)
          (TargetEmitter.configAtLeftWord
            (TargetEmitter.rewindTargetState token)
            (TargetEmitter.tokenFirstSymbol token :: afterTargetLeft)
            (TargetEmitter.tokenSecondSymbol token ::
              WorkSymbol.blank :: outsideRight)) =
        some (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindTargetState token)
          afterBoundaryLeft targetAndTokenRight) := by
    have scanned := scanLeftExact token
      (TargetEmitter.rewindTargetState token)
      TargetEmitter.PackedSymbol
      (fun head left right ordinary =>
        rewindTarget_packed_step token left right head ordinary)
      (TargetEmitter.tokenFirstSymbol token :: target.reverse)
      afterBoundaryLeft
      (TargetEmitter.tokenSecondSymbol token ::
        WorkSymbol.blank :: outsideRight)
      rewindTargetPacked
    simpa [afterTargetLeft, pushLeft_eq_reverse_append,
      targetAndTokenRight, TargetEmitter.tokenSymbols,
      List.append_assoc] using scanned
  have hTargetBoundary :
      workRunExact? (machineFor token) 1
          (TargetEmitter.configAtLeftWord
            (TargetEmitter.rewindTargetState token)
            afterBoundaryLeft targetAndTokenRight) =
        some (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindSourceState token)
          afterSourceLeft
          (sourceTargetBoundary :: targetAndTokenRight)) := by
    apply workRunExact_one token
    exact rewindTarget_boundary_step token afterSourceLeft
      targetAndTokenRight
  have rewindSourceAllowed :
      ∀ symbol, symbol ∈ source.reverse → SourceSymbol symbol := by
    intro symbol found
    exact sourceAllowed symbol (List.mem_reverse.mp found)
  have hRewindSource :
      workRunExact? (machineFor token) source.length
          (TargetEmitter.configAtLeftWord
            (TargetEmitter.rewindSourceState token)
            afterSourceLeft
            (sourceTargetBoundary :: targetAndTokenRight)) =
        some (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindSourceState token)
          baseLeft
          (source ++
            (sourceTargetBoundary :: targetAndTokenRight))) := by
    have scanned := scanLeftExact token
      (TargetEmitter.rewindSourceState token) SourceSymbol
      (fun head left right allowed =>
        rewindSource_symbol_step token left right head allowed)
      source.reverse baseLeft
      (sourceTargetBoundary :: targetAndTokenRight)
      rewindSourceAllowed
    simpa [afterSourceLeft, pushLeft_eq_reverse_append,
      List.append_assoc] using scanned
  have hLeftBoundary :
      workRunExact? (machineFor token) 1
          (TargetEmitter.configAtLeftWord
            (TargetEmitter.rewindSourceState token)
            baseLeft
            (source ++
              (sourceTargetBoundary :: targetAndTokenRight))) =
        some (TargetEmitter.configAtWord (doneState token) baseLeft
          (source ++
            (sourceTargetBoundary :: targetAndTokenRight))) := by
    apply workRunExact_one token
    exact rewindSource_boundary_step token controllerOutside
      (source ++
        (sourceTargetBoundary :: targetAndTokenRight))
  have h01 := workRunExact_compose token
    source.length 1 _ _ _ hSource hSourceBoundary
  have h02 := workRunExact_compose token
    (source.length + 1) target.length _ _ _ h01 hTarget
  have h03 := workRunExact_compose token
    (source.length + 1 + target.length) 1 _ _ _ h02 hFirst
  have h04 := workRunExact_compose token
    (source.length + 1 + target.length + 1) 1 _ _ _ h03 hSecond
  have h05 := workRunExact_compose token
    (source.length + 1 + target.length + 1 + 1)
    (target.length + 1) _ _ _ h04 hRewindTarget
  have h06 := workRunExact_compose token
    (source.length + 1 + target.length + 1 + 1 +
      (target.length + 1))
    1 _ _ _ h05 hTargetBoundary
  have h07 := workRunExact_compose token
    (source.length + 1 + target.length + 1 + 1 +
      (target.length + 1) + 1)
    source.length _ _ _ h06 hRewindSource
  have complete := workRunExact_compose token
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

/-! ### One replaced source cell and exact workspace endpoint -/

/-- The original packed source split before cursor installation. -/
def originalSource (before : List WorkSymbol) (original : WorkSymbol)
    (after : List WorkSymbol) : List WorkSymbol :=
  before ++ original :: after

/-- Replace exactly the distinguished source cell by the contextual cursor. -/
def sourceWithCursor (before : List WorkSymbol) (_original : WorkSymbol)
    (after : List WorkSymbol) : List WorkSymbol :=
  before ++ cursorMarker :: after

theorem sourceWithCursor_eq
    (before : List WorkSymbol) (original : WorkSymbol)
    (after : List WorkSymbol) :
    sourceWithCursor before original after =
      before ++ cursorMarker :: after := by
  rfl

/-- Packed words on either side cannot contain the cursor symbol, so the
displayed cursor cell is the only cursor in this split. -/
theorem sourceWithCursor_unique_context
    (before after : List WorkSymbol)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (afterPacked :
      ∀ symbol, symbol ∈ after →
        TargetEmitter.PackedSymbol symbol) :
    cursorMarker ∉ before ∧ cursorMarker ∉ after := by
  constructor
  · intro found
    exact cursor_not_packed (beforePacked cursorMarker found)
  · intro found
    exact cursor_not_packed (afterPacked cursorMarker found)

def entryConfiguration (token : Token)
    (before : List WorkSymbol) (original : WorkSymbol)
    (after target controllerOutside outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  appendEntry token (sourceWithCursor before original after) target
    controllerOutside outsideRight

def finalConfiguration (token : Token)
    (before : List WorkSymbol) (original : WorkSymbol)
    (after target controllerOutside outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  appendFinal token (sourceWithCursor before original after) target
    controllerOutside outsideRight

theorem finalConfiguration_state (token : Token)
    (before : List WorkSymbol) (original : WorkSymbol)
    (after target controllerOutside outsideRight : List WorkSymbol) :
    (finalConfiguration token before original after target
      controllerOutside outsideRight).state = doneState token := by
  cases before <;>
    rfl

/-- The endpoint's focused cell followed by its right side is exactly the
marked source, boundary, extended target, reserve blank, and untouched
right-side workspace.  In particular, focus has returned to the first source
cell and the unique cursor remains in place. -/
theorem finalConfiguration_focused_word (token : Token)
    (before : List WorkSymbol) (original : WorkSymbol)
    (after target controllerOutside outsideRight : List WorkSymbol) :
    let final :=
      finalConfiguration token before original after target
        controllerOutside outsideRight
    final.tape.head :: final.tape.right =
      sourceWithCursor before original after ++
        (sourceTargetBoundary ::
          (target ++ TargetEmitter.tokenSymbols token ++
            (WorkSymbol.blank :: outsideRight))) := by
  cases before <;>
    simp [finalConfiguration, appendFinal, sourceWithCursor,
      TargetEmitter.configAtWord, List.append_assoc]

theorem finalConfiguration_left_workspace (token : Token)
    (before : List WorkSymbol) (original : WorkSymbol)
    (after target controllerOutside outsideRight : List WorkSymbol) :
    (finalConfiguration token before original after target
      controllerOutside outsideRight).tape.left =
        sourceLeftBoundary :: controllerOutside := by
  cases before <;>
    rfl

/-- Exact work for a source split with one installed cursor. -/
def workSteps (before after target : List WorkSymbol) : Nat :=
  2 * (before.length + 1 + after.length) +
    2 * target.length + 6

theorem workSteps_evaluated
    (before after target : List WorkSymbol) :
    workSteps before after target =
      2 * (before.length + after.length + target.length) + 8 := by
  unfold workSteps
  omega

def workPolynomial : NatPolynomial :=
  NatPolynomial.linear 2 8

theorem workPolynomial_eval (size : Nat) :
    workPolynomial.eval size = 2 * size + 8 := by
  rfl

/-- The exact trace length is the value of a fixed linear polynomial in the
three variable packed-word lengths. -/
theorem workSteps_eq_polynomial
    (before after target : List WorkSymbol) :
    workSteps before after target =
      workPolynomial.eval
        (before.length + after.length + target.length) := by
  rw [workSteps_evaluated, workPolynomial_eval]

theorem workSteps_linear_bound
    (before after target : List WorkSymbol) :
    workSteps before after target ≤
      2 * (before.length + after.length + target.length + 4) := by
  rw [workSteps_evaluated]
  omega

/-- For every packed source split `before ++ original :: after`, replacing
`original` by the unique cursor marker is preserved during both source scans.
The requested literal token is appended to any packed target, the machine
halts on the first source cell, and both outside workspace lists remain
byte-for-byte unchanged. -/
theorem append_split_exact (token : Token)
    (before : List WorkSymbol) (original : WorkSymbol)
    (after target controllerOutside outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol,
        symbol ∈ originalSource before original after →
        TargetEmitter.PackedSymbol symbol)
    (targetPacked :
      ∀ symbol, symbol ∈ target →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? (machineFor token)
        (workSteps before after target)
        (entryConfiguration token before original after target
          controllerOutside outsideRight) =
      some (finalConfiguration token before original after target
        controllerOutside outsideRight) := by
  have sourceAllowed :
      ∀ symbol,
        symbol ∈ sourceWithCursor before original after →
          SourceSymbol symbol := by
    intro symbol found
    rw [sourceWithCursor_eq] at found
    rcases List.mem_append.mp found with beforeMember | restMember
    · exact SourceSymbol.packed
        (sourcePacked symbol
          (List.mem_append.mpr (Or.inl beforeMember)))
    · cases restMember with
      | head =>
          exact SourceSymbol.cursor
      | tail _ afterMember =>
          exact SourceSymbol.packed
            (sourcePacked symbol
              (List.mem_append.mpr
                (Or.inr (List.Mem.tail original afterMember))))
  have exactRun := append_exact token
    (sourceWithCursor before original after) target
    controllerOutside outsideRight sourceAllowed targetPacked
  have sourceLength :
      (sourceWithCursor before original after).length =
        before.length + 1 + after.length := by
    simp [sourceWithCursor]
    omega
  have stepsEq :
      appendWorkSteps (sourceWithCursor before original after) target =
        workSteps before after target := by
    simp [appendWorkSteps, workSteps, sourceLength]
  rw [stepsEq] at exactRun
  simpa [entryConfiguration, finalConfiguration] using exactRun

/-! ### Cursor locality and fail-closed contexts -/

/-- The dedicated cursor is passed through unchanged during the forward
source scan. -/
theorem seekSource_cursor_step (token : Token)
    (leftSide suffix : List WorkSymbol) :
    workStep? (machineFor token)
        (TargetEmitter.configAtWord
          (TargetEmitter.seekSourceState token)
          leftSide (cursorMarker :: suffix)) =
      some (TargetEmitter.configAtWord
        (TargetEmitter.seekSourceState token)
        (cursorMarker :: leftSide) suffix) := by
  exact seekSource_symbol_step token leftSide suffix
    cursorMarker SourceSymbol.cursor

/-- The same cursor is passed through unchanged during the backward source
scan. -/
theorem rewindSource_cursor_step (token : Token)
    (leftTail rightSide : List WorkSymbol) :
    workStep? (machineFor token)
        (TargetEmitter.configAtLeftWord
          (TargetEmitter.rewindSourceState token)
          (cursorMarker :: leftTail) rightSide) =
      some (TargetEmitter.configAtLeftWord
        (TargetEmitter.rewindSourceState token)
        leftTail (cursorMarker :: rightSide)) := by
  exact rewindSource_symbol_step token leftTail rightSide
    cursorMarker SourceSymbol.cursor

theorem seekSource_leftBoundary_is_dead (token : Token) :
    seekSourceAction token sourceLeftBoundary =
      deadAction sourceLeftBoundary := by
  cases token <;> rfl

theorem rewindSource_targetBoundary_is_dead (token : Token) :
    rewindSourceAction token sourceTargetBoundary =
      deadAction sourceTargetBoundary := by
  cases token <;> rfl

theorem seekTarget_cursor_is_dead (token : Token) :
    TargetEmitter.seekTargetAction token cursorMarker =
      deadAction cursorMarker := by
  cases token <;> rfl

theorem writeSecond_cursor_is_dead (token : Token) :
    TargetEmitter.writeSecondAction token cursorMarker =
      deadAction cursorMarker := by
  cases token <;> rfl

theorem rewindTarget_cursor_is_dead (token : Token) :
    TargetEmitter.rewindTargetAction token cursorMarker =
      deadAction cursorMarker := by
  cases token <;> rfl

set_option maxRecDepth 200000 in
private theorem find_seekTarget_cursor (token : Token) :
    findWorkRule rules (TargetEmitter.seekTargetState token)
        cursorMarker =
      some (literalRule (TargetEmitter.seekTargetState token)
        cursorMarker deadState cursorMarker .stay) := by
  cases token <;> decide

/-- A cursor outside the retained-source region cannot be interpreted as
target data: it enters the ruleless, non-halting dead state immediately. -/
theorem target_cursor_enters_dead (token : Token)
    (leftSide suffix : List WorkSymbol) :
    workStep? (machineFor token)
        (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState token)
          leftSide (cursorMarker :: suffix)) =
      some (TargetEmitter.configAtWord deadState
        leftSide (cursorMarker :: suffix)) := by
  have notHalted :
      (machineFor token).isHalted
        (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState token)
          leftSide (cursorMarker :: suffix)) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState token)
          leftSide (cursorMarker :: suffix)) =
      some (applyWorkRule
        (literalRule (TargetEmitter.seekTargetState token)
          cursorMarker deadState cursorMarker .stay)
        (TargetEmitter.configAtWord
          (TargetEmitter.seekTargetState token)
          leftSide (cursorMarker :: suffix))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_seekTarget_cursor token)
    _ = some (TargetEmitter.configAtWord deadState
        leftSide (cursorMarker :: suffix)) := by
      rfl

end PNP.Concrete.LockedNAND.TargetEmitterCursorAppender
