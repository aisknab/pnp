/-
Copyright (c) 2026 PNP Labs.

A standalone finite work-machine scanner for the strict canonical CNF codec.

The scanner reads the packed raw formula from left to right.  It validates
the token grammar, the unique final zero pad, and the following blank cell.
Successful validation removes its temporary left guard and leaves every
source cell unchanged.  Every malformed branch enters a two-state cleanup
which finds that guard, erases the complete source word, and rejects.

This file contains only the literal machine layer and lightweight transition
contracts.  Exact whole-input traces and the compiled polynomial interface
are supplied by later layers.
-/

import PNP.Concrete.CNFWorkMachine

namespace PNP.Concrete.CNFSourceParser

/-! ### Readable alphabet -/

def cellBlank : WorkSymbol := cnfBlank
def leftGuard : WorkSymbol := cnfMarkFalse
def formulaPad : WorkSymbol := cnfRootGuard
def tokenF : WorkSymbol := cnfF
def tokenSep : WorkSymbol := cnfSep
def tokenFinish : WorkSymbol := cnfFinish
def tokenT : WorkSymbol := cnfT

/-- The compiler's complete nine-symbol work alphabet. -/
def workAlphabet : List WorkSymbol := cnfWorkAlphabet

/-! ### Finite control -/

namespace State

def accept : Nat := 0
def reject : Nat := 1
def boot : Nat := 2
def installGuard : Nat := 3
def header : Nat := 4
def clauses : Nat := 5
def clause : Nat := 6
def literal : Nat := 7
def expectPad : Nat := 8
def finalEOF : Nat := 9
def successRestoreLeft : Nat := 10
def cleanupSeekGuard : Nat := 11
def cleanupRight : Nat := 12

end State

/-! ### Total state programs -/

structure Action where
  targetState : Nat
  writeSymbol : WorkSymbol
  move : HeadMove

structure StateProgram where
  state : Nat
  action : WorkSymbol → Action

def keepAction (target : Nat) (move : HeadMove)
    (symbol : WorkSymbol) : Action :=
  { targetState := target
    writeSymbol := symbol
    move := move }

def writeAction (target : Nat) (write : WorkSymbol)
    (move : HeadMove) : Action :=
  { targetState := target
    writeSymbol := write
    move := move }

/-- A mismatch is preserved for the moment and handed to the leftward
cleanup scan. -/
def cleanupAction (symbol : WorkSymbol) : Action :=
  keepAction State.cleanupSeekGuard .stay symbol

def expectOne (expected : WorkSymbol) (action : Action)
    (symbol : WorkSymbol) : Action :=
  if symbol == expected then action else cleanupAction symbol

def stateRules (program : StateProgram) : List WorkRule :=
  workAlphabet.map (fun symbol =>
    let action := program.action symbol
    { sourceState := program.state
      readSymbol := symbol
      targetState := action.targetState
      writeSymbol := action.writeSymbol
      move := action.move })

/-- The eleven operational states.  Accept and reject are deliberately
absent, so both designated halts are ruleless. -/
def statePrograms : List StateProgram :=
  [ { state := State.boot
      action := fun symbol =>
        keepAction State.installGuard .left symbol }
  , { state := State.installGuard
      action := fun _ =>
        writeAction State.header leftGuard .right }
  , { state := State.header
      action := fun symbol =>
        if symbol == tokenT then
          keepAction State.header .right symbol
        else if symbol == tokenF then
          keepAction State.clauses .right symbol
        else
          cleanupAction symbol }
  , { state := State.clauses
      action := fun symbol =>
        if symbol == tokenSep then
          keepAction State.clause .right symbol
        else if symbol == tokenFinish then
          keepAction State.expectPad .right symbol
        else
          cleanupAction symbol }
  , { state := State.clause
      action := fun symbol =>
        if symbol == tokenF then
          keepAction State.literal .right symbol
        else if symbol == tokenT then
          keepAction State.literal .right symbol
        else if symbol == tokenFinish then
          keepAction State.clauses .right symbol
        else
          cleanupAction symbol }
  , { state := State.literal
      action := fun symbol =>
        if symbol == tokenT then
          keepAction State.literal .right symbol
        else if symbol == tokenF then
          keepAction State.clause .right symbol
        else
          cleanupAction symbol }
  , { state := State.expectPad
      action := expectOne formulaPad
        (keepAction State.finalEOF .right formulaPad) }
  , { state := State.finalEOF
      action := expectOne cellBlank
        (keepAction State.successRestoreLeft .left cellBlank) }
  , { state := State.successRestoreLeft
      action := fun symbol =>
        if symbol == leftGuard then
          writeAction State.accept cellBlank .right
        else if symbol == tokenF then
          keepAction State.successRestoreLeft .left symbol
        else if symbol == tokenT then
          keepAction State.successRestoreLeft .left symbol
        else if symbol == tokenSep then
          keepAction State.successRestoreLeft .left symbol
        else if symbol == tokenFinish then
          keepAction State.successRestoreLeft .left symbol
        else if symbol == formulaPad then
          keepAction State.successRestoreLeft .left symbol
        else
          cleanupAction symbol }
  , { state := State.cleanupSeekGuard
      action := fun symbol =>
        if symbol == leftGuard then
          writeAction State.cleanupRight cellBlank .right
        else
          keepAction State.cleanupSeekGuard .left symbol }
  , { state := State.cleanupRight
      action := fun symbol =>
        if symbol == cellBlank then
          keepAction State.reject .stay symbol
        else
          writeAction State.cleanupRight cellBlank .right }
  ]

/-- The complete literal finite rule table.  Each operational state has
exactly one transition for every work symbol. -/
def rules : List WorkRule :=
  statePrograms.flatMap stateRules

/-- Strict canonical-CNF parser/validator over an arbitrary packed raw input
work tape. -/
def machine : WorkMachine :=
  { rules := rules
    startState := State.boot
    acceptState := State.accept
    rejectState := State.reject }

/-- Literal three-symbol single-tape compilation of the scanner. -/
def compiledMachine : Machine :=
  compileWorkMachine machine

/-! ### Literal-table facts -/

/-- Two rules compete exactly when their state/symbol queries coincide. -/
def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

private theorem stateRules_source_eq {program : StateProgram}
    {rule : WorkRule} (member : rule ∈ stateRules program) :
    rule.sourceState = program.state := by
  rcases List.mem_map.mp member with
    ⟨symbol, _symbolMember, ruleEq⟩
  rw [← ruleEq]

private theorem stateRules_pairwise_query_distinct
    (program : StateProgram) :
    (stateRules program).Pairwise QueryDistinct := by
  unfold stateRules workAlphabet cnfWorkAlphabet QueryDistinct
  simp [cnfBlank, cnfMarkFalse, cnfMarkTrue, cnfRootGuard, cnfF,
    cnfSep, cnfBoundaryGuard, cnfFinish, cnfT,
    WorkSymbol.blank, WorkSymbol.blankZero, WorkSymbol.blankOne,
    WorkSymbol.zeroBlank, WorkSymbol.zeroZero, WorkSymbol.zeroOne,
    WorkSymbol.oneBlank, WorkSymbol.oneZero, WorkSymbol.oneOne]

private theorem materializedPrograms_pairwise_query_distinct
    (programs : List StateProgram)
    (stateDistinct : programs.Pairwise (fun left right =>
      left.state ≠ right.state)) :
    (programs.flatMap stateRules).Pairwise QueryDistinct := by
  induction programs with
  | nil => exact List.Pairwise.nil
  | cons first rest ih =>
      cases stateDistinct with
      | cons firstDistinct restDistinct =>
          change
            (stateRules first ++ rest.flatMap stateRules).Pairwise
              QueryDistinct
          rw [List.pairwise_append]
          refine
            ⟨stateRules_pairwise_query_distinct first,
             ih restDistinct, ?_⟩
          intro left leftMember right rightMember queryEq
          rcases List.mem_flatMap.mp rightMember with
            ⟨rightProgram, rightProgramMember, rightRuleMember⟩
          have sourceNe :=
            firstDistinct rightProgram rightProgramMember
          have leftSource := stateRules_source_eq leftMember
          have rightSource := stateRules_source_eq rightRuleMember
          have sourceEq := congrArg Prod.fst queryEq
          exact sourceNe
            (leftSource.symm.trans (sourceEq.trans rightSource))

set_option maxRecDepth 100000 in
private theorem statePrograms_pairwise_state_distinct :
    statePrograms.Pairwise (fun left right =>
      left.state ≠ right.state) := by
  decide

/-- No two literal rules answer the same state/symbol query. -/
theorem rules_pairwise_query_distinct :
    rules.Pairwise QueryDistinct := by
  exact materializedPrograms_pairwise_query_distinct statePrograms
    statePrograms_pairwise_state_distinct

private theorem materializedPrograms_length
    (programs : List StateProgram) :
    (programs.flatMap stateRules).length =
      9 * programs.length := by
  induction programs with
  | nil => rfl
  | cons first rest ih =>
      change
        (stateRules first ++ rest.flatMap stateRules).length =
          9 * Nat.succ rest.length
      rw [List.length_append, ih, Nat.mul_succ]
      have firstLength : (stateRules first).length = 9 := by
        rfl
      rw [firstLength, Nat.add_comm]

theorem statePrograms_length :
    statePrograms.length = 11 := by
  rfl

/-- Exact literal rule count: eleven operational states times nine symbols. -/
def ruleCount : Nat := 99

theorem rules_length : rules.length = ruleCount := by
  change (statePrograms.flatMap stateRules).length = 99
  rw [materializedPrograms_length, statePrograms_length]

/-! ### Halt separation -/

theorem machine_startState_ne_acceptState :
    machine.startState ≠ machine.acceptState := by
  decide

theorem machine_startState_ne_rejectState :
    machine.startState ≠ machine.rejectState := by
  decide

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by
  decide

set_option maxRecDepth 100000 in
theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule rules State.accept symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 100000 in
theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules State.reject symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem accept_configuration_halted (tape : WorkTape) :
    machine.isHalted
      { state := State.accept, tape := tape } = true := by
  rfl

theorem reject_configuration_halted (tape : WorkTape) :
    machine.isHalted
      { state := State.reject, tape := tape } = true := by
  rfl

/-! ### Lightweight exact transition contracts -/

def focusedConfiguration (state : Nat)
    (left : List WorkSymbol) (head : WorkSymbol)
    (right : List WorkSymbol) : WorkConfiguration :=
  { state := state
    tape := { left := left, head := head, right := right } }

theorem boot_step (left right : List WorkSymbol)
    (symbol : WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.boot left symbol right) =
      some
        { state := State.installGuard
          tape :=
            (focusedConfiguration State.boot left symbol right).tape.moveLeft
        } := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> rfl

theorem installGuard_step (left right : List WorkSymbol)
    (symbol : WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.installGuard left symbol right) =
      some
        { state := State.header
          tape :=
            ((focusedConfiguration State.installGuard left symbol right).tape
              |>.write leftGuard).moveRight
        } := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> rfl

theorem header_t_step (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.header left tokenT right) =
      some
        { state := State.header
          tape :=
            (focusedConfiguration State.header left tokenT right).tape.moveRight
        } := by
  rfl

theorem header_f_step (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.header left tokenF right) =
      some
        { state := State.clauses
          tape :=
            (focusedConfiguration State.header left tokenF right).tape.moveRight
        } := by
  rfl

theorem clauses_sep_step (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.clauses left tokenSep right) =
      some
        { state := State.clause
          tape :=
            (focusedConfiguration State.clauses left tokenSep right).tape.moveRight
        } := by
  rfl

theorem clauses_finish_step (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.clauses left tokenFinish right) =
      some
        { state := State.expectPad
          tape :=
            (focusedConfiguration State.clauses left tokenFinish right).tape.moveRight
        } := by
  rfl

theorem clause_f_step (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.clause left tokenF right) =
      some
        { state := State.literal
          tape :=
            (focusedConfiguration State.clause left tokenF right).tape.moveRight
        } := by
  rfl

theorem clause_t_step (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.clause left tokenT right) =
      some
        { state := State.literal
          tape :=
            (focusedConfiguration State.clause left tokenT right).tape.moveRight
        } := by
  rfl

/-- `Finish` is legal immediately after `Sep`, so the scanner preserves the
strict codec's valid empty-clause case. -/
theorem clause_finish_step (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.clause left tokenFinish right) =
      some
        { state := State.clauses
          tape :=
            (focusedConfiguration State.clause left tokenFinish right).tape.moveRight
        } := by
  rfl

theorem literal_t_step (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.literal left tokenT right) =
      some
        { state := State.literal
          tape :=
            (focusedConfiguration State.literal left tokenT right).tape.moveRight
        } := by
  rfl

theorem literal_f_step (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.literal left tokenF right) =
      some
        { state := State.clause
          tape :=
            (focusedConfiguration State.literal left tokenF right).tape.moveRight
        } := by
  rfl

theorem expectPad_step (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.expectPad left formulaPad right) =
      some
        { state := State.finalEOF
          tape :=
            (focusedConfiguration State.expectPad left formulaPad right).tape.moveRight
        } := by
  rfl

theorem finalEOF_blank_step (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.finalEOF left cellBlank right) =
      some
        { state := State.successRestoreLeft
          tape :=
            (focusedConfiguration State.finalEOF left cellBlank right).tape.moveLeft
        } := by
  rfl

theorem header_sep_enters_cleanup (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.header left tokenSep right) =
      some (focusedConfiguration State.cleanupSeekGuard
        left tokenSep right) := by
  rfl

theorem literal_finish_enters_cleanup (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.literal left tokenFinish right) =
      some (focusedConfiguration State.cleanupSeekGuard
        left tokenFinish right) := by
  rfl

theorem successRestore_guard_step (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.successRestoreLeft
          left leftGuard right) =
      some
        { state := State.accept
          tape :=
            ((focusedConfiguration State.successRestoreLeft
              left leftGuard right).tape.write cellBlank).moveRight
        } := by
  rfl

theorem cleanupSeek_guard_step (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.cleanupSeekGuard
          left leftGuard right) =
      some
        { state := State.cleanupRight
          tape :=
            ((focusedConfiguration State.cleanupSeekGuard
              left leftGuard right).tape.write cellBlank).moveRight
        } := by
  rfl

theorem cleanupRight_f_step (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.cleanupRight left tokenF right) =
      some
        { state := State.cleanupRight
          tape :=
            ((focusedConfiguration State.cleanupRight
              left tokenF right).tape.write cellBlank).moveRight
        } := by
  rfl

theorem cleanupRight_blank_step (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.cleanupRight left cellBlank right) =
      some (focusedConfiguration State.reject left cellBlank right) := by
  rfl

end PNP.Concrete.CNFSourceParser
