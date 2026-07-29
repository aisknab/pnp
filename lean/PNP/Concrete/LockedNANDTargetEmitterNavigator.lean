/-
Copyright (c) 2026 PNP Labs.

Literal navigation and branch control for the grammar-only locked-NAND target
emitter.  These machines inspect only already-validated strict-v0 source
cells.  They skip the circuit header, classify one raw source tag, cross the
program delimiter, and advance between raw gates.  Every branch is represented
by an ordinary accept/reject endpoint for later program-graph wiring.
-/

import PNP.Concrete.LockedNANDTargetEmitterGrammarScanner
import PNP.Concrete.LockedNANDTargetEmitterMachine
import PNP.Concrete.PipelineMachineSimulation

namespace PNP.Concrete.LockedNAND.TargetEmitterNavigator

open PNP.Concrete

def cell00 : WorkSymbol := WorkSymbol.zeroZero
def cell01 : WorkSymbol := WorkSymbol.zeroOne
def cell10 : WorkSymbol := WorkSymbol.oneZero
def cell11 : WorkSymbol := WorkSymbol.oneOne

def allWorkSymbols : List WorkSymbol :=
  PNP.Concrete.LockedNAND.TargetEmitter.allWorkSymbols

namespace State

def accept : Nat := 0
def reject : Nat := 1
def dead : Nat := 2

def headerStart : Nat := 10
def versionSecond : Nat := 11
def inputFirst : Nat := 12
def inputSecond : Nat := 13
def gateFirst : Nat := 14
def gateSecond : Nat := 15
def headerLook : Nat := 16

def sourceFirst : Nat := 20
def nonInputFirst : Nat := 21
def nonInputSecond : Nat := 22
def constantFirst : Nat := 23
def constantSecond : Nat := 24

def programFirst : Nat := 30
def programSecond : Nat := 31
def gateEndFirst : Nat := 32
def gateEndSecond : Nat := 33
def gateLook : Nat := 34

end State

structure Action where
  targetState : Nat
  writeSymbol : WorkSymbol
  move : HeadMove

structure StateProgram where
  state : Nat
  action : WorkSymbol → Action

def deadAction (symbol : WorkSymbol) : Action :=
  { targetState := State.dead
    writeSymbol := symbol
    move := .stay }

def keepAction (target : Nat) (move : HeadMove)
    (symbol : WorkSymbol) : Action :=
  { targetState := target
    writeSymbol := symbol
    move := move }

def expect (expected : WorkSymbol) (target : Nat)
    (move : HeadMove) (symbol : WorkSymbol) : Action :=
  if symbol = expected then keepAction target move symbol
  else deadAction symbol

def headerStartAction : WorkSymbol → Action :=
  expect cell00 State.versionSecond .right

def versionSecondAction : WorkSymbol → Action :=
  expect cell00 State.inputFirst .right

def inputFirstAction : WorkSymbol → Action :=
  expect cell00 State.inputSecond .right

def inputSecondAction (symbol : WorkSymbol) : Action :=
  if symbol = cell01 then
    keepAction State.inputFirst .right symbol
  else if symbol = cell10 then
    keepAction State.gateFirst .right symbol
  else deadAction symbol

def gateFirstAction : WorkSymbol → Action :=
  expect cell00 State.gateSecond .right

def gateSecondAction (symbol : WorkSymbol) : Action :=
  if symbol = cell01 then
    keepAction State.gateFirst .right symbol
  else if symbol = cell10 then
    keepAction State.headerLook .right symbol
  else deadAction symbol

def headerLookAction (symbol : WorkSymbol) : Action :=
  if symbol = cell00 ∨ symbol = cell01 then
    keepAction State.accept .stay symbol
  else if symbol = cell10 then
    keepAction State.reject .stay symbol
  else deadAction symbol

def sourceFirstAction (symbol : WorkSymbol) : Action :=
  if symbol = cell00 then
    keepAction State.accept .stay symbol
  else if symbol = cell01 then
    keepAction State.reject .stay symbol
  else deadAction symbol

def nonInputFirstAction : WorkSymbol → Action :=
  expect cell01 State.nonInputSecond .right

def nonInputSecondAction (symbol : WorkSymbol) : Action :=
  if symbol = cell10 then
    keepAction State.accept .left symbol
  else if symbol = cell00 ∨ symbol = cell01 then
    keepAction State.reject .left symbol
  else deadAction symbol

def constantFirstAction : WorkSymbol → Action :=
  expect cell01 State.constantSecond .right

def constantSecondAction (symbol : WorkSymbol) : Action :=
  if symbol = cell00 then
    keepAction State.accept .left symbol
  else if symbol = cell01 then
    keepAction State.reject .left symbol
  else deadAction symbol

def programFirstAction : WorkSymbol → Action :=
  expect cell10 State.programSecond .right

def programSecondAction : WorkSymbol → Action :=
  expect cell00 State.accept .right

def gateEndFirstAction : WorkSymbol → Action :=
  expect cell01 State.gateEndSecond .right

def gateEndSecondAction : WorkSymbol → Action :=
  expect cell11 State.gateLook .right

def gateLookAction (symbol : WorkSymbol) : Action :=
  if symbol = cell00 ∨ symbol = cell01 then
    keepAction State.accept .stay symbol
  else if symbol = cell10 then
    keepAction State.reject .stay symbol
  else deadAction symbol

def statePrograms : List StateProgram :=
  [ { state := State.headerStart, action := headerStartAction }
  , { state := State.versionSecond, action := versionSecondAction }
  , { state := State.inputFirst, action := inputFirstAction }
  , { state := State.inputSecond, action := inputSecondAction }
  , { state := State.gateFirst, action := gateFirstAction }
  , { state := State.gateSecond, action := gateSecondAction }
  , { state := State.headerLook, action := headerLookAction }
  , { state := State.sourceFirst, action := sourceFirstAction }
  , { state := State.nonInputFirst, action := nonInputFirstAction }
  , { state := State.nonInputSecond, action := nonInputSecondAction }
  , { state := State.constantFirst, action := constantFirstAction }
  , { state := State.constantSecond, action := constantSecondAction }
  , { state := State.programFirst, action := programFirstAction }
  , { state := State.programSecond, action := programSecondAction }
  , { state := State.gateEndFirst, action := gateEndFirstAction }
  , { state := State.gateEndSecond, action := gateEndSecondAction }
  , { state := State.gateLook, action := gateLookAction }
  ]

def rulesAt (program : StateProgram) : List WorkRule :=
  allWorkSymbols.map fun symbol =>
    let action := program.action symbol
    { sourceState := program.state
      readSymbol := symbol
      targetState := action.targetState
      writeSymbol := action.writeSymbol
      move := action.move }

def rules : List WorkRule :=
  statePrograms.flatMap rulesAt

def machineFrom (start : Nat) : WorkMachine :=
  { rules := rules
    startState := start
    acceptState := State.accept
    rejectState := State.reject }

def headerMachine : WorkMachine :=
  machineFrom State.headerStart

def sourceFirstMachine : WorkMachine :=
  machineFrom State.sourceFirst

def nonInputMachine : WorkMachine :=
  machineFrom State.nonInputFirst

def constantMachine : WorkMachine :=
  machineFrom State.constantFirst

def programEndMachine : WorkMachine :=
  machineFrom State.programFirst

def gateAdvanceMachine : WorkMachine :=
  machineFrom State.gateEndFirst

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

theorem allWorkSymbols_length :
    allWorkSymbols.length = 9 := by
  rfl

theorem statePrograms_length :
    statePrograms.length = 17 := by
  rfl

theorem rulesAt_length (program : StateProgram) :
    (rulesAt program).length = 9 := by
  rfl

theorem rules_length :
    rules.length = 153 := by
  rfl

private theorem rulesAt_pairwise
    (program : StateProgram) :
    (rulesAt program).Pairwise QueryDistinct := by
  unfold rulesAt allWorkSymbols
    PNP.Concrete.LockedNAND.TargetEmitter.allWorkSymbols
  simp [QueryDistinct, WorkSymbol.blank,
    WorkSymbol.blankZero, WorkSymbol.blankOne,
    WorkSymbol.zeroBlank, WorkSymbol.zeroZero, WorkSymbol.zeroOne,
    WorkSymbol.oneBlank, WorkSymbol.oneZero, WorkSymbol.oneOne]

private theorem rulesAt_source
    {program : StateProgram} {rule : WorkRule}
    (member : rule ∈ rulesAt program) :
    rule.sourceState = program.state := by
  rcases List.mem_map.mp member with
    ⟨symbol, _symbolMember, ruleEq⟩
  rw [← ruleEq]

private theorem flatMap_pairwise
    (programs : List StateProgram)
    (stateDistinct :
      programs.Pairwise fun left right =>
        left.state ≠ right.state) :
    (programs.flatMap rulesAt).Pairwise QueryDistinct := by
  induction programs with
  | nil => exact List.Pairwise.nil
  | cons first rest inductionHypothesis =>
      cases stateDistinct with
      | cons firstDistinct restDistinct =>
          change
            (rulesAt first ++ rest.flatMap rulesAt).Pairwise
              QueryDistinct
          rw [List.pairwise_append]
          refine
            ⟨rulesAt_pairwise first,
             inductionHypothesis restDistinct, ?_⟩
          intro left leftMember right rightMember queryEq
          rcases List.mem_flatMap.mp rightMember with
            ⟨rightProgram, rightProgramMember, rightRuleMember⟩
          have sourceNe :=
            firstDistinct rightProgram rightProgramMember
          have leftSource := rulesAt_source leftMember
          have rightSource := rulesAt_source rightRuleMember
          have sourceEq := congrArg Prod.fst queryEq
          exact sourceNe
            (leftSource.symm.trans
              (sourceEq.trans rightSource))

private theorem statePrograms_pairwise :
    statePrograms.Pairwise fun left right =>
      left.state ≠ right.state := by
  decide

theorem rules_pairwise :
    rules.Pairwise QueryDistinct := by
  exact flatMap_pairwise statePrograms
    statePrograms_pairwise

theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule rules State.accept symbol = none := by
  cases symbol with
  | mk first second =>
      cases first <;> cases second <;> rfl

theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules State.reject symbol = none := by
  cases symbol with
  | mk first second =>
      cases first <;> cases second <;> rfl

theorem no_rule_at_dead (symbol : WorkSymbol) :
    findWorkRule rules State.dead symbol = none := by
  cases symbol with
  | mk first second =>
      cases first <;> cases second <;> rfl

theorem machineFrom_start_ne_accept
    (start : Nat) (startNe : start ≠ State.accept) :
    (machineFrom start).startState ≠
      (machineFrom start).acceptState := by
  exact startNe

theorem machineFrom_start_ne_reject
    (start : Nat) (startNe : start ≠ State.reject) :
    (machineFrom start).startState ≠
      (machineFrom start).rejectState := by
  exact startNe

theorem machineFrom_accept_ne_reject (start : Nat) :
    (machineFrom start).acceptState ≠
      (machineFrom start).rejectState := by
  change State.accept ≠ State.reject
  decide

theorem dead_stuck (start : Nat) (tape : WorkTape) :
    workStep? (machineFrom start)
      { state := State.dead, tape := tape } = none := by
  unfold workStep? WorkMachine.isHalted machineFrom
  rw [no_rule_at_dead]
  rfl

/-! ### Exact physical traces -/

set_option maxRecDepth 100000

def configAtWord (state : Nat) (left word : List WorkSymbol) :
    WorkConfiguration :=
  PNP.Concrete.LockedNAND.TargetEmitter.configAtWord
    state left word

def pushCrossed (word left : List WorkSymbol) :
    List WorkSymbol :=
  word.reverse ++ left

private theorem exactRun_add (machine : WorkMachine)
    (first second : Nat)
    (initial middle final : WorkConfiguration)
    (firstRun :
      workRunExact? machine first initial = some middle)
    (secondRun :
      workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) initial =
      some final :=
  PipelineMachineSimulation.workRunExact?_compose
    machine first second initial middle final firstRun secondRun

private theorem inputNat_exact (value : Nat)
    (left suffix : List WorkSymbol) :
    workRunExact? headerMachine (2 * (value + 1))
        (configAtWord State.inputFirst left
          (SourceParser.natCells value ++ suffix)) =
      some
        (configAtWord State.gateFirst
          (pushCrossed (SourceParser.natCells value) left)
          suffix) := by
  induction value generalizing left with
  | zero =>
      cases suffix <;> rfl
  | succ value inductionHypothesis =>
      have first :
          workRunExact? headerMachine 2
              (configAtWord State.inputFirst left
                (cell00 :: cell01 ::
                  (SourceParser.natCells value ++ suffix))) =
            some
              (configAtWord State.inputFirst
                (cell01 :: cell00 :: left)
                (SourceParser.natCells value ++ suffix)) := by
        cases value <;> rfl
      have tail :=
        inductionHypothesis
          (cell01 :: cell00 :: left)
      have all := exactRun_add headerMachine
        2 (2 * (value + 1)) _ _ _ first tail
      have cost :
          2 + 2 * (value + 1) =
            2 * ((value + 1) + 1) := by
        omega
      rw [cost] at all
      simpa [SourceParser.natCells, pushCrossed,
        List.reverse_append, cell00, cell01,
        SourceParser.cell00, SourceParser.cell01] using all

private theorem gateNat_exact (value : Nat)
    (left suffix : List WorkSymbol) :
    workRunExact? headerMachine (2 * (value + 1))
        (configAtWord State.gateFirst left
          (SourceParser.natCells value ++ suffix)) =
      some
        (configAtWord State.headerLook
          (pushCrossed (SourceParser.natCells value) left)
          suffix) := by
  induction value generalizing left with
  | zero =>
      cases suffix <;> rfl
  | succ value inductionHypothesis =>
      have first :
          workRunExact? headerMachine 2
              (configAtWord State.gateFirst left
                (cell00 :: cell01 ::
                  (SourceParser.natCells value ++ suffix))) =
            some
              (configAtWord State.gateFirst
                (cell01 :: cell00 :: left)
                (SourceParser.natCells value ++ suffix)) := by
        cases value <;> rfl
      have tail :=
        inductionHypothesis
          (cell01 :: cell00 :: left)
      have all := exactRun_add headerMachine
        2 (2 * (value + 1)) _ _ _ first tail
      have cost :
          2 + 2 * (value + 1) =
            2 * ((value + 1) + 1) := by
        omega
      rw [cost] at all
      simpa [SourceParser.natCells, pushCrossed,
        List.reverse_append, cell00, cell01,
        SourceParser.cell00, SourceParser.cell01] using all

def headerWorkSteps (inputs gates : Nat) : Nat :=
  2 * inputs + 2 * gates + 7

theorem header_nonempty_exact
    (inputs gates : Nat)
    (first : WorkSymbol) (rest left : List WorkSymbol)
    (sourceFirst :
      first = cell00 ∨ first = cell01) :
    workRunExact? headerMachine
        (headerWorkSteps inputs gates)
        (configAtWord State.headerStart left
          (cell00 :: cell00 ::
            (SourceParser.natCells inputs ++
              (SourceParser.natCells gates ++ first :: rest)))) =
      some
        (configAtWord State.accept
          (pushCrossed
            ([cell00, cell00] ++
              SourceParser.natCells inputs ++
              SourceParser.natCells gates)
            left)
          (first :: rest)) := by
  have version :
      workRunExact? headerMachine 2
          (configAtWord State.headerStart left
            (cell00 :: cell00 ::
              (SourceParser.natCells inputs ++
                (SourceParser.natCells gates ++ first :: rest)))) =
        some
          (configAtWord State.inputFirst
            (cell00 :: cell00 :: left)
            (SourceParser.natCells inputs ++
              (SourceParser.natCells gates ++ first :: rest))) := by
    cases inputs <;> rfl
  have input :=
    inputNat_exact inputs (cell00 :: cell00 :: left)
      (SourceParser.natCells gates ++ first :: rest)
  have gatesRun :=
    gateNat_exact gates
      (pushCrossed (SourceParser.natCells inputs)
        (cell00 :: cell00 :: left))
      (first :: rest)
  have look :
      workRunExact? headerMachine 1
          (configAtWord State.headerLook
            (pushCrossed (SourceParser.natCells gates)
              (pushCrossed (SourceParser.natCells inputs)
                (cell00 :: cell00 :: left)))
            (first :: rest)) =
        some
          (configAtWord State.accept
            (pushCrossed (SourceParser.natCells gates)
              (pushCrossed (SourceParser.natCells inputs)
                (cell00 :: cell00 :: left)))
            (first :: rest)) := by
    rcases sourceFirst with rfl | rfl <;> rfl
  have throughInput := exactRun_add headerMachine
    2 (2 * (inputs + 1)) _ _ _ version input
  have throughGates := exactRun_add headerMachine
    (2 + 2 * (inputs + 1)) (2 * (gates + 1))
    _ _ _ throughInput gatesRun
  have all := exactRun_add headerMachine
    (2 + 2 * (inputs + 1) + 2 * (gates + 1))
    1 _ _ _ throughGates look
  have cost :
      2 + 2 * (inputs + 1) + 2 * (gates + 1) + 1 =
        headerWorkSteps inputs gates := by
    unfold headerWorkSteps
    omega
  rw [cost] at all
  simpa [pushCrossed,
    List.reverse_append, List.append_assoc] using all

theorem header_empty_exact
    (inputs : Nat) (rest left : List WorkSymbol) :
    workRunExact? headerMachine
        (headerWorkSteps inputs 0)
        (configAtWord State.headerStart left
          (cell00 :: cell00 ::
            (SourceParser.natCells inputs ++
              (SourceParser.natCells 0 ++ cell10 :: rest)))) =
      some
        (configAtWord State.reject
          (pushCrossed
            ([cell00, cell00] ++
              SourceParser.natCells inputs ++
              SourceParser.natCells 0)
            left)
          (cell10 :: rest)) := by
  have version :
      workRunExact? headerMachine 2
          (configAtWord State.headerStart left
            (cell00 :: cell00 ::
              (SourceParser.natCells inputs ++
                (SourceParser.natCells 0 ++ cell10 :: rest)))) =
        some
          (configAtWord State.inputFirst
            (cell00 :: cell00 :: left)
            (SourceParser.natCells inputs ++
              (SourceParser.natCells 0 ++ cell10 :: rest))) := by
    cases inputs <;> rfl
  have input :=
    inputNat_exact inputs (cell00 :: cell00 :: left)
      (SourceParser.natCells 0 ++ cell10 :: rest)
  have gatesRun :=
    gateNat_exact 0
      (pushCrossed (SourceParser.natCells inputs)
        (cell00 :: cell00 :: left))
      (cell10 :: rest)
  have look :
      workRunExact? headerMachine 1
          (configAtWord State.headerLook
            (pushCrossed (SourceParser.natCells 0)
              (pushCrossed (SourceParser.natCells inputs)
                (cell00 :: cell00 :: left)))
            (cell10 :: rest)) =
        some
          (configAtWord State.reject
            (pushCrossed (SourceParser.natCells 0)
              (pushCrossed (SourceParser.natCells inputs)
                (cell00 :: cell00 :: left)))
            (cell10 :: rest)) := by
    rfl
  have throughInput := exactRun_add headerMachine
    2 (2 * (inputs + 1)) _ _ _ version input
  have throughGates := exactRun_add headerMachine
    (2 + 2 * (inputs + 1)) 2
    _ _ _ throughInput gatesRun
  have all := exactRun_add headerMachine
    (2 + 2 * (inputs + 1) + 2) 1
    _ _ _ throughGates look
  have cost :
      2 + 2 * (inputs + 1) + 2 + 1 =
        headerWorkSteps inputs 0 := by
    unfold headerWorkSteps
    omega
  rw [cost] at all
  simpa [pushCrossed,
    List.reverse_append, List.append_assoc] using all

theorem sourceFirst_input_exact
    (left rest : List WorkSymbol) :
    workRunExact? sourceFirstMachine 1
        (configAtWord State.sourceFirst left
          (cell00 :: rest)) =
      some
        (configAtWord State.accept left
          (cell00 :: rest)) := by
  rfl

theorem sourceFirst_noninput_exact
    (left rest : List WorkSymbol) :
    workRunExact? sourceFirstMachine 1
        (configAtWord State.sourceFirst left
          (cell01 :: rest)) =
      some
        (configAtWord State.reject left
          (cell01 :: rest)) := by
  rfl

theorem nonInput_gate_exact
    (left rest : List WorkSymbol) :
    workRunExact? nonInputMachine 2
        (configAtWord State.nonInputFirst left
          (cell01 :: cell10 :: rest)) =
      some
        (configAtWord State.accept left
          (cell01 :: cell10 :: rest)) := by
  cases left <;> rfl

theorem nonInput_constantFalse_exact
    (left rest : List WorkSymbol) :
    workRunExact? nonInputMachine 2
        (configAtWord State.nonInputFirst left
          (cell01 :: cell00 :: rest)) =
      some
        (configAtWord State.reject left
          (cell01 :: cell00 :: rest)) := by
  cases left <;> rfl

theorem nonInput_constantTrue_exact
    (left rest : List WorkSymbol) :
    workRunExact? nonInputMachine 2
        (configAtWord State.nonInputFirst left
          (cell01 :: cell01 :: rest)) =
      some
        (configAtWord State.reject left
          (cell01 :: cell01 :: rest)) := by
  cases left <;> rfl

theorem constantFalse_exact
    (left rest : List WorkSymbol) :
    workRunExact? constantMachine 2
        (configAtWord State.constantFirst left
          (cell01 :: cell00 :: rest)) =
      some
        (configAtWord State.accept left
          (cell01 :: cell00 :: rest)) := by
  cases left <;> rfl

theorem constantTrue_exact
    (left rest : List WorkSymbol) :
    workRunExact? constantMachine 2
        (configAtWord State.constantFirst left
          (cell01 :: cell01 :: rest)) =
      some
        (configAtWord State.reject left
          (cell01 :: cell01 :: rest)) := by
  cases left <;> rfl

theorem programEnd_exact
    (left rest : List WorkSymbol) (outputFirst : WorkSymbol) :
    workRunExact? programEndMachine 2
        (configAtWord State.programFirst left
          (cell10 :: cell00 :: outputFirst :: rest)) =
      some
        (configAtWord State.accept
          (cell00 :: cell10 :: left)
          (outputFirst :: rest)) := by
  cases rest <;> rfl

theorem gateAdvance_next_exact
    (left rest : List WorkSymbol)
    (first : WorkSymbol)
    (sourceFirst :
      first = cell00 ∨ first = cell01) :
    workRunExact? gateAdvanceMachine 3
        (configAtWord State.gateEndFirst left
          (cell01 :: cell11 :: first :: rest)) =
      some
        (configAtWord State.accept
          (cell11 :: cell01 :: left)
          (first :: rest)) := by
  rcases sourceFirst with rfl | rfl <;> rfl

theorem gateAdvance_programEnd_exact
    (left rest : List WorkSymbol) :
    workRunExact? gateAdvanceMachine 3
        (configAtWord State.gateEndFirst left
          (cell01 :: cell11 :: cell10 :: rest)) =
      some
        (configAtWord State.reject
          (cell11 :: cell01 :: left)
          (cell10 :: rest)) := by
  rfl

theorem malformed_header_enters_dead
    (left rest : List WorkSymbol) :
    workRunExact? headerMachine 1
        (configAtWord State.headerStart left
          (cell01 :: rest)) =
      some
        (configAtWord State.dead left
          (cell01 :: rest)) := by
  rfl

theorem malformed_source_enters_dead
    (left rest : List WorkSymbol) :
    workRunExact? sourceFirstMachine 1
        (configAtWord State.sourceFirst left
          (cell10 :: rest)) =
      some
        (configAtWord State.dead left
          (cell10 :: rest)) := by
  rfl

theorem malformed_gateEnd_enters_dead
    (left rest : List WorkSymbol) :
    workRunExact? gateAdvanceMachine 1
        (configAtWord State.gateEndFirst left
          (cell00 :: rest)) =
      some
        (configAtWord State.dead left
          (cell00 :: rest)) := by
  rfl

end PNP.Concrete.LockedNAND.TargetEmitterNavigator
