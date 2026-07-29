/-
Copyright (c) 2026 PNP Labs.

Literal dynamic check-stack primitives for the locked-NAND target emitter.
The stack begins at the contextual boundary emitted immediately after the
sixth fixed ledger slot.  Records are stored oldest-nearest and
newest-farthest, so successive pushes followed by pops implement the
right-fold order required by the closed emitter plan.

The three executable tables below inspect only the nine-symbol work
alphabet.  They contain no raw circuit, decoded target, semantic program,
external control lookup, or caller-supplied execution certificate.
-/

import PNP.Concrete.LockedNANDTargetEmitterLedger
import PNP.Concrete.PipelineMachineSimulation
import PNP.Concrete.WorkMachineBlankEquivalence

namespace PNP.Concrete.LockedNAND.TargetEmitterCheckStack

open PNP.Concrete

/-! ### Frozen contextual layout -/

def cellBlank : WorkSymbol := TargetEmitterLedger.cellBlank
def sourceLeftBoundary : WorkSymbol :=
  TargetEmitterLedger.sourceLeftBoundary
def unaryUnit : WorkSymbol := TargetEmitterLedger.unaryUnit
def unarySeparator : WorkSymbol :=
  TargetEmitterLedger.unarySeparator
def ledgerBoundary : WorkSymbol :=
  TargetEmitterLedger.ledgerBoundary
def slotBoundary : WorkSymbol :=
  TargetEmitterLedger.slotBoundary
def stackBoundary : WorkSymbol :=
  TargetEmitterLedger.stackBoundary

/-- Start of one dynamic check record.  This symbol is contextual and does
not occur in a canonical fixed ledger payload. -/
def recordBoundary : WorkSymbol := WorkSymbol.oneZero

/-- Unique far end of the dynamic stack. -/
def stackEnd : WorkSymbol := WorkSymbol.zeroZero

/-- Temporary mark for a scratch unit already copied by `pushMachine`. -/
def pushMark : WorkSymbol := WorkSymbol.zeroZero

/-- Temporary mark for the farthest record unit being transferred by
`popMachine`. -/
def popMark : WorkSymbol := WorkSymbol.blankZero

def cursorMarker : WorkSymbol := WorkSymbol.oneBlank

theorem stackBoundary_eq_ledger :
    stackBoundary = TargetEmitterLedger.stackBoundary := by
  rfl

theorem recordBoundary_ne_unaryUnit :
    recordBoundary ≠ unaryUnit := by
  decide

theorem recordBoundary_ne_stackEnd :
    recordBoundary ≠ stackEnd := by
  decide

theorem stackBoundary_ne_stackEnd :
    stackBoundary ≠ stackEnd := by
  decide

theorem pushMark_ne_unaryUnit :
    pushMark ≠ unaryUnit := by
  decide

theorem pushMark_ne_unarySeparator :
    pushMark ≠ unarySeparator := by
  decide

theorem popMark_ne_recordBoundary :
    popMark ≠ recordBoundary := by
  decide

theorem popMark_ne_unaryUnit :
    popMark ≠ unaryUnit := by
  decide

def scratchWord (capacity value : Nat) : List WorkSymbol :=
  List.replicate value unaryUnit ++
    unarySeparator ::
      List.replicate (capacity - value) cellBlank

def recordWord (value : Nat) : List WorkSymbol :=
  recordBoundary :: List.replicate value unaryUnit

/-- Chronological physical order: oldest record nearest the ledger and newest
record adjacent to the far stack end. -/
def recordsWord (checks : List Nat) : List WorkSymbol :=
  checks.flatMap recordWord

def stackWord (checks : List Nat) : List WorkSymbol :=
  stackBoundary :: (recordsWord checks ++ [stackEnd])

/-- A finite exterior list that denotes the implicit all-blank tail. -/
def BlankTail (outsideLeft : List WorkSymbol) : Prop :=
  ∀ index, WorkTape.blankCellAt outsideLeft index = cellBlank

theorem blankTail_nil : BlankTail [] := by
  intro index
  rfl

theorem recordWord_length (value : Nat) :
    (recordWord value).length = value + 1 := by
  simp [recordWord]

theorem recordsWord_append (initial suffix : List Nat) :
    recordsWord (initial ++ suffix) =
      recordsWord initial ++ recordsWord suffix := by
  simp [recordsWord, List.flatMap_append]

theorem recordsWord_push (checks : List Nat) (value : Nat) :
    recordsWord (checks ++ [value]) =
      recordsWord checks ++ recordWord value := by
  simp [recordsWord, recordWord]

theorem stackWord_push_farthest (checks : List Nat) (value : Nat) :
    stackWord (checks ++ [value]) =
      stackBoundary ::
        (recordsWord checks ++ recordWord value ++ [stackEnd]) := by
  simp [stackWord, recordsWord_push, List.append_assoc]

theorem stackWord_empty :
    stackWord [] = [stackBoundary, stackEnd] := by
  rfl

private theorem blankTail_replicate_append
    (count : Nat) (outsideLeft : List WorkSymbol)
    (outsideBlank : BlankTail outsideLeft) :
    BlankTail
      (List.replicate count cellBlank ++ outsideLeft) := by
  intro index
  induction count generalizing index with
  | zero =>
      simpa using outsideBlank index
  | succ count inductionHypothesis =>
      rw [List.replicate_succ]
      cases index with
      | zero =>
          rfl
      | succ index =>
          simpa using inductionHypothesis index

private theorem blankCellAt_append_congr
    (fixedPart firstTail secondTail : List WorkSymbol)
    (tailsAgree :
      ∀ index,
        WorkTape.blankCellAt firstTail index =
          WorkTape.blankCellAt secondTail index)
    (index : Nat) :
    WorkTape.blankCellAt (fixedPart ++ firstTail) index =
      WorkTape.blankCellAt (fixedPart ++ secondTail) index := by
  induction fixedPart generalizing index with
  | nil =>
      simpa using tailsAgree index
  | cons head rest inductionHypothesis =>
      cases index with
      | zero =>
          rfl
      | succ index =>
          simpa using inductionHypothesis index

structure LedgerFits (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters) : Prop where
  inputCount : registers.inputCount ≤ capacity
  normalizedGateCount : registers.normalizedGateCount ≤ capacity
  carrierWidth : registers.carrierWidth ≤ capacity
  baseline : registers.baseline ≤ capacity
  currentGate : registers.currentGate ≤ capacity
  outputIndex : registers.outputIndex ≤ capacity

def sourceAllowed (symbol : WorkSymbol) : Prop :=
  symbol = WorkSymbol.zeroZero ∨
    symbol = WorkSymbol.zeroOne ∨
    symbol = WorkSymbol.oneZero ∨
    symbol = WorkSymbol.oneOne ∨
    symbol = cursorMarker

private instance instDecidableSourceAllowed (symbol : WorkSymbol) :
    Decidable (sourceAllowed symbol) := by
  unfold sourceAllowed
  infer_instance

def scratchPayload (symbol : WorkSymbol) : Prop :=
  symbol = unaryUnit ∨ symbol = unarySeparator ∨
    symbol = cellBlank

private instance instDecidableScratchPayload (symbol : WorkSymbol) :
    Decidable (scratchPayload symbol) := by
  unfold scratchPayload
  infer_instance

def ledgerPayload (symbol : WorkSymbol) : Prop :=
  symbol = slotBoundary ∨ symbol = unaryUnit ∨
    symbol = unarySeparator ∨ symbol = cellBlank

private instance instDecidableLedgerPayload (symbol : WorkSymbol) :
    Decidable (ledgerPayload symbol) := by
  unfold ledgerPayload
  infer_instance

def recordPayload (symbol : WorkSymbol) : Prop :=
  symbol = recordBoundary ∨ symbol = unaryUnit

private instance instDecidableRecordPayload (symbol : WorkSymbol) :
    Decidable (recordPayload symbol) := by
  unfold recordPayload
  infer_instance

theorem scratchWord_length_of_le (capacity value : Nat)
    (bounded : value ≤ capacity) :
    (scratchWord capacity value).length = capacity + 1 := by
  simp [scratchWord]
  omega

theorem slotBank_length (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (fits : LedgerFits capacity registers) :
    (TargetEmitterLedger.slotBank capacity registers).length =
      6 * (capacity + 2) := by
  simp [TargetEmitterLedger.slotBank, TargetEmitterLedger.Slot.all,
    TargetEmitterLedger.slotValue,
    TargetEmitterLedger.slotWord_length_of_le,
    fits.inputCount, fits.normalizedGateCount,
    fits.carrierWidth, fits.baseline,
    fits.currentGate, fits.outputIndex]
  omega

private theorem slotWord_allowed (capacity value : Nat) :
    ∀ symbol, symbol ∈ TargetEmitterLedger.slotWord capacity value →
      ledgerPayload symbol := by
  intro symbol found
  unfold TargetEmitterLedger.slotWord at found
  rw [List.mem_append] at found
  rcases found with inPrefix | blank
  · rw [List.mem_append] at inPrefix
    rcases inPrefix with initial | separator
    · rw [List.mem_append] at initial
      rcases initial with boundary | unit
      · exact Or.inl (List.eq_of_mem_singleton boundary)
      · unfold TargetEmitter.unaryWord at unit
        exact Or.inr (Or.inl
          (List.eq_of_mem_replicate unit))
    · exact Or.inr (Or.inr (Or.inl
        (List.eq_of_mem_singleton separator)))
  · exact Or.inr (Or.inr (Or.inr
      (List.eq_of_mem_replicate blank)))

theorem slotBank_allowed (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters) :
    ∀ symbol,
      symbol ∈ TargetEmitterLedger.slotBank capacity registers →
        ledgerPayload symbol := by
  intro symbol found
  rcases List.mem_flatMap.mp found with
    ⟨slot, _slotFound, symbolFound⟩
  exact slotWord_allowed capacity
    (TargetEmitterLedger.slotValue registers slot)
    symbol symbolFound

theorem recordWord_allowed (value : Nat) :
    ∀ symbol, symbol ∈ recordWord value → recordPayload symbol := by
  intro symbol found
  unfold recordWord at found
  cases found with
  | head =>
      exact Or.inl rfl
  | tail _ inUnits =>
      exact Or.inr (List.eq_of_mem_replicate inUnits)

theorem recordsWord_allowed (checks : List Nat) :
    ∀ symbol, symbol ∈ recordsWord checks → recordPayload symbol := by
  intro symbol found
  rcases List.mem_flatMap.mp found with
    ⟨value, _valueFound, symbolFound⟩
  exact recordWord_allowed value symbol symbolFound

def configAtWord (state : Nat)
    (left word : List WorkSymbol) : WorkConfiguration :=
  TargetEmitter.configAtWord state left word

def configAtLeftWord (state : Nat)
    (leftWord right : List WorkSymbol) : WorkConfiguration :=
  TargetEmitter.configAtLeftWord state leftWord right

/-! ### Literal table materialization -/

def allWorkSymbols : List WorkSymbol :=
  TargetEmitter.allWorkSymbols

structure StateProgram where
  state : Nat
  action : WorkSymbol → Nat × WorkSymbol × HeadMove

def deadAction (dead : Nat) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  (dead, symbol, .stay)

def sourceAction (dead target : Nat) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if sourceAllowed symbol then
    (target, symbol, .left)
  else
    deadAction dead symbol

def expectLeftAction (dead : Nat) (expected : WorkSymbol)
    (target : Nat) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = expected then
    (target, symbol, .left)
  else
    deadAction dead symbol

def expectRightAction (dead : Nat) (expected : WorkSymbol)
    (target : Nat) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = expected then
    (target, symbol, .right)
  else
    deadAction dead symbol

def scratchUnitsLeftAction (dead units reserve : Nat)
    (symbol : WorkSymbol) : Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (units, symbol, .left)
  else if symbol = unarySeparator then
    (reserve, symbol, .left)
  else
    deadAction dead symbol

def scratchReserveLeftAction (dead reserve next : Nat)
    (symbol : WorkSymbol) : Nat × WorkSymbol × HeadMove :=
  if symbol = cellBlank then
    (reserve, symbol, .left)
  else if symbol = ledgerBoundary then
    (next, symbol, .left)
  else
    deadAction dead symbol

def ledgerLeftAction (dead same next : Nat)
    (symbol : WorkSymbol) : Nat × WorkSymbol × HeadMove :=
  if ledgerPayload symbol then
    (same, symbol, .left)
  else if symbol = stackBoundary then
    (next, symbol, .left)
  else
    deadAction dead symbol

def recordLeftAction (dead same endTarget : Nat)
    (endWrite : WorkSymbol) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if recordPayload symbol then
    (same, symbol, .left)
  else if symbol = stackEnd then
    (endTarget, endWrite, .left)
  else
    deadAction dead symbol

def recordRightAction (dead same boundaryTarget : Nat)
    (symbol : WorkSymbol) : Nat × WorkSymbol × HeadMove :=
  if recordPayload symbol then
    (same, symbol, .right)
  else if symbol = stackBoundary then
    (boundaryTarget, symbol, .right)
  else
    deadAction dead symbol

def ledgerRightAction (dead same next : Nat)
    (symbol : WorkSymbol) : Nat × WorkSymbol × HeadMove :=
  if ledgerPayload symbol then
    (same, symbol, .right)
  else if symbol = ledgerBoundary then
    (next, symbol, .right)
  else
    deadAction dead symbol

def scratchRightAction (dead same next : Nat)
    (symbol : WorkSymbol) : Nat × WorkSymbol × HeadMove :=
  if scratchPayload symbol then
    (same, symbol, .right)
  else if symbol = sourceLeftBoundary then
    (next, symbol, .right)
  else
    deadAction dead symbol

def rulesAt (program : StateProgram) : List WorkRule :=
  allWorkSymbols.map fun symbol =>
    let action := program.action symbol
    { sourceState := program.state
      readSymbol := symbol
      targetState := action.1
      writeSymbol := action.2.1
      move := action.2.2 }

def materialize (programs : List StateProgram) : List WorkRule :=
  programs.flatMap rulesAt

def machineOf (programs : List StateProgram)
    (start accept reject : Nat) : WorkMachine :=
  { startState := start
    acceptState := accept
    rejectState := reject
    rules := materialize programs }

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

private theorem rulesAt_pairwise (program : StateProgram) :
    (rulesAt program).Pairwise QueryDistinct := by
  unfold rulesAt allWorkSymbols TargetEmitter.allWorkSymbols
  simp [QueryDistinct,
    WorkSymbol.blank, WorkSymbol.blankZero, WorkSymbol.blankOne,
    WorkSymbol.zeroBlank, WorkSymbol.zeroZero, WorkSymbol.zeroOne,
    WorkSymbol.oneBlank, WorkSymbol.oneZero, WorkSymbol.oneOne]

private theorem rulesAt_source
    {program : StateProgram} {rule : WorkRule}
    (member : rule ∈ rulesAt program) :
    rule.sourceState = program.state := by
  rcases List.mem_map.mp member with
    ⟨symbol, _symbolMember, equality⟩
  rw [← equality]

private theorem materialize_pairwise
    (programs : List StateProgram)
    (distinct :
      programs.Pairwise (fun left right => left.state ≠ right.state)) :
    (materialize programs).Pairwise QueryDistinct := by
  induction programs with
  | nil =>
      simp [materialize]
  | cons program rest ih =>
      rw [materialize, List.flatMap_cons,
        List.pairwise_append]
      refine
        ⟨rulesAt_pairwise program,
          ?_, ?_⟩
      · simpa [materialize] using
          ih (List.pairwise_cons.mp distinct).2
      · intro left leftMember right rightMember
        have leftSource := rulesAt_source leftMember
        rcases List.mem_flatMap.mp rightMember with
          ⟨rightProgram, rightProgramMember, rightRuleMember⟩
        have rightSource := rulesAt_source rightRuleMember
        have stateNe :
            program.state ≠ rightProgram.state :=
          (List.pairwise_cons.mp distinct).1 rightProgram
            rightProgramMember
        unfold QueryDistinct
        intro queryEqual
        exact stateNe
          (leftSource.symm.trans
            ((congrArg Prod.fst queryEqual).trans rightSource))

/-! ### Empty-stack initializer -/

namespace Initialize

def startState : Nat := 100
def boundaryState : Nat := 101
def scratchUnitsState : Nat := 102
def scratchReserveState : Nat := 103
def ledgerState : Nat := 104
def writeEndState : Nat := 105
def returnBoundaryState : Nat := 106
def returnLedgerState : Nat := 107
def returnScratchState : Nat := 108
def acceptState : Nat := 109
def rejectState : Nat := 110
def deadState : Nat := 111

def writeEndAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = cellBlank then
    (returnBoundaryState, stackEnd, .right)
  else
    deadAction deadState symbol

def statePrograms : List StateProgram :=
  [ { state := startState
      action := sourceAction deadState boundaryState }
  , { state := boundaryState
      action :=
        expectLeftAction deadState sourceLeftBoundary
          scratchUnitsState }
  , { state := scratchUnitsState
      action :=
        scratchUnitsLeftAction deadState scratchUnitsState
          scratchReserveState }
  , { state := scratchReserveState
      action :=
        scratchReserveLeftAction deadState scratchReserveState
          ledgerState }
  , { state := ledgerState
      action :=
        ledgerLeftAction deadState ledgerState writeEndState }
  , { state := writeEndState
      action := writeEndAction }
  , { state := returnBoundaryState
      action :=
        expectRightAction deadState stackBoundary
          returnLedgerState }
  , { state := returnLedgerState
      action :=
        ledgerRightAction deadState returnLedgerState
          returnScratchState }
  , { state := returnScratchState
      action :=
        scratchRightAction deadState returnScratchState
          acceptState } ]

def rules : List WorkRule := materialize statePrograms

def machine : WorkMachine :=
  machineOf statePrograms startState acceptState rejectState

def compiledMachine : Machine := compileWorkMachine machine

theorem statePrograms_length :
    statePrograms.length = 9 := by
  rfl

theorem rules_length :
    rules.length = 81 := by
  rfl

set_option maxRecDepth 300000 in
private theorem statePrograms_pairwise :
    statePrograms.Pairwise
      (fun left right => left.state ≠ right.state) := by
  decide

theorem rules_pairwise :
    rules.Pairwise QueryDistinct :=
  materialize_pairwise statePrograms statePrograms_pairwise

theorem start_ne_accept :
    machine.startState ≠ machine.acceptState := by
  decide

theorem start_ne_reject :
    machine.startState ≠ machine.rejectState := by
  decide

theorem accept_ne_reject :
    machine.acceptState ≠ machine.rejectState := by
  decide

set_option maxRecDepth 300000 in
theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule rules acceptState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 300000 in
theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules rejectState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 300000 in
theorem no_rule_at_dead (symbol : WorkSymbol) :
    findWorkRule rules deadState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

end Initialize

/-! ### Scratch-preserving farthest push -/

namespace Push

def startState : Nat := 200
def boundaryState : Nat := 201
def scratchUnitsState : Nat := 202
def scratchReserveState : Nat := 203
def ledgerState : Nat := 204
def stackState : Nat := 205
def appendEndState : Nat := 206
def setupReturnStackState : Nat := 207
def setupReturnLedgerState : Nat := 208
def setupReturnScratchState : Nat := 209
def selectStartState : Nat := 210
def selectBoundaryState : Nat := 211
def selectedState : Nat := 212
def selectedDelayState : Nat := 213
def bounceScratchState : Nat := 214
def bounceLedgerState : Nat := 215
def bounceStackState : Nat := 216
def appendUnitState : Nat := 217
def cycleReturnStackState : Nat := 218
def cycleReturnLedgerState : Nat := 219
def seekMarkState : Nat := 220
def restoreState : Nat := 221
def acceptState : Nat := 222
def rejectState : Nat := 223
def deadState : Nat := 224

def stackAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if recordPayload symbol then
    (stackState, symbol, .left)
  else if symbol = stackEnd then
    (appendEndState, recordBoundary, .left)
  else
    deadAction deadState symbol

def appendEndAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = cellBlank then
    (setupReturnStackState, stackEnd, .right)
  else
    deadAction deadState symbol

def selectedAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = pushMark then
    (selectedDelayState, symbol, .stay)
  else if symbol = unaryUnit then
    (bounceScratchState, pushMark, .left)
  else if symbol = unarySeparator then
    (restoreState, symbol, .right)
  else
    deadAction deadState symbol

def selectedDelayAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = pushMark then
    (selectedState, symbol, .left)
  else
    deadAction deadState symbol

def bounceScratchAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if scratchPayload symbol then
    (bounceScratchState, symbol, .left)
  else if symbol = ledgerBoundary then
    (bounceLedgerState, symbol, .left)
  else
    deadAction deadState symbol

def bounceLedgerAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if ledgerPayload symbol then
    (bounceLedgerState, symbol, .left)
  else if symbol = stackBoundary then
    (bounceStackState, symbol, .left)
  else
    deadAction deadState symbol

def bounceStackAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if recordPayload symbol then
    (bounceStackState, symbol, .left)
  else if symbol = stackEnd then
    (appendUnitState, unaryUnit, .left)
  else
    deadAction deadState symbol

def appendUnitAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = cellBlank then
    (cycleReturnStackState, stackEnd, .right)
  else
    deadAction deadState symbol

def cycleReturnLedgerAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if ledgerPayload symbol then
    (cycleReturnLedgerState, symbol, .right)
  else if symbol = ledgerBoundary then
    (seekMarkState, symbol, .right)
  else
    deadAction deadState symbol

def seekMarkAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if scratchPayload symbol then
    (seekMarkState, symbol, .right)
  else if symbol = pushMark then
    (selectedState, symbol, .stay)
  else
    deadAction deadState symbol

def restoreAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = pushMark then
    (restoreState, unaryUnit, .right)
  else if symbol = sourceLeftBoundary then
    (acceptState, symbol, .right)
  else
    deadAction deadState symbol

def statePrograms : List StateProgram :=
  [ { state := startState
      action := sourceAction deadState boundaryState }
  , { state := boundaryState
      action :=
        expectLeftAction deadState sourceLeftBoundary
          scratchUnitsState }
  , { state := scratchUnitsState
      action :=
        scratchUnitsLeftAction deadState scratchUnitsState
          scratchReserveState }
  , { state := scratchReserveState
      action :=
        scratchReserveLeftAction deadState scratchReserveState
          ledgerState }
  , { state := ledgerState
      action :=
        ledgerLeftAction deadState ledgerState stackState }
  , { state := stackState
      action := stackAction }
  , { state := appendEndState
      action := appendEndAction }
  , { state := setupReturnStackState
      action :=
        recordRightAction deadState setupReturnStackState
          setupReturnLedgerState }
  , { state := setupReturnLedgerState
      action :=
        ledgerRightAction deadState setupReturnLedgerState
          setupReturnScratchState }
  , { state := setupReturnScratchState
      action :=
        scratchRightAction deadState setupReturnScratchState
          selectStartState }
  , { state := selectStartState
      action := sourceAction deadState selectBoundaryState }
  , { state := selectBoundaryState
      action :=
        expectLeftAction deadState sourceLeftBoundary
          selectedState }
  , { state := selectedState
      action := selectedAction }
  , { state := selectedDelayState
      action := selectedDelayAction }
  , { state := bounceScratchState
      action := bounceScratchAction }
  , { state := bounceLedgerState
      action := bounceLedgerAction }
  , { state := bounceStackState
      action := bounceStackAction }
  , { state := appendUnitState
      action := appendUnitAction }
  , { state := cycleReturnStackState
      action :=
        recordRightAction deadState cycleReturnStackState
          cycleReturnLedgerState }
  , { state := cycleReturnLedgerState
      action := cycleReturnLedgerAction }
  , { state := seekMarkState
      action := seekMarkAction }
  , { state := restoreState
      action := restoreAction } ]

def rules : List WorkRule := materialize statePrograms

def machine : WorkMachine :=
  machineOf statePrograms startState acceptState rejectState

def compiledMachine : Machine := compileWorkMachine machine

theorem statePrograms_length :
    statePrograms.length = 22 := by
  rfl

theorem rules_length :
    rules.length = 198 := by
  rfl

set_option maxRecDepth 300000 in
private theorem statePrograms_pairwise :
    statePrograms.Pairwise
      (fun left right => left.state ≠ right.state) := by
  decide

theorem rules_pairwise :
    rules.Pairwise QueryDistinct :=
  materialize_pairwise statePrograms statePrograms_pairwise

theorem start_ne_accept :
    machine.startState ≠ machine.acceptState := by
  decide

theorem start_ne_reject :
    machine.startState ≠ machine.rejectState := by
  decide

theorem accept_ne_reject :
    machine.acceptState ≠ machine.rejectState := by
  decide

set_option maxRecDepth 300000 in
theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule rules acceptState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 300000 in
theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules rejectState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 300000 in
theorem no_rule_at_dead (symbol : WorkSymbol) :
    findWorkRule rules deadState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

end Push

/-! ### Conditional newest-record pop into zero scratch -/

namespace Pop

def startState : Nat := 300
def boundaryState : Nat := 301
def scratchZeroState : Nat := 302
def scratchReserveState : Nat := 303
def ledgerState : Nat := 304
def stackMaybeState : Nat := 305
def stackNonemptyState : Nat := 306
def recordState : Nat := 307
def bounceStackState : Nat := 308
def bounceLedgerState : Nat := 309
def bounceScratchState : Nat := 310
def incrementStartState : Nat := 311
def incrementBoundaryState : Nat := 312
def incrementSeekState : Nat := 313
def incrementWriteState : Nat := 314
def incrementReturnState : Nat := 315
def resumeStartState : Nat := 316
def resumeBoundaryState : Nat := 317
def resumeScratchUnitsState : Nat := 318
def resumeScratchReserveState : Nat := 319
def resumeLedgerState : Nat := 320
def resumeStackState : Nat := 321
def eraseOldContinueState : Nat := 322
def crossNewContinueState : Nat := 323
def eraseOldFinishState : Nat := 324
def crossNewFinishState : Nat := 325
def returnStackState : Nat := 326
def returnLedgerState : Nat := 327
def returnScratchState : Nat := 328
def emptyReturnBoundaryState : Nat := 329
def emptyReturnLedgerState : Nat := 330
def emptyReturnScratchState : Nat := 331
def acceptState : Nat := 332
def rejectState : Nat := 333
def deadState : Nat := 334

def scratchZeroAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unarySeparator then
    (scratchReserveState, symbol, .left)
  else
    deadAction deadState symbol

def stackMaybeAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = stackEnd then
    (emptyReturnBoundaryState, symbol, .right)
  else if symbol = recordBoundary then
    (stackNonemptyState, symbol, .left)
  else
    deadAction deadState symbol

def stackNonemptyAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if recordPayload symbol then
    (stackNonemptyState, symbol, .left)
  else if symbol = stackEnd then
    (recordState, stackEnd, .right)
  else
    deadAction deadState symbol

def recordAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (bounceStackState, popMark, .right)
  else if symbol = recordBoundary then
    (eraseOldFinishState, stackEnd, .left)
  else
    deadAction deadState symbol

def bounceStackAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if recordPayload symbol then
    (bounceStackState, symbol, .right)
  else if symbol = stackBoundary then
    (bounceLedgerState, symbol, .right)
  else
    deadAction deadState symbol

def bounceLedgerAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if ledgerPayload symbol then
    (bounceLedgerState, symbol, .right)
  else if symbol = ledgerBoundary then
    (bounceScratchState, symbol, .right)
  else
    deadAction deadState symbol

def bounceScratchAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if scratchPayload symbol then
    (bounceScratchState, symbol, .right)
  else if symbol = sourceLeftBoundary then
    (incrementStartState, symbol, .right)
  else
    deadAction deadState symbol

def incrementSeekAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (incrementSeekState, symbol, .left)
  else if symbol = unarySeparator then
    (incrementWriteState, unaryUnit, .left)
  else
    deadAction deadState symbol

def incrementWriteAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = cellBlank then
    (incrementReturnState, unarySeparator, .right)
  else
    deadAction deadState symbol

def incrementReturnAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (incrementReturnState, symbol, .right)
  else if symbol = sourceLeftBoundary then
    (resumeStartState, symbol, .right)
  else
    deadAction deadState symbol

def resumeLedgerAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if ledgerPayload symbol then
    (resumeLedgerState, symbol, .left)
  else if symbol = stackBoundary then
    (resumeStackState, symbol, .left)
  else
    deadAction deadState symbol

def resumeStackAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if recordPayload symbol then
    (resumeStackState, symbol, .left)
  else if symbol = popMark then
    (eraseOldContinueState, stackEnd, .left)
  else
    deadAction deadState symbol

def eraseOldAction (next : Nat) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = stackEnd then
    (next, cellBlank, .right)
  else
    deadAction deadState symbol

def crossNewAction (next : Nat) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = stackEnd then
    (next, symbol, .right)
  else
    deadAction deadState symbol

def statePrograms : List StateProgram :=
  [ { state := startState
      action := sourceAction deadState boundaryState }
  , { state := boundaryState
      action :=
        expectLeftAction deadState sourceLeftBoundary
          scratchZeroState }
  , { state := scratchZeroState
      action := scratchZeroAction }
  , { state := scratchReserveState
      action :=
        scratchReserveLeftAction deadState scratchReserveState
          ledgerState }
  , { state := ledgerState
      action :=
        ledgerLeftAction deadState ledgerState stackMaybeState }
  , { state := stackMaybeState
      action := stackMaybeAction }
  , { state := stackNonemptyState
      action := stackNonemptyAction }
  , { state := recordState
      action := recordAction }
  , { state := bounceStackState
      action := bounceStackAction }
  , { state := bounceLedgerState
      action := bounceLedgerAction }
  , { state := bounceScratchState
      action := bounceScratchAction }
  , { state := incrementStartState
      action :=
        sourceAction deadState incrementBoundaryState }
  , { state := incrementBoundaryState
      action :=
        expectLeftAction deadState sourceLeftBoundary
          incrementSeekState }
  , { state := incrementSeekState
      action := incrementSeekAction }
  , { state := incrementWriteState
      action := incrementWriteAction }
  , { state := incrementReturnState
      action := incrementReturnAction }
  , { state := resumeStartState
      action := sourceAction deadState resumeBoundaryState }
  , { state := resumeBoundaryState
      action :=
        expectLeftAction deadState sourceLeftBoundary
          resumeScratchUnitsState }
  , { state := resumeScratchUnitsState
      action :=
        scratchUnitsLeftAction deadState resumeScratchUnitsState
          resumeScratchReserveState }
  , { state := resumeScratchReserveState
      action :=
        scratchReserveLeftAction deadState
          resumeScratchReserveState resumeLedgerState }
  , { state := resumeLedgerState
      action := resumeLedgerAction }
  , { state := resumeStackState
      action := resumeStackAction }
  , { state := eraseOldContinueState
      action := eraseOldAction crossNewContinueState }
  , { state := crossNewContinueState
      action := crossNewAction recordState }
  , { state := eraseOldFinishState
      action := eraseOldAction crossNewFinishState }
  , { state := crossNewFinishState
      action := crossNewAction returnStackState }
  , { state := returnStackState
      action :=
        recordRightAction deadState returnStackState
          returnLedgerState }
  , { state := returnLedgerState
      action :=
        ledgerRightAction deadState returnLedgerState
          returnScratchState }
  , { state := returnScratchState
      action :=
        scratchRightAction deadState returnScratchState
          acceptState }
  , { state := emptyReturnBoundaryState
      action :=
        expectRightAction deadState stackBoundary
          emptyReturnLedgerState }
  , { state := emptyReturnLedgerState
      action :=
        ledgerRightAction deadState emptyReturnLedgerState
          emptyReturnScratchState }
  , { state := emptyReturnScratchState
      action :=
        scratchRightAction deadState emptyReturnScratchState
          rejectState } ]

def rules : List WorkRule := materialize statePrograms

def machine : WorkMachine :=
  machineOf statePrograms startState acceptState rejectState

def compiledMachine : Machine := compileWorkMachine machine

theorem statePrograms_length :
    statePrograms.length = 32 := by
  rfl

set_option maxRecDepth 1000000 in
theorem rules_length :
    rules.length = 288 := by
  rfl

set_option maxRecDepth 1000000 in
private theorem statePrograms_pairwise :
    statePrograms.Pairwise
      (fun left right => left.state ≠ right.state) := by
  decide

theorem rules_pairwise :
    rules.Pairwise QueryDistinct :=
  materialize_pairwise statePrograms statePrograms_pairwise

theorem start_ne_accept :
    machine.startState ≠ machine.acceptState := by
  decide

theorem start_ne_reject :
    machine.startState ≠ machine.rejectState := by
  decide

theorem accept_ne_reject :
    machine.acceptState ≠ machine.rejectState := by
  decide

set_option maxRecDepth 300000 in
theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule rules acceptState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 300000 in
theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules rejectState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 300000 in
theorem no_rule_at_dead (symbol : WorkSymbol) :
    findWorkRule rules deadState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

end Pop

/-! ### Shared exact-run infrastructure -/

private def literalRule (source : Nat) (read : WorkSymbol)
    (target : Nat) (write : WorkSymbol) (move : HeadMove) :
    WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := write
    move := move }

private theorem exactRun_add (machine : WorkMachine)
    (first second : Nat)
    (initial middle final : WorkConfiguration)
    (hFirst :
      workRunExact? machine first initial = some middle)
    (hSecond :
      workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) initial = some final :=
  PipelineMachineSimulation.workRunExact?_compose
    machine first second initial middle final hFirst hSecond

private theorem exactRun_one (machine : WorkMachine)
    (initial final : WorkConfiguration)
    (step : workStep? machine initial = some final) :
    workRunExact? machine 1 initial = some final := by
  change
    (match workStep? machine initial with
     | none => none
     | some next => workRunExact? machine 0 next) = some final
  rw [step]
  rfl

private theorem moveLeftFromWord_of_find
    (machine : WorkMachine) (rules : List WorkRule)
    (rulesEq : machine.rules = rules)
    (state target : Nat) (symbol write : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      machine.isHalted
        (configAtWord state left (symbol :: right)) = false)
    (found :
      findWorkRule rules state symbol =
        some (literalRule state symbol target write .left)) :
    workStep? machine
        (configAtWord state left (symbol :: right)) =
      some (configAtLeftWord target left (write :: right)) := by
  calc
    workStep? machine
        (configAtWord state left (symbol :: right)) =
      some (applyWorkRule
        (literalRule state symbol target write .left)
        (configAtWord state left (symbol :: right))) := by
          apply workStep?_eq_apply_of_find
          · exact notHalted
          · rw [rulesEq]
            exact found
    _ = some (configAtLeftWord target left (write :: right)) := by
      cases left <;> rfl

private theorem moveLeftFromLeftWord_of_find
    (machine : WorkMachine) (rules : List WorkRule)
    (rulesEq : machine.rules = rules)
    (state target : Nat) (symbol write : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      machine.isHalted
        (configAtLeftWord state (symbol :: left) right) = false)
    (found :
      findWorkRule rules state symbol =
        some (literalRule state symbol target write .left)) :
    workStep? machine
        (configAtLeftWord state (symbol :: left) right) =
      some (configAtLeftWord target left (write :: right)) := by
  calc
    workStep? machine
        (configAtLeftWord state (symbol :: left) right) =
      some (applyWorkRule
        (literalRule state symbol target write .left)
        (configAtLeftWord state (symbol :: left) right)) := by
          apply workStep?_eq_apply_of_find
          · exact notHalted
          · rw [rulesEq]
            exact found
    _ = some (configAtLeftWord target left (write :: right)) := by
      cases left <;> rfl

private theorem moveRightFromLeftWord_of_find
    (machine : WorkMachine) (rules : List WorkRule)
    (rulesEq : machine.rules = rules)
    (state target : Nat) (symbol write : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      machine.isHalted
        (configAtLeftWord state (symbol :: left) right) = false)
    (found :
      findWorkRule rules state symbol =
        some (literalRule state symbol target write .right)) :
    workStep? machine
        (configAtLeftWord state (symbol :: left) right) =
      some (configAtWord target (write :: left) right) := by
  calc
    workStep? machine
        (configAtLeftWord state (symbol :: left) right) =
      some (applyWorkRule
        (literalRule state symbol target write .right)
        (configAtLeftWord state (symbol :: left) right)) := by
          apply workStep?_eq_apply_of_find
          · exact notHalted
          · rw [rulesEq]
            exact found
    _ = some (configAtWord target (write :: left) right) := by
      cases right <;> rfl

private theorem moveRightFromWord_of_find
    (machine : WorkMachine) (rules : List WorkRule)
    (rulesEq : machine.rules = rules)
    (state target : Nat) (symbol write : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      machine.isHalted
        (configAtWord state left (symbol :: right)) = false)
    (found :
      findWorkRule rules state symbol =
        some (literalRule state symbol target write .right)) :
    workStep? machine
        (configAtWord state left (symbol :: right)) =
      some (configAtWord target (write :: left) right) := by
  calc
    workStep? machine
        (configAtWord state left (symbol :: right)) =
      some (applyWorkRule
        (literalRule state symbol target write .right)
        (configAtWord state left (symbol :: right))) := by
          apply workStep?_eq_apply_of_find
          · exact notHalted
          · rw [rulesEq]
            exact found
    _ = some (configAtWord target (write :: left) right) := by
      cases right <;> rfl

private theorem stayAtWord_of_find
    (machine : WorkMachine) (rules : List WorkRule)
    (rulesEq : machine.rules = rules)
    (state target : Nat) (symbol write : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      machine.isHalted
        (configAtWord state left (symbol :: right)) = false)
    (found :
      findWorkRule rules state symbol =
        some (literalRule state symbol target write .stay)) :
    workStep? machine
        (configAtWord state left (symbol :: right)) =
      some (configAtWord target left (write :: right)) := by
  calc
    workStep? machine
        (configAtWord state left (symbol :: right)) =
      some (applyWorkRule
        (literalRule state symbol target write .stay)
        (configAtWord state left (symbol :: right))) := by
          apply workStep?_eq_apply_of_find
          · exact notHalted
          · rw [rulesEq]
            exact found
    _ = some (configAtWord target left (write :: right)) := by
      rfl

private theorem scanLeftExact (machine : WorkMachine)
    (state : Nat) (Allowed : WorkSymbol → Prop)
    (hStep : ∀ head leftTail rightSide,
      Allowed head →
      workStep? machine
          (configAtLeftWord state (head :: leftTail) rightSide) =
        some (configAtLeftWord state
          leftTail (head :: rightSide)))
    (word leftSuffix rightSide : List WorkSymbol)
    (hAllowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? machine word.length
        (configAtLeftWord state
          (word ++ leftSuffix) rightSide) =
      some (configAtLeftWord state leftSuffix
        (word.reverse ++ rightSide)) := by
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
        (match workStep? machine
          (configAtLeftWord state
            (head :: (rest ++ leftSuffix)) rightSide) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) = _
      rw [hStep head (rest ++ leftSuffix) rightSide headAllowed]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (head :: rightSide) restAllowed

private theorem scanRightExact (machine : WorkMachine)
    (state : Nat) (Allowed : WorkSymbol → Prop)
    (hStep : ∀ leftSide head suffix,
      Allowed head →
      workStep? machine
          (configAtWord state leftSide (head :: suffix)) =
        some (configAtWord state (head :: leftSide) suffix))
    (word suffix leftSide : List WorkSymbol)
    (hAllowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? machine word.length
        (configAtWord state leftSide (word ++ suffix)) =
      some (configAtWord state
        (word.reverse ++ leftSide) suffix) := by
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
        (match workStep? machine
          (configAtWord state leftSide
            (head :: (rest ++ suffix))) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) = _
      rw [hStep leftSide head (rest ++ suffix) headAllowed]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (head :: leftSide) restAllowed

/-! ### Exact empty-stack initialization -/

namespace Initialize

def entryConfiguration (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord startState
    (sourceLeftBoundary ::
      (scratchWord capacity scratch ++
        ledgerBoundary ::
          (TargetEmitterLedger.slotBank capacity registers ++
            stackBoundary :: cellBlank :: outsideLeft)))
    (sourceHead :: sourceTail ++ targetAndRight)

def finalConfiguration (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord acceptState
    (sourceLeftBoundary ::
      (scratchWord capacity scratch ++
        ledgerBoundary ::
          (TargetEmitterLedger.slotBank capacity registers ++
            stackWord [] ++ outsideLeft)))
    (sourceHead :: sourceTail ++ targetAndRight)

def workSteps (capacity : Nat) : Nat :=
  14 * capacity + 34

def polynomialWorkBound (capacity : Nat) : Nat :=
  14 * capacity + 34

theorem workSteps_le_polynomialWorkBound (capacity : Nat) :
    workSteps capacity ≤ polynomialWorkBound capacity := by
  exact Nat.le_refl _

set_option maxRecDepth 300000 in
private theorem find_start
    (symbol : WorkSymbol) (allowed : sourceAllowed symbol) :
    findWorkRule rules startState symbol =
      some (literalRule startState symbol
        boundaryState symbol .left) := by
  rcases allowed with a | b | c | d | e
  all_goals subst symbol
  all_goals decide

set_option maxRecDepth 300000 in
private theorem find_boundary :
    findWorkRule rules boundaryState sourceLeftBoundary =
      some (literalRule boundaryState sourceLeftBoundary
        scratchUnitsState sourceLeftBoundary .left) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_scratch_unit :
    findWorkRule rules scratchUnitsState unaryUnit =
      some (literalRule scratchUnitsState unaryUnit
        scratchUnitsState unaryUnit .left) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_scratch_separator :
    findWorkRule rules scratchUnitsState unarySeparator =
      some (literalRule scratchUnitsState unarySeparator
        scratchReserveState unarySeparator .left) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_scratch_blank :
    findWorkRule rules scratchReserveState cellBlank =
      some (literalRule scratchReserveState cellBlank
        scratchReserveState cellBlank .left) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_ledger_boundary :
    findWorkRule rules scratchReserveState ledgerBoundary =
      some (literalRule scratchReserveState ledgerBoundary
        ledgerState ledgerBoundary .left) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_ledger (symbol : WorkSymbol)
    (allowed : ledgerPayload symbol) :
    findWorkRule rules ledgerState symbol =
      some (literalRule ledgerState symbol
        ledgerState symbol .left) := by
  rcases allowed with a | b | c | d
  all_goals subst symbol
  all_goals decide

set_option maxRecDepth 300000 in
private theorem find_stack_boundary :
    findWorkRule rules ledgerState stackBoundary =
      some (literalRule ledgerState stackBoundary
        writeEndState stackBoundary .left) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_write_blank :
    findWorkRule rules writeEndState cellBlank =
      some (literalRule writeEndState cellBlank
        returnBoundaryState stackEnd .right) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_return_stack_boundary :
    findWorkRule rules returnBoundaryState stackBoundary =
      some (literalRule returnBoundaryState stackBoundary
        returnLedgerState stackBoundary .right) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_return_ledger (symbol : WorkSymbol)
    (allowed : ledgerPayload symbol) :
    findWorkRule rules returnLedgerState symbol =
      some (literalRule returnLedgerState symbol
        returnLedgerState symbol .right) := by
  rcases allowed with a | b | c | d
  all_goals subst symbol
  all_goals decide

set_option maxRecDepth 300000 in
private theorem find_return_ledger_boundary :
    findWorkRule rules returnLedgerState ledgerBoundary =
      some (literalRule returnLedgerState ledgerBoundary
        returnScratchState ledgerBoundary .right) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_return_scratch (symbol : WorkSymbol)
    (allowed : scratchPayload symbol) :
    findWorkRule rules returnScratchState symbol =
      some (literalRule returnScratchState symbol
        returnScratchState symbol .right) := by
  rcases allowed with a | b | c
  all_goals subst symbol
  all_goals decide

set_option maxRecDepth 300000 in
private theorem find_return_source_boundary :
    findWorkRule rules returnScratchState sourceLeftBoundary =
      some (literalRule returnScratchState sourceLeftBoundary
        acceptState sourceLeftBoundary .right) := by
  decide

private theorem start_step (symbol : WorkSymbol)
    (allowed : sourceAllowed symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord startState left (symbol :: right)) =
      some (configAtLeftWord boundaryState
        left (symbol :: right)) := by
  apply moveLeftFromWord_of_find machine rules rfl
  · rfl
  · exact find_start symbol allowed

private theorem boundary_step (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord boundaryState
          (sourceLeftBoundary :: left) right) =
      some (configAtLeftWord scratchUnitsState
        left (sourceLeftBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · exact find_boundary

private theorem scratch_unit_step (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord scratchUnitsState
          (unaryUnit :: left) right) =
      some (configAtLeftWord scratchUnitsState
        left (unaryUnit :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · exact find_scratch_unit

private theorem scratch_separator_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord scratchUnitsState
          (unarySeparator :: left) right) =
      some (configAtLeftWord scratchReserveState
        left (unarySeparator :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · exact find_scratch_separator

private theorem scratch_blank_step (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord scratchReserveState
          (cellBlank :: left) right) =
      some (configAtLeftWord scratchReserveState
        left (cellBlank :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · exact find_scratch_blank

private theorem ledger_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord scratchReserveState
          (ledgerBoundary :: left) right) =
      some (configAtLeftWord ledgerState
        left (ledgerBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · exact find_ledger_boundary

private theorem ledger_step (symbol : WorkSymbol)
    (allowed : ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord ledgerState
          (symbol :: left) right) =
      some (configAtLeftWord ledgerState
        left (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · exact find_ledger symbol allowed

private theorem stack_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord ledgerState
          (stackBoundary :: left) right) =
      some (configAtLeftWord writeEndState
        left (stackBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · exact find_stack_boundary

private theorem write_blank_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord writeEndState
          (cellBlank :: left) right) =
      some (configAtWord returnBoundaryState
        (stackEnd :: left) right) := by
  apply moveRightFromLeftWord_of_find machine rules rfl
  · rfl
  · exact find_write_blank

private theorem return_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord returnBoundaryState left
          (stackBoundary :: right)) =
      some (configAtWord returnLedgerState
        (stackBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · exact find_return_stack_boundary

private theorem return_ledger_step (symbol : WorkSymbol)
    (allowed : ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord returnLedgerState left
          (symbol :: right)) =
      some (configAtWord returnLedgerState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · exact find_return_ledger symbol allowed

private theorem return_ledger_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord returnLedgerState left
          (ledgerBoundary :: right)) =
      some (configAtWord returnScratchState
        (ledgerBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · exact find_return_ledger_boundary

private theorem return_scratch_step (symbol : WorkSymbol)
    (allowed : scratchPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord returnScratchState left
          (symbol :: right)) =
      some (configAtWord returnScratchState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · exact find_return_scratch symbol allowed

private theorem return_source_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord returnScratchState left
          (sourceLeftBoundary :: right)) =
      some (configAtWord acceptState
        (sourceLeftBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · exact find_return_source_boundary

theorem exact (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (scratchBound : scratch ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    workRunExact? machine (workSteps capacity)
        (entryConfiguration capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) =
      some (finalConfiguration capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft) := by
  let scratchW := scratchWord capacity scratch
  let bank := TargetEmitterLedger.slotBank capacity registers
  let source := sourceHead :: sourceTail ++ targetAndRight
  let afterSource :=
    configAtLeftWord boundaryState
      (sourceLeftBoundary :: scratchW ++
        ledgerBoundary :: bank ++
          stackBoundary :: cellBlank :: outsideLeft)
      source
  let afterBoundary :=
    configAtLeftWord scratchUnitsState
      (scratchW ++ ledgerBoundary :: bank ++
        stackBoundary :: cellBlank :: outsideLeft)
      (sourceLeftBoundary :: source)
  let atSeparator :=
    configAtLeftWord scratchUnitsState
      (unarySeparator ::
        List.replicate (capacity - scratch) cellBlank ++
          ledgerBoundary :: bank ++
            stackBoundary :: cellBlank :: outsideLeft)
      (List.replicate scratch unaryUnit ++
        sourceLeftBoundary :: source)
  let afterSeparator :=
    configAtLeftWord scratchReserveState
      (List.replicate (capacity - scratch) cellBlank ++
        ledgerBoundary :: bank ++
          stackBoundary :: cellBlank :: outsideLeft)
      (unarySeparator ::
        List.replicate scratch unaryUnit ++
          sourceLeftBoundary :: source)
  let atLedger :=
    configAtLeftWord scratchReserveState
      (ledgerBoundary :: bank ++
        stackBoundary :: cellBlank :: outsideLeft)
      (scratchW.reverse ++ sourceLeftBoundary :: source)
  let atStackBoundary :=
    configAtLeftWord ledgerState
      (stackBoundary :: cellBlank :: outsideLeft)
      (bank.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: source)
  let atBlank :=
    configAtLeftWord writeEndState
      (cellBlank :: outsideLeft)
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: source)
  let returningBoundary :=
    configAtWord returnBoundaryState
      (stackEnd :: outsideLeft)
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: source)
  let returningLedger :=
    configAtWord returnLedgerState
      (stackBoundary :: stackEnd :: outsideLeft)
      (bank.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: source)
  let returningLedgerBoundary :=
    configAtWord returnLedgerState
      (bank ++ stackBoundary :: stackEnd :: outsideLeft)
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: source)
  let returningScratch :=
    configAtWord returnScratchState
      (ledgerBoundary :: bank ++
        stackBoundary :: stackEnd :: outsideLeft)
      (scratchW.reverse ++ sourceLeftBoundary :: source)
  let returningSource :=
    configAtWord returnScratchState
      (scratchW ++ ledgerBoundary :: bank ++
        stackBoundary :: stackEnd :: outsideLeft)
      (sourceLeftBoundary :: source)
  have hSource :
      workRunExact? machine 1
          (entryConfiguration capacity scratch registers
            sourceHead sourceTail targetAndRight outsideLeft) =
        some afterSource := by
    apply exactRun_one machine
    simpa [entryConfiguration, afterSource, scratchW, bank,
      source, List.append_assoc] using
      start_step sourceHead allowed
        (sourceLeftBoundary :: scratchW ++
          ledgerBoundary :: bank ++
            stackBoundary :: cellBlank :: outsideLeft)
        (sourceTail ++ targetAndRight)
  have hBoundary :
      workRunExact? machine 1 afterSource =
        some afterBoundary := by
    apply exactRun_one machine
    simpa [afterSource, afterBoundary] using
      boundary_step
        (scratchW ++ ledgerBoundary :: bank ++
          stackBoundary :: cellBlank :: outsideLeft)
        source
  have hUnits :
      workRunExact? machine scratch afterBoundary =
        some atSeparator := by
    have scanned := scanLeftExact machine scratchUnitsState
      (fun symbol => symbol = unaryUnit)
      (by
        intro head leftTail rightSide equality
        subst head
        exact scratch_unit_step leftTail rightSide)
      (List.replicate scratch unaryUnit)
      (unarySeparator ::
        List.replicate (capacity - scratch) cellBlank ++
          ledgerBoundary :: bank ++
            stackBoundary :: cellBlank :: outsideLeft)
      (sourceLeftBoundary :: source)
      (by
        intro symbol found
        exact List.eq_of_mem_replicate found)
    simpa [afterBoundary, atSeparator, scratchW, scratchWord,
      List.append_assoc] using scanned
  have hSeparator :
      workRunExact? machine 1 atSeparator =
        some afterSeparator := by
    apply exactRun_one machine
    simpa [atSeparator, afterSeparator] using
      scratch_separator_step
        (List.replicate (capacity - scratch) cellBlank ++
          ledgerBoundary :: bank ++
            stackBoundary :: cellBlank :: outsideLeft)
        (List.replicate scratch unaryUnit ++
          sourceLeftBoundary :: source)
  have hReserve :
      workRunExact? machine (capacity - scratch) afterSeparator =
        some atLedger := by
    have scanned := scanLeftExact machine scratchReserveState
      (fun symbol => symbol = cellBlank)
      (by
        intro head leftTail rightSide equality
        subst head
        exact scratch_blank_step leftTail rightSide)
      (List.replicate (capacity - scratch) cellBlank)
      (ledgerBoundary :: bank ++
        stackBoundary :: cellBlank :: outsideLeft)
      (unarySeparator ::
        List.replicate scratch unaryUnit ++
          sourceLeftBoundary :: source)
      (by
        intro symbol found
        exact List.eq_of_mem_replicate found)
    simpa [afterSeparator, atLedger, scratchW, scratchWord,
      List.reverse_append, List.append_assoc] using scanned
  have hLedgerBoundary :
      workRunExact? machine 1 atLedger =
        some
          (configAtLeftWord ledgerState
            (bank ++ stackBoundary :: cellBlank :: outsideLeft)
            (ledgerBoundary :: scratchW.reverse ++
              sourceLeftBoundary :: source)) := by
    apply exactRun_one machine
    simpa [atLedger] using
      ledger_boundary_step
        (bank ++ stackBoundary :: cellBlank :: outsideLeft)
        (scratchW.reverse ++ sourceLeftBoundary :: source)
  have hBank :
      workRunExact? machine bank.length
          (configAtLeftWord ledgerState
            (bank ++ stackBoundary :: cellBlank :: outsideLeft)
            (ledgerBoundary :: scratchW.reverse ++
              sourceLeftBoundary :: source)) =
        some atStackBoundary := by
    have scanned := scanLeftExact machine ledgerState
      ledgerPayload
      (by
        intro head leftTail rightSide headAllowed
        exact ledger_step head headAllowed leftTail rightSide)
      bank
      (stackBoundary :: cellBlank :: outsideLeft)
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: source)
      (slotBank_allowed capacity registers)
    simpa [atStackBoundary] using scanned
  have hStackBoundary :
      workRunExact? machine 1 atStackBoundary =
        some atBlank := by
    apply exactRun_one machine
    simpa [atStackBoundary, atBlank] using
      stack_boundary_step
        (cellBlank :: outsideLeft)
        (bank.reverse ++ ledgerBoundary ::
          scratchW.reverse ++ sourceLeftBoundary :: source)
  have hWrite :
      workRunExact? machine 1 atBlank =
        some returningBoundary := by
    apply exactRun_one machine
    simpa [atBlank, returningBoundary] using
      write_blank_step outsideLeft
        (stackBoundary :: bank.reverse ++ ledgerBoundary ::
          scratchW.reverse ++ sourceLeftBoundary :: source)
  have hReturnBoundary :
      workRunExact? machine 1 returningBoundary =
        some returningLedger := by
    apply exactRun_one machine
    simpa [returningBoundary, returningLedger] using
      return_boundary_step
        (stackEnd :: outsideLeft)
        (bank.reverse ++ ledgerBoundary ::
          scratchW.reverse ++ sourceLeftBoundary :: source)
  have reversedBankAllowed :
      ∀ symbol, symbol ∈ bank.reverse → ledgerPayload symbol := by
    intro symbol found
    exact slotBank_allowed capacity registers symbol
      (List.mem_reverse.mp found)
  have hReturnBank :
      workRunExact? machine bank.length returningLedger =
        some returningLedgerBoundary := by
    have scanned := scanRightExact machine returnLedgerState
      ledgerPayload
      (by
        intro leftSide head suffix headAllowed
        exact return_ledger_step head headAllowed leftSide suffix)
      bank.reverse
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: source)
      (stackBoundary :: stackEnd :: outsideLeft)
      reversedBankAllowed
    simpa [returningLedger, returningLedgerBoundary] using scanned
  have hReturnLedgerBoundary :
      workRunExact? machine 1 returningLedgerBoundary =
        some returningScratch := by
    apply exactRun_one machine
    simpa [returningLedgerBoundary, returningScratch] using
      return_ledger_boundary_step
        (bank ++ stackBoundary :: stackEnd :: outsideLeft)
        (scratchW.reverse ++ sourceLeftBoundary :: source)
  have reversedScratchAllowed :
      ∀ symbol, symbol ∈ scratchW.reverse →
        scratchPayload symbol := by
    intro symbol found
    have original := List.mem_reverse.mp found
    unfold scratchW scratchWord at original
    rw [List.mem_append] at original
    rcases original with unit | tail
    · exact Or.inl (List.eq_of_mem_replicate unit)
    · cases tail with
      | head =>
          exact Or.inr (Or.inl rfl)
      | tail _ blank =>
          exact Or.inr (Or.inr
            (List.eq_of_mem_replicate blank))
  have hReturnScratch :
      workRunExact? machine scratchW.length returningScratch =
        some returningSource := by
    have scanned := scanRightExact machine returnScratchState
      scratchPayload
      (by
        intro leftSide head suffix headAllowed
        exact return_scratch_step head headAllowed leftSide suffix)
      scratchW.reverse
      (sourceLeftBoundary :: source)
      (ledgerBoundary :: bank ++
        stackBoundary :: stackEnd :: outsideLeft)
      reversedScratchAllowed
    simpa [returningScratch, returningSource] using scanned
  have hReturnSource :
      workRunExact? machine 1 returningSource =
        some (finalConfiguration capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) := by
    apply exactRun_one machine
    simpa [returningSource, finalConfiguration, stackWord,
      recordsWord, source, scratchW, bank, List.append_assoc] using
      return_source_boundary_step
        (scratchW ++ ledgerBoundary :: bank ++
          stackBoundary :: stackEnd :: outsideLeft)
        source
  have h01 := exactRun_add machine 1 1 _ _ _
    hSource hBoundary
  have h02 := exactRun_add machine 2 scratch _ _ _
    h01 hUnits
  have h03 := exactRun_add machine (2 + scratch) 1 _ _ _
    h02 hSeparator
  have h04 := exactRun_add machine
    (2 + scratch + 1) (capacity - scratch) _ _ _
    h03 hReserve
  have h05 := exactRun_add machine
    (2 + scratch + 1 + (capacity - scratch)) 1 _ _ _
    h04 hLedgerBoundary
  have h06 := exactRun_add machine
    (2 + scratch + 1 + (capacity - scratch) + 1)
    bank.length _ _ _ h05 hBank
  have h07 := exactRun_add machine
    (2 + scratch + 1 + (capacity - scratch) + 1 +
      bank.length) 1 _ _ _ h06 hStackBoundary
  have h08 := exactRun_add machine
    (2 + scratch + 1 + (capacity - scratch) + 1 +
      bank.length + 1) 1 _ _ _ h07 hWrite
  have h09 := exactRun_add machine
    (2 + scratch + 1 + (capacity - scratch) + 1 +
      bank.length + 1 + 1) 1 _ _ _ h08 hReturnBoundary
  have h10 := exactRun_add machine
    (2 + scratch + 1 + (capacity - scratch) + 1 +
      bank.length + 1 + 1 + 1) bank.length
    _ _ _ h09 hReturnBank
  have h11 := exactRun_add machine
    (2 + scratch + 1 + (capacity - scratch) + 1 +
      bank.length + 1 + 1 + 1 + bank.length) 1
    _ _ _ h10 hReturnLedgerBoundary
  have h12 := exactRun_add machine
    (2 + scratch + 1 + (capacity - scratch) + 1 +
      bank.length + 1 + 1 + 1 + bank.length + 1)
    scratchW.length _ _ _ h11 hReturnScratch
  have complete := exactRun_add machine
    (2 + scratch + 1 + (capacity - scratch) + 1 +
      bank.length + 1 + 1 + 1 + bank.length + 1 +
      scratchW.length) 1 _ _ _ h12 hReturnSource
  have scratchLength :
      scratchW.length = capacity + 1 := by
    exact scratchWord_length_of_le capacity scratch scratchBound
  have bankLength :
      bank.length = 6 * (capacity + 2) :=
    slotBank_length capacity registers fits
  have steps :
      2 + scratch + 1 + (capacity - scratch) + 1 +
          bank.length + 1 + 1 + 1 + bank.length + 1 +
          scratchW.length + 1 =
        workSteps capacity := by
    rw [scratchLength, bankLength]
    unfold workSteps
    omega
  rw [steps] at complete
  exact complete

theorem final_halted (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    machine.isHalted
      (finalConfiguration capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft) = true := by
  rfl

end Initialize

/-! ### Exact scratch-preserving farthest push -/

namespace Push

def entryConfiguration (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord startState
    (sourceLeftBoundary ::
      (scratchWord capacity value ++
        ledgerBoundary ::
          (TargetEmitterLedger.slotBank capacity registers ++
            stackWord checks ++
              List.replicate (value + 1) cellBlank ++
                outsideLeft)))
    (sourceHead :: sourceTail ++ targetAndRight)

/-- Push is a copy operation: the nearest scratch value is restored exactly.
The `value + 1` explicit blank cells become the new farthest record. -/
def finalConfiguration (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord acceptState
    (sourceLeftBoundary ::
      (scratchWord capacity value ++
        ledgerBoundary ::
          (TargetEmitterLedger.slotBank capacity registers ++
            stackWord (checks ++ [value]) ++ outsideLeft)))
    (sourceHead :: sourceTail ++ targetAndRight)

def workSteps (capacity recordsLength value : Nat) : Nat :=
  14 * capacity + 2 * recordsLength + 40 +
    value * (14 * capacity + 2 * recordsLength + 38)

def polynomialWorkBound
    (capacity recordsLength value : Nat) : Nat :=
  14 * capacity + 2 * recordsLength + 40 +
    value * (14 * capacity + 2 * recordsLength + 38)

theorem workSteps_le_polynomialWorkBound
    (capacity recordsLength value : Nat) :
    workSteps capacity recordsLength value ≤
      polynomialWorkBound capacity recordsLength value := by
  exact Nat.le_refl _

private def selectedScratch (capacity processed remaining : Nat) :
    List WorkSymbol :=
  List.replicate processed pushMark ++
    List.replicate remaining unaryUnit ++
      unarySeparator ::
        List.replicate (capacity - (processed + remaining))
          cellBlank

private def stackDuringPush (checks : List Nat)
    (processed remaining : Nat) (outsideLeft : List WorkSymbol) :
    List WorkSymbol :=
  stackBoundary ::
    (recordsWord checks ++
      recordBoundary ::
        (List.replicate processed unaryUnit ++
          stackEnd ::
            (List.replicate remaining cellBlank ++ outsideLeft)))

private def selectedConfiguration
    (capacity processed remaining : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (sourceWord outsideLeft : List WorkSymbol) :
    WorkConfiguration :=
  configAtLeftWord selectedState
    (List.replicate remaining unaryUnit ++
      unarySeparator ::
        List.replicate (capacity - (processed + remaining))
          cellBlank ++
      ledgerBoundary ::
        (TargetEmitterLedger.slotBank capacity registers ++
          stackDuringPush checks processed remaining outsideLeft))
    (List.replicate processed pushMark ++
      sourceLeftBoundary :: sourceWord)

private theorem start_step (symbol : WorkSymbol)
    (allowed : sourceAllowed symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord startState left (symbol :: right)) =
      some (configAtLeftWord boundaryState
        left (symbol :: right)) := by
  apply moveLeftFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c | d | e
    all_goals subst symbol
    all_goals decide

private theorem boundary_step (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord boundaryState
          (sourceLeftBoundary :: left) right) =
      some (configAtLeftWord scratchUnitsState
        left (sourceLeftBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem scratch_unit_step (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord scratchUnitsState
          (unaryUnit :: left) right) =
      some (configAtLeftWord scratchUnitsState
        left (unaryUnit :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem scratch_separator_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord scratchUnitsState
          (unarySeparator :: left) right) =
      some (configAtLeftWord scratchReserveState
        left (unarySeparator :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem scratch_blank_step (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord scratchReserveState
          (cellBlank :: left) right) =
      some (configAtLeftWord scratchReserveState
        left (cellBlank :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem scratch_ledger_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord scratchReserveState
          (ledgerBoundary :: left) right) =
      some (configAtLeftWord ledgerState
        left (ledgerBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem ledger_step (symbol : WorkSymbol)
    (allowed : ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord ledgerState
          (symbol :: left) right) =
      some (configAtLeftWord ledgerState
        left (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c | d
    all_goals subst symbol
    all_goals decide

private theorem ledger_stack_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord ledgerState
          (stackBoundary :: left) right) =
      some (configAtLeftWord stackState
        left (stackBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem stack_record_step (symbol : WorkSymbol)
    (allowed : recordPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord stackState
          (symbol :: left) right) =
      some (configAtLeftWord stackState
        left (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b
    all_goals subst symbol
    all_goals decide

private theorem stack_end_step (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord stackState
          (stackEnd :: left) right) =
      some (configAtLeftWord appendEndState
        left (recordBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem append_end_step (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord appendEndState
          (cellBlank :: left) right) =
      some (configAtWord setupReturnStackState
        (stackEnd :: left) right) := by
  apply moveRightFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem setup_return_stack_step
    (symbol : WorkSymbol) (allowed : recordPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord setupReturnStackState left
          (symbol :: right)) =
      some (configAtWord setupReturnStackState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b
    all_goals subst symbol
    all_goals decide

private theorem setup_return_stack_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord setupReturnStackState left
          (stackBoundary :: right)) =
      some (configAtWord setupReturnLedgerState
        (stackBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem setup_return_ledger_step
    (symbol : WorkSymbol) (allowed : ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord setupReturnLedgerState left
          (symbol :: right)) =
      some (configAtWord setupReturnLedgerState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c | d
    all_goals subst symbol
    all_goals decide

private theorem setup_return_ledger_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord setupReturnLedgerState left
          (ledgerBoundary :: right)) =
      some (configAtWord setupReturnScratchState
        (ledgerBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem setup_return_scratch_step
    (symbol : WorkSymbol) (allowed : scratchPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord setupReturnScratchState left
          (symbol :: right)) =
      some (configAtWord setupReturnScratchState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c
    all_goals subst symbol
    all_goals decide

private theorem setup_return_source_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord setupReturnScratchState left
          (sourceLeftBoundary :: right)) =
      some (configAtWord selectStartState
        (sourceLeftBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem select_start_step (symbol : WorkSymbol)
    (allowed : sourceAllowed symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord selectStartState left
          (symbol :: right)) =
      some (configAtLeftWord selectBoundaryState
        left (symbol :: right)) := by
  apply moveLeftFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c | d | e
    all_goals subst symbol
    all_goals decide

private theorem select_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord selectBoundaryState
          (sourceLeftBoundary :: left) right) =
      some (configAtLeftWord selectedState
        left (sourceLeftBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem selected_mark_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord selectedState
          (pushMark :: left) right) =
      some (configAtWord selectedDelayState
        left (pushMark :: right)) := by
  apply stayAtWord_of_find machine rules rfl
  · rfl
  · decide

private theorem selected_delay_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord selectedDelayState left
          (pushMark :: right)) =
      some (configAtLeftWord selectedState
        left (pushMark :: right)) := by
  apply moveLeftFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem selected_unit_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord selectedState
          (unaryUnit :: left) right) =
      some (configAtLeftWord bounceScratchState
        left (pushMark :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem selected_separator_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord selectedState
          (unarySeparator :: left) right) =
      some (configAtWord restoreState
        (unarySeparator :: left) right) := by
  apply moveRightFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem bounce_scratch_step
    (symbol : WorkSymbol) (allowed : scratchPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord bounceScratchState
          (symbol :: left) right) =
      some (configAtLeftWord bounceScratchState
        left (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c
    all_goals subst symbol
    all_goals decide

private theorem bounce_scratch_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord bounceScratchState
          (ledgerBoundary :: left) right) =
      some (configAtLeftWord bounceLedgerState
        left (ledgerBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem bounce_ledger_step
    (symbol : WorkSymbol) (allowed : ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord bounceLedgerState
          (symbol :: left) right) =
      some (configAtLeftWord bounceLedgerState
        left (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c | d
    all_goals subst symbol
    all_goals decide

private theorem bounce_ledger_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord bounceLedgerState
          (stackBoundary :: left) right) =
      some (configAtLeftWord bounceStackState
        left (stackBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem bounce_stack_step
    (symbol : WorkSymbol) (allowed : recordPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord bounceStackState
          (symbol :: left) right) =
      some (configAtLeftWord bounceStackState
        left (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b
    all_goals subst symbol
    all_goals decide

private theorem bounce_stack_end_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord bounceStackState
          (stackEnd :: left) right) =
      some (configAtLeftWord appendUnitState
        left (unaryUnit :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem append_unit_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord appendUnitState
          (cellBlank :: left) right) =
      some (configAtWord cycleReturnStackState
        (stackEnd :: left) right) := by
  apply moveRightFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem cycle_return_stack_step
    (symbol : WorkSymbol) (allowed : recordPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord cycleReturnStackState left
          (symbol :: right)) =
      some (configAtWord cycleReturnStackState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b
    all_goals subst symbol
    all_goals decide

private theorem cycle_return_stack_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord cycleReturnStackState left
          (stackBoundary :: right)) =
      some (configAtWord cycleReturnLedgerState
        (stackBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem cycle_return_ledger_step
    (symbol : WorkSymbol) (allowed : ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord cycleReturnLedgerState left
          (symbol :: right)) =
      some (configAtWord cycleReturnLedgerState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c | d
    all_goals subst symbol
    all_goals decide

private theorem cycle_return_ledger_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord cycleReturnLedgerState left
          (ledgerBoundary :: right)) =
      some (configAtWord seekMarkState
        (ledgerBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem seek_mark_scratch_step
    (symbol : WorkSymbol) (allowed : scratchPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord seekMarkState left
          (symbol :: right)) =
      some (configAtWord seekMarkState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c
    all_goals subst symbol
    all_goals decide

private theorem seek_mark_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord seekMarkState left
          (pushMark :: right)) =
      some (configAtWord selectedState left
        (pushMark :: right)) := by
  apply stayAtWord_of_find machine rules rfl
  · rfl
  · decide

private theorem replicate_succ_append {α : Type}
    (count : Nat) (item : α) :
    List.replicate (count + 1) item =
      List.replicate count item ++ [item] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change item :: List.replicate (count + 1) item =
        item :: (List.replicate count item ++ [item])
      rw [ih]

private theorem cons_replicate_eq_succ_append {α : Type}
    (count : Nat) (item : α) (tail : List α) :
    item :: List.replicate count item ++ tail =
      List.replicate (count + 1) item ++ tail := by
  rw [List.replicate_succ]

private theorem replicate_cons_eq_succ_append {α : Type}
    (count : Nat) (item : α) (tail : List α) :
    List.replicate count item ++ item :: tail =
      List.replicate (count + 1) item ++ tail := by
  rw [replicate_succ_append, List.append_assoc]
  rfl

private theorem restore_mark_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord restoreState left
          (pushMark :: right)) =
      some (configAtWord restoreState
        (unaryUnit :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem restore_source_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord restoreState left
          (sourceLeftBoundary :: right)) =
      some (configAtWord acceptState
        (sourceLeftBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem selected_marks_exact (count : Nat)
    (left right : List WorkSymbol) :
    workRunExact? machine (2 * count)
        (configAtLeftWord selectedState
          (List.replicate count pushMark ++ left) right) =
      some (configAtLeftWord selectedState
        left (List.replicate count pushMark ++ right)) := by
  induction count generalizing right with
  | zero =>
      rfl
  | succ count ih =>
      have hMark :
          workRunExact? machine 1
              (configAtLeftWord selectedState
                (pushMark ::
                  List.replicate count pushMark ++ left) right) =
            some (configAtWord selectedDelayState
              (List.replicate count pushMark ++ left)
              (pushMark :: right)) := by
        apply exactRun_one machine
        simpa using selected_mark_step
          (List.replicate count pushMark ++ left) right
      have hDelay :
          workRunExact? machine 1
              (configAtWord selectedDelayState
                (List.replicate count pushMark ++ left)
                (pushMark :: right)) =
            some (configAtLeftWord selectedState
              (List.replicate count pushMark ++ left)
              (pushMark :: right)) := by
        apply exactRun_one machine
        simpa using selected_delay_step
          (List.replicate count pushMark ++ left) right
      have h01 := exactRun_add machine 1 1 _ _ _ hMark hDelay
      have complete := exactRun_add machine 2 (2 * count)
        _ _ _ h01 (ih (pushMark :: right))
      have steps : 2 + 2 * count = 2 * (count + 1) := by
        omega
      rw [steps] at complete
      have moved :
          List.replicate count pushMark ++ pushMark :: right =
            pushMark :: List.replicate count pushMark ++ right := by
        calc
          List.replicate count pushMark ++ pushMark :: right =
              (List.replicate count pushMark ++ [pushMark]) ++ right := by
                simp [List.append_assoc]
          _ = List.replicate (count + 1) pushMark ++ right := by
                rw [replicate_succ_append]
          _ = pushMark :: List.replicate count pushMark ++ right := by
                rw [List.replicate_succ]
      rw [moved] at complete
      simpa [List.replicate_succ] using complete

private theorem restore_marks_exact (count : Nat)
    (left right : List WorkSymbol) :
    workRunExact? machine count
        (configAtWord restoreState left
          (List.replicate count pushMark ++ right)) =
      some (configAtWord restoreState
        (List.replicate count unaryUnit ++ left) right) := by
  induction count generalizing left with
  | zero =>
      rfl
  | succ count ih =>
      change
        (match workStep? machine
          (configAtWord restoreState left
            (pushMark :: List.replicate count pushMark ++ right)) with
         | none => none
         | some next => workRunExact? machine count next) = _
      simp only [List.cons_append]
      rw [restore_mark_step left
        (List.replicate count pushMark ++ right)]
      simpa [replicate_succ_append, List.append_assoc] using
        ih (unaryUnit :: left)

private theorem setup_exact (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    workRunExact? machine
        (14 * capacity + 2 * (recordsWord checks).length + 38)
        (entryConfiguration capacity value registers checks
          sourceHead sourceTail targetAndRight outsideLeft) =
      some (selectedConfiguration capacity 0 value registers checks
        (sourceHead :: sourceTail ++ targetAndRight) outsideLeft) := by
  let scratchW := scratchWord capacity value
  let bank := TargetEmitterLedger.slotBank capacity registers
  let records := recordsWord checks
  let source := sourceHead :: sourceTail ++ targetAndRight
  let far := List.replicate (value + 1) cellBlank ++ outsideLeft
  let afterSource :=
    configAtLeftWord boundaryState
      (sourceLeftBoundary :: scratchW ++
        ledgerBoundary :: bank ++
          stackBoundary :: records ++ stackEnd :: far)
      source
  let afterBoundary :=
    configAtLeftWord scratchUnitsState
      (scratchW ++ ledgerBoundary :: bank ++
        stackBoundary :: records ++ stackEnd :: far)
      (sourceLeftBoundary :: source)
  let atSeparator :=
    configAtLeftWord scratchUnitsState
      (unarySeparator ::
        List.replicate (capacity - value) cellBlank ++
          ledgerBoundary :: bank ++
            stackBoundary :: records ++ stackEnd :: far)
      (List.replicate value unaryUnit ++
        sourceLeftBoundary :: source)
  let afterSeparator :=
    configAtLeftWord scratchReserveState
      (List.replicate (capacity - value) cellBlank ++
        ledgerBoundary :: bank ++
          stackBoundary :: records ++ stackEnd :: far)
      (unarySeparator ::
        List.replicate value unaryUnit ++
          sourceLeftBoundary :: source)
  let atLedger :=
    configAtLeftWord scratchReserveState
      (ledgerBoundary :: bank ++
        stackBoundary :: records ++ stackEnd :: far)
      (scratchW.reverse ++ sourceLeftBoundary :: source)
  let atStackBoundary :=
    configAtLeftWord ledgerState
      (stackBoundary :: records ++ stackEnd :: far)
      (bank.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: source)
  let atStackEnd :=
    configAtLeftWord stackState
      (stackEnd :: far)
      (records.reverse ++ stackBoundary :: bank.reverse ++
        ledgerBoundary :: scratchW.reverse ++
          sourceLeftBoundary :: source)
  let atAppendBlank :=
    configAtLeftWord appendEndState far
      (recordBoundary :: records.reverse ++
        stackBoundary :: bank.reverse ++ ledgerBoundary ::
          scratchW.reverse ++ sourceLeftBoundary :: source)
  let returningStack :=
    configAtWord setupReturnStackState
      (stackEnd :: List.replicate value cellBlank ++ outsideLeft)
      (recordBoundary :: records.reverse ++
        stackBoundary :: bank.reverse ++ ledgerBoundary ::
          scratchW.reverse ++ sourceLeftBoundary :: source)
  let returningStackBoundary :=
    configAtWord setupReturnStackState
      (records ++ recordBoundary :: stackEnd ::
        List.replicate value cellBlank ++ outsideLeft)
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: source)
  let returningLedger :=
    configAtWord setupReturnLedgerState
      (stackBoundary :: records ++ recordBoundary :: stackEnd ::
        List.replicate value cellBlank ++ outsideLeft)
      (bank.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: source)
  let returningLedgerBoundary :=
    configAtWord setupReturnLedgerState
      (bank ++ stackBoundary :: records ++ recordBoundary :: stackEnd ::
        List.replicate value cellBlank ++ outsideLeft)
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: source)
  let returningScratch :=
    configAtWord setupReturnScratchState
      (ledgerBoundary :: bank ++ stackBoundary :: records ++
        recordBoundary :: stackEnd ::
          List.replicate value cellBlank ++ outsideLeft)
      (scratchW.reverse ++ sourceLeftBoundary :: source)
  let returningSource :=
    configAtWord setupReturnScratchState
      (scratchW ++ ledgerBoundary :: bank ++
        stackBoundary :: records ++ recordBoundary :: stackEnd ::
          List.replicate value cellBlank ++ outsideLeft)
      (sourceLeftBoundary :: source)
  let selecting :=
    configAtWord selectStartState
      (sourceLeftBoundary :: scratchW ++ ledgerBoundary :: bank ++
        stackBoundary :: records ++ recordBoundary :: stackEnd ::
          List.replicate value cellBlank ++ outsideLeft)
      source
  let atSelectBoundary :=
    configAtLeftWord selectBoundaryState
      (sourceLeftBoundary :: scratchW ++ ledgerBoundary :: bank ++
        stackBoundary :: records ++ recordBoundary :: stackEnd ::
          List.replicate value cellBlank ++ outsideLeft)
      source
  have hSource :
      workRunExact? machine 1
          (entryConfiguration capacity value registers checks
            sourceHead sourceTail targetAndRight outsideLeft) =
        some afterSource := by
    apply exactRun_one machine
    simpa [entryConfiguration, afterSource, scratchW, bank, records,
      source, far, stackWord, List.append_assoc] using
      start_step sourceHead allowed
        (sourceLeftBoundary :: scratchW ++ ledgerBoundary :: bank ++
          stackBoundary :: records ++ stackEnd :: far)
        (sourceTail ++ targetAndRight)
  have hBoundary :
      workRunExact? machine 1 afterSource =
        some afterBoundary := by
    apply exactRun_one machine
    simpa [afterSource, afterBoundary] using
      boundary_step
        (scratchW ++ ledgerBoundary :: bank ++
          stackBoundary :: records ++ stackEnd :: far)
        source
  have hUnits :
      workRunExact? machine value afterBoundary =
        some atSeparator := by
    have scanned := scanLeftExact machine scratchUnitsState
      (fun symbol => symbol = unaryUnit)
      (by
        intro head leftTail rightSide equality
        subst head
        exact scratch_unit_step leftTail rightSide)
      (List.replicate value unaryUnit)
      (unarySeparator ::
        List.replicate (capacity - value) cellBlank ++
          ledgerBoundary :: bank ++
            stackBoundary :: records ++ stackEnd :: far)
      (sourceLeftBoundary :: source)
      (by
        intro symbol found
        exact List.eq_of_mem_replicate found)
    simpa [afterBoundary, atSeparator, scratchW, scratchWord,
      List.append_assoc] using scanned
  have hSeparator :
      workRunExact? machine 1 atSeparator =
        some afterSeparator := by
    apply exactRun_one machine
    simpa [atSeparator, afterSeparator] using
      scratch_separator_step
        (List.replicate (capacity - value) cellBlank ++
          ledgerBoundary :: bank ++
            stackBoundary :: records ++ stackEnd :: far)
        (List.replicate value unaryUnit ++
          sourceLeftBoundary :: source)
  have hReserve :
      workRunExact? machine (capacity - value) afterSeparator =
        some atLedger := by
    have scanned := scanLeftExact machine scratchReserveState
      (fun symbol => symbol = cellBlank)
      (by
        intro head leftTail rightSide equality
        subst head
        exact scratch_blank_step leftTail rightSide)
      (List.replicate (capacity - value) cellBlank)
      (ledgerBoundary :: bank ++
        stackBoundary :: records ++ stackEnd :: far)
      (unarySeparator ::
        List.replicate value unaryUnit ++
          sourceLeftBoundary :: source)
      (by
        intro symbol found
        exact List.eq_of_mem_replicate found)
    simpa [afterSeparator, atLedger, scratchW, scratchWord,
      List.reverse_append, List.append_assoc] using scanned
  have hScratchLedger :
      workRunExact? machine 1 atLedger =
        some
          (configAtLeftWord ledgerState
            (bank ++ stackBoundary :: records ++ stackEnd :: far)
            (ledgerBoundary :: scratchW.reverse ++
              sourceLeftBoundary :: source)) := by
    apply exactRun_one machine
    simpa [atLedger] using
      scratch_ledger_boundary_step
        (bank ++ stackBoundary :: records ++ stackEnd :: far)
        (scratchW.reverse ++ sourceLeftBoundary :: source)
  have hBank :
      workRunExact? machine bank.length
          (configAtLeftWord ledgerState
            (bank ++ stackBoundary :: records ++ stackEnd :: far)
            (ledgerBoundary :: scratchW.reverse ++
              sourceLeftBoundary :: source)) =
        some atStackBoundary := by
    have scanned := scanLeftExact machine ledgerState ledgerPayload
      (by
        intro head leftTail rightSide headAllowed
        exact ledger_step head headAllowed leftTail rightSide)
      bank
      (stackBoundary :: records ++ stackEnd :: far)
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: source)
      (slotBank_allowed capacity registers)
    simpa [atStackBoundary] using scanned
  have hStackBoundary :
      workRunExact? machine 1 atStackBoundary =
        some
          (configAtLeftWord stackState
            (records ++ stackEnd :: far)
            (stackBoundary :: bank.reverse ++ ledgerBoundary ::
              scratchW.reverse ++ sourceLeftBoundary :: source)) := by
    apply exactRun_one machine
    simpa [atStackBoundary] using
      ledger_stack_boundary_step
        (records ++ stackEnd :: far)
        (bank.reverse ++ ledgerBoundary ::
          scratchW.reverse ++ sourceLeftBoundary :: source)
  have hRecords :
      workRunExact? machine records.length
          (configAtLeftWord stackState
            (records ++ stackEnd :: far)
            (stackBoundary :: bank.reverse ++ ledgerBoundary ::
              scratchW.reverse ++ sourceLeftBoundary :: source)) =
        some atStackEnd := by
    have scanned := scanLeftExact machine stackState recordPayload
      (by
        intro head leftTail rightSide headAllowed
        exact stack_record_step head headAllowed leftTail rightSide)
      records
      (stackEnd :: far)
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: source)
      (recordsWord_allowed checks)
    simpa [atStackEnd, records] using scanned
  have hStackEnd :
      workRunExact? machine 1 atStackEnd =
        some atAppendBlank := by
    apply exactRun_one machine
    simpa [atStackEnd, atAppendBlank] using
      stack_end_step far
        (records.reverse ++ stackBoundary :: bank.reverse ++
          ledgerBoundary :: scratchW.reverse ++
            sourceLeftBoundary :: source)
  have hAppend :
      workRunExact? machine 1 atAppendBlank =
        some returningStack := by
    apply exactRun_one machine
    simpa [atAppendBlank, returningStack, far,
      List.replicate_succ] using
      append_end_step
        (List.replicate value cellBlank ++ outsideLeft)
        (recordBoundary :: records.reverse ++
          stackBoundary :: bank.reverse ++ ledgerBoundary ::
            scratchW.reverse ++ sourceLeftBoundary :: source)
  have returnRecordsAllowed :
      ∀ symbol,
        symbol ∈ recordBoundary :: records.reverse →
          recordPayload symbol := by
    intro symbol found
    cases found with
    | head =>
        exact Or.inl rfl
    | tail _ inRecords =>
        exact recordsWord_allowed checks symbol
          (List.mem_reverse.mp inRecords)
  have hReturnRecords :
      workRunExact? machine (records.length + 1) returningStack =
        some returningStackBoundary := by
    have scanned := scanRightExact machine setupReturnStackState
      recordPayload
      (by
        intro leftSide head suffix headAllowed
        exact setup_return_stack_step
          head headAllowed leftSide suffix)
      (recordBoundary :: records.reverse)
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: source)
      (stackEnd :: List.replicate value cellBlank ++ outsideLeft)
      returnRecordsAllowed
    simpa [returningStack, returningStackBoundary,
      List.reverse_cons, List.append_assoc] using scanned
  have hReturnStackBoundary :
      workRunExact? machine 1 returningStackBoundary =
        some returningLedger := by
    apply exactRun_one machine
    simpa [returningStackBoundary, returningLedger] using
      setup_return_stack_boundary_step
        (records ++ recordBoundary :: stackEnd ::
          List.replicate value cellBlank ++ outsideLeft)
        (bank.reverse ++ ledgerBoundary ::
          scratchW.reverse ++ sourceLeftBoundary :: source)
  have reverseBankAllowed :
      ∀ symbol, symbol ∈ bank.reverse → ledgerPayload symbol := by
    intro symbol found
    exact slotBank_allowed capacity registers symbol
      (List.mem_reverse.mp found)
  have hReturnBank :
      workRunExact? machine bank.length returningLedger =
        some returningLedgerBoundary := by
    have scanned := scanRightExact machine setupReturnLedgerState
      ledgerPayload
      (by
        intro leftSide head suffix headAllowed
        exact setup_return_ledger_step
          head headAllowed leftSide suffix)
      bank.reverse
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: source)
      (stackBoundary :: records ++ recordBoundary :: stackEnd ::
        List.replicate value cellBlank ++ outsideLeft)
      reverseBankAllowed
    simpa [returningLedger, returningLedgerBoundary] using scanned
  have hReturnLedgerBoundary :
      workRunExact? machine 1 returningLedgerBoundary =
        some returningScratch := by
    apply exactRun_one machine
    simpa [returningLedgerBoundary, returningScratch] using
      setup_return_ledger_boundary_step
        (bank ++ stackBoundary :: records ++ recordBoundary ::
          stackEnd :: List.replicate value cellBlank ++ outsideLeft)
        (scratchW.reverse ++ sourceLeftBoundary :: source)
  have reverseScratchAllowed :
      ∀ symbol, symbol ∈ scratchW.reverse →
        scratchPayload symbol := by
    intro symbol found
    have original := List.mem_reverse.mp found
    unfold scratchW scratchWord at original
    rw [List.mem_append] at original
    rcases original with unit | tail
    · exact Or.inl (List.eq_of_mem_replicate unit)
    · cases tail with
      | head =>
          exact Or.inr (Or.inl rfl)
      | tail _ blank =>
          exact Or.inr (Or.inr
            (List.eq_of_mem_replicate blank))
  have hReturnScratch :
      workRunExact? machine scratchW.length returningScratch =
        some returningSource := by
    have scanned := scanRightExact machine setupReturnScratchState
      scratchPayload
      (by
        intro leftSide head suffix headAllowed
        exact setup_return_scratch_step
          head headAllowed leftSide suffix)
      scratchW.reverse
      (sourceLeftBoundary :: source)
      (ledgerBoundary :: bank ++ stackBoundary :: records ++
        recordBoundary :: stackEnd ::
          List.replicate value cellBlank ++ outsideLeft)
      reverseScratchAllowed
    simpa [returningScratch, returningSource] using scanned
  have hReturnSource :
      workRunExact? machine 1 returningSource =
        some selecting := by
    apply exactRun_one machine
    simpa [returningSource, selecting] using
      setup_return_source_step
        (scratchW ++ ledgerBoundary :: bank ++
          stackBoundary :: records ++ recordBoundary :: stackEnd ::
            List.replicate value cellBlank ++ outsideLeft)
        source
  have hSelectSource :
      workRunExact? machine 1 selecting =
        some atSelectBoundary := by
    apply exactRun_one machine
    simpa [selecting, atSelectBoundary, source] using
      select_start_step sourceHead allowed
        (sourceLeftBoundary :: scratchW ++ ledgerBoundary :: bank ++
          stackBoundary :: records ++ recordBoundary :: stackEnd ::
            List.replicate value cellBlank ++ outsideLeft)
        (sourceTail ++ targetAndRight)
  have hSelectBoundary :
      workRunExact? machine 1 atSelectBoundary =
        some (selectedConfiguration capacity 0 value registers checks
          source outsideLeft) := by
    apply exactRun_one machine
    simpa [atSelectBoundary, selectedConfiguration,
      stackDuringPush, scratchW, scratchWord, bank, records, far,
      Nat.zero_add, valueBound, List.append_assoc] using
      select_boundary_step
        (scratchW ++ ledgerBoundary :: bank ++
          stackBoundary :: records ++ recordBoundary :: stackEnd ::
            List.replicate value cellBlank ++ outsideLeft)
        source
  have h01 := exactRun_add machine 1 1 _ _ _
    hSource hBoundary
  have h02 := exactRun_add machine 2 value _ _ _
    h01 hUnits
  have h03 := exactRun_add machine (2 + value) 1 _ _ _
    h02 hSeparator
  have h04 := exactRun_add machine
    (2 + value + 1) (capacity - value) _ _ _
    h03 hReserve
  have h05 := exactRun_add machine
    (2 + value + 1 + (capacity - value)) 1 _ _ _
    h04 hScratchLedger
  have h06 := exactRun_add machine
    (2 + value + 1 + (capacity - value) + 1)
    bank.length _ _ _ h05 hBank
  have h07 := exactRun_add machine
    (2 + value + 1 + (capacity - value) + 1 +
      bank.length) 1 _ _ _ h06 hStackBoundary
  have h08 := exactRun_add machine
    (2 + value + 1 + (capacity - value) + 1 +
      bank.length + 1) records.length _ _ _
    h07 hRecords
  have h09 := exactRun_add machine
    (2 + value + 1 + (capacity - value) + 1 +
      bank.length + 1 + records.length) 1 _ _ _
    h08 hStackEnd
  have h10 := exactRun_add machine
    (2 + value + 1 + (capacity - value) + 1 +
      bank.length + 1 + records.length + 1) 1 _ _ _
    h09 hAppend
  have h11 := exactRun_add machine
    (2 + value + 1 + (capacity - value) + 1 +
      bank.length + 1 + records.length + 1 + 1)
    (records.length + 1) _ _ _ h10 hReturnRecords
  have h12 := exactRun_add machine
    (2 + value + 1 + (capacity - value) + 1 +
      bank.length + 1 + records.length + 1 + 1 +
        (records.length + 1)) 1 _ _ _
    h11 hReturnStackBoundary
  have h13 := exactRun_add machine
    (2 + value + 1 + (capacity - value) + 1 +
      bank.length + 1 + records.length + 1 + 1 +
        (records.length + 1) + 1) bank.length _ _ _
    h12 hReturnBank
  have h14 := exactRun_add machine
    (2 + value + 1 + (capacity - value) + 1 +
      bank.length + 1 + records.length + 1 + 1 +
        (records.length + 1) + 1 + bank.length) 1 _ _ _
    h13 hReturnLedgerBoundary
  have h15 := exactRun_add machine
    (2 + value + 1 + (capacity - value) + 1 +
      bank.length + 1 + records.length + 1 + 1 +
        (records.length + 1) + 1 + bank.length + 1)
    scratchW.length _ _ _ h14 hReturnScratch
  have h16 := exactRun_add machine
    (2 + value + 1 + (capacity - value) + 1 +
      bank.length + 1 + records.length + 1 + 1 +
        (records.length + 1) + 1 + bank.length + 1 +
          scratchW.length) 1 _ _ _ h15 hReturnSource
  have h17 := exactRun_add machine
    (2 + value + 1 + (capacity - value) + 1 +
      bank.length + 1 + records.length + 1 + 1 +
        (records.length + 1) + 1 + bank.length + 1 +
          scratchW.length + 1) 1 _ _ _ h16 hSelectSource
  have complete := exactRun_add machine
    (2 + value + 1 + (capacity - value) + 1 +
      bank.length + 1 + records.length + 1 + 1 +
        (records.length + 1) + 1 + bank.length + 1 +
          scratchW.length + 1 + 1) 1 _ _ _
    h17 hSelectBoundary
  have scratchLength :
      scratchW.length = capacity + 1 := by
    exact scratchWord_length_of_le capacity value valueBound
  have bankLength :
      bank.length = 6 * (capacity + 2) :=
    slotBank_length capacity registers fits
  have steps :
      2 + value + 1 + (capacity - value) + 1 +
          bank.length + 1 + records.length + 1 + 1 +
            (records.length + 1) + 1 + bank.length + 1 +
              scratchW.length + 1 + 1 + 1 =
        14 * capacity + 2 * (recordsWord checks).length + 38 := by
    rw [scratchLength, bankLength]
    simp [records]
    omega
  rw [steps] at complete
  exact complete

private theorem copy_cycle_exact
    (capacity processed remaining : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceWord outsideLeft : List WorkSymbol)
    (bounded : processed + (remaining + 1) ≤ capacity) :
    workRunExact? machine
        (2 * capacity +
          2 * (TargetEmitterLedger.slotBank capacity registers).length +
          2 * (recordsWord checks).length + 13)
        (selectedConfiguration capacity processed (remaining + 1)
          registers checks sourceWord outsideLeft) =
      some (selectedConfiguration capacity (processed + 1) remaining
        registers checks sourceWord outsideLeft) := by
  let bank := TargetEmitterLedger.slotBank capacity registers
  let records := recordsWord checks
  let travel :=
    List.replicate remaining unaryUnit ++
      unarySeparator ::
        List.replicate
          (capacity - (processed + (remaining + 1))) cellBlank
  let stackPrefix :=
    records ++ recordBoundary ::
      List.replicate processed unaryUnit
  let markedRight :=
    pushMark :: List.replicate processed pushMark ++
      sourceLeftBoundary :: sourceWord
  let afterSelected :=
    configAtLeftWord bounceScratchState
      (travel ++ ledgerBoundary :: bank ++
        stackDuringPush checks processed (remaining + 1)
          outsideLeft)
      markedRight
  let atLedger :=
    configAtLeftWord bounceScratchState
      (ledgerBoundary :: bank ++
        stackDuringPush checks processed (remaining + 1)
          outsideLeft)
      (travel.reverse ++ markedRight)
  let atBank :=
    configAtLeftWord bounceLedgerState
      (bank ++ stackDuringPush checks processed (remaining + 1)
        outsideLeft)
      (ledgerBoundary :: travel.reverse ++ markedRight)
  let atStackBoundary :=
    configAtLeftWord bounceLedgerState
      (stackDuringPush checks processed (remaining + 1)
        outsideLeft)
      (bank.reverse ++ ledgerBoundary :: travel.reverse ++ markedRight)
  let atStack :=
    configAtLeftWord bounceStackState
      (stackPrefix ++ stackEnd ::
        List.replicate (remaining + 1) cellBlank ++ outsideLeft)
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        travel.reverse ++ markedRight)
  let atStackEnd :=
    configAtLeftWord bounceStackState
      (stackEnd ::
        List.replicate (remaining + 1) cellBlank ++ outsideLeft)
      (stackPrefix.reverse ++ stackBoundary :: bank.reverse ++
        ledgerBoundary :: travel.reverse ++ markedRight)
  let atAppend :=
    configAtLeftWord appendUnitState
      (List.replicate (remaining + 1) cellBlank ++ outsideLeft)
      (unaryUnit :: stackPrefix.reverse ++ stackBoundary ::
        bank.reverse ++ ledgerBoundary :: travel.reverse ++ markedRight)
  let returningStack :=
    configAtWord cycleReturnStackState
      (stackEnd :: List.replicate remaining cellBlank ++ outsideLeft)
      (unaryUnit :: stackPrefix.reverse ++ stackBoundary ::
        bank.reverse ++ ledgerBoundary :: travel.reverse ++ markedRight)
  let returningStackBoundary :=
    configAtWord cycleReturnStackState
      (stackPrefix ++ unaryUnit :: stackEnd ::
        List.replicate remaining cellBlank ++ outsideLeft)
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        travel.reverse ++ markedRight)
  let returningLedger :=
    configAtWord cycleReturnLedgerState
      (stackBoundary :: stackPrefix ++ unaryUnit :: stackEnd ::
        List.replicate remaining cellBlank ++ outsideLeft)
      (bank.reverse ++ ledgerBoundary :: travel.reverse ++ markedRight)
  let returningLedgerBoundary :=
    configAtWord cycleReturnLedgerState
      (bank ++ stackBoundary :: stackPrefix ++ unaryUnit :: stackEnd ::
        List.replicate remaining cellBlank ++ outsideLeft)
      (ledgerBoundary :: travel.reverse ++ markedRight)
  let seeking :=
    configAtWord seekMarkState
      (ledgerBoundary :: bank ++ stackBoundary :: stackPrefix ++
        unaryUnit :: stackEnd ::
          List.replicate remaining cellBlank ++ outsideLeft)
      (travel.reverse ++ markedRight)
  let atMark :=
    configAtWord seekMarkState
      (travel ++ ledgerBoundary :: bank ++ stackBoundary :: stackPrefix ++
        unaryUnit :: stackEnd ::
          List.replicate remaining cellBlank ++ outsideLeft)
      markedRight
  let selectedMark :=
    configAtWord selectedState
      (travel ++ ledgerBoundary :: bank ++ stackBoundary :: stackPrefix ++
        unaryUnit :: stackEnd ::
          List.replicate remaining cellBlank ++ outsideLeft)
      markedRight
  let delayedMark :=
    configAtWord selectedDelayState
      (travel ++ ledgerBoundary :: bank ++ stackBoundary :: stackPrefix ++
        unaryUnit :: stackEnd ::
          List.replicate remaining cellBlank ++ outsideLeft)
      markedRight
  have hSelected :
      workRunExact? machine 1
          (selectedConfiguration capacity processed (remaining + 1)
            registers checks sourceWord outsideLeft) =
        some afterSelected := by
    apply exactRun_one machine
    simpa [selectedConfiguration, afterSelected, travel, markedRight,
      List.replicate_succ, List.append_assoc] using
      selected_unit_step
        (travel ++ ledgerBoundary :: bank ++
          stackDuringPush checks processed (remaining + 1)
            outsideLeft)
        (List.replicate processed pushMark ++
          sourceLeftBoundary :: sourceWord)
  have travelAllowed :
      ∀ symbol, symbol ∈ travel → scratchPayload symbol := by
    intro symbol found
    unfold travel at found
    rw [List.mem_append] at found
    rcases found with inUnits | inTail
    · exact Or.inl (List.eq_of_mem_replicate inUnits)
    · cases inTail with
      | head =>
          exact Or.inr (Or.inl rfl)
      | tail _ inBlanks =>
          exact Or.inr (Or.inr
            (List.eq_of_mem_replicate inBlanks))
  have hTravel :
      workRunExact? machine travel.length afterSelected =
        some atLedger := by
    have scanned := scanLeftExact machine bounceScratchState
      scratchPayload
      (by
        intro head leftTail rightSide headAllowed
        exact bounce_scratch_step
          head headAllowed leftTail rightSide)
      travel
      (ledgerBoundary :: bank ++
        stackDuringPush checks processed (remaining + 1)
          outsideLeft)
      markedRight
      travelAllowed
    simpa [afterSelected, atLedger] using scanned
  have hScratchBoundary :
      workRunExact? machine 1 atLedger =
        some atBank := by
    apply exactRun_one machine
    simpa [atLedger, atBank] using
      bounce_scratch_boundary_step
        (bank ++ stackDuringPush checks processed (remaining + 1)
          outsideLeft)
        (travel.reverse ++ markedRight)
  have hBank :
      workRunExact? machine bank.length atBank =
        some atStackBoundary := by
    have scanned := scanLeftExact machine bounceLedgerState
      ledgerPayload
      (by
        intro head leftTail rightSide headAllowed
        exact bounce_ledger_step
          head headAllowed leftTail rightSide)
      bank
      (stackDuringPush checks processed (remaining + 1)
        outsideLeft)
      (ledgerBoundary :: travel.reverse ++ markedRight)
      (slotBank_allowed capacity registers)
    simpa [atBank, atStackBoundary] using scanned
  have hLedgerBoundary :
      workRunExact? machine 1 atStackBoundary =
        some atStack := by
    apply exactRun_one machine
    simpa [atStackBoundary, atStack, stackDuringPush, stackPrefix,
      records, List.append_assoc] using
      bounce_ledger_boundary_step
        (stackPrefix ++ stackEnd ::
          List.replicate (remaining + 1) cellBlank ++ outsideLeft)
        (bank.reverse ++ ledgerBoundary :: travel.reverse ++ markedRight)
  have prefixAllowed :
      ∀ symbol, symbol ∈ stackPrefix → recordPayload symbol := by
    intro symbol found
    unfold stackPrefix at found
    rw [List.mem_append] at found
    rcases found with inRecords | inTail
    · exact recordsWord_allowed checks symbol inRecords
    · cases inTail with
      | head =>
          exact Or.inl rfl
      | tail _ inUnits =>
          exact Or.inr (List.eq_of_mem_replicate inUnits)
  have hPrefix :
      workRunExact? machine stackPrefix.length atStack =
        some atStackEnd := by
    have scanned := scanLeftExact machine bounceStackState
      recordPayload
      (by
        intro head leftTail rightSide headAllowed
        exact bounce_stack_step
          head headAllowed leftTail rightSide)
      stackPrefix
      (stackEnd ::
        List.replicate (remaining + 1) cellBlank ++ outsideLeft)
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        travel.reverse ++ markedRight)
      prefixAllowed
    simpa [atStack, atStackEnd] using scanned
  have hStackEnd :
      workRunExact? machine 1 atStackEnd =
        some atAppend := by
    apply exactRun_one machine
    simpa [atStackEnd, atAppend] using
      bounce_stack_end_step
        (List.replicate (remaining + 1) cellBlank ++ outsideLeft)
        (stackPrefix.reverse ++ stackBoundary :: bank.reverse ++
          ledgerBoundary :: travel.reverse ++ markedRight)
  have hAppend :
      workRunExact? machine 1 atAppend =
        some returningStack := by
    apply exactRun_one machine
    simpa [atAppend, returningStack, List.replicate_succ] using
      append_unit_step
        (List.replicate remaining cellBlank ++ outsideLeft)
        (unaryUnit :: stackPrefix.reverse ++ stackBoundary ::
          bank.reverse ++ ledgerBoundary :: travel.reverse ++ markedRight)
  have returnPrefixAllowed :
      ∀ symbol,
        symbol ∈ unaryUnit :: stackPrefix.reverse →
          recordPayload symbol := by
    intro symbol found
    cases found with
    | head =>
        exact Or.inr rfl
    | tail _ inPrefix =>
        exact prefixAllowed symbol (List.mem_reverse.mp inPrefix)
  have hReturnPrefix :
      workRunExact? machine (stackPrefix.length + 1) returningStack =
        some returningStackBoundary := by
    have scanned := scanRightExact machine cycleReturnStackState
      recordPayload
      (by
        intro leftSide head suffix headAllowed
        exact cycle_return_stack_step
          head headAllowed leftSide suffix)
      (unaryUnit :: stackPrefix.reverse)
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        travel.reverse ++ markedRight)
      (stackEnd :: List.replicate remaining cellBlank ++ outsideLeft)
      returnPrefixAllowed
    simpa [returningStack, returningStackBoundary,
      List.reverse_cons, List.append_assoc] using scanned
  have hReturnStackBoundary :
      workRunExact? machine 1 returningStackBoundary =
        some returningLedger := by
    apply exactRun_one machine
    simpa [returningStackBoundary, returningLedger] using
      cycle_return_stack_boundary_step
        (stackPrefix ++ unaryUnit :: stackEnd ::
          List.replicate remaining cellBlank ++ outsideLeft)
        (bank.reverse ++ ledgerBoundary :: travel.reverse ++ markedRight)
  have reverseBankAllowed :
      ∀ symbol, symbol ∈ bank.reverse → ledgerPayload symbol := by
    intro symbol found
    exact slotBank_allowed capacity registers symbol
      (List.mem_reverse.mp found)
  have hReturnBank :
      workRunExact? machine bank.length returningLedger =
        some returningLedgerBoundary := by
    have scanned := scanRightExact machine cycleReturnLedgerState
      ledgerPayload
      (by
        intro leftSide head suffix headAllowed
        exact cycle_return_ledger_step
          head headAllowed leftSide suffix)
      bank.reverse
      (ledgerBoundary :: travel.reverse ++ markedRight)
      (stackBoundary :: stackPrefix ++ unaryUnit :: stackEnd ::
        List.replicate remaining cellBlank ++ outsideLeft)
      reverseBankAllowed
    simpa [returningLedger, returningLedgerBoundary] using scanned
  have hReturnLedgerBoundary :
      workRunExact? machine 1 returningLedgerBoundary =
        some seeking := by
    apply exactRun_one machine
    simpa [returningLedgerBoundary, seeking] using
      cycle_return_ledger_boundary_step
        (bank ++ stackBoundary :: stackPrefix ++ unaryUnit :: stackEnd ::
          List.replicate remaining cellBlank ++ outsideLeft)
        (travel.reverse ++ markedRight)
  have reverseTravelAllowed :
      ∀ symbol, symbol ∈ travel.reverse →
        scratchPayload symbol := by
    intro symbol found
    exact travelAllowed symbol (List.mem_reverse.mp found)
  have hSeek :
      workRunExact? machine travel.length seeking =
        some atMark := by
    have scanned := scanRightExact machine seekMarkState
      scratchPayload
      (by
        intro leftSide head suffix headAllowed
        exact seek_mark_scratch_step
          head headAllowed leftSide suffix)
      travel.reverse
      markedRight
      (ledgerBoundary :: bank ++ stackBoundary :: stackPrefix ++
        unaryUnit :: stackEnd ::
          List.replicate remaining cellBlank ++ outsideLeft)
      reverseTravelAllowed
    simpa [seeking, atMark] using scanned
  have hSeekMark :
      workRunExact? machine 1 atMark =
        some selectedMark := by
    apply exactRun_one machine
    simpa [atMark, selectedMark, markedRight] using
      seek_mark_step
        (travel ++ ledgerBoundary :: bank ++ stackBoundary :: stackPrefix ++
          unaryUnit :: stackEnd ::
            List.replicate remaining cellBlank ++ outsideLeft)
        (List.replicate processed pushMark ++
          sourceLeftBoundary :: sourceWord)
  have hSelectedMark :
      workRunExact? machine 1 selectedMark =
        some delayedMark := by
    apply exactRun_one machine
    unfold selectedMark delayedMark
    apply stayAtWord_of_find machine rules rfl
    · rfl
    · decide
  have hDelay :
      workRunExact? machine 1 delayedMark =
        some (selectedConfiguration capacity (processed + 1) remaining
          registers checks sourceWord outsideLeft) := by
    apply exactRun_one machine
    simpa [delayedMark, selectedConfiguration, travel, markedRight,
      stackDuringPush, stackPrefix, records,
      cons_replicate_eq_succ_append,
      replicate_cons_eq_succ_append,
      List.replicate_succ,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      List.append_assoc] using
      selected_delay_step
        (travel ++ ledgerBoundary :: bank ++ stackBoundary :: stackPrefix ++
          unaryUnit :: stackEnd ::
            List.replicate remaining cellBlank ++ outsideLeft)
        (List.replicate processed pushMark ++
          sourceLeftBoundary :: sourceWord)
  have h01 := exactRun_add machine 1 travel.length _ _ _
    hSelected hTravel
  have h02 := exactRun_add machine (1 + travel.length) 1 _ _ _
    h01 hScratchBoundary
  have h03 := exactRun_add machine
    (1 + travel.length + 1) bank.length _ _ _ h02 hBank
  have h04 := exactRun_add machine
    (1 + travel.length + 1 + bank.length) 1 _ _ _
    h03 hLedgerBoundary
  have h05 := exactRun_add machine
    (1 + travel.length + 1 + bank.length + 1)
    stackPrefix.length _ _ _ h04 hPrefix
  have h06 := exactRun_add machine
    (1 + travel.length + 1 + bank.length + 1 +
      stackPrefix.length) 1 _ _ _ h05 hStackEnd
  have h07 := exactRun_add machine
    (1 + travel.length + 1 + bank.length + 1 +
      stackPrefix.length + 1) 1 _ _ _ h06 hAppend
  have h08 := exactRun_add machine
    (1 + travel.length + 1 + bank.length + 1 +
      stackPrefix.length + 1 + 1) (stackPrefix.length + 1)
    _ _ _ h07 hReturnPrefix
  have h09 := exactRun_add machine
    (1 + travel.length + 1 + bank.length + 1 +
      stackPrefix.length + 1 + 1 + (stackPrefix.length + 1)) 1
    _ _ _ h08 hReturnStackBoundary
  have h10 := exactRun_add machine
    (1 + travel.length + 1 + bank.length + 1 +
      stackPrefix.length + 1 + 1 + (stackPrefix.length + 1) + 1)
    bank.length _ _ _ h09 hReturnBank
  have h11 := exactRun_add machine
    (1 + travel.length + 1 + bank.length + 1 +
      stackPrefix.length + 1 + 1 + (stackPrefix.length + 1) + 1 +
        bank.length) 1 _ _ _ h10 hReturnLedgerBoundary
  have h12 := exactRun_add machine
    (1 + travel.length + 1 + bank.length + 1 +
      stackPrefix.length + 1 + 1 + (stackPrefix.length + 1) + 1 +
        bank.length + 1) travel.length _ _ _ h11 hSeek
  have h13 := exactRun_add machine
    (1 + travel.length + 1 + bank.length + 1 +
      stackPrefix.length + 1 + 1 + (stackPrefix.length + 1) + 1 +
        bank.length + 1 + travel.length) 1 _ _ _ h12 hSeekMark
  have h14 := exactRun_add machine
    (1 + travel.length + 1 + bank.length + 1 +
      stackPrefix.length + 1 + 1 + (stackPrefix.length + 1) + 1 +
        bank.length + 1 + travel.length + 1) 1 _ _ _
    h13 hSelectedMark
  have complete := exactRun_add machine
    (1 + travel.length + 1 + bank.length + 1 +
      stackPrefix.length + 1 + 1 + (stackPrefix.length + 1) + 1 +
        bank.length + 1 + travel.length + 1 + 1) 1 _ _ _
    h14 hDelay
  have travelLength :
      travel.length = capacity - processed := by
    simp [travel]
    omega
  have prefixLength :
      stackPrefix.length = records.length + processed + 1 := by
    simp [stackPrefix]
    omega
  have steps :
      1 + travel.length + 1 + bank.length + 1 +
          stackPrefix.length + 1 + 1 + (stackPrefix.length + 1) + 1 +
            bank.length + 1 + travel.length + 1 + 1 + 1 =
        2 * capacity + 2 * bank.length + 2 * records.length + 13 := by
    rw [travelLength, prefixLength]
    omega
  rw [steps] at complete
  simpa [bank, records] using complete

private theorem copy_cycles_exact
    (capacity processed remaining : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceWord outsideLeft : List WorkSymbol)
    (bounded : processed + remaining ≤ capacity) :
    workRunExact? machine
        (remaining *
          (2 * capacity +
            2 * (TargetEmitterLedger.slotBank capacity registers).length +
            2 * (recordsWord checks).length + 13))
        (selectedConfiguration capacity processed remaining
          registers checks sourceWord outsideLeft) =
      some (selectedConfiguration capacity (processed + remaining) 0
        registers checks sourceWord outsideLeft) := by
  induction remaining generalizing processed with
  | zero =>
      simp [workRunExact?]
  | succ remaining ih =>
      have oneCycle :=
        copy_cycle_exact capacity processed remaining registers checks
          sourceWord outsideLeft (by omega)
      have rest :=
        ih (processed := processed + 1) (by omega)
      have complete := exactRun_add machine
        (2 * capacity +
          2 * (TargetEmitterLedger.slotBank capacity registers).length +
          2 * (recordsWord checks).length + 13)
        (remaining *
          (2 * capacity +
            2 * (TargetEmitterLedger.slotBank capacity registers).length +
            2 * (recordsWord checks).length + 13))
        _ _ _ oneCycle rest
      simpa [Nat.succ_eq_add_one, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm, Nat.add_mul] using complete

private theorem finish_exact (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (_valueBound : value ≤ capacity) :
    workRunExact? machine (value + 2)
        (selectedConfiguration capacity value 0 registers checks
          (sourceHead :: sourceTail ++ targetAndRight) outsideLeft) =
      some (finalConfiguration capacity value registers checks
        sourceHead sourceTail targetAndRight outsideLeft) := by
  let bank := TargetEmitterLedger.slotBank capacity registers
  let records := recordsWord checks
  let source := sourceHead :: sourceTail ++ targetAndRight
  let restoreLeft :=
    unarySeparator ::
      List.replicate (capacity - value) cellBlank ++
        ledgerBoundary :: bank ++ stackBoundary :: records ++
          recordBoundary :: List.replicate value unaryUnit ++
            stackEnd :: outsideLeft
  let restoring :=
    configAtWord restoreState restoreLeft
      (List.replicate value pushMark ++
        sourceLeftBoundary :: source)
  let atSource :=
    configAtWord restoreState
      (List.replicate value unaryUnit ++ restoreLeft)
      (sourceLeftBoundary :: source)
  have hSeparator :
      workRunExact? machine 1
          (selectedConfiguration capacity value 0 registers checks
            source outsideLeft) =
        some restoring := by
    apply exactRun_one machine
    simpa [selectedConfiguration, restoring, restoreLeft,
      stackDuringPush, bank, records,
      List.append_assoc] using
      selected_separator_step
        (List.replicate (capacity - value) cellBlank ++
          ledgerBoundary :: bank ++ stackBoundary :: records ++
            recordBoundary :: List.replicate value unaryUnit ++
              stackEnd :: outsideLeft)
        (List.replicate value pushMark ++
          sourceLeftBoundary :: source)
  have hRestore :
      workRunExact? machine value restoring =
        some atSource := by
    simpa [restoring, atSource] using
      restore_marks_exact value restoreLeft
        (sourceLeftBoundary :: source)
  have hSource :
      workRunExact? machine 1 atSource =
        some (finalConfiguration capacity value registers checks
          sourceHead sourceTail targetAndRight outsideLeft) := by
    apply exactRun_one machine
    simpa [atSource, finalConfiguration, restoreLeft, scratchWord,
      stackWord, recordsWord_push, recordWord, bank, records, source,
      List.append_assoc] using
      restore_source_step
        (List.replicate value unaryUnit ++ restoreLeft)
        source
  have h01 := exactRun_add machine 1 value _ _ _
    hSeparator hRestore
  have complete := exactRun_add machine (1 + value) 1 _ _ _
    h01 hSource
  have steps : 1 + value + 1 = value + 2 := by
    omega
  rw [steps] at complete
  exact complete

theorem exact (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    workRunExact? machine
        (workSteps capacity (recordsWord checks).length value)
        (entryConfiguration capacity value registers checks
          sourceHead sourceTail targetAndRight outsideLeft) =
      some (finalConfiguration capacity value registers checks
        sourceHead sourceTail targetAndRight outsideLeft) := by
  let source := sourceHead :: sourceTail ++ targetAndRight
  have setup :=
    setup_exact capacity value registers checks sourceHead sourceTail
      targetAndRight outsideLeft fits valueBound allowed
  have cycles :=
    copy_cycles_exact capacity 0 value registers checks source
      outsideLeft (by omega)
  have finish :=
    finish_exact capacity value registers checks sourceHead sourceTail
      targetAndRight outsideLeft valueBound
  have finish' :
      workRunExact? machine (value + 2)
          (selectedConfiguration capacity (0 + value) 0
            registers checks source outsideLeft) =
        some (finalConfiguration capacity value registers checks
          sourceHead sourceTail targetAndRight outsideLeft) := by
    simpa [source] using finish
  have h01 := exactRun_add machine
    (14 * capacity + 2 * (recordsWord checks).length + 38)
    (value *
      (2 * capacity +
        2 * (TargetEmitterLedger.slotBank capacity registers).length +
        2 * (recordsWord checks).length + 13))
    _ _ _ setup cycles
  have complete := exactRun_add machine
    (14 * capacity + 2 * (recordsWord checks).length + 38 +
      value *
        (2 * capacity +
          2 * (TargetEmitterLedger.slotBank capacity registers).length +
          2 * (recordsWord checks).length + 13))
    (value + 2) _ _ _ h01 finish'
  have bankLength :
      (TargetEmitterLedger.slotBank capacity registers).length =
        6 * (capacity + 2) :=
    slotBank_length capacity registers fits
  have steps :
      14 * capacity + 2 * (recordsWord checks).length + 38 +
          value *
            (2 * capacity +
              2 *
                (TargetEmitterLedger.slotBank capacity registers).length +
              2 * (recordsWord checks).length + 13) +
          (value + 2) =
        workSteps capacity (recordsWord checks).length value := by
    rw [bankLength]
    have cycleSize :
        2 * capacity + 2 * (6 * (capacity + 2)) +
            2 * (recordsWord checks).length + 13 =
          14 * capacity + 2 * (recordsWord checks).length + 37 := by
      omega
    rw [cycleSize]
    unfold workSteps
    have coefficient :
        14 * capacity + 2 * (recordsWord checks).length + 38 =
          (14 * capacity + 2 * (recordsWord checks).length + 37) + 1 := by
      omega
    rw [coefficient]
    have multipliedCoefficient :
        value *
            ((14 * capacity +
                2 * (recordsWord checks).length + 37) + 1) =
          value *
              (14 * capacity +
                2 * (recordsWord checks).length + 37) + value :=
      Nat.mul_succ value
        (14 * capacity + 2 * (recordsWord checks).length + 37)
    rw [multipliedCoefficient]
    omega
  rw [steps] at complete
  exact complete

theorem final_halted (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    machine.isHalted
      (finalConfiguration capacity value registers checks
        sourceHead sourceTail targetAndRight outsideLeft) = true := by
  rfl

end Push

/-! ### Exact conditional newest-record pop -/

namespace Pop

def entryConfiguration (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord startState
    (sourceLeftBoundary ::
      (scratchWord capacity 0 ++
        ledgerBoundary ::
          (TargetEmitterLedger.slotBank capacity registers ++
            stackWord checks ++ outsideLeft)))
    (sourceHead :: sourceTail ++ targetAndRight)

def emptyFinalConfiguration (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord rejectState
    (sourceLeftBoundary ::
      (scratchWord capacity 0 ++
        ledgerBoundary ::
          (TargetEmitterLedger.slotBank capacity registers ++
            stackWord [] ++ outsideLeft)))
    (sourceHead :: sourceTail ++ targetAndRight)

def nonemptyFinalConfiguration (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord acceptState
    (sourceLeftBoundary ::
      (scratchWord capacity value ++
        ledgerBoundary ::
          (TargetEmitterLedger.slotBank capacity registers ++
            stackWord prior ++
              List.replicate (value + 1) cellBlank ++ outsideLeft)))
    (sourceHead :: sourceTail ++ targetAndRight)

def emptyWorkSteps (capacity : Nat) : Nat :=
  14 * capacity + 34

def emptyPolynomialWorkBound (capacity : Nat) : Nat :=
  14 * capacity + 34

theorem emptyWorkSteps_le_polynomialWorkBound (capacity : Nat) :
    emptyWorkSteps capacity ≤ emptyPolynomialWorkBound capacity := by
  exact Nat.le_refl _

def nonemptyWorkSteps
    (capacity recordsLength value : Nat) : Nat :=
  14 * capacity + 2 * recordsLength + value + 38 +
    value * (14 * capacity + 2 * recordsLength + 2 * value + 43)

def nonemptyPolynomialWorkBound
    (capacity recordsLength value : Nat) : Nat :=
  14 * capacity + 2 * recordsLength + value + 38 +
    value * (14 * capacity + 2 * recordsLength + 2 * value + 43)

theorem nonemptyWorkSteps_le_polynomialWorkBound
    (capacity recordsLength value : Nat) :
    nonemptyWorkSteps capacity recordsLength value ≤
      nonemptyPolynomialWorkBound capacity recordsLength value := by
  exact Nat.le_refl _

private theorem start_step (symbol : WorkSymbol)
    (allowed : sourceAllowed symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord startState left (symbol :: right)) =
      some (configAtLeftWord boundaryState
        left (symbol :: right)) := by
  apply moveLeftFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c | d | e
    all_goals subst symbol
    all_goals decide

private theorem boundary_step (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord boundaryState
          (sourceLeftBoundary :: left) right) =
      some (configAtLeftWord scratchZeroState
        left (sourceLeftBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem scratch_zero_step (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord scratchZeroState
          (unarySeparator :: left) right) =
      some (configAtLeftWord scratchReserveState
        left (unarySeparator :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem scratch_blank_step (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord scratchReserveState
          (cellBlank :: left) right) =
      some (configAtLeftWord scratchReserveState
        left (cellBlank :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem scratch_ledger_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord scratchReserveState
          (ledgerBoundary :: left) right) =
      some (configAtLeftWord ledgerState
        left (ledgerBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem ledger_step (symbol : WorkSymbol)
    (allowed : ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord ledgerState
          (symbol :: left) right) =
      some (configAtLeftWord ledgerState
        left (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c | d
    all_goals subst symbol
    all_goals decide

private theorem ledger_stack_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord ledgerState
          (stackBoundary :: left) right) =
      some (configAtLeftWord stackMaybeState
        left (stackBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem stack_maybe_empty_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord stackMaybeState
          (stackEnd :: left) right) =
      some (configAtWord emptyReturnBoundaryState
        (stackEnd :: left) right) := by
  apply moveRightFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem stack_maybe_record_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord stackMaybeState
          (recordBoundary :: left) right) =
      some (configAtLeftWord stackNonemptyState
        left (recordBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem stack_nonempty_record_step
    (symbol : WorkSymbol) (allowed : recordPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord stackNonemptyState
          (symbol :: left) right) =
      some (configAtLeftWord stackNonemptyState
        left (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b
    all_goals subst symbol
    all_goals decide

private theorem stack_nonempty_end_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord stackNonemptyState
          (stackEnd :: left) right) =
      some (configAtWord recordState
        (stackEnd :: left) right) := by
  apply moveRightFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem record_unit_step (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord recordState left
          (unaryUnit :: right)) =
      some (configAtWord bounceStackState
        (popMark :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem record_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord recordState left
          (recordBoundary :: right)) =
      some (configAtLeftWord eraseOldFinishState
        left (stackEnd :: right)) := by
  apply moveLeftFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem bounce_stack_step
    (symbol : WorkSymbol) (allowed : recordPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord bounceStackState left
          (symbol :: right)) =
      some (configAtWord bounceStackState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b
    all_goals subst symbol
    all_goals decide

private theorem bounce_stack_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord bounceStackState left
          (stackBoundary :: right)) =
      some (configAtWord bounceLedgerState
        (stackBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem bounce_ledger_step
    (symbol : WorkSymbol) (allowed : ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord bounceLedgerState left
          (symbol :: right)) =
      some (configAtWord bounceLedgerState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c | d
    all_goals subst symbol
    all_goals decide

private theorem bounce_ledger_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord bounceLedgerState left
          (ledgerBoundary :: right)) =
      some (configAtWord bounceScratchState
        (ledgerBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem bounce_scratch_step
    (symbol : WorkSymbol) (allowed : scratchPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord bounceScratchState left
          (symbol :: right)) =
      some (configAtWord bounceScratchState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c
    all_goals subst symbol
    all_goals decide

private theorem bounce_source_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord bounceScratchState left
          (sourceLeftBoundary :: right)) =
      some (configAtWord incrementStartState
        (sourceLeftBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem increment_start_step (symbol : WorkSymbol)
    (allowed : sourceAllowed symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord incrementStartState left
          (symbol :: right)) =
      some (configAtLeftWord incrementBoundaryState
        left (symbol :: right)) := by
  apply moveLeftFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c | d | e
    all_goals subst symbol
    all_goals decide

private theorem increment_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord incrementBoundaryState
          (sourceLeftBoundary :: left) right) =
      some (configAtLeftWord incrementSeekState
        left (sourceLeftBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem increment_seek_unit_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord incrementSeekState
          (unaryUnit :: left) right) =
      some (configAtLeftWord incrementSeekState
        left (unaryUnit :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem increment_seek_separator_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord incrementSeekState
          (unarySeparator :: left) right) =
      some (configAtLeftWord incrementWriteState
        left (unaryUnit :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem increment_write_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord incrementWriteState
          (cellBlank :: left) right) =
      some (configAtWord incrementReturnState
        (unarySeparator :: left) right) := by
  apply moveRightFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem increment_return_unit_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord incrementReturnState left
          (unaryUnit :: right)) =
      some (configAtWord incrementReturnState
        (unaryUnit :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem increment_return_source_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord incrementReturnState left
          (sourceLeftBoundary :: right)) =
      some (configAtWord resumeStartState
        (sourceLeftBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem resume_start_step (symbol : WorkSymbol)
    (allowed : sourceAllowed symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord resumeStartState left
          (symbol :: right)) =
      some (configAtLeftWord resumeBoundaryState
        left (symbol :: right)) := by
  apply moveLeftFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c | d | e
    all_goals subst symbol
    all_goals decide

private theorem resume_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord resumeBoundaryState
          (sourceLeftBoundary :: left) right) =
      some (configAtLeftWord resumeScratchUnitsState
        left (sourceLeftBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem resume_scratch_unit_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord resumeScratchUnitsState
          (unaryUnit :: left) right) =
      some (configAtLeftWord resumeScratchUnitsState
        left (unaryUnit :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem resume_scratch_separator_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord resumeScratchUnitsState
          (unarySeparator :: left) right) =
      some (configAtLeftWord resumeScratchReserveState
        left (unarySeparator :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem resume_scratch_blank_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord resumeScratchReserveState
          (cellBlank :: left) right) =
      some (configAtLeftWord resumeScratchReserveState
        left (cellBlank :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem resume_scratch_ledger_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord resumeScratchReserveState
          (ledgerBoundary :: left) right) =
      some (configAtLeftWord resumeLedgerState
        left (ledgerBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem resume_ledger_step
    (symbol : WorkSymbol) (allowed : ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord resumeLedgerState
          (symbol :: left) right) =
      some (configAtLeftWord resumeLedgerState
        left (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c | d
    all_goals subst symbol
    all_goals decide

private theorem resume_ledger_stack_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord resumeLedgerState
          (stackBoundary :: left) right) =
      some (configAtLeftWord resumeStackState
        left (stackBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem resume_stack_record_step
    (symbol : WorkSymbol) (allowed : recordPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord resumeStackState
          (symbol :: left) right) =
      some (configAtLeftWord resumeStackState
        left (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b
    all_goals subst symbol
    all_goals decide

private theorem resume_stack_mark_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord resumeStackState
          (popMark :: left) right) =
      some (configAtLeftWord eraseOldContinueState
        left (stackEnd :: right)) := by
  apply moveLeftFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem erase_old_continue_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord eraseOldContinueState
          (stackEnd :: left) right) =
      some (configAtWord crossNewContinueState
        (cellBlank :: left) right) := by
  apply moveRightFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem cross_new_continue_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord crossNewContinueState left
          (stackEnd :: right)) =
      some (configAtWord recordState
        (stackEnd :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem erase_old_finish_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord eraseOldFinishState
          (stackEnd :: left) right) =
      some (configAtWord crossNewFinishState
        (cellBlank :: left) right) := by
  apply moveRightFromLeftWord_of_find machine rules rfl
  · rfl
  · decide

private theorem cross_new_finish_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord crossNewFinishState left
          (stackEnd :: right)) =
      some (configAtWord returnStackState
        (stackEnd :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem return_stack_step
    (symbol : WorkSymbol) (allowed : recordPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord returnStackState left
          (symbol :: right)) =
      some (configAtWord returnStackState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b
    all_goals subst symbol
    all_goals decide

private theorem return_stack_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord returnStackState left
          (stackBoundary :: right)) =
      some (configAtWord returnLedgerState
        (stackBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem return_ledger_step
    (symbol : WorkSymbol) (allowed : ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord returnLedgerState left
          (symbol :: right)) =
      some (configAtWord returnLedgerState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c | d
    all_goals subst symbol
    all_goals decide

private theorem return_ledger_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord returnLedgerState left
          (ledgerBoundary :: right)) =
      some (configAtWord returnScratchState
        (ledgerBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem return_scratch_step
    (symbol : WorkSymbol) (allowed : scratchPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord returnScratchState left
          (symbol :: right)) =
      some (configAtWord returnScratchState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c
    all_goals subst symbol
    all_goals decide

private theorem return_source_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord returnScratchState left
          (sourceLeftBoundary :: right)) =
      some (configAtWord acceptState
        (sourceLeftBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem empty_return_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord emptyReturnBoundaryState left
          (stackBoundary :: right)) =
      some (configAtWord emptyReturnLedgerState
        (stackBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem empty_return_ledger_step
    (symbol : WorkSymbol) (allowed : ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord emptyReturnLedgerState left
          (symbol :: right)) =
      some (configAtWord emptyReturnLedgerState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c | d
    all_goals subst symbol
    all_goals decide

private theorem empty_return_ledger_boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord emptyReturnLedgerState left
          (ledgerBoundary :: right)) =
      some (configAtWord emptyReturnScratchState
        (ledgerBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

private theorem empty_return_scratch_step
    (symbol : WorkSymbol) (allowed : scratchPayload symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord emptyReturnScratchState left
          (symbol :: right)) =
      some (configAtWord emptyReturnScratchState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · rcases allowed with a | b | c
    all_goals subst symbol
    all_goals decide

private theorem empty_return_source_step
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord emptyReturnScratchState left
          (sourceLeftBoundary :: right)) =
      some (configAtWord rejectState
        (sourceLeftBoundary :: left) right) := by
  apply moveRightFromWord_of_find machine rules rfl
  · rfl
  · decide

theorem empty_exact (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (allowed : sourceAllowed sourceHead) :
    workRunExact? machine (emptyWorkSteps capacity)
        (entryConfiguration capacity registers []
          sourceHead sourceTail targetAndRight outsideLeft) =
      some (emptyFinalConfiguration capacity registers
        sourceHead sourceTail targetAndRight outsideLeft) := by
  let scratchW := scratchWord capacity 0
  let bank := TargetEmitterLedger.slotBank capacity registers
  let source := sourceHead :: sourceTail ++ targetAndRight
  let afterSource :=
    configAtLeftWord boundaryState
      (sourceLeftBoundary :: scratchW ++ ledgerBoundary :: bank ++
        stackBoundary :: stackEnd :: outsideLeft)
      source
  let afterBoundary :=
    configAtLeftWord scratchZeroState
      (scratchW ++ ledgerBoundary :: bank ++
        stackBoundary :: stackEnd :: outsideLeft)
      (sourceLeftBoundary :: source)
  let afterZero :=
    configAtLeftWord scratchReserveState
      (List.replicate capacity cellBlank ++ ledgerBoundary :: bank ++
        stackBoundary :: stackEnd :: outsideLeft)
      (unarySeparator :: sourceLeftBoundary :: source)
  let atLedger :=
    configAtLeftWord scratchReserveState
      (ledgerBoundary :: bank ++ stackBoundary :: stackEnd :: outsideLeft)
      (scratchW.reverse ++ sourceLeftBoundary :: source)
  let atStackBoundary :=
    configAtLeftWord ledgerState
      (stackBoundary :: stackEnd :: outsideLeft)
      (bank.reverse ++ ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: source)
  let atEnd :=
    configAtLeftWord stackMaybeState
      (stackEnd :: outsideLeft)
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: source)
  let returningBoundary :=
    configAtWord emptyReturnBoundaryState
      (stackEnd :: outsideLeft)
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: source)
  let returningLedger :=
    configAtWord emptyReturnLedgerState
      (stackBoundary :: stackEnd :: outsideLeft)
      (bank.reverse ++ ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: source)
  let returningLedgerBoundary :=
    configAtWord emptyReturnLedgerState
      (bank ++ stackBoundary :: stackEnd :: outsideLeft)
      (ledgerBoundary :: scratchW.reverse ++ sourceLeftBoundary :: source)
  let returningScratch :=
    configAtWord emptyReturnScratchState
      (ledgerBoundary :: bank ++ stackBoundary :: stackEnd :: outsideLeft)
      (scratchW.reverse ++ sourceLeftBoundary :: source)
  let returningSource :=
    configAtWord emptyReturnScratchState
      (scratchW ++ ledgerBoundary :: bank ++
        stackBoundary :: stackEnd :: outsideLeft)
      (sourceLeftBoundary :: source)
  have hSource :
      workRunExact? machine 1
          (entryConfiguration capacity registers []
            sourceHead sourceTail targetAndRight outsideLeft) =
        some afterSource := by
    apply exactRun_one machine
    simpa [entryConfiguration, afterSource, scratchW, bank, source,
      stackWord, recordsWord, List.append_assoc] using
      start_step sourceHead allowed
        (sourceLeftBoundary :: scratchW ++ ledgerBoundary :: bank ++
          stackBoundary :: stackEnd :: outsideLeft)
        (sourceTail ++ targetAndRight)
  have hBoundary :
      workRunExact? machine 1 afterSource =
        some afterBoundary := by
    apply exactRun_one machine
    simpa [afterSource, afterBoundary] using
      boundary_step
        (scratchW ++ ledgerBoundary :: bank ++
          stackBoundary :: stackEnd :: outsideLeft)
        source
  have hZero :
      workRunExact? machine 1 afterBoundary =
        some afterZero := by
    apply exactRun_one machine
    simpa [afterBoundary, afterZero, scratchW, scratchWord] using
      scratch_zero_step
        (List.replicate capacity cellBlank ++ ledgerBoundary :: bank ++
          stackBoundary :: stackEnd :: outsideLeft)
        (sourceLeftBoundary :: source)
  have hReserve :
      workRunExact? machine capacity afterZero =
        some atLedger := by
    have scanned := scanLeftExact machine scratchReserveState
      (fun symbol => symbol = cellBlank)
      (by
        intro head leftTail rightSide equality
        subst head
        exact scratch_blank_step leftTail rightSide)
      (List.replicate capacity cellBlank)
      (ledgerBoundary :: bank ++ stackBoundary :: stackEnd :: outsideLeft)
      (unarySeparator :: sourceLeftBoundary :: source)
      (by
        intro symbol found
        exact List.eq_of_mem_replicate found)
    simpa [afterZero, atLedger, scratchW, scratchWord,
      List.append_assoc] using scanned
  have hScratchLedger :
      workRunExact? machine 1 atLedger =
        some
          (configAtLeftWord ledgerState
            (bank ++ stackBoundary :: stackEnd :: outsideLeft)
            (ledgerBoundary :: scratchW.reverse ++
              sourceLeftBoundary :: source)) := by
    apply exactRun_one machine
    simpa [atLedger] using
      scratch_ledger_boundary_step
        (bank ++ stackBoundary :: stackEnd :: outsideLeft)
        (scratchW.reverse ++ sourceLeftBoundary :: source)
  have hBank :
      workRunExact? machine bank.length
          (configAtLeftWord ledgerState
            (bank ++ stackBoundary :: stackEnd :: outsideLeft)
            (ledgerBoundary :: scratchW.reverse ++
              sourceLeftBoundary :: source)) =
        some atStackBoundary := by
    have scanned := scanLeftExact machine ledgerState ledgerPayload
      (by
        intro head leftTail rightSide headAllowed
        exact ledger_step head headAllowed leftTail rightSide)
      bank
      (stackBoundary :: stackEnd :: outsideLeft)
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: source)
      (slotBank_allowed capacity registers)
    simpa [atStackBoundary] using scanned
  have hStackBoundary :
      workRunExact? machine 1 atStackBoundary =
        some atEnd := by
    apply exactRun_one machine
    simpa [atStackBoundary, atEnd] using
      ledger_stack_boundary_step
        (stackEnd :: outsideLeft)
        (bank.reverse ++ ledgerBoundary :: scratchW.reverse ++
          sourceLeftBoundary :: source)
  have hEmpty :
      workRunExact? machine 1 atEnd =
        some returningBoundary := by
    apply exactRun_one machine
    simpa [atEnd, returningBoundary] using
      stack_maybe_empty_step outsideLeft
        (stackBoundary :: bank.reverse ++ ledgerBoundary ::
          scratchW.reverse ++ sourceLeftBoundary :: source)
  have hReturnBoundary :
      workRunExact? machine 1 returningBoundary =
        some returningLedger := by
    apply exactRun_one machine
    simpa [returningBoundary, returningLedger] using
      empty_return_boundary_step
        (stackEnd :: outsideLeft)
        (bank.reverse ++ ledgerBoundary :: scratchW.reverse ++
          sourceLeftBoundary :: source)
  have reverseBankAllowed :
      ∀ symbol, symbol ∈ bank.reverse → ledgerPayload symbol := by
    intro symbol found
    exact slotBank_allowed capacity registers symbol
      (List.mem_reverse.mp found)
  have hReturnBank :
      workRunExact? machine bank.length returningLedger =
        some returningLedgerBoundary := by
    have scanned := scanRightExact machine emptyReturnLedgerState
      ledgerPayload
      (by
        intro leftSide head suffix headAllowed
        exact empty_return_ledger_step
          head headAllowed leftSide suffix)
      bank.reverse
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: source)
      (stackBoundary :: stackEnd :: outsideLeft)
      reverseBankAllowed
    simpa [returningLedger, returningLedgerBoundary] using scanned
  have hReturnLedgerBoundary :
      workRunExact? machine 1 returningLedgerBoundary =
        some returningScratch := by
    apply exactRun_one machine
    simpa [returningLedgerBoundary, returningScratch] using
      empty_return_ledger_boundary_step
        (bank ++ stackBoundary :: stackEnd :: outsideLeft)
        (scratchW.reverse ++ sourceLeftBoundary :: source)
  have reverseScratchAllowed :
      ∀ symbol, symbol ∈ scratchW.reverse →
        scratchPayload symbol := by
    intro symbol found
    have original := List.mem_reverse.mp found
    unfold scratchW scratchWord at original
    rw [List.mem_append] at original
    rcases original with unit | tail
    · exact Or.inl (List.eq_of_mem_replicate unit)
    · cases tail with
      | head =>
          exact Or.inr (Or.inl rfl)
      | tail _ blank =>
          exact Or.inr (Or.inr
            (List.eq_of_mem_replicate blank))
  have hReturnScratch :
      workRunExact? machine scratchW.length returningScratch =
        some returningSource := by
    have scanned := scanRightExact machine emptyReturnScratchState
      scratchPayload
      (by
        intro leftSide head suffix headAllowed
        exact empty_return_scratch_step
          head headAllowed leftSide suffix)
      scratchW.reverse
      (sourceLeftBoundary :: source)
      (ledgerBoundary :: bank ++
        stackBoundary :: stackEnd :: outsideLeft)
      reverseScratchAllowed
    simpa [returningScratch, returningSource] using scanned
  have hReturnSource :
      workRunExact? machine 1 returningSource =
        some (emptyFinalConfiguration capacity registers
          sourceHead sourceTail targetAndRight outsideLeft) := by
    apply exactRun_one machine
    simpa [returningSource, emptyFinalConfiguration, scratchW, bank,
      source, stackWord, recordsWord, List.append_assoc] using
      empty_return_source_step
        (scratchW ++ ledgerBoundary :: bank ++
          stackBoundary :: stackEnd :: outsideLeft)
        source
  have h01 := exactRun_add machine 1 1 _ _ _
    hSource hBoundary
  have h02 := exactRun_add machine 2 1 _ _ _
    h01 hZero
  have h03 := exactRun_add machine 3 capacity _ _ _
    h02 hReserve
  have h04 := exactRun_add machine (3 + capacity) 1 _ _ _
    h03 hScratchLedger
  have h05 := exactRun_add machine
    (3 + capacity + 1) bank.length _ _ _ h04 hBank
  have h06 := exactRun_add machine
    (3 + capacity + 1 + bank.length) 1 _ _ _
    h05 hStackBoundary
  have h07 := exactRun_add machine
    (3 + capacity + 1 + bank.length + 1) 1 _ _ _
    h06 hEmpty
  have h08 := exactRun_add machine
    (3 + capacity + 1 + bank.length + 1 + 1) 1 _ _ _
    h07 hReturnBoundary
  have h09 := exactRun_add machine
    (3 + capacity + 1 + bank.length + 1 + 1 + 1)
    bank.length _ _ _ h08 hReturnBank
  have h10 := exactRun_add machine
    (3 + capacity + 1 + bank.length + 1 + 1 + 1 +
      bank.length) 1 _ _ _ h09 hReturnLedgerBoundary
  have h11 := exactRun_add machine
    (3 + capacity + 1 + bank.length + 1 + 1 + 1 +
      bank.length + 1) scratchW.length _ _ _
    h10 hReturnScratch
  have complete := exactRun_add machine
    (3 + capacity + 1 + bank.length + 1 + 1 + 1 +
      bank.length + 1 + scratchW.length) 1 _ _ _
    h11 hReturnSource
  have scratchLength :
      scratchW.length = capacity + 1 := by
    exact scratchWord_length_of_le capacity 0 (Nat.zero_le _)
  have bankLength :
      bank.length = 6 * (capacity + 2) :=
    slotBank_length capacity registers fits
  have steps :
      3 + capacity + 1 + bank.length + 1 + 1 + 1 +
          bank.length + 1 + scratchW.length + 1 =
        emptyWorkSteps capacity := by
    rw [scratchLength, bankLength]
    unfold emptyWorkSteps
    omega
  rw [steps] at complete
  exact complete

theorem empty_final_halted (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    machine.isHalted
      (emptyFinalConfiguration capacity registers
        sourceHead sourceTail targetAndRight outsideLeft) = true := by
  rfl

private def firstRecordTail (prior : List Nat) (value : Nat) :
    List WorkSymbol :=
  match prior with
  | [] =>
      List.replicate value unaryUnit
  | first :: rest =>
      List.replicate first unaryUnit ++
        recordsWord rest ++ recordWord value

private theorem records_append_last_eq_boundary_tail
    (prior : List Nat) (value : Nat) :
    recordsWord (prior ++ [value]) =
      recordBoundary :: firstRecordTail prior value := by
  cases prior with
  | nil =>
      simp [recordsWord, recordWord, firstRecordTail]
  | cons first rest =>
      simp [recordsWord, recordWord, firstRecordTail,
        List.append_assoc]

private def remainingRecordPrefix
    (prior : List Nat) (value processed : Nat) :
    List WorkSymbol :=
  recordsWord prior ++
    recordBoundary ::
      List.replicate (value - processed) unaryUnit

private def poppingConfiguration
    (capacity value processed : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat) (sourceWord outsideLeft : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord recordState
    (stackEnd ::
      List.replicate processed cellBlank ++ outsideLeft)
    ((remainingRecordPrefix prior value processed).reverse ++
      stackBoundary ::
        (TargetEmitterLedger.slotBank capacity registers).reverse ++
          ledgerBoundary ::
            (scratchWord capacity processed).reverse ++
              sourceLeftBoundary :: sourceWord)

private theorem nonempty_setup_exact
    (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (_fits : LedgerFits capacity registers)
    (allowed : sourceAllowed sourceHead) :
    workRunExact? machine
        (capacity +
          (TargetEmitterLedger.slotBank capacity registers).length +
          (recordsWord (prior ++ [value])).length + 6)
        (entryConfiguration capacity registers (prior ++ [value])
          sourceHead sourceTail targetAndRight outsideLeft) =
      some (poppingConfiguration capacity value 0 registers prior
        (sourceHead :: sourceTail ++ targetAndRight) outsideLeft) := by
  let scratchW := scratchWord capacity 0
  let bank := TargetEmitterLedger.slotBank capacity registers
  let fullRecords := recordsWord (prior ++ [value])
  let recordTail := firstRecordTail prior value
  let source := sourceHead :: sourceTail ++ targetAndRight
  let afterSource :=
    configAtLeftWord boundaryState
      (sourceLeftBoundary :: scratchW ++ ledgerBoundary :: bank ++
        stackBoundary :: fullRecords ++ stackEnd :: outsideLeft)
      source
  let afterBoundary :=
    configAtLeftWord scratchZeroState
      (scratchW ++ ledgerBoundary :: bank ++
        stackBoundary :: fullRecords ++ stackEnd :: outsideLeft)
      (sourceLeftBoundary :: source)
  let afterZero :=
    configAtLeftWord scratchReserveState
      (List.replicate capacity cellBlank ++ ledgerBoundary :: bank ++
        stackBoundary :: fullRecords ++ stackEnd :: outsideLeft)
      (unarySeparator :: sourceLeftBoundary :: source)
  let atLedger :=
    configAtLeftWord scratchReserveState
      (ledgerBoundary :: bank ++ stackBoundary ::
        fullRecords ++ stackEnd :: outsideLeft)
      (scratchW.reverse ++ sourceLeftBoundary :: source)
  let atStackBoundary :=
    configAtLeftWord ledgerState
      (stackBoundary :: fullRecords ++ stackEnd :: outsideLeft)
      (bank.reverse ++ ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: source)
  let atFirstRecord :=
    configAtLeftWord stackMaybeState
      (fullRecords ++ stackEnd :: outsideLeft)
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: source)
  let scanningRecords :=
    configAtLeftWord stackNonemptyState
      (recordTail ++ stackEnd :: outsideLeft)
      (recordBoundary :: stackBoundary :: bank.reverse ++
        ledgerBoundary :: scratchW.reverse ++
          sourceLeftBoundary :: source)
  let atEnd :=
    configAtLeftWord stackNonemptyState
      (stackEnd :: outsideLeft)
      (recordTail.reverse ++ recordBoundary ::
        stackBoundary :: bank.reverse ++ ledgerBoundary ::
          scratchW.reverse ++ sourceLeftBoundary :: source)
  have hSource :
      workRunExact? machine 1
          (entryConfiguration capacity registers (prior ++ [value])
            sourceHead sourceTail targetAndRight outsideLeft) =
        some afterSource := by
    apply exactRun_one machine
    simpa [entryConfiguration, afterSource, scratchW, bank,
      fullRecords, source, stackWord, List.append_assoc] using
      start_step sourceHead allowed
        (sourceLeftBoundary :: scratchW ++ ledgerBoundary :: bank ++
          stackBoundary :: fullRecords ++ stackEnd :: outsideLeft)
        (sourceTail ++ targetAndRight)
  have hBoundary :
      workRunExact? machine 1 afterSource =
        some afterBoundary := by
    apply exactRun_one machine
    simpa [afterSource, afterBoundary] using
      boundary_step
        (scratchW ++ ledgerBoundary :: bank ++
          stackBoundary :: fullRecords ++ stackEnd :: outsideLeft)
        source
  have hZero :
      workRunExact? machine 1 afterBoundary =
        some afterZero := by
    apply exactRun_one machine
    simpa [afterBoundary, afterZero, scratchW, scratchWord] using
      scratch_zero_step
        (List.replicate capacity cellBlank ++ ledgerBoundary :: bank ++
          stackBoundary :: fullRecords ++ stackEnd :: outsideLeft)
        (sourceLeftBoundary :: source)
  have hReserve :
      workRunExact? machine capacity afterZero =
        some atLedger := by
    have scanned := scanLeftExact machine scratchReserveState
      (fun symbol => symbol = cellBlank)
      (by
        intro head leftTail rightSide equality
        subst head
        exact scratch_blank_step leftTail rightSide)
      (List.replicate capacity cellBlank)
      (ledgerBoundary :: bank ++ stackBoundary ::
        fullRecords ++ stackEnd :: outsideLeft)
      (unarySeparator :: sourceLeftBoundary :: source)
      (by
        intro symbol found
        exact List.eq_of_mem_replicate found)
    simpa [afterZero, atLedger, scratchW, scratchWord,
      List.append_assoc] using scanned
  have hScratchLedger :
      workRunExact? machine 1 atLedger =
        some
          (configAtLeftWord ledgerState
            (bank ++ stackBoundary :: fullRecords ++
              stackEnd :: outsideLeft)
            (ledgerBoundary :: scratchW.reverse ++
              sourceLeftBoundary :: source)) := by
    apply exactRun_one machine
    simpa [atLedger] using
      scratch_ledger_boundary_step
        (bank ++ stackBoundary :: fullRecords ++
          stackEnd :: outsideLeft)
        (scratchW.reverse ++ sourceLeftBoundary :: source)
  have hBank :
      workRunExact? machine bank.length
          (configAtLeftWord ledgerState
            (bank ++ stackBoundary :: fullRecords ++
              stackEnd :: outsideLeft)
            (ledgerBoundary :: scratchW.reverse ++
              sourceLeftBoundary :: source)) =
        some atStackBoundary := by
    have scanned := scanLeftExact machine ledgerState ledgerPayload
      (by
        intro head leftTail rightSide headAllowed
        exact ledger_step head headAllowed leftTail rightSide)
      bank
      (stackBoundary :: fullRecords ++ stackEnd :: outsideLeft)
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: source)
      (slotBank_allowed capacity registers)
    simpa [atStackBoundary] using scanned
  have hStackBoundary :
      workRunExact? machine 1 atStackBoundary =
        some atFirstRecord := by
    apply exactRun_one machine
    simpa [atStackBoundary, atFirstRecord] using
      ledger_stack_boundary_step
        (fullRecords ++ stackEnd :: outsideLeft)
        (bank.reverse ++ ledgerBoundary :: scratchW.reverse ++
          sourceLeftBoundary :: source)
  have fullRecordsShape :
      fullRecords = recordBoundary :: recordTail := by
    exact records_append_last_eq_boundary_tail prior value
  have hFirstRecord :
      workRunExact? machine 1 atFirstRecord =
        some scanningRecords := by
    apply exactRun_one machine
    simpa [atFirstRecord, scanningRecords, fullRecordsShape] using
      stack_maybe_record_step
        (recordTail ++ stackEnd :: outsideLeft)
        (stackBoundary :: bank.reverse ++ ledgerBoundary ::
          scratchW.reverse ++ sourceLeftBoundary :: source)
  have recordTailAllowed :
      ∀ symbol, symbol ∈ recordTail → recordPayload symbol := by
    intro symbol found
    have inFull :
        symbol ∈ fullRecords := by
      rw [fullRecordsShape]
      exact List.Mem.tail recordBoundary found
    exact recordsWord_allowed (prior ++ [value]) symbol inFull
  have hRecordTail :
      workRunExact? machine recordTail.length scanningRecords =
        some atEnd := by
    have scanned := scanLeftExact machine stackNonemptyState
      recordPayload
      (by
        intro head leftTail rightSide headAllowed
        exact stack_nonempty_record_step
          head headAllowed leftTail rightSide)
      recordTail
      (stackEnd :: outsideLeft)
      (recordBoundary :: stackBoundary :: bank.reverse ++
        ledgerBoundary :: scratchW.reverse ++
          sourceLeftBoundary :: source)
      recordTailAllowed
    simpa [scanningRecords, atEnd] using scanned
  have hEndRaw :
      workRunExact? machine 1 atEnd =
        some
          (configAtWord recordState (stackEnd :: outsideLeft)
            (fullRecords.reverse ++ stackBoundary :: bank.reverse ++
              ledgerBoundary :: scratchW.reverse ++
                sourceLeftBoundary :: source)) := by
    apply exactRun_one machine
    simpa [atEnd, fullRecordsShape, List.reverse_cons,
      List.append_assoc] using
      stack_nonempty_end_step outsideLeft
        (recordTail.reverse ++ recordBoundary ::
          stackBoundary :: bank.reverse ++ ledgerBoundary ::
            scratchW.reverse ++ sourceLeftBoundary :: source)
  have fullRecordsRemaining :
      fullRecords = remainingRecordPrefix prior value 0 := by
    simp [fullRecords, remainingRecordPrefix, recordsWord_push,
      recordWord]
  have hEnd :
      workRunExact? machine 1 atEnd =
        some (poppingConfiguration capacity value 0 registers prior
          source outsideLeft) := by
    simpa [poppingConfiguration, fullRecordsRemaining, scratchW,
      scratchWord, bank] using hEndRaw
  have h01 := exactRun_add machine 1 1 _ _ _
    hSource hBoundary
  have h02 := exactRun_add machine 2 1 _ _ _
    h01 hZero
  have h03 := exactRun_add machine 3 capacity _ _ _
    h02 hReserve
  have h04 := exactRun_add machine (3 + capacity) 1 _ _ _
    h03 hScratchLedger
  have h05 := exactRun_add machine
    (3 + capacity + 1) bank.length _ _ _ h04 hBank
  have h06 := exactRun_add machine
    (3 + capacity + 1 + bank.length) 1 _ _ _
    h05 hStackBoundary
  have h07 := exactRun_add machine
    (3 + capacity + 1 + bank.length + 1) 1 _ _ _
    h06 hFirstRecord
  have h08 := exactRun_add machine
    (3 + capacity + 1 + bank.length + 1 + 1)
    recordTail.length _ _ _ h07 hRecordTail
  have complete := exactRun_add machine
    (3 + capacity + 1 + bank.length + 1 + 1 +
      recordTail.length) 1 _ _ _ h08 hEnd
  have fullLength :
      fullRecords.length = recordTail.length + 1 := by
    rw [fullRecordsShape]
    simp
  have steps :
      3 + capacity + 1 + bank.length + 1 + 1 +
          recordTail.length + 1 =
        capacity + bank.length + fullRecords.length + 6 := by
    rw [fullLength]
    omega
  rw [steps] at complete
  simpa only [bank, fullRecords, source] using complete

private theorem replicate_succ_append {α : Type}
    (count : Nat) (item : α) :
    List.replicate (count + 1) item =
      List.replicate count item ++ [item] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change item :: List.replicate (count + 1) item =
        item :: (List.replicate count item ++ [item])
      rw [ih]

private theorem increment_exact
    (capacity processed : Nat)
    (farLeft : List WorkSymbol)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (bounded : processed + 1 ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    workRunExact? machine (2 * processed + 6)
        (configAtWord incrementStartState
          (sourceLeftBoundary ::
            scratchWord capacity processed ++ farLeft)
          (sourceHead :: sourceTail)) =
      some
        (configAtWord resumeStartState
          (sourceLeftBoundary ::
            scratchWord capacity (processed + 1) ++ farLeft)
          (sourceHead :: sourceTail)) := by
  let before := scratchWord capacity processed
  let after := scratchWord capacity (processed + 1)
  let source := sourceHead :: sourceTail
  let atBoundary :=
    configAtLeftWord incrementBoundaryState
      (sourceLeftBoundary :: before ++ farLeft) source
  let atScratch :=
    configAtLeftWord incrementSeekState
      (before ++ farLeft) (sourceLeftBoundary :: source)
  let atSeparator :=
    configAtLeftWord incrementSeekState
      (unarySeparator ::
        List.replicate (capacity - processed) cellBlank ++ farLeft)
      (List.replicate processed unaryUnit ++
        sourceLeftBoundary :: source)
  let atWrite :=
    configAtLeftWord incrementWriteState
      (List.replicate (capacity - processed) cellBlank ++ farLeft)
      (unaryUnit :: List.replicate processed unaryUnit ++
        sourceLeftBoundary :: source)
  let returning :=
    configAtWord incrementReturnState
      (unarySeparator ::
        List.replicate (capacity - (processed + 1)) cellBlank ++ farLeft)
      (unaryUnit :: List.replicate processed unaryUnit ++
        sourceLeftBoundary :: source)
  let atSource :=
    configAtWord incrementReturnState
      (after ++ farLeft)
      (sourceLeftBoundary :: source)
  have hStart :
      workRunExact? machine 1
          (configAtWord incrementStartState
            (sourceLeftBoundary :: before ++ farLeft) source) =
        some atBoundary := by
    apply exactRun_one machine
    simpa [atBoundary, source] using
      increment_start_step sourceHead allowed
        (sourceLeftBoundary :: before ++ farLeft) sourceTail
  have hBoundary :
      workRunExact? machine 1 atBoundary =
        some atScratch := by
    apply exactRun_one machine
    simpa [atBoundary, atScratch] using
      increment_boundary_step
        (before ++ farLeft)
        source
  have hUnits :
      workRunExact? machine processed atScratch =
        some atSeparator := by
    have scanned := scanLeftExact machine incrementSeekState
      (fun symbol => symbol = unaryUnit)
      (by
        intro head leftTail rightSide equality
        subst head
        exact increment_seek_unit_step leftTail rightSide)
      (List.replicate processed unaryUnit)
      (unarySeparator ::
        List.replicate (capacity - processed) cellBlank ++ farLeft)
      (sourceLeftBoundary :: source)
      (by
        intro symbol found
        exact List.eq_of_mem_replicate found)
    simpa [atScratch, atSeparator, before, scratchWord,
      List.append_assoc] using scanned
  have hSeparator :
      workRunExact? machine 1 atSeparator =
        some atWrite := by
    apply exactRun_one machine
    simpa [atSeparator, atWrite] using
      increment_seek_separator_step
        (List.replicate (capacity - processed) cellBlank ++ farLeft)
        (List.replicate processed unaryUnit ++
          sourceLeftBoundary :: source)
  have reserveShape :
      List.replicate (capacity - processed) cellBlank =
        cellBlank ::
          List.replicate (capacity - (processed + 1)) cellBlank := by
    have positive : 0 < capacity - processed := by
      omega
    have successor :
        capacity - processed =
          (capacity - (processed + 1)) + 1 := by
      omega
    rw [successor, List.replicate_succ]
  have hWrite :
      workRunExact? machine 1 atWrite =
        some returning := by
    apply exactRun_one machine
    simpa [atWrite, returning, reserveShape] using
      increment_write_step
        (List.replicate (capacity - (processed + 1)) cellBlank ++
          farLeft)
        (unaryUnit :: List.replicate processed unaryUnit ++
          sourceLeftBoundary :: source)
  have returnUnitsAllowed :
      ∀ symbol,
        symbol ∈ unaryUnit :: List.replicate processed unaryUnit →
          symbol = unaryUnit := by
    intro symbol found
    cases found with
    | head =>
        rfl
    | tail _ inUnits =>
        exact List.eq_of_mem_replicate inUnits
  have hReturnUnits :
      workRunExact? machine (processed + 1) returning =
        some atSource := by
    have scanned := scanRightExact machine incrementReturnState
      (fun symbol => symbol = unaryUnit)
      (by
        intro leftSide head suffix equality
        subst head
        exact increment_return_unit_step leftSide suffix)
      (unaryUnit :: List.replicate processed unaryUnit)
      (sourceLeftBoundary :: source)
      (unarySeparator ::
        List.replicate (capacity - (processed + 1)) cellBlank ++ farLeft)
      returnUnitsAllowed
    simpa [returning, atSource, after, scratchWord,
      replicate_succ_append, List.reverse_cons,
      List.append_assoc] using scanned
  have hSource :
      workRunExact? machine 1 atSource =
        some
          (configAtWord resumeStartState
            (sourceLeftBoundary :: after ++ farLeft) source) := by
    apply exactRun_one machine
    simpa [atSource] using
      increment_return_source_step
        (after ++ farLeft)
        source
  have h01 := exactRun_add machine 1 1 _ _ _
    hStart hBoundary
  have h02 := exactRun_add machine 2 processed _ _ _
    h01 hUnits
  have h03 := exactRun_add machine (2 + processed) 1 _ _ _
    h02 hSeparator
  have h04 := exactRun_add machine
    (2 + processed + 1) 1 _ _ _ h03 hWrite
  have h05 := exactRun_add machine
    (2 + processed + 1 + 1) (processed + 1) _ _ _
    h04 hReturnUnits
  have complete := exactRun_add machine
    (2 + processed + 1 + 1 + (processed + 1)) 1 _ _ _
    h05 hSource
  have steps :
      2 + processed + 1 + 1 + (processed + 1) + 1 =
        2 * processed + 6 := by
    omega
  rw [steps] at complete
  simpa [before, after, source] using complete

private theorem scratch_word_allowed
    (capacity value : Nat) :
    ∀ symbol, symbol ∈ scratchWord capacity value →
      scratchPayload symbol := by
  intro symbol found
  unfold scratchWord at found
  rw [List.mem_append] at found
  rcases found with inUnits | inTail
  · exact Or.inl (List.eq_of_mem_replicate inUnits)
  · cases inTail with
    | head =>
        exact Or.inr (Or.inl rfl)
    | tail _ inBlanks =>
        exact Or.inr (Or.inr
          (List.eq_of_mem_replicate inBlanks))

private theorem pop_cycle_exact
    (capacity value processed : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat)
    (sourceHead : WorkSymbol) (sourceTail outsideLeft : List WorkSymbol)
    (valueBound : value ≤ capacity)
    (processedLt : processed < value)
    (allowed : sourceAllowed sourceHead) :
    workRunExact? machine
        (2 * capacity +
          2 * (TargetEmitterLedger.slotBank capacity registers).length +
          2 * (recordsWord prior).length + 2 * value + 19)
        (poppingConfiguration capacity value processed registers prior
          (sourceHead :: sourceTail) outsideLeft) =
      some
        (poppingConfiguration capacity value (processed + 1)
          registers prior (sourceHead :: sourceTail) outsideLeft) := by
  let before := scratchWord capacity processed
  let after := scratchWord capacity (processed + 1)
  let bank := TargetEmitterLedger.slotBank capacity registers
  let records := recordsWord prior
  let source := sourceHead :: sourceTail
  let stackPrefix :=
    records ++ recordBoundary ::
      List.replicate (value - (processed + 1)) unaryUnit
  let oldFar :=
    stackEnd :: List.replicate processed cellBlank ++ outsideLeft
  let markedFar := popMark :: oldFar
  let farLeft :=
    ledgerBoundary :: bank ++ stackBoundary ::
      stackPrefix ++ markedFar
  let afterRecord :=
    configAtWord bounceStackState markedFar
      (stackPrefix.reverse ++ stackBoundary :: bank.reverse ++
        ledgerBoundary :: before.reverse ++
          sourceLeftBoundary :: source)
  let afterStack :=
    configAtWord bounceStackState
      (stackPrefix ++ markedFar)
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        before.reverse ++ sourceLeftBoundary :: source)
  let afterStackBoundary :=
    configAtWord bounceLedgerState
      (stackBoundary :: stackPrefix ++ markedFar)
      (bank.reverse ++ ledgerBoundary :: before.reverse ++
        sourceLeftBoundary :: source)
  let atLedgerBoundary :=
    configAtWord bounceLedgerState
      (bank ++ stackBoundary :: stackPrefix ++ markedFar)
      (ledgerBoundary :: before.reverse ++
        sourceLeftBoundary :: source)
  let atScratch :=
    configAtWord bounceScratchState
      (ledgerBoundary :: bank ++ stackBoundary ::
        stackPrefix ++ markedFar)
      (before.reverse ++ sourceLeftBoundary :: source)
  let atSourceBoundary :=
    configAtWord bounceScratchState
      (before ++ ledgerBoundary :: bank ++ stackBoundary ::
        stackPrefix ++ markedFar)
      (sourceLeftBoundary :: source)
  let incrementing :=
    configAtWord incrementStartState
      (sourceLeftBoundary :: before ++ farLeft)
      source
  let resuming :=
    configAtWord resumeStartState
      (sourceLeftBoundary :: after ++ farLeft)
      source
  let resumeBoundary :=
    configAtLeftWord resumeBoundaryState
      (sourceLeftBoundary :: after ++ farLeft)
      source
  let resumeScratch :=
    configAtLeftWord resumeScratchUnitsState
      (after ++ farLeft)
      (sourceLeftBoundary :: source)
  let resumeSeparator :=
    configAtLeftWord resumeScratchUnitsState
      (unarySeparator ::
        List.replicate (capacity - (processed + 1)) cellBlank ++
          farLeft)
      (List.replicate (processed + 1) unaryUnit ++
        sourceLeftBoundary :: source)
  let resumeReserve :=
    configAtLeftWord resumeScratchReserveState
      (List.replicate (capacity - (processed + 1)) cellBlank ++
        farLeft)
      (unarySeparator ::
        List.replicate (processed + 1) unaryUnit ++
          sourceLeftBoundary :: source)
  let resumeLedgerBoundary :=
    configAtLeftWord resumeScratchReserveState
      (ledgerBoundary :: bank ++ stackBoundary ::
        stackPrefix ++ markedFar)
      (after.reverse ++ sourceLeftBoundary :: source)
  let resumeBank :=
    configAtLeftWord resumeLedgerState
      (bank ++ stackBoundary :: stackPrefix ++ markedFar)
      (ledgerBoundary :: after.reverse ++
        sourceLeftBoundary :: source)
  let resumeStackBoundary :=
    configAtLeftWord resumeLedgerState
      (stackBoundary :: stackPrefix ++ markedFar)
      (bank.reverse ++ ledgerBoundary :: after.reverse ++
        sourceLeftBoundary :: source)
  let resumeStack :=
    configAtLeftWord resumeStackState
      (stackPrefix ++ markedFar)
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        after.reverse ++ sourceLeftBoundary :: source)
  let atMark :=
    configAtLeftWord resumeStackState markedFar
      (stackPrefix.reverse ++ stackBoundary :: bank.reverse ++
        ledgerBoundary :: after.reverse ++
          sourceLeftBoundary :: source)
  let erasing :=
    configAtLeftWord eraseOldContinueState oldFar
      (stackEnd :: stackPrefix.reverse ++ stackBoundary ::
        bank.reverse ++ ledgerBoundary :: after.reverse ++
          sourceLeftBoundary :: source)
  let crossing :=
    configAtWord crossNewContinueState
      (cellBlank :: List.replicate processed cellBlank ++ outsideLeft)
      (stackEnd :: stackPrefix.reverse ++ stackBoundary ::
        bank.reverse ++ ledgerBoundary :: after.reverse ++
          sourceLeftBoundary :: source)
  have remainingShape :
      remainingRecordPrefix prior value processed =
        stackPrefix ++ [unaryUnit] := by
    have subtraction :
        value - processed =
          (value - (processed + 1)) + 1 := by
      omega
    simp [remainingRecordPrefix, stackPrefix, records, subtraction,
      replicate_succ_append, List.append_assoc]
  have hRecord :
      workRunExact? machine 1
          (poppingConfiguration capacity value processed registers prior
            source outsideLeft) =
        some afterRecord := by
    apply exactRun_one machine
    simpa [poppingConfiguration, afterRecord, before, bank,
      oldFar, markedFar, remainingShape,
      List.reverse_append, List.append_assoc] using
      record_unit_step oldFar
        (stackPrefix.reverse ++ stackBoundary :: bank.reverse ++
          ledgerBoundary :: before.reverse ++
            sourceLeftBoundary :: source)
  have stackPrefixAllowed :
      ∀ symbol, symbol ∈ stackPrefix → recordPayload symbol := by
    intro symbol found
    unfold stackPrefix at found
    rw [List.mem_append] at found
    rcases found with inRecords | inTail
    · exact recordsWord_allowed prior symbol inRecords
    · cases inTail with
      | head =>
          exact Or.inl rfl
      | tail _ inUnits =>
          exact Or.inr (List.eq_of_mem_replicate inUnits)
  have reverseStackPrefixAllowed :
      ∀ symbol, symbol ∈ stackPrefix.reverse →
        recordPayload symbol := by
    intro symbol found
    exact stackPrefixAllowed symbol (List.mem_reverse.mp found)
  have hBounceStack :
      workRunExact? machine stackPrefix.length afterRecord =
        some afterStack := by
    have scanned := scanRightExact machine bounceStackState
      recordPayload
      (by
        intro leftSide head suffix headAllowed
        exact bounce_stack_step
          head headAllowed leftSide suffix)
      stackPrefix.reverse
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        before.reverse ++ sourceLeftBoundary :: source)
      markedFar
      reverseStackPrefixAllowed
    simpa [afterRecord, afterStack] using scanned
  have hStackBoundary :
      workRunExact? machine 1 afterStack =
        some afterStackBoundary := by
    apply exactRun_one machine
    simpa [afterStack, afterStackBoundary] using
      bounce_stack_boundary_step
        (stackPrefix ++ markedFar)
        (bank.reverse ++ ledgerBoundary :: before.reverse ++
          sourceLeftBoundary :: source)
  have reverseBankAllowed :
      ∀ symbol, symbol ∈ bank.reverse → ledgerPayload symbol := by
    intro symbol found
    exact slotBank_allowed capacity registers symbol
      (List.mem_reverse.mp found)
  have hBounceBank :
      workRunExact? machine bank.length afterStackBoundary =
        some atLedgerBoundary := by
    have scanned := scanRightExact machine bounceLedgerState
      ledgerPayload
      (by
        intro leftSide head suffix headAllowed
        exact bounce_ledger_step
          head headAllowed leftSide suffix)
      bank.reverse
      (ledgerBoundary :: before.reverse ++
        sourceLeftBoundary :: source)
      (stackBoundary :: stackPrefix ++ markedFar)
      reverseBankAllowed
    simpa [afterStackBoundary, atLedgerBoundary] using scanned
  have hLedgerBoundary :
      workRunExact? machine 1 atLedgerBoundary =
        some atScratch := by
    apply exactRun_one machine
    simpa [atLedgerBoundary, atScratch] using
      bounce_ledger_boundary_step
        (bank ++ stackBoundary :: stackPrefix ++ markedFar)
        (before.reverse ++ sourceLeftBoundary :: source)
  have reverseBeforeAllowed :
      ∀ symbol, symbol ∈ before.reverse →
        scratchPayload symbol := by
    intro symbol found
    exact scratch_word_allowed capacity processed symbol
      (List.mem_reverse.mp found)
  have hBounceScratch :
      workRunExact? machine before.length atScratch =
        some atSourceBoundary := by
    have scanned := scanRightExact machine bounceScratchState
      scratchPayload
      (by
        intro leftSide head suffix headAllowed
        exact bounce_scratch_step
          head headAllowed leftSide suffix)
      before.reverse
      (sourceLeftBoundary :: source)
      (ledgerBoundary :: bank ++ stackBoundary ::
        stackPrefix ++ markedFar)
      reverseBeforeAllowed
    simpa [atScratch, atSourceBoundary] using scanned
  have hSourceBoundary :
      workRunExact? machine 1 atSourceBoundary =
        some incrementing := by
    apply exactRun_one machine
    simpa [atSourceBoundary, incrementing, farLeft] using
      bounce_source_boundary_step
        (before ++ ledgerBoundary :: bank ++ stackBoundary ::
          stackPrefix ++ markedFar)
        source
  have hIncrement :
      workRunExact? machine (2 * processed + 6) incrementing =
        some resuming := by
    simpa [incrementing, resuming, before, after, farLeft, source] using
      increment_exact capacity processed farLeft
        sourceHead sourceTail (by omega) allowed
  have hResumeStart :
      workRunExact? machine 1 resuming =
        some resumeBoundary := by
    apply exactRun_one machine
    simpa [resuming, resumeBoundary, source] using
      resume_start_step sourceHead allowed
        (sourceLeftBoundary :: after ++ farLeft)
        sourceTail
  have hResumeBoundary :
      workRunExact? machine 1 resumeBoundary =
        some resumeScratch := by
    apply exactRun_one machine
    simpa [resumeBoundary, resumeScratch] using
      resume_boundary_step
        (after ++ farLeft)
        source
  have hResumeUnits :
      workRunExact? machine (processed + 1) resumeScratch =
        some resumeSeparator := by
    have scanned := scanLeftExact machine resumeScratchUnitsState
      (fun symbol => symbol = unaryUnit)
      (by
        intro head leftTail rightSide equality
        subst head
        exact resume_scratch_unit_step leftTail rightSide)
      (List.replicate (processed + 1) unaryUnit)
      (unarySeparator ::
        List.replicate (capacity - (processed + 1)) cellBlank ++
          farLeft)
      (sourceLeftBoundary :: source)
      (by
        intro symbol found
        exact List.eq_of_mem_replicate found)
    simpa [resumeScratch, resumeSeparator, after, scratchWord,
      List.append_assoc] using scanned
  have hResumeSeparator :
      workRunExact? machine 1 resumeSeparator =
        some resumeReserve := by
    apply exactRun_one machine
    simpa [resumeSeparator, resumeReserve] using
      resume_scratch_separator_step
        (List.replicate (capacity - (processed + 1)) cellBlank ++
          farLeft)
        (List.replicate (processed + 1) unaryUnit ++
          sourceLeftBoundary :: source)
  have hResumeReserve :
      workRunExact? machine (capacity - (processed + 1))
          resumeReserve =
        some resumeLedgerBoundary := by
    have scanned := scanLeftExact machine resumeScratchReserveState
      (fun symbol => symbol = cellBlank)
      (by
        intro head leftTail rightSide equality
        subst head
        exact resume_scratch_blank_step leftTail rightSide)
      (List.replicate (capacity - (processed + 1)) cellBlank)
      farLeft
      (unarySeparator ::
        List.replicate (processed + 1) unaryUnit ++
          sourceLeftBoundary :: source)
      (by
        intro symbol found
        exact List.eq_of_mem_replicate found)
    simpa [resumeReserve, resumeLedgerBoundary, farLeft, after,
      scratchWord, List.reverse_append, List.append_assoc] using scanned
  have hResumeLedgerBoundary :
      workRunExact? machine 1 resumeLedgerBoundary =
        some resumeBank := by
    apply exactRun_one machine
    simpa [resumeLedgerBoundary, resumeBank] using
      resume_scratch_ledger_boundary_step
        (bank ++ stackBoundary :: stackPrefix ++ markedFar)
        (after.reverse ++ sourceLeftBoundary :: source)
  have hResumeBank :
      workRunExact? machine bank.length resumeBank =
        some resumeStackBoundary := by
    have scanned := scanLeftExact machine resumeLedgerState
      ledgerPayload
      (by
        intro head leftTail rightSide headAllowed
        exact resume_ledger_step
          head headAllowed leftTail rightSide)
      bank
      (stackBoundary :: stackPrefix ++ markedFar)
      (ledgerBoundary :: after.reverse ++
        sourceLeftBoundary :: source)
      (slotBank_allowed capacity registers)
    simpa [resumeBank, resumeStackBoundary] using scanned
  have hResumeStackBoundary :
      workRunExact? machine 1 resumeStackBoundary =
        some resumeStack := by
    apply exactRun_one machine
    simpa [resumeStackBoundary, resumeStack] using
      resume_ledger_stack_boundary_step
        (stackPrefix ++ markedFar)
        (bank.reverse ++ ledgerBoundary :: after.reverse ++
          sourceLeftBoundary :: source)
  have hResumeStack :
      workRunExact? machine stackPrefix.length resumeStack =
        some atMark := by
    have scanned := scanLeftExact machine resumeStackState
      recordPayload
      (by
        intro head leftTail rightSide headAllowed
        exact resume_stack_record_step
          head headAllowed leftTail rightSide)
      stackPrefix
      markedFar
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        after.reverse ++ sourceLeftBoundary :: source)
      stackPrefixAllowed
    simpa [resumeStack, atMark] using scanned
  have hMark :
      workRunExact? machine 1 atMark =
        some erasing := by
    apply exactRun_one machine
    simpa [atMark, erasing, markedFar, oldFar] using
      resume_stack_mark_step oldFar
        (stackPrefix.reverse ++ stackBoundary :: bank.reverse ++
          ledgerBoundary :: after.reverse ++
            sourceLeftBoundary :: source)
  have hErase :
      workRunExact? machine 1 erasing =
        some crossing := by
    apply exactRun_one machine
    simpa [erasing, crossing, oldFar] using
      erase_old_continue_step
        (List.replicate processed cellBlank ++ outsideLeft)
        (stackEnd :: stackPrefix.reverse ++ stackBoundary ::
          bank.reverse ++ ledgerBoundary :: after.reverse ++
            sourceLeftBoundary :: source)
  have hCross :
      workRunExact? machine 1 crossing =
        some
          (poppingConfiguration capacity value (processed + 1)
            registers prior source outsideLeft) := by
    apply exactRun_one machine
    simpa [crossing, poppingConfiguration, remainingRecordPrefix,
      stackPrefix, records, after, bank, source,
      List.replicate_succ, List.append_assoc] using
      cross_new_continue_step
        (cellBlank :: List.replicate processed cellBlank ++ outsideLeft)
        (stackPrefix.reverse ++ stackBoundary :: bank.reverse ++
          ledgerBoundary :: after.reverse ++
            sourceLeftBoundary :: source)
  have h01 := exactRun_add machine 1 stackPrefix.length _ _ _
    hRecord hBounceStack
  have h02 := exactRun_add machine
    (1 + stackPrefix.length) 1 _ _ _ h01 hStackBoundary
  have h03 := exactRun_add machine
    (1 + stackPrefix.length + 1) bank.length _ _ _
    h02 hBounceBank
  have h04 := exactRun_add machine
    (1 + stackPrefix.length + 1 + bank.length) 1 _ _ _
    h03 hLedgerBoundary
  have h05 := exactRun_add machine
    (1 + stackPrefix.length + 1 + bank.length + 1)
    before.length _ _ _ h04 hBounceScratch
  have h06 := exactRun_add machine
    (1 + stackPrefix.length + 1 + bank.length + 1 +
      before.length) 1 _ _ _ h05 hSourceBoundary
  have h07 := exactRun_add machine
    (1 + stackPrefix.length + 1 + bank.length + 1 +
      before.length + 1) (2 * processed + 6) _ _ _
    h06 hIncrement
  have h08 := exactRun_add machine
    (1 + stackPrefix.length + 1 + bank.length + 1 +
      before.length + 1 + (2 * processed + 6)) 1 _ _ _
    h07 hResumeStart
  have h09 := exactRun_add machine
    (1 + stackPrefix.length + 1 + bank.length + 1 +
      before.length + 1 + (2 * processed + 6) + 1) 1 _ _ _
    h08 hResumeBoundary
  have h10 := exactRun_add machine
    (1 + stackPrefix.length + 1 + bank.length + 1 +
      before.length + 1 + (2 * processed + 6) + 1 + 1)
    (processed + 1) _ _ _ h09 hResumeUnits
  have h11 := exactRun_add machine
    (1 + stackPrefix.length + 1 + bank.length + 1 +
      before.length + 1 + (2 * processed + 6) + 1 + 1 +
        (processed + 1)) 1 _ _ _ h10 hResumeSeparator
  have h12 := exactRun_add machine
    (1 + stackPrefix.length + 1 + bank.length + 1 +
      before.length + 1 + (2 * processed + 6) + 1 + 1 +
        (processed + 1) + 1)
    (capacity - (processed + 1)) _ _ _
    h11 hResumeReserve
  have h13 := exactRun_add machine
    (1 + stackPrefix.length + 1 + bank.length + 1 +
      before.length + 1 + (2 * processed + 6) + 1 + 1 +
        (processed + 1) + 1 +
          (capacity - (processed + 1))) 1 _ _ _
    h12 hResumeLedgerBoundary
  have h14 := exactRun_add machine
    (1 + stackPrefix.length + 1 + bank.length + 1 +
      before.length + 1 + (2 * processed + 6) + 1 + 1 +
        (processed + 1) + 1 +
          (capacity - (processed + 1)) + 1)
    bank.length _ _ _ h13 hResumeBank
  have h15 := exactRun_add machine
    (1 + stackPrefix.length + 1 + bank.length + 1 +
      before.length + 1 + (2 * processed + 6) + 1 + 1 +
        (processed + 1) + 1 +
          (capacity - (processed + 1)) + 1 + bank.length)
    1 _ _ _ h14 hResumeStackBoundary
  have h16 := exactRun_add machine
    (1 + stackPrefix.length + 1 + bank.length + 1 +
      before.length + 1 + (2 * processed + 6) + 1 + 1 +
        (processed + 1) + 1 +
          (capacity - (processed + 1)) + 1 + bank.length + 1)
    stackPrefix.length _ _ _ h15 hResumeStack
  have h17 := exactRun_add machine
    (1 + stackPrefix.length + 1 + bank.length + 1 +
      before.length + 1 + (2 * processed + 6) + 1 + 1 +
        (processed + 1) + 1 +
          (capacity - (processed + 1)) + 1 + bank.length + 1 +
            stackPrefix.length) 1 _ _ _ h16 hMark
  have h18 := exactRun_add machine
    (1 + stackPrefix.length + 1 + bank.length + 1 +
      before.length + 1 + (2 * processed + 6) + 1 + 1 +
        (processed + 1) + 1 +
          (capacity - (processed + 1)) + 1 + bank.length + 1 +
            stackPrefix.length + 1) 1 _ _ _ h17 hErase
  have complete := exactRun_add machine
    (1 + stackPrefix.length + 1 + bank.length + 1 +
      before.length + 1 + (2 * processed + 6) + 1 + 1 +
        (processed + 1) + 1 +
          (capacity - (processed + 1)) + 1 + bank.length + 1 +
            stackPrefix.length + 1 + 1) 1 _ _ _ h18 hCross
  have beforeLength :
      before.length = capacity + 1 := by
    exact scratchWord_length_of_le capacity processed (by omega)
  have stackPrefixLength :
      stackPrefix.length =
        records.length + (value - (processed + 1)) + 1 := by
    simp [stackPrefix]
    omega
  have steps :
      1 + stackPrefix.length + 1 + bank.length + 1 +
          before.length + 1 + (2 * processed + 6) + 1 + 1 +
            (processed + 1) + 1 +
              (capacity - (processed + 1)) + 1 + bank.length + 1 +
                stackPrefix.length + 1 + 1 + 1 =
        2 * capacity + 2 * bank.length +
          2 * records.length + 2 * value + 19 := by
    rw [beforeLength, stackPrefixLength]
    omega
  rw [steps] at complete
  simpa [bank, records, source] using complete

private theorem pop_cycles_exact
    (capacity value processed count : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat)
    (sourceHead : WorkSymbol) (sourceTail outsideLeft : List WorkSymbol)
    (valueBound : value ≤ capacity)
    (sum : processed + count = value)
    (allowed : sourceAllowed sourceHead) :
    workRunExact? machine
        (count *
          (2 * capacity +
            2 * (TargetEmitterLedger.slotBank capacity registers).length +
            2 * (recordsWord prior).length + 2 * value + 19))
        (poppingConfiguration capacity value processed registers prior
          (sourceHead :: sourceTail) outsideLeft) =
      some
        (poppingConfiguration capacity value (processed + count)
          registers prior (sourceHead :: sourceTail) outsideLeft) := by
  induction count generalizing processed with
  | zero =>
      simp [workRunExact?]
  | succ count ih =>
      have oneCycle :=
        pop_cycle_exact capacity value processed registers prior
          sourceHead sourceTail outsideLeft valueBound (by omega) allowed
      have rest :=
        ih (processed := processed + 1) (by omega)
      have complete := exactRun_add machine
        (2 * capacity +
          2 * (TargetEmitterLedger.slotBank capacity registers).length +
          2 * (recordsWord prior).length + 2 * value + 19)
        (count *
          (2 * capacity +
            2 * (TargetEmitterLedger.slotBank capacity registers).length +
            2 * (recordsWord prior).length + 2 * value + 19))
        _ _ _ oneCycle rest
      simpa [Nat.succ_eq_add_one, Nat.add_mul,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using complete

private theorem nonempty_finish_exact
    (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat)
    (sourceHead : WorkSymbol) (sourceTail outsideLeft : List WorkSymbol)
    (valueBound : value ≤ capacity) :
    workRunExact? machine
        (capacity +
          (TargetEmitterLedger.slotBank capacity registers).length +
          (recordsWord prior).length + 7)
        (poppingConfiguration capacity value value registers prior
          (sourceHead :: sourceTail) outsideLeft) =
      some
        (nonemptyFinalConfiguration capacity value registers prior
          sourceHead sourceTail [] outsideLeft) := by
  let scratchW := scratchWord capacity value
  let bank := TargetEmitterLedger.slotBank capacity registers
  let records := recordsWord prior
  let source := sourceHead :: sourceTail
  let oldFar :=
    stackEnd :: List.replicate value cellBlank ++ outsideLeft
  let erasing :=
    configAtLeftWord eraseOldFinishState oldFar
      (stackEnd :: records.reverse ++ stackBoundary :: bank.reverse ++
        ledgerBoundary :: scratchW.reverse ++
          sourceLeftBoundary :: source)
  let crossing :=
    configAtWord crossNewFinishState
      (cellBlank :: List.replicate value cellBlank ++ outsideLeft)
      (stackEnd :: records.reverse ++ stackBoundary :: bank.reverse ++
        ledgerBoundary :: scratchW.reverse ++
          sourceLeftBoundary :: source)
  let returningStack :=
    configAtWord returnStackState
      (stackEnd :: cellBlank ::
        List.replicate value cellBlank ++ outsideLeft)
      (records.reverse ++ stackBoundary :: bank.reverse ++
        ledgerBoundary :: scratchW.reverse ++
          sourceLeftBoundary :: source)
  let returningStackBoundary :=
    configAtWord returnStackState
      (records ++ stackEnd :: cellBlank ::
        List.replicate value cellBlank ++ outsideLeft)
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: source)
  let returningLedger :=
    configAtWord returnLedgerState
      (stackBoundary :: records ++ stackEnd :: cellBlank ::
        List.replicate value cellBlank ++ outsideLeft)
      (bank.reverse ++ ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: source)
  let returningLedgerBoundary :=
    configAtWord returnLedgerState
      (bank ++ stackBoundary :: records ++ stackEnd :: cellBlank ::
        List.replicate value cellBlank ++ outsideLeft)
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: source)
  let returningScratch :=
    configAtWord returnScratchState
      (ledgerBoundary :: bank ++ stackBoundary :: records ++
        stackEnd :: cellBlank ::
          List.replicate value cellBlank ++ outsideLeft)
      (scratchW.reverse ++ sourceLeftBoundary :: source)
  let returningSource :=
    configAtWord returnScratchState
      (scratchW ++ ledgerBoundary :: bank ++ stackBoundary :: records ++
        stackEnd :: cellBlank ::
          List.replicate value cellBlank ++ outsideLeft)
      (sourceLeftBoundary :: source)
  have remainingAtValue :
      remainingRecordPrefix prior value value =
        records ++ [recordBoundary] := by
    simp [remainingRecordPrefix, records]
  have hBoundary :
      workRunExact? machine 1
          (poppingConfiguration capacity value value registers prior
            source outsideLeft) =
        some erasing := by
    apply exactRun_one machine
    simpa [poppingConfiguration, erasing, oldFar, remainingAtValue,
      scratchW, bank, records, List.reverse_append,
      List.append_assoc] using
      record_boundary_step oldFar
        (records.reverse ++ stackBoundary :: bank.reverse ++
          ledgerBoundary :: scratchW.reverse ++
            sourceLeftBoundary :: source)
  have hErase :
      workRunExact? machine 1 erasing =
        some crossing := by
    apply exactRun_one machine
    simpa [erasing, crossing, oldFar] using
      erase_old_finish_step
        (List.replicate value cellBlank ++ outsideLeft)
        (stackEnd :: records.reverse ++ stackBoundary :: bank.reverse ++
          ledgerBoundary :: scratchW.reverse ++
            sourceLeftBoundary :: source)
  have hCross :
      workRunExact? machine 1 crossing =
        some returningStack := by
    apply exactRun_one machine
    simpa [crossing, returningStack] using
      cross_new_finish_step
        (cellBlank :: List.replicate value cellBlank ++ outsideLeft)
        (records.reverse ++ stackBoundary :: bank.reverse ++
          ledgerBoundary :: scratchW.reverse ++
            sourceLeftBoundary :: source)
  have reverseRecordsAllowed :
      ∀ symbol, symbol ∈ records.reverse → recordPayload symbol := by
    intro symbol found
    exact recordsWord_allowed prior symbol
      (List.mem_reverse.mp found)
  have hReturnRecords :
      workRunExact? machine records.length returningStack =
        some returningStackBoundary := by
    have scanned := scanRightExact machine returnStackState
      recordPayload
      (by
        intro leftSide head suffix headAllowed
        exact return_stack_step
          head headAllowed leftSide suffix)
      records.reverse
      (stackBoundary :: bank.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: source)
      (stackEnd :: cellBlank ::
        List.replicate value cellBlank ++ outsideLeft)
      reverseRecordsAllowed
    simpa [returningStack, returningStackBoundary] using scanned
  have hReturnStackBoundary :
      workRunExact? machine 1 returningStackBoundary =
        some returningLedger := by
    apply exactRun_one machine
    simpa [returningStackBoundary, returningLedger] using
      return_stack_boundary_step
        (records ++ stackEnd :: cellBlank ::
          List.replicate value cellBlank ++ outsideLeft)
        (bank.reverse ++ ledgerBoundary :: scratchW.reverse ++
          sourceLeftBoundary :: source)
  have reverseBankAllowed :
      ∀ symbol, symbol ∈ bank.reverse → ledgerPayload symbol := by
    intro symbol found
    exact slotBank_allowed capacity registers symbol
      (List.mem_reverse.mp found)
  have hReturnBank :
      workRunExact? machine bank.length returningLedger =
        some returningLedgerBoundary := by
    have scanned := scanRightExact machine returnLedgerState
      ledgerPayload
      (by
        intro leftSide head suffix headAllowed
        exact return_ledger_step
          head headAllowed leftSide suffix)
      bank.reverse
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: source)
      (stackBoundary :: records ++ stackEnd :: cellBlank ::
        List.replicate value cellBlank ++ outsideLeft)
      reverseBankAllowed
    simpa [returningLedger, returningLedgerBoundary] using scanned
  have hReturnLedgerBoundary :
      workRunExact? machine 1 returningLedgerBoundary =
        some returningScratch := by
    apply exactRun_one machine
    simpa [returningLedgerBoundary, returningScratch] using
      return_ledger_boundary_step
        (bank ++ stackBoundary :: records ++ stackEnd :: cellBlank ::
          List.replicate value cellBlank ++ outsideLeft)
        (scratchW.reverse ++ sourceLeftBoundary :: source)
  have reverseScratchAllowed :
      ∀ symbol, symbol ∈ scratchW.reverse →
        scratchPayload symbol := by
    intro symbol found
    exact scratch_word_allowed capacity value symbol
      (List.mem_reverse.mp found)
  have hReturnScratch :
      workRunExact? machine scratchW.length returningScratch =
        some returningSource := by
    have scanned := scanRightExact machine returnScratchState
      scratchPayload
      (by
        intro leftSide head suffix headAllowed
        exact return_scratch_step
          head headAllowed leftSide suffix)
      scratchW.reverse
      (sourceLeftBoundary :: source)
      (ledgerBoundary :: bank ++ stackBoundary :: records ++
        stackEnd :: cellBlank ::
          List.replicate value cellBlank ++ outsideLeft)
      reverseScratchAllowed
    simpa [returningScratch, returningSource] using scanned
  have hReturnSource :
      workRunExact? machine 1 returningSource =
        some
          (nonemptyFinalConfiguration capacity value registers prior
            sourceHead sourceTail [] outsideLeft) := by
    apply exactRun_one machine
    simpa [returningSource, nonemptyFinalConfiguration, scratchW,
      bank, records, source, stackWord, List.replicate_succ,
      List.append_assoc] using
      return_source_step
        (scratchW ++ ledgerBoundary :: bank ++ stackBoundary :: records ++
          stackEnd :: cellBlank ::
            List.replicate value cellBlank ++ outsideLeft)
        source
  have h01 := exactRun_add machine 1 1 _ _ _
    hBoundary hErase
  have h02 := exactRun_add machine 2 1 _ _ _
    h01 hCross
  have h03 := exactRun_add machine 3 records.length _ _ _
    h02 hReturnRecords
  have h04 := exactRun_add machine
    (3 + records.length) 1 _ _ _ h03 hReturnStackBoundary
  have h05 := exactRun_add machine
    (3 + records.length + 1) bank.length _ _ _
    h04 hReturnBank
  have h06 := exactRun_add machine
    (3 + records.length + 1 + bank.length) 1 _ _ _
    h05 hReturnLedgerBoundary
  have h07 := exactRun_add machine
    (3 + records.length + 1 + bank.length + 1)
    scratchW.length _ _ _ h06 hReturnScratch
  have complete := exactRun_add machine
    (3 + records.length + 1 + bank.length + 1 +
      scratchW.length) 1 _ _ _ h07 hReturnSource
  have scratchLength :
      scratchW.length = capacity + 1 := by
    exact scratchWord_length_of_le capacity value valueBound
  have steps :
      3 + records.length + 1 + bank.length + 1 +
          scratchW.length + 1 =
        capacity + bank.length + records.length + 7 := by
    rw [scratchLength]
    omega
  rw [steps] at complete
  simpa [bank, records, source] using complete

theorem nonempty_exact (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    workRunExact? machine
        (nonemptyWorkSteps capacity (recordsWord prior).length value)
        (entryConfiguration capacity registers (prior ++ [value])
          sourceHead sourceTail targetAndRight outsideLeft) =
      some
        (nonemptyFinalConfiguration capacity value registers prior
          sourceHead sourceTail targetAndRight outsideLeft) := by
  let combinedTail := sourceTail ++ targetAndRight
  have setup :=
    nonempty_setup_exact capacity value registers prior sourceHead
      sourceTail targetAndRight outsideLeft fits allowed
  have cycles :=
    pop_cycles_exact capacity value 0 value registers prior
      sourceHead combinedTail outsideLeft valueBound (by omega) allowed
  have finish :=
    nonempty_finish_exact capacity value registers prior
      sourceHead combinedTail outsideLeft valueBound
  have finish' :
      workRunExact? machine
          (capacity +
            (TargetEmitterLedger.slotBank capacity registers).length +
            (recordsWord prior).length + 7)
          (poppingConfiguration capacity value (0 + value)
            registers prior (sourceHead :: combinedTail) outsideLeft) =
        some
          (nonemptyFinalConfiguration capacity value registers prior
            sourceHead sourceTail targetAndRight outsideLeft) := by
    simpa [combinedTail, nonemptyFinalConfiguration,
      List.append_assoc] using finish
  have h01 := exactRun_add machine
    (capacity +
      (TargetEmitterLedger.slotBank capacity registers).length +
      (recordsWord (prior ++ [value])).length + 6)
    (value *
      (2 * capacity +
        2 * (TargetEmitterLedger.slotBank capacity registers).length +
        2 * (recordsWord prior).length + 2 * value + 19))
    _ _ _ setup cycles
  have complete := exactRun_add machine
    (capacity +
      (TargetEmitterLedger.slotBank capacity registers).length +
      (recordsWord (prior ++ [value])).length + 6 +
      value *
        (2 * capacity +
          2 * (TargetEmitterLedger.slotBank capacity registers).length +
          2 * (recordsWord prior).length + 2 * value + 19))
    (capacity +
      (TargetEmitterLedger.slotBank capacity registers).length +
      (recordsWord prior).length + 7)
    _ _ _ h01 finish'
  have bankLength :
      (TargetEmitterLedger.slotBank capacity registers).length =
        6 * (capacity + 2) :=
    slotBank_length capacity registers fits
  have fullRecordsLength :
      (recordsWord (prior ++ [value])).length =
        (recordsWord prior).length + value + 1 := by
    simp [recordsWord_push, recordWord]
    omega
  have cycleSize :
      2 * capacity + 2 * (6 * (capacity + 2)) +
          2 * (recordsWord prior).length + 2 * value + 19 =
        14 * capacity + 2 * (recordsWord prior).length +
          2 * value + 43 := by
    omega
  have steps :
      capacity +
          (TargetEmitterLedger.slotBank capacity registers).length +
          (recordsWord (prior ++ [value])).length + 6 +
          value *
            (2 * capacity +
              2 *
                (TargetEmitterLedger.slotBank capacity registers).length +
              2 * (recordsWord prior).length + 2 * value + 19) +
          (capacity +
            (TargetEmitterLedger.slotBank capacity registers).length +
            (recordsWord prior).length + 7) =
        nonemptyWorkSteps capacity (recordsWord prior).length value := by
    rw [bankLength, fullRecordsLength, cycleSize]
    unfold nonemptyWorkSteps
    omega
  rw [steps] at complete
  exact complete

theorem popped_value_is_newest (prior : List Nat) (value : Nat) :
    (prior ++ [value]).getLast? = some value := by
  simp

theorem nonempty_final_halted (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    machine.isHalted
      (nonemptyFinalConfiguration capacity value registers prior
        sourceHead sourceTail targetAndRight outsideLeft) = true := by
  rfl

end Pop

/-! ### Observable preservation and LIFO order -/

theorem right_fold_pop_order (checks : List Nat) :
    checks.foldr (fun value order => order ++ [value]) [] =
      checks.reverse := by
  induction checks with
  | nil =>
      rfl
  | cons value rest ih =>
      simp [ih, List.reverse_cons]

namespace Initialize

theorem final_state_eq_accept (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    (finalConfiguration capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft).state =
        machine.acceptState := by
  rfl

theorem final_source_preserved (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    let final :=
      finalConfiguration capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft
    final.tape.head :: final.tape.right =
      sourceHead :: sourceTail ++ targetAndRight := by
  rfl

theorem final_left_workspace (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    (finalConfiguration capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft).tape.left =
        sourceLeftBoundary ::
          (scratchWord capacity scratch ++ ledgerBoundary ::
            (TargetEmitterLedger.slotBank capacity registers ++
              stackWord [] ++ outsideLeft)) := by
  rfl

theorem workRun_bounded (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (scratchBound : scratch ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    workRun machine (polynomialWorkBound capacity)
        (entryConfiguration capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) =
      finalConfiguration capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft := by
  exact workRun_of_workRunExact_halted_le
    machine (workSteps capacity) (polynomialWorkBound capacity)
    (entryConfiguration capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (finalConfiguration capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (exact capacity scratch registers sourceHead sourceTail
      targetAndRight outsideLeft fits scratchBound allowed)
    (final_halted capacity scratch registers sourceHead sourceTail
      targetAndRight outsideLeft)
    (workSteps_le_polynomialWorkBound capacity)

theorem workRun_bounded_accepts (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (scratchBound : scratch ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    (workRun machine (polynomialWorkBound capacity)
      (entryConfiguration capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft)).state =
      machine.acceptState := by
  rw [workRun_bounded capacity scratch registers sourceHead sourceTail
    targetAndRight outsideLeft fits scratchBound allowed]
  exact final_state_eq_accept capacity scratch registers sourceHead
    sourceTail targetAndRight outsideLeft

def rawTimeBound (capacity : Nat) : Nat :=
  6 * polynomialWorkBound capacity

theorem six_workSteps_le_rawTimeBound (capacity : Nat) :
    6 * workSteps capacity ≤ rawTimeBound capacity := by
  unfold rawTimeBound
  exact Nat.mul_le_mul_left 6
    (workSteps_le_polynomialWorkBound capacity)

theorem run_compiled_exact (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (scratchBound : scratch ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    run compiledMachine (6 * workSteps capacity)
        (encodeWorkConfiguration
          (entryConfiguration capacity scratch registers
            sourceHead sourceTail targetAndRight outsideLeft)) =
      encodeWorkConfiguration
        (finalConfiguration capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) := by
  exact run_compileWorkMachine_mul_of_workRunExact
    machine (workSteps capacity)
    (entryConfiguration capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (finalConfiguration capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (exact capacity scratch registers sourceHead sourceTail
      targetAndRight outsideLeft fits scratchBound allowed)

theorem run_compiled_bounded (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (scratchBound : scratch ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    run compiledMachine (rawTimeBound capacity)
        (encodeWorkConfiguration
          (entryConfiguration capacity scratch registers
            sourceHead sourceTail targetAndRight outsideLeft)) =
      encodeWorkConfiguration
        (finalConfiguration capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le
    machine (workSteps capacity) (rawTimeBound capacity)
    (entryConfiguration capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (finalConfiguration capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (exact capacity scratch registers sourceHead sourceTail
      targetAndRight outsideLeft fits scratchBound allowed)
    (final_halted capacity scratch registers sourceHead sourceTail
      targetAndRight outsideLeft)
    (six_workSteps_le_rawTimeBound capacity)

theorem run_compiled_blankEquivalent (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (scratchBound : scratch ≤ capacity)
    (allowed : sourceAllowed sourceHead)
    (initial : Configuration)
    (equivalent :
      Configuration.BlankEquivalent initial
        (encodeWorkConfiguration
          (entryConfiguration capacity scratch registers
            sourceHead sourceTail targetAndRight outsideLeft))) :
    Configuration.BlankEquivalent
      (run compiledMachine (rawTimeBound capacity) initial)
      (encodeWorkConfiguration
        (finalConfiguration capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft)) := by
  have transported :=
    run_blankEquivalent compiledMachine
      (rawTimeBound capacity) equivalent
  rw [run_compiled_bounded capacity scratch registers sourceHead
    sourceTail targetAndRight outsideLeft fits scratchBound allowed]
    at transported
  exact transported

end Initialize

namespace Push

theorem final_state_eq_accept (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    (finalConfiguration capacity value registers checks
      sourceHead sourceTail targetAndRight outsideLeft).state =
        machine.acceptState := by
  rfl

theorem final_source_preserved (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    let final :=
      finalConfiguration capacity value registers checks
        sourceHead sourceTail targetAndRight outsideLeft
    final.tape.head :: final.tape.right =
      sourceHead :: sourceTail ++ targetAndRight := by
  rfl

theorem final_left_workspace (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    (finalConfiguration capacity value registers checks
      sourceHead sourceTail targetAndRight outsideLeft).tape.left =
        sourceLeftBoundary ::
          (scratchWord capacity value ++ ledgerBoundary ::
            (TargetEmitterLedger.slotBank capacity registers ++
              stackWord (checks ++ [value]) ++ outsideLeft)) := by
  rfl

theorem workRun_bounded (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    workRun machine
        (polynomialWorkBound capacity (recordsWord checks).length value)
        (entryConfiguration capacity value registers checks
          sourceHead sourceTail targetAndRight outsideLeft) =
      finalConfiguration capacity value registers checks
        sourceHead sourceTail targetAndRight outsideLeft := by
  exact workRun_of_workRunExact_halted_le
    machine (workSteps capacity (recordsWord checks).length value)
    (polynomialWorkBound capacity (recordsWord checks).length value)
    (entryConfiguration capacity value registers checks
      sourceHead sourceTail targetAndRight outsideLeft)
    (finalConfiguration capacity value registers checks
      sourceHead sourceTail targetAndRight outsideLeft)
    (exact capacity value registers checks sourceHead sourceTail
      targetAndRight outsideLeft fits valueBound allowed)
    (final_halted capacity value registers checks sourceHead sourceTail
      targetAndRight outsideLeft)
    (workSteps_le_polynomialWorkBound capacity
      (recordsWord checks).length value)

theorem workRun_bounded_accepts (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    (workRun machine
      (polynomialWorkBound capacity (recordsWord checks).length value)
      (entryConfiguration capacity value registers checks
        sourceHead sourceTail targetAndRight outsideLeft)).state =
      machine.acceptState := by
  rw [workRun_bounded capacity value registers checks sourceHead
    sourceTail targetAndRight outsideLeft fits valueBound allowed]
  exact final_state_eq_accept capacity value registers checks sourceHead
    sourceTail targetAndRight outsideLeft

def rawTimeBound
    (capacity recordsLength value : Nat) : Nat :=
  6 * polynomialWorkBound capacity recordsLength value

theorem six_workSteps_le_rawTimeBound
    (capacity recordsLength value : Nat) :
    6 * workSteps capacity recordsLength value ≤
      rawTimeBound capacity recordsLength value := by
  unfold rawTimeBound
  exact Nat.mul_le_mul_left 6
    (workSteps_le_polynomialWorkBound capacity recordsLength value)

theorem run_compiled_exact (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    run compiledMachine
        (6 * workSteps capacity (recordsWord checks).length value)
        (encodeWorkConfiguration
          (entryConfiguration capacity value registers checks
            sourceHead sourceTail targetAndRight outsideLeft)) =
      encodeWorkConfiguration
        (finalConfiguration capacity value registers checks
          sourceHead sourceTail targetAndRight outsideLeft) := by
  exact run_compileWorkMachine_mul_of_workRunExact
    machine (workSteps capacity (recordsWord checks).length value)
    (entryConfiguration capacity value registers checks
      sourceHead sourceTail targetAndRight outsideLeft)
    (finalConfiguration capacity value registers checks
      sourceHead sourceTail targetAndRight outsideLeft)
    (exact capacity value registers checks sourceHead sourceTail
      targetAndRight outsideLeft fits valueBound allowed)

theorem run_compiled_bounded (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    run compiledMachine
        (rawTimeBound capacity (recordsWord checks).length value)
        (encodeWorkConfiguration
          (entryConfiguration capacity value registers checks
            sourceHead sourceTail targetAndRight outsideLeft)) =
      encodeWorkConfiguration
        (finalConfiguration capacity value registers checks
          sourceHead sourceTail targetAndRight outsideLeft) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le
    machine (workSteps capacity (recordsWord checks).length value)
    (rawTimeBound capacity (recordsWord checks).length value)
    (entryConfiguration capacity value registers checks
      sourceHead sourceTail targetAndRight outsideLeft)
    (finalConfiguration capacity value registers checks
      sourceHead sourceTail targetAndRight outsideLeft)
    (exact capacity value registers checks sourceHead sourceTail
      targetAndRight outsideLeft fits valueBound allowed)
    (final_halted capacity value registers checks sourceHead sourceTail
      targetAndRight outsideLeft)
    (six_workSteps_le_rawTimeBound capacity
      (recordsWord checks).length value)

theorem run_compiled_blankEquivalent (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : sourceAllowed sourceHead)
    (initial : Configuration)
    (equivalent :
      Configuration.BlankEquivalent initial
        (encodeWorkConfiguration
          (entryConfiguration capacity value registers checks
            sourceHead sourceTail targetAndRight outsideLeft))) :
    Configuration.BlankEquivalent
      (run compiledMachine
        (rawTimeBound capacity (recordsWord checks).length value)
        initial)
      (encodeWorkConfiguration
        (finalConfiguration capacity value registers checks
          sourceHead sourceTail targetAndRight outsideLeft)) := by
  have transported :=
    run_blankEquivalent compiledMachine
      (rawTimeBound capacity (recordsWord checks).length value)
      equivalent
  rw [run_compiled_bounded capacity value registers checks sourceHead
    sourceTail targetAndRight outsideLeft fits valueBound allowed]
    at transported
  exact transported

end Push

namespace Pop

theorem empty_final_state_eq_reject (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    (emptyFinalConfiguration capacity registers
      sourceHead sourceTail targetAndRight outsideLeft).state =
        machine.rejectState := by
  rfl

theorem empty_final_source_preserved (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    let final :=
      emptyFinalConfiguration capacity registers
        sourceHead sourceTail targetAndRight outsideLeft
    final.tape.head :: final.tape.right =
      sourceHead :: sourceTail ++ targetAndRight := by
  rfl

theorem empty_final_left_workspace (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    (emptyFinalConfiguration capacity registers
      sourceHead sourceTail targetAndRight outsideLeft).tape.left =
        sourceLeftBoundary ::
          (scratchWord capacity 0 ++ ledgerBoundary ::
            (TargetEmitterLedger.slotBank capacity registers ++
              stackWord [] ++ outsideLeft)) := by
  rfl

theorem nonempty_final_state_eq_accept (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    (nonemptyFinalConfiguration capacity value registers prior
      sourceHead sourceTail targetAndRight outsideLeft).state =
        machine.acceptState := by
  rfl

theorem nonempty_final_source_preserved (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    let final :=
      nonemptyFinalConfiguration capacity value registers prior
        sourceHead sourceTail targetAndRight outsideLeft
    final.tape.head :: final.tape.right =
      sourceHead :: sourceTail ++ targetAndRight := by
  rfl

theorem nonempty_final_left_workspace (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    (nonemptyFinalConfiguration capacity value registers prior
      sourceHead sourceTail targetAndRight outsideLeft).tape.left =
        sourceLeftBoundary ::
          (scratchWord capacity value ++ ledgerBoundary ::
            (TargetEmitterLedger.slotBank capacity registers ++
              stackWord prior ++
                List.replicate (value + 1) cellBlank ++ outsideLeft)) := by
  rfl

theorem empty_workRun_bounded (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (allowed : sourceAllowed sourceHead) :
    workRun machine (emptyPolynomialWorkBound capacity)
        (entryConfiguration capacity registers []
          sourceHead sourceTail targetAndRight outsideLeft) =
      emptyFinalConfiguration capacity registers
        sourceHead sourceTail targetAndRight outsideLeft := by
  exact workRun_of_workRunExact_halted_le
    machine (emptyWorkSteps capacity)
    (emptyPolynomialWorkBound capacity)
    (entryConfiguration capacity registers []
      sourceHead sourceTail targetAndRight outsideLeft)
    (emptyFinalConfiguration capacity registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (empty_exact capacity registers sourceHead sourceTail
      targetAndRight outsideLeft fits allowed)
    (empty_final_halted capacity registers sourceHead sourceTail
      targetAndRight outsideLeft)
    (emptyWorkSteps_le_polynomialWorkBound capacity)

theorem empty_workRun_bounded_rejects (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (allowed : sourceAllowed sourceHead) :
    (workRun machine (emptyPolynomialWorkBound capacity)
      (entryConfiguration capacity registers []
        sourceHead sourceTail targetAndRight outsideLeft)).state =
      machine.rejectState := by
  rw [empty_workRun_bounded capacity registers sourceHead sourceTail
    targetAndRight outsideLeft fits allowed]
  exact empty_final_state_eq_reject capacity registers sourceHead
    sourceTail targetAndRight outsideLeft

theorem nonempty_workRun_bounded (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    workRun machine
        (nonemptyPolynomialWorkBound capacity
          (recordsWord prior).length value)
        (entryConfiguration capacity registers (prior ++ [value])
          sourceHead sourceTail targetAndRight outsideLeft) =
      nonemptyFinalConfiguration capacity value registers prior
        sourceHead sourceTail targetAndRight outsideLeft := by
  exact workRun_of_workRunExact_halted_le
    machine
    (nonemptyWorkSteps capacity (recordsWord prior).length value)
    (nonemptyPolynomialWorkBound capacity
      (recordsWord prior).length value)
    (entryConfiguration capacity registers (prior ++ [value])
      sourceHead sourceTail targetAndRight outsideLeft)
    (nonemptyFinalConfiguration capacity value registers prior
      sourceHead sourceTail targetAndRight outsideLeft)
    (nonempty_exact capacity value registers prior sourceHead sourceTail
      targetAndRight outsideLeft fits valueBound allowed)
    (nonempty_final_halted capacity value registers prior sourceHead
      sourceTail targetAndRight outsideLeft)
    (nonemptyWorkSteps_le_polynomialWorkBound capacity
      (recordsWord prior).length value)

theorem nonempty_workRun_bounded_accepts (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    (workRun machine
      (nonemptyPolynomialWorkBound capacity
        (recordsWord prior).length value)
      (entryConfiguration capacity registers (prior ++ [value])
        sourceHead sourceTail targetAndRight outsideLeft)).state =
      machine.acceptState := by
  rw [nonempty_workRun_bounded capacity value registers prior sourceHead
    sourceTail targetAndRight outsideLeft fits valueBound allowed]
  exact nonempty_final_state_eq_accept capacity value registers prior
    sourceHead sourceTail targetAndRight outsideLeft

def emptyRawTimeBound (capacity : Nat) : Nat :=
  6 * emptyPolynomialWorkBound capacity

def nonemptyRawTimeBound
    (capacity recordsLength value : Nat) : Nat :=
  6 * nonemptyPolynomialWorkBound capacity recordsLength value

theorem six_emptyWorkSteps_le_rawTimeBound (capacity : Nat) :
    6 * emptyWorkSteps capacity ≤ emptyRawTimeBound capacity := by
  unfold emptyRawTimeBound
  exact Nat.mul_le_mul_left 6
    (emptyWorkSteps_le_polynomialWorkBound capacity)

theorem six_nonemptyWorkSteps_le_rawTimeBound
    (capacity recordsLength value : Nat) :
    6 * nonemptyWorkSteps capacity recordsLength value ≤
      nonemptyRawTimeBound capacity recordsLength value := by
  unfold nonemptyRawTimeBound
  exact Nat.mul_le_mul_left 6
    (nonemptyWorkSteps_le_polynomialWorkBound
      capacity recordsLength value)

theorem run_compiled_empty_exact (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (allowed : sourceAllowed sourceHead) :
    run compiledMachine (6 * emptyWorkSteps capacity)
        (encodeWorkConfiguration
          (entryConfiguration capacity registers []
            sourceHead sourceTail targetAndRight outsideLeft)) =
      encodeWorkConfiguration
        (emptyFinalConfiguration capacity registers
          sourceHead sourceTail targetAndRight outsideLeft) := by
  exact run_compileWorkMachine_mul_of_workRunExact
    machine (emptyWorkSteps capacity)
    (entryConfiguration capacity registers []
      sourceHead sourceTail targetAndRight outsideLeft)
    (emptyFinalConfiguration capacity registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (empty_exact capacity registers sourceHead sourceTail
      targetAndRight outsideLeft fits allowed)

theorem run_compiled_nonempty_exact (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    run compiledMachine
        (6 * nonemptyWorkSteps capacity (recordsWord prior).length value)
        (encodeWorkConfiguration
          (entryConfiguration capacity registers (prior ++ [value])
            sourceHead sourceTail targetAndRight outsideLeft)) =
      encodeWorkConfiguration
        (nonemptyFinalConfiguration capacity value registers prior
          sourceHead sourceTail targetAndRight outsideLeft) := by
  exact run_compileWorkMachine_mul_of_workRunExact
    machine
    (nonemptyWorkSteps capacity (recordsWord prior).length value)
    (entryConfiguration capacity registers (prior ++ [value])
      sourceHead sourceTail targetAndRight outsideLeft)
    (nonemptyFinalConfiguration capacity value registers prior
      sourceHead sourceTail targetAndRight outsideLeft)
    (nonempty_exact capacity value registers prior sourceHead sourceTail
      targetAndRight outsideLeft fits valueBound allowed)

theorem run_compiled_empty_bounded (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (allowed : sourceAllowed sourceHead) :
    run compiledMachine (emptyRawTimeBound capacity)
        (encodeWorkConfiguration
          (entryConfiguration capacity registers []
            sourceHead sourceTail targetAndRight outsideLeft)) =
      encodeWorkConfiguration
        (emptyFinalConfiguration capacity registers
          sourceHead sourceTail targetAndRight outsideLeft) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le
    machine (emptyWorkSteps capacity) (emptyRawTimeBound capacity)
    (entryConfiguration capacity registers []
      sourceHead sourceTail targetAndRight outsideLeft)
    (emptyFinalConfiguration capacity registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (empty_exact capacity registers sourceHead sourceTail
      targetAndRight outsideLeft fits allowed)
    (empty_final_halted capacity registers sourceHead sourceTail
      targetAndRight outsideLeft)
    (six_emptyWorkSteps_le_rawTimeBound capacity)

theorem run_compiled_nonempty_bounded (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    run compiledMachine
        (nonemptyRawTimeBound capacity (recordsWord prior).length value)
        (encodeWorkConfiguration
          (entryConfiguration capacity registers (prior ++ [value])
            sourceHead sourceTail targetAndRight outsideLeft)) =
      encodeWorkConfiguration
        (nonemptyFinalConfiguration capacity value registers prior
          sourceHead sourceTail targetAndRight outsideLeft) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le
    machine
    (nonemptyWorkSteps capacity (recordsWord prior).length value)
    (nonemptyRawTimeBound capacity (recordsWord prior).length value)
    (entryConfiguration capacity registers (prior ++ [value])
      sourceHead sourceTail targetAndRight outsideLeft)
    (nonemptyFinalConfiguration capacity value registers prior
      sourceHead sourceTail targetAndRight outsideLeft)
    (nonempty_exact capacity value registers prior sourceHead sourceTail
      targetAndRight outsideLeft fits valueBound allowed)
    (nonempty_final_halted capacity value registers prior sourceHead
      sourceTail targetAndRight outsideLeft)
    (six_nonemptyWorkSteps_le_rawTimeBound capacity
      (recordsWord prior).length value)

theorem run_compiled_empty_blankEquivalent (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (allowed : sourceAllowed sourceHead)
    (initial : Configuration)
    (equivalent :
      Configuration.BlankEquivalent initial
        (encodeWorkConfiguration
          (entryConfiguration capacity registers []
            sourceHead sourceTail targetAndRight outsideLeft))) :
    Configuration.BlankEquivalent
      (run compiledMachine (emptyRawTimeBound capacity) initial)
      (encodeWorkConfiguration
        (emptyFinalConfiguration capacity registers
          sourceHead sourceTail targetAndRight outsideLeft)) := by
  have transported :=
    run_blankEquivalent compiledMachine
      (emptyRawTimeBound capacity) equivalent
  rw [run_compiled_empty_bounded capacity registers sourceHead
    sourceTail targetAndRight outsideLeft fits allowed] at transported
  exact transported

theorem run_compiled_nonempty_blankEquivalent (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : sourceAllowed sourceHead)
    (initial : Configuration)
    (equivalent :
      Configuration.BlankEquivalent initial
        (encodeWorkConfiguration
          (entryConfiguration capacity registers (prior ++ [value])
            sourceHead sourceTail targetAndRight outsideLeft))) :
    Configuration.BlankEquivalent
      (run compiledMachine
        (nonemptyRawTimeBound capacity (recordsWord prior).length value)
        initial)
      (encodeWorkConfiguration
        (nonemptyFinalConfiguration capacity value registers prior
          sourceHead sourceTail targetAndRight outsideLeft)) := by
  have transported :=
    run_blankEquivalent compiledMachine
      (nonemptyRawTimeBound capacity (recordsWord prior).length value)
      equivalent
  rw [run_compiled_nonempty_bounded capacity value registers prior
    sourceHead sourceTail targetAndRight outsideLeft fits valueBound
    allowed] at transported
  exact transported

end Pop

/-! ### Sparse-tail controller wrappers

`Push.entryConfiguration` materializes the exact `value + 1` blank work
cells consumed by the trace.  A controller may instead carry the same
infinite blank tape using a shorter finite exterior window.  The wrappers
below transport the already-proved exact traces across that representational
difference.  Their endpoints are existential because the finite blank window
is intentionally not canonical.

The pop entry already has no pre-materialized reserve.  Its two transport
wrappers let a controller invoke it from any blank-equivalent finite window.
-/

namespace Push

/-- Push entry with the stack followed directly by the controller's finite
exterior list.  No explicit blank reserve is materialized. -/
def sparseEntryConfiguration (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord startState
    (sourceLeftBoundary ::
      (scratchWord capacity value ++
        ledgerBoundary ::
          (TargetEmitterLedger.slotBank capacity registers ++
            stackWord checks ++ outsideLeft)))
    (sourceHead :: sourceTail ++ targetAndRight)

theorem sparse_entry_blankEquivalent (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (outsideBlank : BlankTail outsideLeft) :
    WorkConfiguration.BlankEquivalent
      (sparseEntryConfiguration capacity value registers checks
        sourceHead sourceTail targetAndRight outsideLeft)
      (entryConfiguration capacity value registers checks
        sourceHead sourceTail targetAndRight outsideLeft) := by
  refine ⟨rfl, ⟨rfl, ?_, fun _ => rfl⟩⟩
  intro index
  let fixedPart :=
    sourceLeftBoundary ::
      (scratchWord capacity value ++
        ledgerBoundary ::
          (TargetEmitterLedger.slotBank capacity registers ++
            stackWord checks))
  have paddedBlank :
      BlankTail
        (List.replicate (value + 1) cellBlank ++ outsideLeft) :=
    blankTail_replicate_append (value + 1) outsideLeft outsideBlank
  have tailsAgree :
      ∀ tailIndex,
        WorkTape.blankCellAt outsideLeft tailIndex =
          WorkTape.blankCellAt
            (List.replicate (value + 1) cellBlank ++ outsideLeft)
            tailIndex := by
    intro tailIndex
    exact
      (outsideBlank tailIndex).trans
        (paddedBlank tailIndex).symm
  have congruent :=
    blankCellAt_append_congr fixedPart outsideLeft
      (List.replicate (value + 1) cellBlank ++ outsideLeft)
      tailsAgree index
  simpa [fixedPart, sparseEntryConfiguration, entryConfiguration,
    configAtWord, TargetEmitter.configAtWord, List.append_assoc] using
    congruent

/-- Transport Push's canonical exact trace from any blank-equivalent entry. -/
theorem exact_of_blankEquivalent_entry (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : sourceAllowed sourceHead)
    (actualEntry : WorkConfiguration)
    (equivalent :
      WorkConfiguration.BlankEquivalent actualEntry
        (entryConfiguration capacity value registers checks
          sourceHead sourceTail targetAndRight outsideLeft)) :
    ∃ actualFinal,
      workRunExact? machine
          (workSteps capacity (recordsWord checks).length value)
          actualEntry =
        some actualFinal ∧
      WorkConfiguration.BlankEquivalent actualFinal
        (finalConfiguration capacity value registers checks
          sourceHead sourceTail targetAndRight outsideLeft) := by
  exact workRunExact?_transport machine
    (workSteps capacity (recordsWord checks).length value)
    equivalent
    (Push.exact capacity value registers checks sourceHead sourceTail
      targetAndRight outsideLeft fits valueBound allowed)

/-- Exact sparse-tail Push.  The returned finite window is
blank-equivalent to the canonical pushed stack and therefore composes with
later literal controllers without reserving cells in advance. -/
theorem sparse_exact (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : sourceAllowed sourceHead)
    (outsideBlank : BlankTail outsideLeft) :
    ∃ actualFinal,
      workRunExact? machine
          (workSteps capacity (recordsWord checks).length value)
          (sparseEntryConfiguration capacity value registers checks
            sourceHead sourceTail targetAndRight outsideLeft) =
        some actualFinal ∧
      WorkConfiguration.BlankEquivalent actualFinal
        (finalConfiguration capacity value registers checks
          sourceHead sourceTail targetAndRight outsideLeft) := by
  exact exact_of_blankEquivalent_entry capacity value registers checks
    sourceHead sourceTail targetAndRight outsideLeft fits valueBound
    allowed
    (sparseEntryConfiguration capacity value registers checks sourceHead
      sourceTail targetAndRight outsideLeft)
    (sparse_entry_blankEquivalent capacity value registers checks
      sourceHead sourceTail targetAndRight outsideLeft outsideBlank)

end Push

namespace Pop

/-- Transport empty-stack rejection from any blank-equivalent finite entry
window. -/
theorem empty_exact_of_blankEquivalent_entry (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (allowed : sourceAllowed sourceHead)
    (actualEntry : WorkConfiguration)
    (equivalent :
      WorkConfiguration.BlankEquivalent actualEntry
        (entryConfiguration capacity registers []
          sourceHead sourceTail targetAndRight outsideLeft)) :
    ∃ actualFinal,
      workRunExact? machine (emptyWorkSteps capacity) actualEntry =
        some actualFinal ∧
      WorkConfiguration.BlankEquivalent actualFinal
        (emptyFinalConfiguration capacity registers
          sourceHead sourceTail targetAndRight outsideLeft) := by
  exact workRunExact?_transport machine (emptyWorkSteps capacity)
    equivalent
    (empty_exact capacity registers sourceHead sourceTail targetAndRight
      outsideLeft fits allowed)

/-- Transport newest-record pop from any blank-equivalent finite entry
window. -/
theorem nonempty_exact_of_blankEquivalent_entry
    (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat) (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : sourceAllowed sourceHead)
    (actualEntry : WorkConfiguration)
    (equivalent :
      WorkConfiguration.BlankEquivalent actualEntry
        (entryConfiguration capacity registers (prior ++ [value])
          sourceHead sourceTail targetAndRight outsideLeft)) :
    ∃ actualFinal,
      workRunExact? machine
          (nonemptyWorkSteps capacity (recordsWord prior).length value)
          actualEntry =
        some actualFinal ∧
      WorkConfiguration.BlankEquivalent actualFinal
        (nonemptyFinalConfiguration capacity value registers prior
          sourceHead sourceTail targetAndRight outsideLeft) := by
  exact workRunExact?_transport machine
    (nonemptyWorkSteps capacity (recordsWord prior).length value)
    equivalent
    (nonempty_exact capacity value registers prior sourceHead sourceTail
      targetAndRight outsideLeft fits valueBound allowed)

end Pop

/-! ### Fail-closed malformed workspaces -/

private theorem left_dead_step
    (machine : WorkMachine) (rules : List WorkRule)
    (state dead : Nat) (symbol : WorkSymbol)
    (left right : List WorkSymbol)
    (rulesEq : machine.rules = rules)
    (notHalted :
      machine.isHalted
        (configAtLeftWord state (symbol :: left) right) = false)
    (found :
      findWorkRule rules state symbol =
        some (literalRule state symbol dead symbol .stay)) :
    workStep? machine
        (configAtLeftWord state (symbol :: left) right) =
      some (configAtLeftWord dead
        (symbol :: left) right) := by
  calc
    workStep? machine
        (configAtLeftWord state (symbol :: left) right) =
      some
        (applyWorkRule
          (literalRule state symbol dead symbol .stay)
          (configAtLeftWord state (symbol :: left) right)) := by
            apply workStep?_eq_apply_of_find
            · exact notHalted
            · rw [rulesEq]
              exact found
    _ = some (configAtLeftWord dead
        (symbol :: left) right) := by
      rfl

private theorem right_dead_step
    (machine : WorkMachine) (rules : List WorkRule)
    (state dead : Nat) (symbol : WorkSymbol)
    (left right : List WorkSymbol)
    (rulesEq : machine.rules = rules)
    (notHalted :
      machine.isHalted
        (configAtWord state left (symbol :: right)) = false)
    (found :
      findWorkRule rules state symbol =
        some (literalRule state symbol dead symbol .stay)) :
    workStep? machine
        (configAtWord state left (symbol :: right)) =
      some (configAtWord dead left (symbol :: right)) := by
  calc
    workStep? machine
        (configAtWord state left (symbol :: right)) =
      some
        (applyWorkRule
          (literalRule state symbol dead symbol .stay)
          (configAtWord state left (symbol :: right))) := by
            apply workStep?_eq_apply_of_find
            · exact notHalted
            · rw [rulesEq]
              exact found
    _ = some (configAtWord dead left (symbol :: right)) := by
      rfl

namespace Initialize

set_option maxRecDepth 1000000 in
private theorem find_write_end_malformed
    (symbol : WorkSymbol) (notBlank : symbol ≠ cellBlank) :
    findWorkRule rules writeEndState symbol =
      some (literalRule writeEndState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · exact (notBlank rfl).elim
  all_goals decide

theorem malformed_stack_cell_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notBlank : symbol ≠ cellBlank) :
    workStep? machine
        (configAtLeftWord writeEndState
          (symbol :: left) right) =
      some (configAtLeftWord deadState
        (symbol :: left) right) := by
  exact left_dead_step machine rules writeEndState deadState
    symbol left right rfl (by rfl)
    (find_write_end_malformed symbol notBlank)

theorem dead_configuration_not_halted (tape : WorkTape) :
    machine.isHalted { state := deadState, tape := tape } = false := by
  rfl

theorem dead_stuck (tape : WorkTape) :
    workStep? machine { state := deadState, tape := tape } = none := by
  have notHalted := dead_configuration_not_halted tape
  unfold workStep?
  rw [notHalted]
  change
    (match findWorkRule rules deadState tape.head with
     | none => none
     | some rule =>
         some (applyWorkRule rule
           { state := deadState, tape := tape })) = none
  rw [no_rule_at_dead]

end Initialize

namespace Push

set_option maxRecDepth 1000000 in
private theorem find_selected_malformed
    (symbol : WorkSymbol)
    (notMark : symbol ≠ pushMark)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    findWorkRule rules selectedState symbol =
      some (literalRule selectedState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  all_goals first
    | exact (notMark rfl).elim
    | exact (notUnit rfl).elim
    | exact (notSeparator rfl).elim
    | decide

set_option maxRecDepth 1000000 in
private theorem find_append_occupied
    (state : Nat)
    (stateEq : state = appendEndState ∨ state = appendUnitState)
    (symbol : WorkSymbol) (occupied : symbol ≠ cellBlank) :
    findWorkRule rules state symbol =
      some (literalRule state symbol
        deadState symbol .stay) := by
  rcases stateEq with rfl | rfl
  all_goals
    rcases symbol with ⟨first, second⟩
    cases first <;> cases second
    · exact (occupied rfl).elim
    all_goals decide

theorem malformed_selected_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notMark : symbol ≠ pushMark)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    workStep? machine
        (configAtLeftWord selectedState
          (symbol :: left) right) =
      some (configAtLeftWord deadState
        (symbol :: left) right) := by
  exact left_dead_step machine rules selectedState deadState
    symbol left right rfl (by rfl)
    (find_selected_malformed symbol notMark notUnit notSeparator)

theorem occupied_append_enters_dead
    (state : Nat)
    (stateEq : state = appendEndState ∨ state = appendUnitState)
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (occupied : symbol ≠ cellBlank) :
    workStep? machine
        (configAtLeftWord state (symbol :: left) right) =
      some (configAtLeftWord deadState
        (symbol :: left) right) := by
  rcases stateEq with rfl | rfl
  · exact left_dead_step machine rules appendEndState deadState
      symbol left right rfl (by rfl)
      (find_append_occupied appendEndState (Or.inl rfl)
        symbol occupied)
  · exact left_dead_step machine rules appendUnitState deadState
      symbol left right rfl (by rfl)
      (find_append_occupied appendUnitState (Or.inr rfl)
        symbol occupied)

theorem dead_configuration_not_halted (tape : WorkTape) :
    machine.isHalted { state := deadState, tape := tape } = false := by
  rfl

theorem dead_stuck (tape : WorkTape) :
    workStep? machine { state := deadState, tape := tape } = none := by
  have notHalted := dead_configuration_not_halted tape
  unfold workStep?
  rw [notHalted]
  change
    (match findWorkRule rules deadState tape.head with
     | none => none
     | some rule =>
         some (applyWorkRule rule
           { state := deadState, tape := tape })) = none
  rw [no_rule_at_dead]

end Push

namespace Pop

set_option maxRecDepth 1000000 in
private theorem find_nonzero_scratch
    (symbol : WorkSymbol) (notSeparator : symbol ≠ unarySeparator) :
    findWorkRule rules scratchZeroState symbol =
      some (literalRule scratchZeroState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  all_goals first
    | exact (notSeparator rfl).elim
    | decide

set_option maxRecDepth 1000000 in
private theorem find_increment_occupied
    (symbol : WorkSymbol) (occupied : symbol ≠ cellBlank) :
    findWorkRule rules incrementWriteState symbol =
      some (literalRule incrementWriteState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · exact (occupied rfl).elim
  all_goals decide

set_option maxRecDepth 1000000 in
private theorem find_stack_launch_malformed
    (symbol : WorkSymbol)
    (notEnd : symbol ≠ stackEnd)
    (notBoundary : symbol ≠ recordBoundary) :
    findWorkRule rules stackMaybeState symbol =
      some (literalRule stackMaybeState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  all_goals first
    | exact (notEnd rfl).elim
    | exact (notBoundary rfl).elim
    | decide

theorem nonzero_scratch_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notSeparator : symbol ≠ unarySeparator) :
    workStep? machine
        (configAtLeftWord scratchZeroState
          (symbol :: left) right) =
      some (configAtLeftWord deadState
        (symbol :: left) right) := by
  exact left_dead_step machine rules scratchZeroState deadState
    symbol left right rfl (by rfl)
    (find_nonzero_scratch symbol notSeparator)

theorem exhausted_scratch_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (occupied : symbol ≠ cellBlank) :
    workStep? machine
        (configAtLeftWord incrementWriteState
          (symbol :: left) right) =
      some (configAtLeftWord deadState
        (symbol :: left) right) := by
  exact left_dead_step machine rules incrementWriteState deadState
    symbol left right rfl (by rfl)
    (find_increment_occupied symbol occupied)

theorem malformed_stack_launch_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notEnd : symbol ≠ stackEnd)
    (notBoundary : symbol ≠ recordBoundary) :
    workStep? machine
        (configAtLeftWord stackMaybeState
          (symbol :: left) right) =
      some (configAtLeftWord deadState
        (symbol :: left) right) := by
  exact left_dead_step machine rules stackMaybeState deadState
    symbol left right rfl (by rfl)
    (find_stack_launch_malformed symbol notEnd notBoundary)

theorem dead_configuration_not_halted (tape : WorkTape) :
    machine.isHalted { state := deadState, tape := tape } = false := by
  rfl

theorem dead_stuck (tape : WorkTape) :
    workStep? machine { state := deadState, tape := tape } = none := by
  have notHalted := dead_configuration_not_halted tape
  unfold workStep?
  rw [notHalted]
  change
    (match findWorkRule rules deadState tape.head with
     | none => none
     | some rule =>
         some (applyWorkRule rule
           { state := deadState, tape := tape })) = none
  rw [no_rule_at_dead]

end Pop

end PNP.Concrete.LockedNAND.TargetEmitterCheckStack
