/-
Copyright (c) 2026 PNP Labs.

Literal controller that adds one selected fixed-ledger slot to the nearest
unary scratch record.  Six finite entry modes select the slot.  The machine
marks one selected unary unit, bounces to the retained source, performs one
literal scratch increment, and rediscovers the contextual mark on tape.
After the selected separator is reached, it restores every mark and returns
to the original source head.

No executable transition knows a slot value, scratch value, capacity,
decoded circuit, target word, or external control lookup.
-/

import PNP.Concrete.LockedNANDTargetEmitterLedger
import PNP.Concrete.PipelineMachineSimulation

namespace PNP.Concrete.LockedNAND.TargetEmitterScratchAddSlot

open PNP.Concrete

abbrev Slot := TargetEmitterLedger.Slot

def allSlots : List Slot :=
  TargetEmitterLedger.Slot.all

def slotCode (slot : Slot) : Nat :=
  TargetEmitterLedger.Slot.index slot

theorem slotCode_le_five (slot : Slot) :
    slotCode slot ≤ 5 := by
  cases slot <;> decide

def startState (slot : Slot) : Nat := 3000 + slotCode slot
def boundaryState (slot : Slot) : Nat := 3010 + slotCode slot
def scratchUnitsState (slot : Slot) : Nat := 3020 + slotCode slot
def scratchReserveState (slot : Slot) : Nat := 3030 + slotCode slot
def seekSlotState (remaining : Nat) : Nat := 3040 + remaining
def selectedState : Nat := 3050
def bounceLedgerState : Nat := 3051
def bounceScratchState : Nat := 3052
def incrementStartState : Nat := 3053
def incrementBoundaryState : Nat := 3054
def incrementSeekState : Nat := 3055
def incrementWriteState : Nat := 3056
def incrementReturnState : Nat := 3057
def resumeStartState : Nat := 3058
def resumeBoundaryState : Nat := 3059
def resumeScratchUnitsState : Nat := 3060
def resumeScratchReserveState : Nat := 3061
def seekMarkState : Nat := 3062
def restoreState : Nat := 3063
def finalLedgerState : Nat := 3064
def finalScratchState : Nat := 3065
def acceptState : Nat := 3066
def rejectState : Nat := 3067
def deadState : Nat := 3068

def unaryUnit : WorkSymbol := TargetEmitterLedger.unaryUnit
def unarySeparator : WorkSymbol :=
  TargetEmitterLedger.unarySeparator
def sourceLeftBoundary : WorkSymbol :=
  TargetEmitterLedger.sourceLeftBoundary
def ledgerBoundary : WorkSymbol :=
  TargetEmitterLedger.ledgerBoundary
def slotBoundary : WorkSymbol :=
  TargetEmitterLedger.slotBoundary
def unitMark : WorkSymbol := WorkSymbol.zeroZero
def cursorMarker : WorkSymbol := WorkSymbol.oneBlank

theorem cursorMarker_eq_unarySeparator :
    cursorMarker = unarySeparator := by
  rfl

theorem unitMark_ne_unaryUnit :
    unitMark ≠ unaryUnit := by
  decide

theorem unitMark_ne_unarySeparator :
    unitMark ≠ unarySeparator := by
  decide

theorem unitMark_ne_slotBoundary :
    unitMark ≠ slotBoundary := by
  decide

theorem unitMark_ne_ledgerBoundary :
    unitMark ≠ ledgerBoundary := by
  decide

def allWorkSymbols : List WorkSymbol :=
  TargetEmitter.allWorkSymbols

structure StateProgram where
  state : Nat
  action : WorkSymbol → Nat × WorkSymbol × HeadMove

def deadAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  (deadState, symbol, .stay)

def sourceAllowed (symbol : WorkSymbol) : Prop :=
  TargetEmitter.PackedSymbol symbol ∨ symbol = cursorMarker

def sourceAction (target : Nat) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.zeroZero ∨
      symbol = WorkSymbol.zeroOne ∨
      symbol = WorkSymbol.oneZero ∨
      symbol = WorkSymbol.oneOne ∨
      symbol = cursorMarker then
    (target, symbol, .left)
  else
    deadAction symbol

def expectLeft (expected : WorkSymbol) (target : Nat)
    (symbol : WorkSymbol) : Nat × WorkSymbol × HeadMove :=
  if symbol = expected then
    (target, symbol, .left)
  else
    deadAction symbol

def scratchUnitsAction (targetUnits targetReserve : Nat)
    (symbol : WorkSymbol) : Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (targetUnits, symbol, .left)
  else if symbol = unarySeparator then
    (targetReserve, symbol, .left)
  else
    deadAction symbol

def scratchReserveAction (targetReserve targetLedger : Nat)
    (symbol : WorkSymbol) : Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.blank then
    (targetReserve, symbol, .left)
  else if symbol = ledgerBoundary then
    (targetLedger, symbol, .left)
  else
    deadAction symbol

def seekSlotAction (remaining : Nat) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = slotBoundary then
    if remaining = 0 then
      (selectedState, symbol, .left)
    else
      (seekSlotState (remaining - 1), symbol, .left)
  else if symbol = unaryUnit ∨ symbol = unarySeparator ∨
      symbol = WorkSymbol.blank then
    (seekSlotState remaining, symbol, .left)
  else
    deadAction symbol

def selectedAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unitMark then
    (selectedState, symbol, .left)
  else if symbol = unaryUnit then
    (bounceLedgerState, unitMark, .right)
  else if symbol = unarySeparator then
    (restoreState, symbol, .right)
  else
    deadAction symbol

def ledgerPayload (symbol : WorkSymbol) : Prop :=
  symbol = unaryUnit ∨ symbol = unarySeparator ∨
    symbol = WorkSymbol.blank ∨ symbol = slotBoundary

private instance instDecidableLedgerPayload (symbol : WorkSymbol) :
    Decidable (ledgerPayload symbol) := by
  unfold ledgerPayload
  infer_instance

def bounceLedgerAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unitMark ∨ ledgerPayload symbol then
    (bounceLedgerState, symbol, .right)
  else if symbol = ledgerBoundary then
    (bounceScratchState, symbol, .right)
  else
    deadAction symbol

def scratchPayload (symbol : WorkSymbol) : Prop :=
  symbol = unaryUnit ∨ symbol = unarySeparator ∨
    symbol = WorkSymbol.blank

private instance instDecidableScratchPayload (symbol : WorkSymbol) :
    Decidable (scratchPayload symbol) := by
  unfold scratchPayload
  infer_instance

def bounceScratchAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if scratchPayload symbol then
    (bounceScratchState, symbol, .right)
  else if symbol = sourceLeftBoundary then
    (incrementStartState, symbol, .right)
  else
    deadAction symbol

def incrementSeekAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (incrementSeekState, symbol, .left)
  else if symbol = unarySeparator then
    (incrementWriteState, unaryUnit, .left)
  else
    deadAction symbol

def incrementWriteAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.blank then
    (incrementReturnState, unarySeparator, .right)
  else
    deadAction symbol

def incrementReturnAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (incrementReturnState, symbol, .right)
  else if symbol = sourceLeftBoundary then
    (resumeStartState, symbol, .right)
  else
    deadAction symbol

def seekMarkAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unitMark then
    (selectedState, symbol, .stay)
  else if ledgerPayload symbol then
    (seekMarkState, symbol, .left)
  else
    deadAction symbol

def restoreAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unitMark then
    (restoreState, unaryUnit, .right)
  else if symbol = slotBoundary then
    (finalLedgerState, symbol, .right)
  else
    deadAction symbol

def finalLedgerAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if ledgerPayload symbol then
    (finalLedgerState, symbol, .right)
  else if symbol = ledgerBoundary then
    (finalScratchState, symbol, .right)
  else
    deadAction symbol

def finalScratchAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if scratchPayload symbol then
    (finalScratchState, symbol, .right)
  else if symbol = sourceLeftBoundary then
    (acceptState, symbol, .right)
  else
    deadAction symbol

def slotPrograms (slot : Slot) : List StateProgram :=
  [ { state := startState slot,
      action := sourceAction (boundaryState slot) }
  , { state := boundaryState slot,
      action := expectLeft sourceLeftBoundary
        (scratchUnitsState slot) }
  , { state := scratchUnitsState slot,
      action := scratchUnitsAction
        (scratchUnitsState slot) (scratchReserveState slot) }
  , { state := scratchReserveState slot,
      action := scratchReserveAction
        (scratchReserveState slot) (seekSlotState (slotCode slot)) } ]

def statePrograms : List StateProgram :=
  slotPrograms .inputCount ++
  slotPrograms .normalizedGateCount ++
  slotPrograms .carrierWidth ++
  slotPrograms .baseline ++
  slotPrograms .currentGate ++
  slotPrograms .outputIndex ++
  [ { state := seekSlotState 0, action := seekSlotAction 0 }
  , { state := seekSlotState 1, action := seekSlotAction 1 }
  , { state := seekSlotState 2, action := seekSlotAction 2 }
  , { state := seekSlotState 3, action := seekSlotAction 3 }
  , { state := seekSlotState 4, action := seekSlotAction 4 }
  , { state := seekSlotState 5, action := seekSlotAction 5 }
  , { state := selectedState, action := selectedAction }
  , { state := bounceLedgerState, action := bounceLedgerAction }
  , { state := bounceScratchState, action := bounceScratchAction }
  , { state := incrementStartState,
      action := sourceAction incrementBoundaryState }
  , { state := incrementBoundaryState,
      action := expectLeft sourceLeftBoundary incrementSeekState }
  , { state := incrementSeekState, action := incrementSeekAction }
  , { state := incrementWriteState, action := incrementWriteAction }
  , { state := incrementReturnState, action := incrementReturnAction }
  , { state := resumeStartState,
      action := sourceAction resumeBoundaryState }
  , { state := resumeBoundaryState,
      action := expectLeft sourceLeftBoundary resumeScratchUnitsState }
  , { state := resumeScratchUnitsState,
      action := scratchUnitsAction
        resumeScratchUnitsState resumeScratchReserveState }
  , { state := resumeScratchReserveState,
      action := scratchReserveAction
        resumeScratchReserveState seekMarkState }
  , { state := seekMarkState, action := seekMarkAction }
  , { state := restoreState, action := restoreAction }
  , { state := finalLedgerState, action := finalLedgerAction }
  , { state := finalScratchState, action := finalScratchAction } ]

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

def machineFor (slot : Slot) : WorkMachine :=
  { rules := rules
    startState := startState slot
    acceptState := acceptState
    rejectState := rejectState }

def compiledMachineFor (slot : Slot) : Machine :=
  compileWorkMachine (machineFor slot)

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

theorem slotPrograms_length (slot : Slot) :
    (slotPrograms slot).length = 4 := by
  rfl

theorem statePrograms_length :
    statePrograms.length = 46 := by
  rfl

theorem rulesAt_length (program : StateProgram) :
    (rulesAt program).length = 9 := by
  rfl

set_option maxRecDepth 300000 in
theorem rules_length :
    rules.length = 414 := by
  rfl

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

set_option maxRecDepth 300000 in
private theorem statePrograms_pairwise :
    statePrograms.Pairwise
      (fun left right => left.state ≠ right.state) := by
  decide

private theorem materialized_pairwise
    (programs : List StateProgram)
    (distinct :
      programs.Pairwise (fun left right => left.state ≠ right.state)) :
    (programs.flatMap rulesAt).Pairwise QueryDistinct := by
  induction programs with
  | nil =>
      simp
  | cons program rest ih =>
      rw [List.flatMap_cons, List.pairwise_append]
      refine
        ⟨rulesAt_pairwise program,
          ih (List.pairwise_cons.mp distinct).2,
          ?_⟩
      intro left leftMember right rightMember
      have leftSource := rulesAt_source leftMember
      rcases List.mem_flatMap.mp rightMember with
        ⟨rightProgram, rightProgramMember, rightRuleMember⟩
      have rightSource := rulesAt_source rightRuleMember
      have stateNe :
          program.state ≠ rightProgram.state :=
        (List.pairwise_cons.mp distinct).1 rightProgram
          rightProgramMember
      intro queryEqual
      exact stateNe
        (leftSource.symm.trans
          ((congrArg Prod.fst queryEqual).trans rightSource))

theorem rules_pairwise :
    rules.Pairwise QueryDistinct :=
  materialized_pairwise statePrograms statePrograms_pairwise

theorem start_ne_accept (slot : Slot) :
    (machineFor slot).startState ≠
      (machineFor slot).acceptState := by
  cases slot <;> decide

theorem start_ne_reject (slot : Slot) :
    (machineFor slot).startState ≠
      (machineFor slot).rejectState := by
  cases slot <;> decide

theorem accept_ne_reject (slot : Slot) :
    (machineFor slot).acceptState ≠
      (machineFor slot).rejectState := by
  cases slot <;> decide

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

/-! ### Frozen six-slot layout -/

structure LedgerFits (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters) : Prop where
  inputCount : registers.inputCount ≤ capacity
  normalizedGateCount : registers.normalizedGateCount ≤ capacity
  carrierWidth : registers.carrierWidth ≤ capacity
  baseline : registers.baseline ≤ capacity
  currentGate : registers.currentGate ≤ capacity
  outputIndex : registers.outputIndex ≤ capacity

def selectedValue (slot : Slot)
    (registers : TargetEmitter.UnaryRegisters) : Nat :=
  TargetEmitterLedger.slotValue registers slot

def prefixValues (slot : Slot)
    (registers : TargetEmitter.UnaryRegisters) : List Nat :=
  match slot with
  | .inputCount => []
  | .normalizedGateCount => [registers.inputCount]
  | .carrierWidth =>
      [registers.inputCount, registers.normalizedGateCount]
  | .baseline =>
      [registers.inputCount, registers.normalizedGateCount,
        registers.carrierWidth]
  | .currentGate =>
      [registers.inputCount, registers.normalizedGateCount,
        registers.carrierWidth, registers.baseline]
  | .outputIndex =>
      [registers.inputCount, registers.normalizedGateCount,
        registers.carrierWidth, registers.baseline,
        registers.currentGate]

def suffixValues (slot : Slot)
    (registers : TargetEmitter.UnaryRegisters) : List Nat :=
  match slot with
  | .inputCount =>
      [registers.normalizedGateCount, registers.carrierWidth,
        registers.baseline, registers.currentGate,
        registers.outputIndex]
  | .normalizedGateCount =>
      [registers.carrierWidth, registers.baseline,
        registers.currentGate, registers.outputIndex]
  | .carrierWidth =>
      [registers.baseline, registers.currentGate,
        registers.outputIndex]
  | .baseline =>
      [registers.currentGate, registers.outputIndex]
  | .currentGate => [registers.outputIndex]
  | .outputIndex => []

def valuesWord (capacity : Nat) (values : List Nat) :
    List WorkSymbol :=
  values.flatMap (TargetEmitterLedger.slotWord capacity)

def prefixWord (capacity : Nat) (slot : Slot)
    (registers : TargetEmitter.UnaryRegisters) : List WorkSymbol :=
  valuesWord capacity (prefixValues slot registers)

def suffixWord (capacity : Nat) (slot : Slot)
    (registers : TargetEmitter.UnaryRegisters) : List WorkSymbol :=
  valuesWord capacity (suffixValues slot registers)

theorem prefixValues_length (slot : Slot)
    (registers : TargetEmitter.UnaryRegisters) :
    (prefixValues slot registers).length = slotCode slot := by
  cases slot <;> rfl

theorem slotBank_decompose (capacity : Nat) (slot : Slot)
    (registers : TargetEmitter.UnaryRegisters) :
    TargetEmitterLedger.slotBank capacity registers =
      prefixWord capacity slot registers ++
        TargetEmitterLedger.slotWord capacity
          (selectedValue slot registers) ++
        suffixWord capacity slot registers := by
  cases slot <;>
    simp [TargetEmitterLedger.slotBank, TargetEmitterLedger.Slot.all,
      TargetEmitterLedger.slotValue, prefixWord, suffixWord,
      prefixValues, suffixValues, valuesWord, selectedValue,
      List.append_assoc]

theorem selectedValue_le (capacity : Nat) (slot : Slot)
    (registers : TargetEmitter.UnaryRegisters)
    (fits : LedgerFits capacity registers) :
    selectedValue slot registers ≤ capacity := by
  cases slot with
  | inputCount =>
      exact fits.inputCount
  | normalizedGateCount =>
      exact fits.normalizedGateCount
  | carrierWidth =>
      exact fits.carrierWidth
  | baseline =>
      exact fits.baseline
  | currentGate =>
      exact fits.currentGate
  | outputIndex =>
      exact fits.outputIndex

theorem prefixWord_length (capacity : Nat) (slot : Slot)
    (registers : TargetEmitter.UnaryRegisters)
    (fits : LedgerFits capacity registers) :
    (prefixWord capacity slot registers).length =
      slotCode slot * (capacity + 2) := by
  cases slot <;>
    simp [prefixWord, prefixValues, valuesWord,
      TargetEmitterLedger.slotWord_length_of_le,
      fits.inputCount, fits.normalizedGateCount,
      fits.carrierWidth, fits.baseline, fits.currentGate,
      slotCode, TargetEmitterLedger.Slot.index] <;>
    omega

def scratchWord (capacity scratch : Nat) : List WorkSymbol :=
  List.replicate scratch unaryUnit ++
    unarySeparator ::
      List.replicate (capacity - scratch) WorkSymbol.blank

def selectedPayload (capacity processed remaining : Nat) :
    List WorkSymbol :=
  List.replicate processed unitMark ++
    List.replicate remaining unaryUnit ++
      unarySeparator ::
        List.replicate (capacity - (processed + remaining))
          WorkSymbol.blank

def configAtWord (state : Nat)
    (left word : List WorkSymbol) : WorkConfiguration :=
  TargetEmitter.configAtWord state left word

def configAtLeftWord (state : Nat)
    (leftWord right : List WorkSymbol) : WorkConfiguration :=
  TargetEmitter.configAtLeftWord state leftWord right

def entryConfiguration (slot : Slot) (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft :
      List WorkSymbol) : WorkConfiguration :=
  configAtWord (startState slot)
    (sourceLeftBoundary ::
      (scratchWord capacity scratch ++
        ledgerBoundary ::
          (TargetEmitterLedger.slotBank capacity registers ++
            outsideLeft)))
    (sourceHead :: sourceTail ++ targetAndRight)

def finalConfiguration (slot : Slot) (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft :
      List WorkSymbol) : WorkConfiguration :=
  let value := selectedValue slot registers
  configAtWord acceptState
    (sourceLeftBoundary ::
      (scratchWord capacity (scratch + value) ++
        ledgerBoundary ::
          (TargetEmitterLedger.slotBank capacity registers ++
            outsideLeft)))
    (sourceHead :: sourceTail ++ targetAndRight)

def prefixLength (slot : Slot) (capacity : Nat) : Nat :=
  slotCode slot * (capacity + 2)

def workSteps (slot : Slot) (capacity scratch value : Nat) : Nat :=
  let prior := prefixLength slot capacity
  2 * capacity + 2 * prior + 10 +
    value * (2 * capacity + 2 * prior + 2 * scratch + 17) +
    2 * value * value

theorem workSteps_evaluated (slot : Slot)
    (capacity scratch value : Nat) :
    workSteps slot capacity scratch value =
      2 * capacity +
        2 * (slotCode slot * (capacity + 2)) + 10 +
        value *
          (2 * capacity +
            2 * (slotCode slot * (capacity + 2)) +
            2 * scratch + 17) +
        2 * value * value := by
  rfl

/-! ### Exact-run infrastructure -/

private theorem exactRun_add (slot : Slot)
    (first second : Nat)
    (initial middle final : WorkConfiguration)
    (hFirst :
      workRunExact? (machineFor slot) first initial = some middle)
    (hSecond :
      workRunExact? (machineFor slot) second middle = some final) :
    workRunExact? (machineFor slot) (first + second) initial =
      some final :=
  PipelineMachineSimulation.workRunExact?_compose
    (machineFor slot) first second initial middle final hFirst hSecond

private theorem exactRun_one (slot : Slot)
    (initial final : WorkConfiguration)
    (step :
      workStep? (machineFor slot) initial = some final) :
    workRunExact? (machineFor slot) 1 initial = some final := by
  change
    (match workStep? (machineFor slot) initial with
     | none => none
     | some next => workRunExact? (machineFor slot) 0 next) =
      some final
  rw [step]
  rfl

private def literalRule (source : Nat) (read : WorkSymbol)
    (target : Nat) (write : WorkSymbol) (move : HeadMove) :
    WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := write
    move := move }

private theorem scanLeftExact (slot : Slot) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ head leftTail rightSide,
      Allowed head →
      workStep? (machineFor slot)
          (configAtLeftWord state (head :: leftTail) rightSide) =
        some (configAtLeftWord state
          leftTail (head :: rightSide)))
    (word leftSuffix rightSide : List WorkSymbol)
    (hAllowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? (machineFor slot) word.length
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
        (match workStep? (machineFor slot)
          (configAtLeftWord state
            (head :: (rest ++ leftSuffix)) rightSide) with
         | none => none
         | some next =>
             workRunExact? (machineFor slot) rest.length next) = _
      rw [hStep head (rest ++ leftSuffix) rightSide headAllowed]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (head :: rightSide) restAllowed

private theorem scanRightExact (slot : Slot) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ leftSide head suffix,
      Allowed head →
      workStep? (machineFor slot)
          (configAtWord state leftSide (head :: suffix)) =
        some (configAtWord state (head :: leftSide) suffix))
    (word suffix leftSide : List WorkSymbol)
    (hAllowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? (machineFor slot) word.length
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
        (match workStep? (machineFor slot)
          (configAtWord state leftSide
            (head :: (rest ++ suffix))) with
         | none => none
         | some next =>
             workRunExact? (machineFor slot) rest.length next) = _
      rw [hStep leftSide head (rest ++ suffix) headAllowed]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (head :: leftSide) restAllowed

private theorem moveLeftFromWord_of_find (slot : Slot)
    (state target : Nat) (symbol write : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      (machineFor slot).isHalted
        (configAtWord state left (symbol :: right)) = false)
    (found :
      findWorkRule rules state symbol =
        some (literalRule state symbol target write .left)) :
    workStep? (machineFor slot)
        (configAtWord state left (symbol :: right)) =
      some (configAtLeftWord target left (write :: right)) := by
  calc
    workStep? (machineFor slot)
        (configAtWord state left (symbol :: right)) =
      some (applyWorkRule
        (literalRule state symbol target write .left)
        (configAtWord state left (symbol :: right))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some (configAtLeftWord target left (write :: right)) := by
      cases left <;> rfl

private theorem moveLeftFromLeftWord_of_find (slot : Slot)
    (state target : Nat) (symbol write : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      (machineFor slot).isHalted
        (configAtLeftWord state (symbol :: left) right) = false)
    (found :
      findWorkRule rules state symbol =
        some (literalRule state symbol target write .left)) :
    workStep? (machineFor slot)
        (configAtLeftWord state (symbol :: left) right) =
      some (configAtLeftWord target left (write :: right)) := by
  calc
    workStep? (machineFor slot)
        (configAtLeftWord state (symbol :: left) right) =
      some (applyWorkRule
        (literalRule state symbol target write .left)
        (configAtLeftWord state (symbol :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some (configAtLeftWord target left (write :: right)) := by
      cases left <;> rfl

private theorem moveRightFromLeftWord_of_find (slot : Slot)
    (state target : Nat) (symbol write : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      (machineFor slot).isHalted
        (configAtLeftWord state (symbol :: left) right) = false)
    (found :
      findWorkRule rules state symbol =
        some (literalRule state symbol target write .right)) :
    workStep? (machineFor slot)
        (configAtLeftWord state (symbol :: left) right) =
      some (configAtWord target (write :: left) right) := by
  calc
    workStep? (machineFor slot)
        (configAtLeftWord state (symbol :: left) right) =
      some (applyWorkRule
        (literalRule state symbol target write .right)
        (configAtLeftWord state (symbol :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some (configAtWord target (write :: left) right) := by
      cases right <;> rfl

private theorem moveRightFromWord_of_find (slot : Slot)
    (state target : Nat) (symbol write : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      (machineFor slot).isHalted
        (configAtWord state left (symbol :: right)) = false)
    (found :
      findWorkRule rules state symbol =
        some (literalRule state symbol target write .right)) :
    workStep? (machineFor slot)
        (configAtWord state left (symbol :: right)) =
      some (configAtWord target (write :: left) right) := by
  calc
    workStep? (machineFor slot)
        (configAtWord state left (symbol :: right)) =
      some (applyWorkRule
        (literalRule state symbol target write .right)
        (configAtWord state left (symbol :: right))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some (configAtWord target (write :: left) right) := by
      cases right <;> rfl

private theorem stayAtLeftWord_of_find (slot : Slot)
    (state target : Nat) (symbol write : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      (machineFor slot).isHalted
        (configAtLeftWord state (symbol :: left) right) = false)
    (found :
      findWorkRule rules state symbol =
        some (literalRule state symbol target write .stay)) :
    workStep? (machineFor slot)
        (configAtLeftWord state (symbol :: left) right) =
      some (configAtLeftWord target (write :: left) right) := by
  calc
    workStep? (machineFor slot)
        (configAtLeftWord state (symbol :: left) right) =
      some (applyWorkRule
        (literalRule state symbol target write .stay)
        (configAtLeftWord state (symbol :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some (configAtLeftWord target
        (write :: left) right) := by
      rfl

set_option maxRecDepth 300000 in
private theorem find_start_source (slot : Slot)
    (symbol : WorkSymbol) (allowed : sourceAllowed symbol) :
    findWorkRule rules (startState slot) symbol =
      some (literalRule (startState slot) symbol
        (boundaryState slot) symbol .left) := by
  rcases allowed with packed | cursor
  · cases slot <;> cases packed <;> decide
  · subst symbol
    cases slot <;> decide

set_option maxRecDepth 300000 in
private theorem find_boundary (slot : Slot) :
    findWorkRule rules (boundaryState slot) sourceLeftBoundary =
      some (literalRule (boundaryState slot) sourceLeftBoundary
        (scratchUnitsState slot) sourceLeftBoundary .left) := by
  cases slot <;> decide

set_option maxRecDepth 300000 in
private theorem find_scratch_unit (slot : Slot) :
    findWorkRule rules (scratchUnitsState slot) unaryUnit =
      some (literalRule (scratchUnitsState slot) unaryUnit
        (scratchUnitsState slot) unaryUnit .left) := by
  cases slot <;> decide

set_option maxRecDepth 300000 in
private theorem find_scratch_separator (slot : Slot) :
    findWorkRule rules (scratchUnitsState slot) unarySeparator =
      some (literalRule (scratchUnitsState slot) unarySeparator
        (scratchReserveState slot) unarySeparator .left) := by
  cases slot <;> decide

set_option maxRecDepth 300000 in
private theorem find_scratch_blank (slot : Slot) :
    findWorkRule rules (scratchReserveState slot) WorkSymbol.blank =
      some (literalRule (scratchReserveState slot) WorkSymbol.blank
        (scratchReserveState slot) WorkSymbol.blank .left) := by
  cases slot <;> decide

set_option maxRecDepth 300000 in
private theorem find_ledger_boundary (slot : Slot) :
    findWorkRule rules (scratchReserveState slot) ledgerBoundary =
      some (literalRule (scratchReserveState slot) ledgerBoundary
        (seekSlotState (slotCode slot)) ledgerBoundary .left) := by
  cases slot <;> decide

private theorem remaining_cases (remaining : Nat)
    (remainingLe : remaining ≤ 5) :
    remaining = 0 ∨ remaining = 1 ∨ remaining = 2 ∨
      remaining = 3 ∨ remaining = 4 ∨ remaining = 5 := by
  omega

set_option maxRecDepth 300000 in
private theorem find_seek_payload (remaining : Nat)
    (symbol : WorkSymbol) (remainingLe : remaining ≤ 5)
    (allowed : scratchPayload symbol) :
    findWorkRule rules (seekSlotState remaining) symbol =
      some (literalRule (seekSlotState remaining) symbol
        (seekSlotState remaining) symbol .left) := by
  rcases allowed with unit | separator | blank
  all_goals subst symbol
  all_goals
    rcases remaining_cases remaining remainingLe with
      first | second | third | fourth | fifth | sixth
  all_goals subst remaining
  all_goals decide

set_option maxRecDepth 300000 in
private theorem find_seek_skip_boundary (remaining : Nat)
    (positive : 0 < remaining) (remainingLe : remaining ≤ 5) :
    findWorkRule rules (seekSlotState remaining) slotBoundary =
      some (literalRule (seekSlotState remaining) slotBoundary
        (seekSlotState (remaining - 1)) slotBoundary .left) := by
  rcases remaining_cases remaining remainingLe with
    first | second | third | fourth | fifth | sixth
  · subst remaining
    contradiction
  all_goals subst remaining
  all_goals decide

set_option maxRecDepth 300000 in
private theorem find_seek_selected_boundary :
    findWorkRule rules (seekSlotState 0) slotBoundary =
      some (literalRule (seekSlotState 0) slotBoundary
        selectedState slotBoundary .left) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_selected_mark :
    findWorkRule rules selectedState unitMark =
      some (literalRule selectedState unitMark
        selectedState unitMark .left) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_selected_unit :
    findWorkRule rules selectedState unaryUnit =
      some (literalRule selectedState unaryUnit
        bounceLedgerState unitMark .right) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_selected_separator :
    findWorkRule rules selectedState unarySeparator =
      some (literalRule selectedState unarySeparator
        restoreState unarySeparator .right) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_bounce_ledger (symbol : WorkSymbol)
    (allowed : symbol = unitMark ∨ ledgerPayload symbol) :
    findWorkRule rules bounceLedgerState symbol =
      some (literalRule bounceLedgerState symbol
        bounceLedgerState symbol .right) := by
  rcases allowed with mark | payload
  · subst symbol
    decide
  · rcases payload with unit | separator | blank | boundary
    all_goals subst symbol
    all_goals decide

set_option maxRecDepth 300000 in
private theorem find_bounce_ledger_boundary :
    findWorkRule rules bounceLedgerState ledgerBoundary =
      some (literalRule bounceLedgerState ledgerBoundary
        bounceScratchState ledgerBoundary .right) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_bounce_scratch (symbol : WorkSymbol)
    (allowed : scratchPayload symbol) :
    findWorkRule rules bounceScratchState symbol =
      some (literalRule bounceScratchState symbol
        bounceScratchState symbol .right) := by
  rcases allowed with unit | separator | blank
  all_goals subst symbol
  all_goals decide

set_option maxRecDepth 300000 in
private theorem find_bounce_source_boundary :
    findWorkRule rules bounceScratchState sourceLeftBoundary =
      some (literalRule bounceScratchState sourceLeftBoundary
        incrementStartState sourceLeftBoundary .right) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_increment_source
    (symbol : WorkSymbol) (allowed : sourceAllowed symbol) :
    findWorkRule rules incrementStartState symbol =
      some (literalRule incrementStartState symbol
        incrementBoundaryState symbol .left) := by
  rcases allowed with packed | cursor
  · cases packed <;> decide
  · subst symbol
    decide

set_option maxRecDepth 300000 in
private theorem find_increment_boundary :
    findWorkRule rules incrementBoundaryState sourceLeftBoundary =
      some (literalRule incrementBoundaryState sourceLeftBoundary
        incrementSeekState sourceLeftBoundary .left) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_increment_unit :
    findWorkRule rules incrementSeekState unaryUnit =
      some (literalRule incrementSeekState unaryUnit
        incrementSeekState unaryUnit .left) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_increment_separator :
    findWorkRule rules incrementSeekState unarySeparator =
      some (literalRule incrementSeekState unarySeparator
        incrementWriteState unaryUnit .left) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_increment_blank :
    findWorkRule rules incrementWriteState WorkSymbol.blank =
      some (literalRule incrementWriteState WorkSymbol.blank
        incrementReturnState unarySeparator .right) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_increment_return_unit :
    findWorkRule rules incrementReturnState unaryUnit =
      some (literalRule incrementReturnState unaryUnit
        incrementReturnState unaryUnit .right) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_increment_return_boundary :
    findWorkRule rules incrementReturnState sourceLeftBoundary =
      some (literalRule incrementReturnState sourceLeftBoundary
        resumeStartState sourceLeftBoundary .right) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_resume_source
    (symbol : WorkSymbol) (allowed : sourceAllowed symbol) :
    findWorkRule rules resumeStartState symbol =
      some (literalRule resumeStartState symbol
        resumeBoundaryState symbol .left) := by
  rcases allowed with packed | cursor
  · cases packed <;> decide
  · subst symbol
    decide

set_option maxRecDepth 300000 in
private theorem find_resume_boundary :
    findWorkRule rules resumeBoundaryState sourceLeftBoundary =
      some (literalRule resumeBoundaryState sourceLeftBoundary
        resumeScratchUnitsState sourceLeftBoundary .left) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_resume_scratch_unit :
    findWorkRule rules resumeScratchUnitsState unaryUnit =
      some (literalRule resumeScratchUnitsState unaryUnit
        resumeScratchUnitsState unaryUnit .left) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_resume_scratch_separator :
    findWorkRule rules resumeScratchUnitsState unarySeparator =
      some (literalRule resumeScratchUnitsState unarySeparator
        resumeScratchReserveState unarySeparator .left) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_resume_scratch_blank :
    findWorkRule rules resumeScratchReserveState WorkSymbol.blank =
      some (literalRule resumeScratchReserveState WorkSymbol.blank
        resumeScratchReserveState WorkSymbol.blank .left) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_resume_ledger_boundary :
    findWorkRule rules resumeScratchReserveState ledgerBoundary =
      some (literalRule resumeScratchReserveState ledgerBoundary
        seekMarkState ledgerBoundary .left) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_seek_mark_payload (symbol : WorkSymbol)
    (allowed : ledgerPayload symbol) :
    findWorkRule rules seekMarkState symbol =
      some (literalRule seekMarkState symbol
        seekMarkState symbol .left) := by
  rcases allowed with unit | separator | blank | boundary
  all_goals subst symbol
  all_goals decide

set_option maxRecDepth 300000 in
private theorem find_seek_mark :
    findWorkRule rules seekMarkState unitMark =
      some (literalRule seekMarkState unitMark
        selectedState unitMark .stay) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_restore_mark :
    findWorkRule rules restoreState unitMark =
      some (literalRule restoreState unitMark
        restoreState unaryUnit .right) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_restore_boundary :
    findWorkRule rules restoreState slotBoundary =
      some (literalRule restoreState slotBoundary
        finalLedgerState slotBoundary .right) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_final_ledger (symbol : WorkSymbol)
    (allowed : ledgerPayload symbol) :
    findWorkRule rules finalLedgerState symbol =
      some (literalRule finalLedgerState symbol
        finalLedgerState symbol .right) := by
  rcases allowed with unit | separator | blank | boundary
  all_goals subst symbol
  all_goals decide

set_option maxRecDepth 300000 in
private theorem find_final_ledger_boundary :
    findWorkRule rules finalLedgerState ledgerBoundary =
      some (literalRule finalLedgerState ledgerBoundary
        finalScratchState ledgerBoundary .right) := by
  decide

set_option maxRecDepth 300000 in
private theorem find_final_scratch (symbol : WorkSymbol)
    (allowed : scratchPayload symbol) :
    findWorkRule rules finalScratchState symbol =
      some (literalRule finalScratchState symbol
        finalScratchState symbol .right) := by
  rcases allowed with unit | separator | blank
  all_goals subst symbol
  all_goals decide

set_option maxRecDepth 300000 in
private theorem find_final_source_boundary :
    findWorkRule rules finalScratchState sourceLeftBoundary =
      some (literalRule finalScratchState sourceLeftBoundary
        acceptState sourceLeftBoundary .right) := by
  decide

/-! ### Literal step and scan lemmas -/

private theorem start_source_step (slot : Slot)
    (symbol : WorkSymbol) (allowed : sourceAllowed symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord (startState slot) left (symbol :: right)) =
      some (configAtLeftWord (boundaryState slot)
        left (symbol :: right)) := by
  apply moveLeftFromWord_of_find slot
  · cases slot <;> rfl
  · exact find_start_source slot symbol allowed

private theorem boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (boundaryState slot)
          (sourceLeftBoundary :: left) right) =
      some (configAtLeftWord (scratchUnitsState slot)
        left (sourceLeftBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_boundary slot

private theorem scratch_unit_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (scratchUnitsState slot)
          (unaryUnit :: left) right) =
      some (configAtLeftWord (scratchUnitsState slot)
        left (unaryUnit :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_scratch_unit slot

private theorem scratch_separator_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (scratchUnitsState slot)
          (unarySeparator :: left) right) =
      some (configAtLeftWord (scratchReserveState slot)
        left (unarySeparator :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_scratch_separator slot

private theorem scratch_blank_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (scratchReserveState slot)
          (WorkSymbol.blank :: left) right) =
      some (configAtLeftWord (scratchReserveState slot)
        left (WorkSymbol.blank :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_scratch_blank slot

private theorem ledger_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (scratchReserveState slot)
          (ledgerBoundary :: left) right) =
      some (configAtLeftWord (seekSlotState (slotCode slot))
        left (ledgerBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_ledger_boundary slot

private theorem seek_payload_step (slot : Slot)
    (remaining : Nat) (remainingLe : remaining ≤ 5)
    (symbol : WorkSymbol) (allowed : scratchPayload symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (seekSlotState remaining)
          (symbol :: left) right) =
      some (configAtLeftWord (seekSlotState remaining)
        left (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · have acceptNe : seekSlotState remaining ≠ acceptState := by
      unfold seekSlotState acceptState
      omega
    have rejectNe : seekSlotState remaining ≠ rejectState := by
      unfold seekSlotState rejectState
      omega
    simp [WorkMachine.isHalted, machineFor, configAtLeftWord,
      TargetEmitter.configAtLeftWord, acceptNe, rejectNe]
  · exact find_seek_payload remaining symbol remainingLe allowed

private theorem seek_skip_boundary_step (slot : Slot)
    (remaining : Nat) (positive : 0 < remaining)
    (remainingLe : remaining ≤ 5)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (seekSlotState remaining)
          (slotBoundary :: left) right) =
      some (configAtLeftWord (seekSlotState (remaining - 1))
        left (slotBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · have acceptNe : seekSlotState remaining ≠ acceptState := by
      unfold seekSlotState acceptState
      omega
    have rejectNe : seekSlotState remaining ≠ rejectState := by
      unfold seekSlotState rejectState
      omega
    simp [WorkMachine.isHalted, machineFor, configAtLeftWord,
      TargetEmitter.configAtLeftWord, acceptNe, rejectNe]
  · exact find_seek_skip_boundary remaining positive remainingLe

private theorem seek_selected_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (seekSlotState 0)
          (slotBoundary :: left) right) =
      some (configAtLeftWord selectedState
        left (slotBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rfl
  · exact find_seek_selected_boundary

private theorem selected_mark_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord selectedState
          (unitMark :: left) right) =
      some (configAtLeftWord selectedState
        left (unitMark :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rfl
  · exact find_selected_mark

private theorem selected_unit_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord selectedState
          (unaryUnit :: left) right) =
      some (configAtWord bounceLedgerState
        (unitMark :: left) right) := by
  apply moveRightFromLeftWord_of_find slot
  · rfl
  · exact find_selected_unit

private theorem selected_separator_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord selectedState
          (unarySeparator :: left) right) =
      some (configAtWord restoreState
        (unarySeparator :: left) right) := by
  apply moveRightFromLeftWord_of_find slot
  · rfl
  · exact find_selected_separator

private theorem bounce_ledger_step (slot : Slot)
    (symbol : WorkSymbol)
    (allowed : symbol = unitMark ∨ ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord bounceLedgerState left (symbol :: right)) =
      some (configAtWord bounceLedgerState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find slot
  · rfl
  · exact find_bounce_ledger symbol allowed

private theorem bounce_ledger_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord bounceLedgerState left
          (ledgerBoundary :: right)) =
      some (configAtWord bounceScratchState
        (ledgerBoundary :: left) right) := by
  apply moveRightFromWord_of_find slot
  · rfl
  · exact find_bounce_ledger_boundary

private theorem bounce_scratch_step (slot : Slot)
    (symbol : WorkSymbol) (allowed : scratchPayload symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord bounceScratchState left (symbol :: right)) =
      some (configAtWord bounceScratchState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find slot
  · rfl
  · exact find_bounce_scratch symbol allowed

private theorem bounce_source_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord bounceScratchState left
          (sourceLeftBoundary :: right)) =
      some (configAtWord incrementStartState
        (sourceLeftBoundary :: left) right) := by
  apply moveRightFromWord_of_find slot
  · rfl
  · exact find_bounce_source_boundary

private theorem increment_source_step (slot : Slot)
    (symbol : WorkSymbol) (allowed : sourceAllowed symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord incrementStartState left (symbol :: right)) =
      some (configAtLeftWord incrementBoundaryState
        left (symbol :: right)) := by
  apply moveLeftFromWord_of_find slot
  · rfl
  · exact find_increment_source symbol allowed

private theorem increment_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord incrementBoundaryState
          (sourceLeftBoundary :: left) right) =
      some (configAtLeftWord incrementSeekState
        left (sourceLeftBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rfl
  · exact find_increment_boundary

private theorem increment_unit_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord incrementSeekState
          (unaryUnit :: left) right) =
      some (configAtLeftWord incrementSeekState
        left (unaryUnit :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rfl
  · exact find_increment_unit

private theorem increment_separator_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord incrementSeekState
          (unarySeparator :: left) right) =
      some (configAtLeftWord incrementWriteState
        left (unaryUnit :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rfl
  · exact find_increment_separator

private theorem increment_blank_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord incrementWriteState
          (WorkSymbol.blank :: left) right) =
      some (configAtWord incrementReturnState
        (unarySeparator :: left) right) := by
  apply moveRightFromLeftWord_of_find slot
  · rfl
  · exact find_increment_blank

private theorem increment_return_unit_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord incrementReturnState left
          (unaryUnit :: right)) =
      some (configAtWord incrementReturnState
        (unaryUnit :: left) right) := by
  apply moveRightFromWord_of_find slot
  · rfl
  · exact find_increment_return_unit

private theorem increment_return_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord incrementReturnState left
          (sourceLeftBoundary :: right)) =
      some (configAtWord resumeStartState
        (sourceLeftBoundary :: left) right) := by
  apply moveRightFromWord_of_find slot
  · rfl
  · exact find_increment_return_boundary

private theorem resume_source_step (slot : Slot)
    (symbol : WorkSymbol) (allowed : sourceAllowed symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord resumeStartState left (symbol :: right)) =
      some (configAtLeftWord resumeBoundaryState
        left (symbol :: right)) := by
  apply moveLeftFromWord_of_find slot
  · rfl
  · exact find_resume_source symbol allowed

private theorem resume_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord resumeBoundaryState
          (sourceLeftBoundary :: left) right) =
      some (configAtLeftWord resumeScratchUnitsState
        left (sourceLeftBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rfl
  · exact find_resume_boundary

private theorem resume_scratch_unit_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord resumeScratchUnitsState
          (unaryUnit :: left) right) =
      some (configAtLeftWord resumeScratchUnitsState
        left (unaryUnit :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rfl
  · exact find_resume_scratch_unit

private theorem resume_scratch_separator_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord resumeScratchUnitsState
          (unarySeparator :: left) right) =
      some (configAtLeftWord resumeScratchReserveState
        left (unarySeparator :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rfl
  · exact find_resume_scratch_separator

private theorem resume_scratch_blank_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord resumeScratchReserveState
          (WorkSymbol.blank :: left) right) =
      some (configAtLeftWord resumeScratchReserveState
        left (WorkSymbol.blank :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rfl
  · exact find_resume_scratch_blank

private theorem resume_ledger_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord resumeScratchReserveState
          (ledgerBoundary :: left) right) =
      some (configAtLeftWord seekMarkState
        left (ledgerBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rfl
  · exact find_resume_ledger_boundary

private theorem seek_mark_payload_step (slot : Slot)
    (symbol : WorkSymbol) (allowed : ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord seekMarkState
          (symbol :: left) right) =
      some (configAtLeftWord seekMarkState
        left (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rfl
  · exact find_seek_mark_payload symbol allowed

private theorem seek_mark_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord seekMarkState
          (unitMark :: left) right) =
      some (configAtLeftWord selectedState
        (unitMark :: left) right) := by
  apply stayAtLeftWord_of_find slot
  · rfl
  · exact find_seek_mark

private theorem restore_mark_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord restoreState left (unitMark :: right)) =
      some (configAtWord restoreState
        (unaryUnit :: left) right) := by
  apply moveRightFromWord_of_find slot
  · rfl
  · exact find_restore_mark

private theorem restore_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord restoreState left
          (slotBoundary :: right)) =
      some (configAtWord finalLedgerState
        (slotBoundary :: left) right) := by
  apply moveRightFromWord_of_find slot
  · rfl
  · exact find_restore_boundary

private theorem final_ledger_step (slot : Slot)
    (symbol : WorkSymbol) (allowed : ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord finalLedgerState left (symbol :: right)) =
      some (configAtWord finalLedgerState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find slot
  · rfl
  · exact find_final_ledger symbol allowed

private theorem final_ledger_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord finalLedgerState left
          (ledgerBoundary :: right)) =
      some (configAtWord finalScratchState
        (ledgerBoundary :: left) right) := by
  apply moveRightFromWord_of_find slot
  · rfl
  · exact find_final_ledger_boundary

private theorem final_scratch_step (slot : Slot)
    (symbol : WorkSymbol) (allowed : scratchPayload symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord finalScratchState left (symbol :: right)) =
      some (configAtWord finalScratchState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find slot
  · rfl
  · exact find_final_scratch symbol allowed

private theorem final_source_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord finalScratchState left
          (sourceLeftBoundary :: right)) =
      some (configAtWord acceptState
        (sourceLeftBoundary :: left) right) := by
  apply moveRightFromWord_of_find slot
  · rfl
  · exact find_final_source_boundary

private def slotPayload (capacity value : Nat) :
    List WorkSymbol :=
  List.replicate value unaryUnit ++
    unarySeparator ::
      List.replicate (capacity - value) WorkSymbol.blank

private theorem slotWord_eq (capacity value : Nat) :
    TargetEmitterLedger.slotWord capacity value =
      slotBoundary :: slotPayload capacity value := by
  simp [TargetEmitterLedger.slotWord, slotPayload,
    TargetEmitter.unaryWord, slotBoundary, unaryUnit,
    unarySeparator, TargetEmitterLedger.slotSeparator,
    TargetEmitterLedger.unaryUnit, TargetEmitterLedger.cellBlank,
    List.append_assoc]

private theorem slotPayload_allowed (capacity value : Nat) :
    ∀ symbol, symbol ∈ slotPayload capacity value →
      scratchPayload symbol := by
  intro symbol found
  unfold slotPayload at found
  rw [List.mem_append] at found
  rcases found with inUnits | inTail
  · exact Or.inl (List.eq_of_mem_replicate inUnits)
  · cases inTail with
    | head => exact Or.inr (Or.inl rfl)
    | tail _ inBlanks =>
        exact Or.inr (Or.inr
          (List.eq_of_mem_replicate inBlanks))

private theorem valuesWord_allowed (capacity : Nat)
    (values : List Nat) :
    ∀ symbol, symbol ∈ valuesWord capacity values →
      ledgerPayload symbol := by
  intro symbol found
  rcases List.mem_flatMap.mp found with
    ⟨value, _valueFound, symbolFound⟩
  rw [slotWord_eq] at symbolFound
  cases symbolFound with
  | head =>
      exact Or.inr (Or.inr (Or.inr rfl))
  | tail _ inPayload =>
      rcases slotPayload_allowed capacity value symbol inPayload with
        unit | separator | blank
      · exact Or.inl unit
      · exact Or.inr (Or.inl separator)
      · exact Or.inr (Or.inr (Or.inl blank))

private theorem scratchWord_allowed (capacity scratch : Nat) :
    ∀ symbol, symbol ∈ scratchWord capacity scratch →
      scratchPayload symbol := by
  intro symbol found
  unfold scratchWord at found
  rw [List.mem_append] at found
  rcases found with inUnits | inTail
  · exact Or.inl (List.eq_of_mem_replicate inUnits)
  · cases inTail with
    | head => exact Or.inr (Or.inl rfl)
    | tail _ inBlanks =>
        exact Or.inr (Or.inr
          (List.eq_of_mem_replicate inBlanks))

private theorem scratch_units_exact (slot : Slot)
    (state : Nat)
    (step : ∀ left right,
      workStep? (machineFor slot)
          (configAtLeftWord state (unaryUnit :: left) right) =
        some (configAtLeftWord state left (unaryUnit :: right)))
    (count : Nat) (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) count
        (configAtLeftWord state
          (List.replicate count unaryUnit ++ left) right) =
      some (configAtLeftWord state left
        (List.replicate count unaryUnit ++ right)) := by
  have scanned := scanLeftExact slot state
    (fun symbol => symbol = unaryUnit)
    (fun head leftTail rightSide equality => by
      subst head
      exact step leftTail rightSide)
    (List.replicate count unaryUnit) left right (by simp)
  simpa using scanned

private theorem scratch_blanks_exact (slot : Slot)
    (state : Nat)
    (step : ∀ left right,
      workStep? (machineFor slot)
          (configAtLeftWord state
            (WorkSymbol.blank :: left) right) =
        some (configAtLeftWord state
          left (WorkSymbol.blank :: right)))
    (count : Nat) (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) count
        (configAtLeftWord state
          (List.replicate count WorkSymbol.blank ++ left) right) =
      some (configAtLeftWord state left
        (List.replicate count WorkSymbol.blank ++ right)) := by
  have scanned := scanLeftExact slot state
    (fun symbol => symbol = WorkSymbol.blank)
    (fun head leftTail rightSide equality => by
      subst head
      exact step leftTail rightSide)
    (List.replicate count WorkSymbol.blank) left right (by simp)
  simpa using scanned

private theorem seekPayload_exact (slot : Slot)
    (remaining : Nat) (remainingLe : remaining ≤ 5)
    (capacity value : Nat) (left right : List WorkSymbol) :
    workRunExact? (machineFor slot)
        (slotPayload capacity value).length
        (configAtLeftWord (seekSlotState remaining)
          (slotPayload capacity value ++ left) right) =
      some (configAtLeftWord (seekSlotState remaining)
        left ((slotPayload capacity value).reverse ++ right)) := by
  exact scanLeftExact slot (seekSlotState remaining)
    scratchPayload
    (fun head leftTail rightSide allowed =>
      seek_payload_step slot remaining remainingLe head allowed
        leftTail rightSide)
    (slotPayload capacity value) left right
    (slotPayload_allowed capacity value)

private theorem seekPrefix_exact (slot : Slot)
    (capacity : Nat) (values : List Nat)
    (valuesLe : values.length ≤ 5)
    (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) (valuesWord capacity values).length
        (configAtLeftWord (seekSlotState values.length)
          (valuesWord capacity values ++ left) right) =
      some (configAtLeftWord (seekSlotState 0)
        left ((valuesWord capacity values).reverse ++ right)) := by
  induction values generalizing right with
  | nil =>
      rfl
  | cons value rest ih =>
      have positive : 0 < rest.length + 1 := by omega
      have remainingLe : rest.length + 1 ≤ 5 := by
        simpa using valuesLe
      have restLe : rest.length ≤ 5 := by omega
      let afterBoundary :=
        configAtLeftWord (seekSlotState rest.length)
          (slotPayload capacity value ++
            valuesWord capacity rest ++ left)
          (slotBoundary :: right)
      let afterPayload :=
        configAtLeftWord (seekSlotState rest.length)
          (valuesWord capacity rest ++ left)
          ((slotPayload capacity value).reverse ++
            slotBoundary :: right)
      have hBoundary :
          workRunExact? (machineFor slot) 1
              (configAtLeftWord
                (seekSlotState (rest.length + 1))
                (slotBoundary ::
                  slotPayload capacity value ++
                    valuesWord capacity rest ++ left) right) =
            some afterBoundary := by
        apply exactRun_one slot
        simpa [afterBoundary, List.append_assoc] using
          seek_skip_boundary_step slot (rest.length + 1)
            positive remainingLe
            (slotPayload capacity value ++
              valuesWord capacity rest ++ left) right
      have hPayload :
          workRunExact? (machineFor slot)
              (slotPayload capacity value).length afterBoundary =
            some afterPayload := by
        simpa [afterBoundary, afterPayload, List.append_assoc] using
          seekPayload_exact slot rest.length restLe capacity value
            (valuesWord capacity rest ++ left)
            (slotBoundary :: right)
      have hRest :
          workRunExact? (machineFor slot)
              (valuesWord capacity rest).length afterPayload =
            some (configAtLeftWord (seekSlotState 0) left
              ((valuesWord capacity rest).reverse ++
                (slotPayload capacity value).reverse ++
                  slotBoundary :: right)) := by
        simpa [afterPayload, List.append_assoc] using
          ih restLe
            ((slotPayload capacity value).reverse ++
              slotBoundary :: right)
      have first := exactRun_add slot 1
        (slotPayload capacity value).length _ _ _
        hBoundary hPayload
      have complete := exactRun_add slot
        (1 + (slotPayload capacity value).length)
        (valuesWord capacity rest).length _ _ _
        first hRest
      have stepCount :
          1 + (slotPayload capacity value).length +
              (valuesWord capacity rest).length =
            (valuesWord capacity (value :: rest)).length := by
        simp [valuesWord, slotWord_eq]
        omega
      rw [stepCount] at complete
      simpa [valuesWord, slotWord_eq, List.reverse_append,
        List.append_assoc] using complete

private theorem selected_marks_exact (slot : Slot)
    (count : Nat) (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) count
        (configAtLeftWord selectedState
          (List.replicate count unitMark ++ left) right) =
      some (configAtLeftWord selectedState left
        (List.replicate count unitMark ++ right)) := by
  have scanned := scanLeftExact slot selectedState
    (fun symbol => symbol = unitMark)
    (fun head leftTail rightSide equality => by
      subst head
      exact selected_mark_step slot leftTail rightSide)
    (List.replicate count unitMark) left right (by simp)
  simpa using scanned

private theorem scanBounceLedgerExact (slot : Slot)
    (word : List WorkSymbol)
    (allowed :
      ∀ symbol, symbol ∈ word →
        symbol = unitMark ∨ ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) word.length
        (configAtWord bounceLedgerState left (word ++ right)) =
      some (configAtWord bounceLedgerState
        (word.reverse ++ left) right) :=
  scanRightExact slot bounceLedgerState
    (fun symbol => symbol = unitMark ∨ ledgerPayload symbol)
    (fun leftSide head suffix headAllowed =>
      bounce_ledger_step slot head headAllowed leftSide suffix)
    word right left allowed

private theorem scanBounceScratchExact (slot : Slot)
    (capacity scratch : Nat)
    (left right : List WorkSymbol) :
    workRunExact? (machineFor slot)
        (scratchWord capacity scratch).length
        (configAtWord bounceScratchState left
          ((scratchWord capacity scratch).reverse ++ right)) =
      some (configAtWord bounceScratchState
        (scratchWord capacity scratch ++ left) right) := by
  have scanned := scanRightExact slot bounceScratchState
    scratchPayload
    (fun leftSide head suffix headAllowed =>
      bounce_scratch_step slot head headAllowed leftSide suffix)
    (scratchWord capacity scratch).reverse right left (by
      intro symbol found
      exact scratchWord_allowed capacity scratch symbol
        (List.mem_reverse.mp found))
  simpa using scanned

private theorem scanSeekMarkExact (slot : Slot)
    (word : List WorkSymbol)
    (allowed :
      ∀ symbol, symbol ∈ word → ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) word.length
        (configAtLeftWord seekMarkState
          (word ++ left) right) =
      some (configAtLeftWord seekMarkState left
        (word.reverse ++ right)) :=
  scanLeftExact slot seekMarkState ledgerPayload
    (fun head leftTail rightSide headAllowed =>
      seek_mark_payload_step slot head headAllowed leftTail rightSide)
    word left right allowed

private theorem scanFinalLedgerExact (slot : Slot)
    (word : List WorkSymbol)
    (allowed :
      ∀ symbol, symbol ∈ word → ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) word.length
        (configAtWord finalLedgerState left (word ++ right)) =
      some (configAtWord finalLedgerState
        (word.reverse ++ left) right) :=
  scanRightExact slot finalLedgerState ledgerPayload
    (fun leftSide head suffix headAllowed =>
      final_ledger_step slot head headAllowed leftSide suffix)
    word right left allowed

private theorem scanFinalScratchExact (slot : Slot)
    (capacity scratch : Nat)
    (left right : List WorkSymbol) :
    workRunExact? (machineFor slot)
        (scratchWord capacity scratch).length
        (configAtWord finalScratchState left
          ((scratchWord capacity scratch).reverse ++ right)) =
      some (configAtWord finalScratchState
        (scratchWord capacity scratch ++ left) right) := by
  have scanned := scanRightExact slot finalScratchState
    scratchPayload
    (fun leftSide head suffix headAllowed =>
      final_scratch_step slot head headAllowed leftSide suffix)
    (scratchWord capacity scratch).reverse right left (by
      intro symbol found
      exact scratchWord_allowed capacity scratch symbol
        (List.mem_reverse.mp found))
  simpa using scanned

private theorem increment_units_exact (slot : Slot)
    (count : Nat) (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) count
        (configAtLeftWord incrementSeekState
          (List.replicate count unaryUnit ++ left) right) =
      some (configAtLeftWord incrementSeekState left
        (List.replicate count unaryUnit ++ right)) :=
  scratch_units_exact slot incrementSeekState
    (increment_unit_step slot) count left right

private theorem increment_return_units_exact (slot : Slot)
    (count : Nat) (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) count
        (configAtWord incrementReturnState left
          (List.replicate count unaryUnit ++ right)) =
      some (configAtWord incrementReturnState
        (List.replicate count unaryUnit ++ left) right) := by
  have scanned := scanRightExact slot incrementReturnState
    (fun symbol => symbol = unaryUnit)
    (fun leftSide head suffix equality => by
      subst head
      exact increment_return_unit_step slot leftSide suffix)
    (List.replicate count unaryUnit) right left (by simp)
  simpa using scanned

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

private theorem increment_exact (slot : Slot) (count : Nat)
    (reserveTail outsideLeft sourceWord : List WorkSymbol)
    (sourceHead : WorkSymbol) (allowed : sourceAllowed sourceHead) :
    workRunExact? (machineFor slot) (2 * count + 6)
        (configAtWord incrementStartState
          (sourceLeftBoundary ::
            (List.replicate count unaryUnit ++
              unarySeparator :: WorkSymbol.blank ::
                reserveTail ++ outsideLeft))
          (sourceHead :: sourceWord)) =
      some (configAtWord resumeStartState
        (sourceLeftBoundary ::
          (List.replicate (count + 1) unaryUnit ++
            unarySeparator :: reserveTail ++ outsideLeft))
        (sourceHead :: sourceWord)) := by
  let source := sourceHead :: sourceWord
  let tail :=
    List.replicate count unaryUnit ++
      unarySeparator :: WorkSymbol.blank ::
        reserveTail ++ outsideLeft
  let afterSource :=
    configAtLeftWord incrementBoundaryState
      (sourceLeftBoundary :: tail) source
  let afterBoundary :=
    configAtLeftWord incrementSeekState tail
      (sourceLeftBoundary :: source)
  let atSeparator :=
    configAtLeftWord incrementSeekState
      (unarySeparator :: WorkSymbol.blank ::
        reserveTail ++ outsideLeft)
      (List.replicate count unaryUnit ++
        sourceLeftBoundary :: source)
  let atBlank :=
    configAtLeftWord incrementWriteState
      (WorkSymbol.blank :: reserveTail ++ outsideLeft)
      (unaryUnit :: List.replicate count unaryUnit ++
        sourceLeftBoundary :: source)
  let returning :=
    configAtWord incrementReturnState
      (unarySeparator :: reserveTail ++ outsideLeft)
      (List.replicate (count + 1) unaryUnit ++
        sourceLeftBoundary :: source)
  let atBoundary :=
    configAtWord incrementReturnState
      (List.replicate (count + 1) unaryUnit ++
        unarySeparator :: reserveTail ++ outsideLeft)
      (sourceLeftBoundary :: source)
  have hSource :
      workRunExact? (machineFor slot) 1
          (configAtWord incrementStartState
            (sourceLeftBoundary :: tail) source) =
        some afterSource := by
    apply exactRun_one slot
    simpa [afterSource, source] using
      increment_source_step slot sourceHead allowed
        (sourceLeftBoundary :: tail) sourceWord
  have hBoundary :
      workRunExact? (machineFor slot) 1 afterSource =
        some afterBoundary := by
    apply exactRun_one slot
    simpa [afterSource, afterBoundary] using
      increment_boundary_step slot tail source
  have hUnits :
      workRunExact? (machineFor slot) count afterBoundary =
        some atSeparator := by
    simpa [afterBoundary, atSeparator, tail,
      List.append_assoc] using
      increment_units_exact slot count
        (unarySeparator :: WorkSymbol.blank ::
          reserveTail ++ outsideLeft)
        (sourceLeftBoundary :: source)
  have hSeparator :
      workRunExact? (machineFor slot) 1 atSeparator =
        some atBlank := by
    apply exactRun_one slot
    simpa [atSeparator, atBlank] using
      increment_separator_step slot
        (WorkSymbol.blank :: reserveTail ++ outsideLeft)
        (List.replicate count unaryUnit ++
          sourceLeftBoundary :: source)
  have hBlank :
      workRunExact? (machineFor slot) 1 atBlank =
        some returning := by
    apply exactRun_one slot
    simpa [atBlank, returning, List.replicate_succ,
      Nat.add_comm, List.append_assoc] using
      increment_blank_step slot
        (reserveTail ++ outsideLeft)
        (unaryUnit :: List.replicate count unaryUnit ++
          sourceLeftBoundary :: source)
  have hReturn :
      workRunExact? (machineFor slot) (count + 1) returning =
        some atBoundary := by
    simpa [returning, atBoundary] using
      increment_return_units_exact slot (count + 1)
        (unarySeparator :: reserveTail ++ outsideLeft)
        (sourceLeftBoundary :: source)
  have hLast :
      workRunExact? (machineFor slot) 1 atBoundary =
        some (configAtWord resumeStartState
          (sourceLeftBoundary ::
            (List.replicate (count + 1) unaryUnit ++
              unarySeparator :: reserveTail ++ outsideLeft))
          source) := by
    apply exactRun_one slot
    simpa [atBoundary, List.append_assoc] using
      increment_return_boundary_step slot
        (List.replicate (count + 1) unaryUnit ++
          unarySeparator :: reserveTail ++ outsideLeft)
        source
  have h01 := exactRun_add slot 1 1 _ _ _ hSource hBoundary
  have h02 := exactRun_add slot 2 count _ _ _ h01 hUnits
  have h03 := exactRun_add slot (2 + count) 1 _ _ _
    h02 hSeparator
  have h04 := exactRun_add slot (2 + count + 1) 1 _ _ _
    h03 hBlank
  have h05 := exactRun_add slot (2 + count + 1 + 1)
    (count + 1) _ _ _ h04 hReturn
  have complete := exactRun_add slot
    (2 + count + 1 + 1 + (count + 1)) 1
    _ _ _ h05 hLast
  have steps :
      2 + count + 1 + 1 + (count + 1) + 1 =
        2 * count + 6 := by omega
  rw [steps] at complete
  simpa [source, tail, List.append_assoc] using complete

private def coreEntryConfiguration (slot : Slot)
    (capacity scratch value : Nat)
    (priorValues : List Nat) (outerLeft : List WorkSymbol)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord (startState slot)
    (sourceLeftBoundary ::
      (scratchWord capacity scratch ++
        ledgerBoundary ::
          (valuesWord capacity priorValues ++
            slotBoundary ::
              selectedPayload capacity 0 value ++ outerLeft)))
    (sourceHead :: sourceTail)

private def loopSourceConfiguration (capacity scratch
    processed remaining : Nat)
    (priorWord outerLeft sourceWord : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord resumeStartState
    (sourceLeftBoundary ::
      (scratchWord capacity (scratch + processed) ++
        ledgerBoundary ::
          (priorWord ++
            slotBoundary ::
              selectedPayload capacity processed remaining ++
                outerLeft)))
    sourceWord

private def selectedConfiguration (capacity scratch
    processed remaining : Nat)
    (priorWord outerLeft sourceWord : List WorkSymbol) :
    WorkConfiguration :=
  configAtLeftWord selectedState
    (selectedPayload capacity processed remaining ++ outerLeft)
    (slotBoundary :: priorWord.reverse ++
      ledgerBoundary ::
        (scratchWord capacity (scratch + processed)).reverse ++
          sourceLeftBoundary :: sourceWord)

private def coreFinalConfiguration (capacity scratch value : Nat)
    (priorWord outerLeft sourceWord : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord acceptState
    (sourceLeftBoundary ::
      (scratchWord capacity (scratch + value) ++
        ledgerBoundary ::
          (priorWord ++
            slotBoundary ::
              slotPayload capacity value ++ outerLeft)))
    sourceWord

private theorem scratchWord_length_of_le
    (capacity scratch : Nat) (bounded : scratch ≤ capacity) :
    (scratchWord capacity scratch).length = capacity + 1 := by
  simp [scratchWord]
  omega

private theorem initial_to_selected_exact (slot : Slot)
    (capacity scratch value : Nat)
    (priorValues : List Nat) (outerLeft : List WorkSymbol)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (priorLength : priorValues.length = slotCode slot)
    (scratchBound : scratch ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    workRunExact? (machineFor slot)
        (capacity + (valuesWord capacity priorValues).length + 5)
        (coreEntryConfiguration slot capacity scratch value
          priorValues outerLeft sourceHead sourceTail) =
      some (selectedConfiguration capacity scratch 0 value
        (valuesWord capacity priorValues) outerLeft
        (sourceHead :: sourceTail)) := by
  let sourceWord := sourceHead :: sourceTail
  let scratchW := scratchWord capacity scratch
  let priorWord := valuesWord capacity priorValues
  let selected := selectedPayload capacity 0 value
  let afterSource :=
    configAtLeftWord (boundaryState slot)
      (sourceLeftBoundary ::
        scratchW ++ ledgerBoundary ::
          (priorWord ++ slotBoundary :: selected ++ outerLeft))
      sourceWord
  let afterBoundary :=
    configAtLeftWord (scratchUnitsState slot)
      (scratchW ++ ledgerBoundary ::
        (priorWord ++ slotBoundary :: selected ++ outerLeft))
      (sourceLeftBoundary :: sourceWord)
  let atSeparator :=
    configAtLeftWord (scratchUnitsState slot)
      (unarySeparator ::
        List.replicate (capacity - scratch) WorkSymbol.blank ++
          ledgerBoundary ::
            (priorWord ++ slotBoundary :: selected ++ outerLeft))
      (List.replicate scratch unaryUnit ++
        sourceLeftBoundary :: sourceWord)
  let afterSeparator :=
    configAtLeftWord (scratchReserveState slot)
      (List.replicate (capacity - scratch) WorkSymbol.blank ++
        ledgerBoundary ::
          (priorWord ++ slotBoundary :: selected ++ outerLeft))
      (unarySeparator ::
        List.replicate scratch unaryUnit ++
          sourceLeftBoundary :: sourceWord)
  let atLedger :=
    configAtLeftWord (scratchReserveState slot)
      (ledgerBoundary ::
        (priorWord ++ slotBoundary :: selected ++ outerLeft))
      (scratchW.reverse ++ sourceLeftBoundary :: sourceWord)
  let afterLedger :=
    configAtLeftWord (seekSlotState (slotCode slot))
      (priorWord ++ slotBoundary :: selected ++ outerLeft)
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: sourceWord)
  let atSelectedBoundary :=
    configAtLeftWord (seekSlotState 0)
      (slotBoundary :: selected ++ outerLeft)
      (priorWord.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: sourceWord)
  have hSource :
      workRunExact? (machineFor slot) 1
          (coreEntryConfiguration slot capacity scratch value
            priorValues outerLeft sourceHead sourceTail) =
        some afterSource := by
    apply exactRun_one slot
    simpa [coreEntryConfiguration, afterSource, sourceWord,
      scratchW, priorWord, selected, List.append_assoc] using
      start_source_step slot sourceHead allowed
        (sourceLeftBoundary ::
          scratchW ++ ledgerBoundary ::
            (priorWord ++ slotBoundary :: selected ++ outerLeft))
        sourceTail
  have hBoundary :
      workRunExact? (machineFor slot) 1 afterSource =
        some afterBoundary := by
    apply exactRun_one slot
    simpa [afterSource, afterBoundary] using
      boundary_step slot
        (scratchW ++ ledgerBoundary ::
          (priorWord ++ slotBoundary :: selected ++ outerLeft))
        sourceWord
  have hUnits :
      workRunExact? (machineFor slot) scratch afterBoundary =
        some atSeparator := by
    simpa [afterBoundary, atSeparator, scratchW, scratchWord,
      List.append_assoc] using
      scratch_units_exact slot (scratchUnitsState slot)
        (scratch_unit_step slot) scratch
        (unarySeparator ::
          List.replicate (capacity - scratch) WorkSymbol.blank ++
            ledgerBoundary ::
              (priorWord ++ slotBoundary :: selected ++ outerLeft))
        (sourceLeftBoundary :: sourceWord)
  have hSeparator :
      workRunExact? (machineFor slot) 1 atSeparator =
        some afterSeparator := by
    apply exactRun_one slot
    simpa [atSeparator, afterSeparator] using
      scratch_separator_step slot
        (List.replicate (capacity - scratch) WorkSymbol.blank ++
          ledgerBoundary ::
            (priorWord ++ slotBoundary :: selected ++ outerLeft))
        (List.replicate scratch unaryUnit ++
          sourceLeftBoundary :: sourceWord)
  have hBlanks :
      workRunExact? (machineFor slot) (capacity - scratch)
          afterSeparator =
        some atLedger := by
    have scanned := scratch_blanks_exact slot
      (scratchReserveState slot) (scratch_blank_step slot)
      (capacity - scratch)
      (ledgerBoundary ::
        (priorWord ++ slotBoundary :: selected ++ outerLeft))
      (unarySeparator ::
        List.replicate scratch unaryUnit ++
          sourceLeftBoundary :: sourceWord)
    simpa [afterSeparator, atLedger, scratchW, scratchWord,
      List.reverse_append, List.append_assoc] using scanned
  have hLedger :
      workRunExact? (machineFor slot) 1 atLedger =
        some afterLedger := by
    apply exactRun_one slot
    simpa [atLedger, afterLedger] using
      ledger_boundary_step slot
        (priorWord ++ slotBoundary :: selected ++ outerLeft)
        (scratchW.reverse ++ sourceLeftBoundary :: sourceWord)
  have priorLe : priorValues.length ≤ 5 := by
    rw [priorLength]
    exact slotCode_le_five slot
  have hPrior :
      workRunExact? (machineFor slot) priorWord.length
          afterLedger =
        some atSelectedBoundary := by
    have scanned := seekPrefix_exact slot capacity priorValues
      priorLe (slotBoundary :: selected ++ outerLeft)
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: sourceWord)
    simpa [afterLedger, atSelectedBoundary, priorWord,
      priorLength, List.append_assoc] using scanned
  have hSelectedBoundary :
      workRunExact? (machineFor slot) 1 atSelectedBoundary =
        some (selectedConfiguration capacity scratch 0 value
          priorWord outerLeft sourceWord) := by
    apply exactRun_one slot
    simpa [atSelectedBoundary, selectedConfiguration, selected,
      priorWord, scratchW, sourceWord, List.append_assoc] using
      seek_selected_boundary_step slot
        (selected ++ outerLeft)
        (priorWord.reverse ++ ledgerBoundary ::
          scratchW.reverse ++ sourceLeftBoundary :: sourceWord)
  have h01 := exactRun_add slot 1 1 _ _ _ hSource hBoundary
  have h02 := exactRun_add slot 2 scratch _ _ _ h01 hUnits
  have h03 := exactRun_add slot (2 + scratch) 1 _ _ _
    h02 hSeparator
  have h04 := exactRun_add slot (2 + scratch + 1)
    (capacity - scratch) _ _ _ h03 hBlanks
  have h05 := exactRun_add slot
    (2 + scratch + 1 + (capacity - scratch)) 1
    _ _ _ h04 hLedger
  have h06 := exactRun_add slot
    (2 + scratch + 1 + (capacity - scratch) + 1)
    priorWord.length _ _ _ h05 hPrior
  have complete := exactRun_add slot
    (2 + scratch + 1 + (capacity - scratch) + 1 +
      priorWord.length) 1 _ _ _ h06 hSelectedBoundary
  have steps :
      2 + scratch + 1 + (capacity - scratch) + 1 +
          priorWord.length + 1 =
        capacity + priorWord.length + 5 := by
    omega
  rw [steps] at complete
  simpa [priorWord] using complete

private theorem resume_to_selected_exact (slot : Slot)
    (capacity scratch processed remaining : Nat)
    (priorWord outerLeft : List WorkSymbol)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (scratchBound : scratch + (processed + 1) ≤ capacity)
    (priorAllowed :
      ∀ symbol, symbol ∈ priorWord → ledgerPayload symbol)
    (allowed : sourceAllowed sourceHead) :
    workRunExact? (machineFor slot)
        (capacity + priorWord.length + 6)
        (loopSourceConfiguration capacity scratch
          (processed + 1) remaining priorWord outerLeft
          (sourceHead :: sourceTail)) =
      some (selectedConfiguration capacity scratch
        (processed + 1) remaining priorWord outerLeft
        (sourceHead :: sourceTail)) := by
  let count := scratch + (processed + 1)
  let sourceWord := sourceHead :: sourceTail
  let scratchW := scratchWord capacity count
  let selected :=
    selectedPayload capacity (processed + 1) remaining
  let afterSource :=
    configAtLeftWord resumeBoundaryState
      (sourceLeftBoundary ::
        scratchW ++ ledgerBoundary ::
          (priorWord ++ slotBoundary :: selected ++ outerLeft))
      sourceWord
  let afterBoundary :=
    configAtLeftWord resumeScratchUnitsState
      (scratchW ++ ledgerBoundary ::
        (priorWord ++ slotBoundary :: selected ++ outerLeft))
      (sourceLeftBoundary :: sourceWord)
  let atSeparator :=
    configAtLeftWord resumeScratchUnitsState
      (unarySeparator ::
        List.replicate (capacity - count) WorkSymbol.blank ++
          ledgerBoundary ::
            (priorWord ++ slotBoundary :: selected ++ outerLeft))
      (List.replicate count unaryUnit ++
        sourceLeftBoundary :: sourceWord)
  let afterSeparator :=
    configAtLeftWord resumeScratchReserveState
      (List.replicate (capacity - count) WorkSymbol.blank ++
        ledgerBoundary ::
          (priorWord ++ slotBoundary :: selected ++ outerLeft))
      (unarySeparator ::
        List.replicate count unaryUnit ++
          sourceLeftBoundary :: sourceWord)
  let atLedger :=
    configAtLeftWord resumeScratchReserveState
      (ledgerBoundary ::
        (priorWord ++ slotBoundary :: selected ++ outerLeft))
      (scratchW.reverse ++ sourceLeftBoundary :: sourceWord)
  let afterLedger :=
    configAtLeftWord seekMarkState
      (priorWord ++ slotBoundary :: selected ++ outerLeft)
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: sourceWord)
  let atMark :=
    configAtLeftWord seekMarkState
      (selected ++ outerLeft)
      (slotBoundary :: priorWord.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: sourceWord)
  have hSource :
      workRunExact? (machineFor slot) 1
          (loopSourceConfiguration capacity scratch
            (processed + 1) remaining priorWord outerLeft sourceWord) =
        some afterSource := by
    apply exactRun_one slot
    simpa [loopSourceConfiguration, afterSource, count,
      scratchW, selected, sourceWord, List.append_assoc] using
      resume_source_step slot sourceHead allowed
        (sourceLeftBoundary ::
          scratchW ++ ledgerBoundary ::
            (priorWord ++ slotBoundary :: selected ++ outerLeft))
        sourceTail
  have hBoundary :
      workRunExact? (machineFor slot) 1 afterSource =
        some afterBoundary := by
    apply exactRun_one slot
    simpa [afterSource, afterBoundary] using
      resume_boundary_step slot
        (scratchW ++ ledgerBoundary ::
          (priorWord ++ slotBoundary :: selected ++ outerLeft))
        sourceWord
  have hUnits :
      workRunExact? (machineFor slot) count afterBoundary =
        some atSeparator := by
    simpa [afterBoundary, atSeparator, scratchW, scratchWord,
      List.append_assoc] using
      scratch_units_exact slot resumeScratchUnitsState
        (resume_scratch_unit_step slot) count
        (unarySeparator ::
          List.replicate (capacity - count) WorkSymbol.blank ++
            ledgerBoundary ::
              (priorWord ++ slotBoundary :: selected ++ outerLeft))
        (sourceLeftBoundary :: sourceWord)
  have hSeparator :
      workRunExact? (machineFor slot) 1 atSeparator =
        some afterSeparator := by
    apply exactRun_one slot
    simpa [atSeparator, afterSeparator] using
      resume_scratch_separator_step slot
        (List.replicate (capacity - count) WorkSymbol.blank ++
          ledgerBoundary ::
            (priorWord ++ slotBoundary :: selected ++ outerLeft))
        (List.replicate count unaryUnit ++
          sourceLeftBoundary :: sourceWord)
  have hBlanks :
      workRunExact? (machineFor slot) (capacity - count)
          afterSeparator =
        some atLedger := by
    have scanned := scratch_blanks_exact slot
      resumeScratchReserveState (resume_scratch_blank_step slot)
      (capacity - count)
      (ledgerBoundary ::
        (priorWord ++ slotBoundary :: selected ++ outerLeft))
      (unarySeparator ::
        List.replicate count unaryUnit ++
          sourceLeftBoundary :: sourceWord)
    simpa [afterSeparator, atLedger, scratchW, scratchWord,
      List.reverse_append, List.append_assoc] using scanned
  have hLedger :
      workRunExact? (machineFor slot) 1 atLedger =
        some afterLedger := by
    apply exactRun_one slot
    simpa [atLedger, afterLedger] using
      resume_ledger_boundary_step slot
        (priorWord ++ slotBoundary :: selected ++ outerLeft)
        (scratchW.reverse ++ sourceLeftBoundary :: sourceWord)
  let seekWord := priorWord ++ [slotBoundary]
  have seekAllowed :
      ∀ symbol, symbol ∈ seekWord → ledgerPayload symbol := by
    intro symbol found
    rw [List.mem_append] at found
    rcases found with inPrior | inBoundary
    · exact priorAllowed symbol inPrior
    · have equality := List.eq_of_mem_singleton inBoundary
      subst symbol
      exact Or.inr (Or.inr (Or.inr rfl))
  have hSeek :
      workRunExact? (machineFor slot) seekWord.length afterLedger =
        some atMark := by
    have scanned := scanSeekMarkExact slot seekWord seekAllowed
      (selected ++ outerLeft)
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: sourceWord)
    simpa [afterLedger, atMark, seekWord,
      List.reverse_append, List.append_assoc] using scanned
  have hMark :
      workRunExact? (machineFor slot) 1 atMark =
        some (selectedConfiguration capacity scratch
          (processed + 1) remaining priorWord outerLeft sourceWord) := by
    apply exactRun_one slot
    have step := seek_mark_step slot
      (List.replicate processed unitMark ++
        List.replicate remaining unaryUnit ++
          unarySeparator ::
            List.replicate
              (capacity - ((processed + 1) + remaining))
              WorkSymbol.blank ++ outerLeft)
      (slotBoundary :: priorWord.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: sourceWord)
    simpa [atMark, selectedConfiguration, selected,
      selectedPayload, scratchW, count, sourceWord,
      List.replicate_succ, List.append_assoc] using step
  have h01 := exactRun_add slot 1 1 _ _ _ hSource hBoundary
  have h02 := exactRun_add slot 2 count _ _ _ h01 hUnits
  have h03 := exactRun_add slot (2 + count) 1 _ _ _
    h02 hSeparator
  have h04 := exactRun_add slot (2 + count + 1)
    (capacity - count) _ _ _ h03 hBlanks
  have h05 := exactRun_add slot
    (2 + count + 1 + (capacity - count)) 1
    _ _ _ h04 hLedger
  have h06 := exactRun_add slot
    (2 + count + 1 + (capacity - count) + 1)
    seekWord.length _ _ _ h05 hSeek
  have complete := exactRun_add slot
    (2 + count + 1 + (capacity - count) + 1 +
      seekWord.length) 1 _ _ _ h06 hMark
  have steps :
      2 + count + 1 + (capacity - count) + 1 +
          seekWord.length + 1 =
        capacity + priorWord.length + 6 := by
    simp [seekWord]
    omega
  rw [steps] at complete
  exact complete

private theorem restore_marks_exact (slot : Slot)
    (count : Nat) (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) count
        (configAtWord restoreState left
          (List.replicate count unitMark ++ right)) =
      some (configAtWord restoreState
        (List.replicate count unaryUnit ++ left) right) := by
  induction count generalizing left with
  | zero =>
      rfl
  | succ count ih =>
      change
        (match workStep? (machineFor slot)
          (configAtWord restoreState left
            (unitMark :: List.replicate count unitMark ++ right)) with
         | none => none
         | some next =>
             workRunExact? (machineFor slot) count next) = _
      simp only [List.cons_append]
      rw [restore_mark_step slot left
        (List.replicate count unitMark ++ right)]
      simpa [replicate_succ_append, List.append_assoc] using
        ih (unaryUnit :: left)

private theorem finish_exact (slot : Slot)
    (capacity scratch processed : Nat)
    (priorWord outerLeft : List WorkSymbol)
    (sourceWord : List WorkSymbol)
    (scratchBound : scratch + processed ≤ capacity)
    (priorAllowed :
      ∀ symbol, symbol ∈ priorWord → ledgerPayload symbol) :
    workRunExact? (machineFor slot)
        (capacity + priorWord.length + 2 * processed + 5)
        (selectedConfiguration capacity scratch processed 0
          priorWord outerLeft sourceWord) =
      some (coreFinalConfiguration capacity scratch processed
        priorWord outerLeft sourceWord) := by
  let scratchW := scratchWord capacity (scratch + processed)
  let reserve :=
    List.replicate (capacity - processed) WorkSymbol.blank
  let rightContext :=
    slotBoundary :: priorWord.reverse ++ ledgerBoundary ::
      scratchW.reverse ++ sourceLeftBoundary :: sourceWord
  let atSeparator :=
    configAtLeftWord selectedState
      (unarySeparator :: reserve ++ outerLeft)
      (List.replicate processed unitMark ++ rightContext)
  let restoring :=
    configAtWord restoreState
      (unarySeparator :: reserve ++ outerLeft)
      (List.replicate processed unitMark ++ rightContext)
  let atSlotBoundary :=
    configAtWord restoreState
      (List.replicate processed unaryUnit ++
        unarySeparator :: reserve ++ outerLeft)
      rightContext
  let atPrior :=
    configAtWord finalLedgerState
      (slotBoundary ::
        List.replicate processed unaryUnit ++
          unarySeparator :: reserve ++ outerLeft)
      (priorWord.reverse ++ ledgerBoundary ::
        scratchW.reverse ++ sourceLeftBoundary :: sourceWord)
  let atLedger :=
    configAtWord finalLedgerState
      (priorWord ++ slotBoundary ::
        List.replicate processed unaryUnit ++
          unarySeparator :: reserve ++ outerLeft)
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: sourceWord)
  let atScratch :=
    configAtWord finalScratchState
      (ledgerBoundary :: priorWord ++ slotBoundary ::
        List.replicate processed unaryUnit ++
          unarySeparator :: reserve ++ outerLeft)
      (scratchW.reverse ++ sourceLeftBoundary :: sourceWord)
  let atSourceBoundary :=
    configAtWord finalScratchState
      (scratchW ++ ledgerBoundary :: priorWord ++ slotBoundary ::
        List.replicate processed unaryUnit ++
          unarySeparator :: reserve ++ outerLeft)
      (sourceLeftBoundary :: sourceWord)
  have hMarks :
      workRunExact? (machineFor slot) processed
          (selectedConfiguration capacity scratch processed 0
            priorWord outerLeft sourceWord) =
        some atSeparator := by
    have scanned := selected_marks_exact slot processed
      (unarySeparator ::
        List.replicate (capacity - processed) WorkSymbol.blank ++
          outerLeft)
      rightContext
    simpa [selectedConfiguration, selectedPayload, atSeparator,
      rightContext, reserve, scratchW, List.append_assoc] using scanned
  have hSeparator :
      workRunExact? (machineFor slot) 1 atSeparator =
        some restoring := by
    apply exactRun_one slot
    simpa [atSeparator, restoring] using
      selected_separator_step slot
        (reserve ++ outerLeft)
        (List.replicate processed unitMark ++ rightContext)
  have hRestore :
      workRunExact? (machineFor slot) processed restoring =
        some atSlotBoundary := by
    simpa [restoring, atSlotBoundary, rightContext] using
      restore_marks_exact slot processed
        (unarySeparator :: reserve ++ outerLeft)
        rightContext
  have hSlotBoundary :
      workRunExact? (machineFor slot) 1 atSlotBoundary =
        some atPrior := by
    apply exactRun_one slot
    simpa [atSlotBoundary, atPrior, rightContext] using
      restore_boundary_step slot
        (List.replicate processed unaryUnit ++
          unarySeparator :: reserve ++ outerLeft)
        (priorWord.reverse ++ ledgerBoundary ::
          scratchW.reverse ++ sourceLeftBoundary :: sourceWord)
  have hPrior :
      workRunExact? (machineFor slot) priorWord.length atPrior =
        some atLedger := by
    have reversedAllowed :
        ∀ symbol, symbol ∈ priorWord.reverse →
          ledgerPayload symbol := by
      intro symbol found
      exact priorAllowed symbol (List.mem_reverse.mp found)
    have scanned := scanFinalLedgerExact slot priorWord.reverse
      reversedAllowed
      (slotBoundary ::
        List.replicate processed unaryUnit ++
          unarySeparator :: reserve ++ outerLeft)
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: sourceWord)
    simpa [atPrior, atLedger, List.append_assoc] using scanned
  have hLedger :
      workRunExact? (machineFor slot) 1 atLedger =
        some atScratch := by
    apply exactRun_one slot
    simpa [atLedger, atScratch] using
      final_ledger_boundary_step slot
        (priorWord ++ slotBoundary ::
          List.replicate processed unaryUnit ++
            unarySeparator :: reserve ++ outerLeft)
        (scratchW.reverse ++ sourceLeftBoundary :: sourceWord)
  have hScratch :
      workRunExact? (machineFor slot) scratchW.length atScratch =
        some atSourceBoundary := by
    simpa [atScratch, atSourceBoundary, scratchW] using
      scanFinalScratchExact slot capacity (scratch + processed)
        (ledgerBoundary :: priorWord ++ slotBoundary ::
          List.replicate processed unaryUnit ++
            unarySeparator :: reserve ++ outerLeft)
        (sourceLeftBoundary :: sourceWord)
  have hBoundary :
      workRunExact? (machineFor slot) 1 atSourceBoundary =
        some (coreFinalConfiguration capacity scratch processed
          priorWord outerLeft sourceWord) := by
    apply exactRun_one slot
    simpa [atSourceBoundary, coreFinalConfiguration, reserve,
      scratchW, slotPayload, List.append_assoc] using
      final_source_boundary_step slot
        (scratchW ++ ledgerBoundary :: priorWord ++ slotBoundary ::
          List.replicate processed unaryUnit ++
            unarySeparator :: reserve ++ outerLeft)
        sourceWord
  have h01 := exactRun_add slot processed 1 _ _ _
    hMarks hSeparator
  have h02 := exactRun_add slot (processed + 1) processed
    _ _ _ h01 hRestore
  have h03 := exactRun_add slot
    (processed + 1 + processed) 1 _ _ _ h02 hSlotBoundary
  have h04 := exactRun_add slot
    (processed + 1 + processed + 1) priorWord.length
    _ _ _ h03 hPrior
  have h05 := exactRun_add slot
    (processed + 1 + processed + 1 + priorWord.length) 1
    _ _ _ h04 hLedger
  have h06 := exactRun_add slot
    (processed + 1 + processed + 1 + priorWord.length + 1)
    scratchW.length _ _ _ h05 hScratch
  have complete := exactRun_add slot
    (processed + 1 + processed + 1 + priorWord.length + 1 +
      scratchW.length) 1 _ _ _ h06 hBoundary
  have scratchLength :
      scratchW.length = capacity + 1 := by
    exact scratchWord_length_of_le capacity (scratch + processed)
      scratchBound
  have steps :
      processed + 1 + processed + 1 + priorWord.length + 1 +
          scratchW.length + 1 =
        capacity + priorWord.length + 2 * processed + 5 := by
    rw [scratchLength]
    omega
  rw [steps] at complete
  exact complete

private theorem cycle_exact (slot : Slot)
    (capacity scratch processed remaining : Nat)
    (priorWord outerLeft : List WorkSymbol)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (enough :
      scratch + (processed + (remaining + 1)) ≤ capacity)
    (priorAllowed :
      ∀ symbol, symbol ∈ priorWord → ledgerPayload symbol)
    (allowed : sourceAllowed sourceHead) :
    workRunExact? (machineFor slot)
        (2 * capacity + 2 * priorWord.length + 2 * scratch +
          4 * processed + 17)
        (selectedConfiguration capacity scratch processed
          (remaining + 1) priorWord outerLeft
          (sourceHead :: sourceTail)) =
      some (selectedConfiguration capacity scratch
        (processed + 1) remaining priorWord outerLeft
        (sourceHead :: sourceTail)) := by
  let count := scratch + processed
  let sourceWord := sourceHead :: sourceTail
  let scratchW := scratchWord capacity count
  let reserve :=
    List.replicate
      (capacity - (processed + (remaining + 1)))
      WorkSymbol.blank
  let unitTail :=
    List.replicate remaining unaryUnit ++
      unarySeparator :: reserve ++ outerLeft
  let rightContext :=
    slotBoundary :: priorWord.reverse ++ ledgerBoundary ::
      scratchW.reverse ++ sourceLeftBoundary :: sourceWord
  let atUnit :=
    configAtLeftWord selectedState
      (unaryUnit :: unitTail)
      (List.replicate processed unitMark ++ rightContext)
  let bouncing :=
    configAtWord bounceLedgerState
      (unitMark :: unitTail)
      (List.replicate processed unitMark ++ rightContext)
  let bounceWord :=
    List.replicate processed unitMark ++
      slotBoundary :: priorWord.reverse
  let atLedger :=
    configAtWord bounceLedgerState
      (priorWord ++ slotBoundary ::
        List.replicate (processed + 1) unitMark ++ unitTail)
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: sourceWord)
  let atScratch :=
    configAtWord bounceScratchState
      (ledgerBoundary :: priorWord ++ slotBoundary ::
        List.replicate (processed + 1) unitMark ++ unitTail)
      (scratchW.reverse ++ sourceLeftBoundary :: sourceWord)
  let atSourceBoundary :=
    configAtWord bounceScratchState
      (scratchW ++ ledgerBoundary :: priorWord ++ slotBoundary ::
        List.replicate (processed + 1) unitMark ++ unitTail)
      (sourceLeftBoundary :: sourceWord)
  let atIncrement :=
    configAtWord incrementStartState
      (sourceLeftBoundary :: scratchW ++ ledgerBoundary ::
        priorWord ++ slotBoundary ::
          List.replicate (processed + 1) unitMark ++ unitTail)
      sourceWord
  have hMarks :
      workRunExact? (machineFor slot) processed
          (selectedConfiguration capacity scratch processed
            (remaining + 1) priorWord outerLeft sourceWord) =
        some atUnit := by
    have scanned := selected_marks_exact slot processed
      (unaryUnit :: unitTail) rightContext
    simpa [selectedConfiguration, selectedPayload, atUnit,
      unitTail, rightContext, reserve, scratchW, count,
      sourceWord, List.replicate_succ, List.append_assoc] using scanned
  have hUnit :
      workRunExact? (machineFor slot) 1 atUnit =
        some bouncing := by
    apply exactRun_one slot
    simpa [atUnit, bouncing] using
      selected_unit_step slot unitTail
        (List.replicate processed unitMark ++ rightContext)
  have bounceAllowed :
      ∀ symbol, symbol ∈ bounceWord →
        symbol = unitMark ∨ ledgerPayload symbol := by
    intro symbol found
    unfold bounceWord at found
    rw [List.mem_append] at found
    rcases found with inMarks | inRest
    · exact Or.inl (List.eq_of_mem_replicate inMarks)
    · cases inRest with
      | head =>
          exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      | tail _ inPriorReverse =>
          exact Or.inr
            (priorAllowed symbol
              (List.mem_reverse.mp inPriorReverse))
  have hBounce :
      workRunExact? (machineFor slot) bounceWord.length bouncing =
        some atLedger := by
    have scanned := scanBounceLedgerExact slot bounceWord
      bounceAllowed (unitMark :: unitTail)
      (ledgerBoundary :: scratchW.reverse ++
        sourceLeftBoundary :: sourceWord)
    simpa [bouncing, atLedger, bounceWord, rightContext,
      List.reverse_append, replicate_succ_append,
      List.append_assoc] using scanned
  have hLedger :
      workRunExact? (machineFor slot) 1 atLedger =
        some atScratch := by
    apply exactRun_one slot
    simpa [atLedger, atScratch] using
      bounce_ledger_boundary_step slot
        (priorWord ++ slotBoundary ::
          List.replicate (processed + 1) unitMark ++ unitTail)
        (scratchW.reverse ++ sourceLeftBoundary :: sourceWord)
  have hScratch :
      workRunExact? (machineFor slot) scratchW.length atScratch =
        some atSourceBoundary := by
    simpa [atScratch, atSourceBoundary, scratchW] using
      scanBounceScratchExact slot capacity count
        (ledgerBoundary :: priorWord ++ slotBoundary ::
          List.replicate (processed + 1) unitMark ++ unitTail)
        (sourceLeftBoundary :: sourceWord)
  have hSourceBoundary :
      workRunExact? (machineFor slot) 1 atSourceBoundary =
        some atIncrement := by
    apply exactRun_one slot
    simpa [atSourceBoundary, atIncrement] using
      bounce_source_boundary_step slot
        (scratchW ++ ledgerBoundary :: priorWord ++ slotBoundary ::
          List.replicate (processed + 1) unitMark ++ unitTail)
        sourceWord
  have nextBound :
      count + 1 ≤ capacity := by
    unfold count
    omega
  have reserveEquality :
      capacity - count =
        capacity - (count + 1) + 1 := by
    omega
  have scratchProcessed :
      scratch + (processed + 1) = count + 1 := by
    unfold count
    omega
  have processedRemaining :
      (processed + 1) + remaining =
        processed + (remaining + 1) := by
    omega
  let ledgerAndOutside :=
    ledgerBoundary :: priorWord ++ slotBoundary ::
      List.replicate (processed + 1) unitMark ++ unitTail
  have hIncrement :
      workRunExact? (machineFor slot) (2 * count + 6)
          atIncrement =
        some (loopSourceConfiguration capacity scratch
          (processed + 1) remaining priorWord outerLeft sourceWord) := by
    have incremented := increment_exact slot count
      (List.replicate (capacity - (count + 1))
        WorkSymbol.blank)
      ledgerAndOutside sourceTail sourceHead allowed
    simpa [atIncrement, loopSourceConfiguration, scratchW,
      scratchWord, selectedPayload, count, sourceWord,
      ledgerAndOutside, unitTail, reserve, reserveEquality, scratchProcessed,
      processedRemaining, List.replicate_succ,
      List.append_assoc] using incremented
  have hResume :=
    resume_to_selected_exact slot capacity scratch processed
      remaining priorWord outerLeft sourceHead sourceTail
      nextBound priorAllowed allowed
  have h01 := exactRun_add slot processed 1 _ _ _ hMarks hUnit
  have h02 := exactRun_add slot (processed + 1)
    bounceWord.length _ _ _ h01 hBounce
  have h03 := exactRun_add slot
    (processed + 1 + bounceWord.length) 1 _ _ _ h02 hLedger
  have h04 := exactRun_add slot
    (processed + 1 + bounceWord.length + 1)
    scratchW.length _ _ _ h03 hScratch
  have h05 := exactRun_add slot
    (processed + 1 + bounceWord.length + 1 +
      scratchW.length) 1 _ _ _ h04 hSourceBoundary
  have h06 := exactRun_add slot
    (processed + 1 + bounceWord.length + 1 +
      scratchW.length + 1) (2 * count + 6)
    _ _ _ h05 hIncrement
  have complete := exactRun_add slot
    (processed + 1 + bounceWord.length + 1 +
      scratchW.length + 1 + (2 * count + 6))
    (capacity + priorWord.length + 6)
    _ _ _ h06 hResume
  have bounceLength :
      bounceWord.length = processed + priorWord.length + 1 := by
    simp [bounceWord]
    omega
  have scratchLength :
      scratchW.length = capacity + 1 := by
    exact scratchWord_length_of_le capacity count (by
      exact Nat.le_trans (Nat.le_add_right count 1) nextBound)
  have steps :
      processed + 1 + bounceWord.length + 1 +
          scratchW.length + 1 + (2 * count + 6) +
          (capacity + priorWord.length + 6) =
        2 * capacity + 2 * priorWord.length + 2 * scratch +
          4 * processed + 17 := by
    rw [bounceLength, scratchLength]
    unfold count
    omega
  rw [steps] at complete
  exact complete

/-! ### Whole selected-slot trace -/

private def processSteps (capacity scratch priorLength processed : Nat) :
    Nat → Nat
  | 0 =>
      capacity + priorLength + 2 * processed + 5
  | remaining + 1 =>
      2 * capacity + 2 * priorLength + 2 * scratch +
          4 * processed + 17 +
        processSteps capacity scratch priorLength
          (processed + 1) remaining

private theorem processSteps_evaluated
    (capacity scratch priorLength processed remaining : Nat) :
    processSteps capacity scratch priorLength processed remaining =
      remaining *
          (2 * capacity + 2 * priorLength + 2 * scratch +
            4 * processed + 17) +
        2 * remaining * remaining +
        capacity + priorLength + 2 * processed + 5 := by
  induction remaining generalizing processed with
  | zero =>
      simp [processSteps]
  | succ remaining ih =>
      simp only [processSteps]
      rw [ih (processed + 1)]
      simp only [Nat.succ_mul, Nat.mul_succ, Nat.mul_add,
        Nat.add_mul]
      omega

private theorem process_exact (slot : Slot)
    (capacity scratch processed remaining : Nat)
    (priorWord outerLeft : List WorkSymbol)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (enough : scratch + (processed + remaining) ≤ capacity)
    (priorAllowed :
      ∀ symbol, symbol ∈ priorWord → ledgerPayload symbol)
    (allowed : sourceAllowed sourceHead) :
    workRunExact? (machineFor slot)
        (processSteps capacity scratch priorWord.length
          processed remaining)
        (selectedConfiguration capacity scratch processed remaining
          priorWord outerLeft (sourceHead :: sourceTail)) =
      some (coreFinalConfiguration capacity scratch
        (processed + remaining) priorWord outerLeft
        (sourceHead :: sourceTail)) := by
  induction remaining generalizing processed with
  | zero =>
      simpa [processSteps] using
        finish_exact slot capacity scratch processed
          priorWord outerLeft (sourceHead :: sourceTail)
          enough priorAllowed
  | succ remaining ih =>
      have nextEnough :
          scratch + ((processed + 1) + remaining) ≤ capacity := by
        omega
      have hCycle :=
        cycle_exact slot capacity scratch processed remaining
          priorWord outerLeft sourceHead sourceTail enough
          priorAllowed allowed
      have hRest :=
        ih (processed + 1) nextEnough
      have complete := exactRun_add slot
        (2 * capacity + 2 * priorWord.length + 2 * scratch +
          4 * processed + 17)
        (processSteps capacity scratch priorWord.length
          (processed + 1) remaining)
        _ _ _ hCycle hRest
      have total :
          (processed + 1) + remaining =
            processed + (remaining + 1) := by
        omega
      simpa [processSteps, total] using complete

private theorem core_exact (slot : Slot)
    (capacity scratch value : Nat)
    (priorValues : List Nat) (outerLeft : List WorkSymbol)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (priorLength : priorValues.length = slotCode slot)
    (enough : scratch + value ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    workRunExact? (machineFor slot)
        (2 * capacity +
          2 * (valuesWord capacity priorValues).length + 10 +
          value *
            (2 * capacity +
              2 * (valuesWord capacity priorValues).length +
              2 * scratch + 17) +
          2 * value * value)
        (coreEntryConfiguration slot capacity scratch value
          priorValues outerLeft sourceHead sourceTail) =
      some (coreFinalConfiguration capacity scratch value
        (valuesWord capacity priorValues) outerLeft
        (sourceHead :: sourceTail)) := by
  have scratchBound : scratch ≤ capacity := by
    omega
  have hInitial :=
    initial_to_selected_exact slot capacity scratch value
      priorValues outerLeft sourceHead sourceTail
      priorLength scratchBound allowed
  have hProcess :=
    process_exact slot capacity scratch 0 value
      (valuesWord capacity priorValues) outerLeft
      sourceHead sourceTail (by simpa using enough)
      (valuesWord_allowed capacity priorValues) allowed
  have complete := exactRun_add slot
    (capacity + (valuesWord capacity priorValues).length + 5)
    (processSteps capacity scratch
      (valuesWord capacity priorValues).length 0 value)
    _ _ _ hInitial hProcess
  have evaluated :=
    processSteps_evaluated capacity scratch
      (valuesWord capacity priorValues).length 0 value
  have steps :
      capacity + (valuesWord capacity priorValues).length + 5 +
          processSteps capacity scratch
            (valuesWord capacity priorValues).length 0 value =
        2 * capacity +
          2 * (valuesWord capacity priorValues).length + 10 +
          value *
            (2 * capacity +
              2 * (valuesWord capacity priorValues).length +
              2 * scratch + 17) +
          2 * value * value := by
    rw [evaluated]
    simp only [Nat.mul_zero, Nat.add_zero]
    omega
  rw [steps] at complete
  simpa using complete

/-! ### Public exact endpoint -/

/-- Exact bounded execution of the literal six-mode controller.  The
selected slot value is added to scratch, every ledger cell and the retained
source are restored byte-for-byte, and the source head is retained. -/
theorem exact (slot : Slot) (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (enough :
      scratch + selectedValue slot registers ≤ capacity)
    (allowed : sourceAllowed sourceHead) :
    workRunExact? (machineFor slot)
        (workSteps slot capacity scratch
          (selectedValue slot registers))
        (entryConfiguration slot capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) =
      some (finalConfiguration slot capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft) := by
  let priorValues := prefixValues slot registers
  let priorWord := prefixWord capacity slot registers
  let outerLeft :=
    suffixWord capacity slot registers ++ outsideLeft
  let value := selectedValue slot registers
  have core := core_exact slot capacity scratch value
    priorValues outerLeft sourceHead
    (sourceTail ++ targetAndRight)
    (prefixValues_length slot registers) enough allowed
  have priorWordEq :
      valuesWord capacity priorValues = priorWord := by
    rfl
  have entryEq :
      coreEntryConfiguration slot capacity scratch value
          priorValues outerLeft sourceHead
          (sourceTail ++ targetAndRight) =
        entryConfiguration slot capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft := by
    unfold coreEntryConfiguration entryConfiguration
    rw [slotBank_decompose capacity slot registers]
    simp [priorValues, outerLeft, value, prefixWord,
      slotWord_eq, selectedPayload, slotPayload,
      List.append_assoc]
  have finalEq :
      coreFinalConfiguration capacity scratch value priorWord
          outerLeft
          (sourceHead :: (sourceTail ++ targetAndRight)) =
        finalConfiguration slot capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft := by
    unfold coreFinalConfiguration finalConfiguration
    rw [slotBank_decompose capacity slot registers]
    simp [priorWord, outerLeft, value, prefixWord,
      slotWord_eq, List.append_assoc]
  have stepsEq :
      2 * capacity +
          2 * (valuesWord capacity priorValues).length + 10 +
          value *
            (2 * capacity +
              2 * (valuesWord capacity priorValues).length +
              2 * scratch + 17) +
          2 * value * value =
        workSteps slot capacity scratch
          (selectedValue slot registers) := by
    rw [priorWordEq,
      prefixWord_length capacity slot registers fits]
    rfl
  rw [stepsEq, entryEq, priorWordEq] at core
  rw [finalEq] at core
  exact core

theorem final_halted (slot : Slot) (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    (machineFor slot).isHalted
      (finalConfiguration slot capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft) = true := by
  rfl

theorem final_source_preserved (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    let final :=
      finalConfiguration slot capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft
    final.tape.head :: final.tape.right =
      sourceHead :: sourceTail ++ targetAndRight := by
  rfl

theorem final_left_workspace (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    (finalConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft).tape.left =
        sourceLeftBoundary ::
          (scratchWord capacity
              (scratch + selectedValue slot registers) ++
            ledgerBoundary ::
              (TargetEmitterLedger.slotBank capacity registers ++
                outsideLeft)) := by
  rfl

/-! ### Polynomial bound -/

def polynomialWorkBound (capacity scratch value : Nat) : Nat :=
  12 * capacity + 30 +
    value * (12 * capacity + 2 * scratch + 37) +
    2 * value * value

theorem workSteps_le_polynomialWorkBound (slot : Slot)
    (capacity scratch value : Nat) :
    workSteps slot capacity scratch value ≤
      polynomialWorkBound capacity scratch value := by
  have priorLe :
      slotCode slot * (capacity + 2) ≤
        5 * (capacity + 2) :=
    Nat.mul_le_mul_right (capacity + 2) (slotCode_le_five slot)
  have fixedLe :
      2 * capacity +
          2 * (slotCode slot * (capacity + 2)) + 10 ≤
        12 * capacity + 30 := by
    omega
  have cycleLe :
      2 * capacity +
          2 * (slotCode slot * (capacity + 2)) +
          2 * scratch + 17 ≤
        12 * capacity + 2 * scratch + 37 := by
    omega
  have multipliedLe :=
    Nat.mul_le_mul_left value cycleLe
  change
    2 * capacity +
          2 * (slotCode slot * (capacity + 2)) + 10 +
          value *
            (2 * capacity +
              2 * (slotCode slot * (capacity + 2)) +
              2 * scratch + 17) +
          2 * value * value ≤
      12 * capacity + 30 +
          value * (12 * capacity + 2 * scratch + 37) +
          2 * value * value
  omega

/-! ### Fail-closed malformed layouts and exhausted capacity -/

set_option maxRecDepth 300000 in
private theorem find_selected_malformed
    (symbol : WorkSymbol)
    (notMark : symbol ≠ unitMark)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    findWorkRule rules selectedState symbol =
      some (literalRule selectedState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · decide
  · decide
  · decide
  · exact (notUnit rfl).elim
  · exact (notMark rfl).elim
  · decide
  · exact (notSeparator rfl).elim
  all_goals decide

set_option maxRecDepth 300000 in
private theorem find_increment_occupied
    (symbol : WorkSymbol)
    (occupied : symbol ≠ WorkSymbol.blank) :
    findWorkRule rules incrementWriteState symbol =
      some (literalRule incrementWriteState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · exact (occupied rfl).elim
  all_goals decide

set_option maxRecDepth 300000 in
private theorem find_bounce_scratch_malformed
    (symbol : WorkSymbol)
    (notBlank : symbol ≠ WorkSymbol.blank)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator)
    (notBoundary : symbol ≠ sourceLeftBoundary) :
    findWorkRule rules bounceScratchState symbol =
      some (literalRule bounceScratchState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · exact (notBlank rfl).elim
  · exact (notBoundary rfl).elim
  · decide
  · exact (notUnit rfl).elim
  · decide
  · decide
  · exact (notSeparator rfl).elim
  all_goals decide

private theorem left_dead_step (slot : Slot)
    (state : Nat) (symbol : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      (machineFor slot).isHalted
        (configAtLeftWord state (symbol :: left) right) = false)
    (found :
      findWorkRule rules state symbol =
        some (literalRule state symbol
          deadState symbol .stay)) :
    workStep? (machineFor slot)
        (configAtLeftWord state (symbol :: left) right) =
      some (configAtLeftWord deadState
        (symbol :: left) right) := by
  calc
    workStep? (machineFor slot)
        (configAtLeftWord state (symbol :: left) right) =
      some (applyWorkRule
        (literalRule state symbol deadState symbol .stay)
        (configAtLeftWord state (symbol :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some (configAtLeftWord deadState
        (symbol :: left) right) := by
      rfl

private theorem right_dead_step (slot : Slot)
    (state : Nat) (symbol : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      (machineFor slot).isHalted
        (configAtWord state left (symbol :: right)) = false)
    (found :
      findWorkRule rules state symbol =
        some (literalRule state symbol
          deadState symbol .stay)) :
    workStep? (machineFor slot)
        (configAtWord state left (symbol :: right)) =
      some (configAtWord deadState left
        (symbol :: right)) := by
  calc
    workStep? (machineFor slot)
        (configAtWord state left (symbol :: right)) =
      some (applyWorkRule
        (literalRule state symbol deadState symbol .stay)
        (configAtWord state left (symbol :: right))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some (configAtWord deadState left
        (symbol :: right)) := by
      rfl

/-- A selected slot may contain only contextual marks, unary units, and its
separator.  Any other observed symbol enters the ruleless dead state without
changing the tape. -/
theorem malformed_selected_enters_dead (slot : Slot)
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notMark : symbol ≠ unitMark)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    workStep? (machineFor slot)
        (configAtLeftWord selectedState
          (symbol :: left) right) =
      some (configAtLeftWord deadState
        (symbol :: left) right) := by
  exact left_dead_step slot selectedState symbol left right
    (by rfl)
    (find_selected_malformed symbol notMark notUnit notSeparator)

/-- Scratch capacity is fail-closed.  The literal increment writes its new
separator only over a blank; an occupied cell is observed but preserved. -/
theorem exhausted_scratch_enters_dead (slot : Slot)
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (occupied : symbol ≠ WorkSymbol.blank) :
    workStep? (machineFor slot)
        (configAtLeftWord incrementWriteState
          (symbol :: left) right) =
      some (configAtLeftWord deadState
        (symbol :: left) right) := by
  exact left_dead_step slot incrementWriteState
    symbol left right (by rfl)
    (find_increment_occupied symbol occupied)

/-- The bounce through scratch accepts only its three unary symbols and the
source-left boundary.  A misplaced ledger or packed symbol fails closed. -/
theorem malformed_scratch_bounce_enters_dead (slot : Slot)
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notBlank : symbol ≠ WorkSymbol.blank)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator)
    (notBoundary : symbol ≠ sourceLeftBoundary) :
    workStep? (machineFor slot)
        (configAtWord bounceScratchState left
          (symbol :: right)) =
      some (configAtWord deadState left
        (symbol :: right)) := by
  exact right_dead_step slot bounceScratchState
    symbol left right (by rfl)
    (find_bounce_scratch_malformed symbol notBlank notUnit
      notSeparator notBoundary)

theorem dead_configuration_not_halted
    (slot : Slot) (tape : WorkTape) :
    (machineFor slot).isHalted
      { state := deadState, tape := tape } = false := by
  rfl

theorem dead_stuck (slot : Slot) (tape : WorkTape) :
    workStep? (machineFor slot)
      { state := deadState, tape := tape } = none := by
  have notHalted :=
    dead_configuration_not_halted slot tape
  unfold workStep?
  rw [notHalted]
  change
    (match findWorkRule rules deadState tape.head with
     | none => none
     | some rule =>
         some (applyWorkRule rule
           { state := deadState, tape := tape })) = none
  rw [no_rule_at_dead]

end PNP.Concrete.LockedNAND.TargetEmitterScratchAddSlot
