/-
Copyright (c) 2026 PNP Labs.

Literal comparison of the nearest unary scratch register with one selected
fixed ledger slot.

The machine pairs scratch units with selected-slot units using two contextual
marks, restores both records, and halts at distinct equality and strict-less
endpoints.  The emitter uses the baseline specialization to control its final
output loop.  No transition contains a capacity, register value, decoded
circuit, target word, or host-side branch lookup.
-/

import PNP.Concrete.LockedNANDTargetEmitterScratchAddSlot

namespace PNP.Concrete.LockedNAND.TargetEmitterScratchCompareSlot

open PNP.Concrete

abbrev Slot := TargetEmitterLedger.Slot

def allSlots : List Slot :=
  TargetEmitterLedger.Slot.all

def slotCode (slot : Slot) : Nat :=
  TargetEmitterLedger.Slot.index slot

def startState (slot : Slot) : Nat := 5000 + slotCode slot
def scratchState (slot : Slot) : Nat := 5010 + slotCode slot
def seekLedgerState (slot : Slot) : Nat := 5020 + slotCode slot
def compareSeekLedgerState (slot : Slot) : Nat :=
  5030 + slotCode slot
def pairSeekSlotState (slot : Slot) (remaining : Nat) : Nat :=
  5040 + 6 * slotCode slot + remaining
def selectedState (slot : Slot) : Nat := 5080 + slotCode slot
def returnLedgerState (slot : Slot) : Nat := 5090 + slotCode slot
def returnScratchState (slot : Slot) : Nat := 5100 + slotCode slot
def compareSeekSlotState (slot : Slot) (remaining : Nat) : Nat :=
  5110 + 6 * slotCode slot + remaining
def compareSelectedState (slot : Slot) : Nat :=
  5150 + slotCode slot
def restoreEqualLedgerState : Nat := 5160
def restoreLessLedgerState : Nat := 5161
def restoreEqualScratchState : Nat := 5162
def restoreLessScratchState : Nat := 5163
def acceptState : Nat := 5164
def rejectState : Nat := 5165
def deadState : Nat := 5166

def unaryUnit : WorkSymbol := TargetEmitterLedger.unaryUnit
def unarySeparator : WorkSymbol :=
  TargetEmitterLedger.unarySeparator
def sourceLeftBoundary : WorkSymbol :=
  TargetEmitterLedger.sourceLeftBoundary
def ledgerBoundary : WorkSymbol :=
  TargetEmitterLedger.ledgerBoundary
def slotBoundary : WorkSymbol :=
  TargetEmitterLedger.slotBoundary
def scratchMark : WorkSymbol := WorkSymbol.zeroZero
def selectedMark : WorkSymbol := WorkSymbol.oneZero
def cursorMarker : WorkSymbol := WorkSymbol.oneBlank

theorem scratchMark_ne_selectedMark :
    scratchMark ≠ selectedMark := by
  decide

theorem scratchMark_ne_unaryUnit :
    scratchMark ≠ unaryUnit := by
  decide

theorem selectedMark_ne_unaryUnit :
    selectedMark ≠ unaryUnit := by
  decide

def allWorkSymbols : List WorkSymbol :=
  TargetEmitter.allWorkSymbols

structure StateProgram where
  state : Nat
  action : WorkSymbol → Nat × WorkSymbol × HeadMove

def deadAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  (deadState, symbol, .stay)

def sourceAction (slot : Slot) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.zeroZero ∨
      symbol = WorkSymbol.zeroOne ∨
      symbol = WorkSymbol.oneZero ∨
      symbol = WorkSymbol.oneOne ∨
      symbol = cursorMarker then
    (startState slot, symbol, .left)
  else if symbol = sourceLeftBoundary then
    (scratchState slot, symbol, .left)
  else
    deadAction symbol

def scratchAction (slot : Slot) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (seekLedgerState slot, scratchMark, .left)
  else if symbol = unarySeparator then
    (compareSeekLedgerState slot, symbol, .left)
  else
    deadAction symbol

def seekLedgerAction (slot : Slot) (compare : Bool)
    (symbol : WorkSymbol) : Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit ∨ symbol = unarySeparator ∨
      symbol = WorkSymbol.blank then
    (if compare then compareSeekLedgerState slot
      else seekLedgerState slot, symbol, .left)
  else if symbol = ledgerBoundary then
    (if compare then compareSeekSlotState slot (slotCode slot)
      else pairSeekSlotState slot (slotCode slot), symbol, .left)
  else
    deadAction symbol

def ledgerPayload (symbol : WorkSymbol) : Prop :=
  symbol = unaryUnit ∨ symbol = unarySeparator ∨
    symbol = WorkSymbol.blank ∨ symbol = slotBoundary ∨
    symbol = selectedMark

private instance instDecidableLedgerPayload (symbol : WorkSymbol) :
    Decidable (ledgerPayload symbol) := by
  unfold ledgerPayload
  infer_instance

def pairSeekSlotAction (slot : Slot) (remaining : Nat)
    (symbol : WorkSymbol) : Nat × WorkSymbol × HeadMove :=
  if symbol = slotBoundary then
    if remaining = 0 then
      (selectedState slot, symbol, .left)
    else
      (pairSeekSlotState slot (remaining - 1), symbol, .left)
  else if symbol = unaryUnit ∨ symbol = unarySeparator ∨
      symbol = WorkSymbol.blank ∨ symbol = selectedMark then
    (pairSeekSlotState slot remaining, symbol, .left)
  else
    deadAction symbol

def selectedAction (slot : Slot) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = selectedMark then
    (selectedState slot, symbol, .left)
  else if symbol = unaryUnit then
    (returnLedgerState slot, selectedMark, .right)
  else
    deadAction symbol

def returnLedgerAction (slot : Slot) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if ledgerPayload symbol then
    (returnLedgerState slot, symbol, .right)
  else if symbol = ledgerBoundary then
    (returnScratchState slot, symbol, .right)
  else
    deadAction symbol

def returnScratchAction (slot : Slot) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit ∨ symbol = unarySeparator ∨
      symbol = WorkSymbol.blank then
    (returnScratchState slot, symbol, .right)
  else if symbol = scratchMark then
    (scratchState slot, unaryUnit, .left)
  else
    deadAction symbol

def compareSeekSlotAction (slot : Slot) (remaining : Nat)
    (symbol : WorkSymbol) : Nat × WorkSymbol × HeadMove :=
  if symbol = slotBoundary then
    if remaining = 0 then
      (compareSelectedState slot, symbol, .left)
    else
      (compareSeekSlotState slot (remaining - 1), symbol, .left)
  else if symbol = unaryUnit ∨ symbol = unarySeparator ∨
      symbol = WorkSymbol.blank ∨ symbol = selectedMark then
    (compareSeekSlotState slot remaining, symbol, .left)
  else
    deadAction symbol

def compareSelectedAction (slot : Slot) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = selectedMark then
    (compareSelectedState slot, symbol, .left)
  else if symbol = unaryUnit then
    (restoreLessLedgerState, symbol, .right)
  else if symbol = unarySeparator then
    (restoreEqualLedgerState, symbol, .right)
  else
    deadAction symbol

def restoreLedgerAction (equal : Bool) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  let state :=
    if equal then restoreEqualLedgerState else restoreLessLedgerState
  if symbol = selectedMark then
    (state, unaryUnit, .right)
  else if symbol = unaryUnit ∨ symbol = unarySeparator ∨
      symbol = WorkSymbol.blank ∨ symbol = slotBoundary then
    (state, symbol, .right)
  else if symbol = ledgerBoundary then
    (if equal then restoreEqualScratchState
      else restoreLessScratchState, symbol, .right)
  else
    deadAction symbol

def restoreScratchAction (equal : Bool) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  let state :=
    if equal then restoreEqualScratchState else restoreLessScratchState
  if symbol = unaryUnit ∨ symbol = unarySeparator ∨
      symbol = WorkSymbol.blank then
    (state, symbol, .right)
  else if symbol = sourceLeftBoundary then
    (if equal then acceptState else rejectState, symbol, .right)
  else
    deadAction symbol

def seekPrograms (slot : Slot) : List StateProgram :=
  [ { state := pairSeekSlotState slot 0,
      action := pairSeekSlotAction slot 0 }
  , { state := pairSeekSlotState slot 1,
      action := pairSeekSlotAction slot 1 }
  , { state := pairSeekSlotState slot 2,
      action := pairSeekSlotAction slot 2 }
  , { state := pairSeekSlotState slot 3,
      action := pairSeekSlotAction slot 3 }
  , { state := pairSeekSlotState slot 4,
      action := pairSeekSlotAction slot 4 }
  , { state := pairSeekSlotState slot 5,
      action := pairSeekSlotAction slot 5 }
  , { state := compareSeekSlotState slot 0,
      action := compareSeekSlotAction slot 0 }
  , { state := compareSeekSlotState slot 1,
      action := compareSeekSlotAction slot 1 }
  , { state := compareSeekSlotState slot 2,
      action := compareSeekSlotAction slot 2 }
  , { state := compareSeekSlotState slot 3,
      action := compareSeekSlotAction slot 3 }
  , { state := compareSeekSlotState slot 4,
      action := compareSeekSlotAction slot 4 }
  , { state := compareSeekSlotState slot 5,
      action := compareSeekSlotAction slot 5 } ]

def slotPrograms (slot : Slot) : List StateProgram :=
  [ { state := startState slot, action := sourceAction slot }
  , { state := scratchState slot, action := scratchAction slot }
  , { state := seekLedgerState slot,
      action := seekLedgerAction slot false }
  , { state := compareSeekLedgerState slot,
      action := seekLedgerAction slot true } ] ++
  seekPrograms slot ++
  [ { state := selectedState slot, action := selectedAction slot }
  , { state := returnLedgerState slot,
      action := returnLedgerAction slot }
  , { state := returnScratchState slot,
      action := returnScratchAction slot }
  , { state := compareSelectedState slot,
      action := compareSelectedAction slot } ]

def statePrograms : List StateProgram :=
  allSlots.flatMap slotPrograms ++
  [ { state := restoreEqualLedgerState,
      action := restoreLedgerAction true }
  , { state := restoreLessLedgerState,
      action := restoreLedgerAction false }
  , { state := restoreEqualScratchState,
      action := restoreScratchAction true }
  , { state := restoreLessScratchState,
      action := restoreScratchAction false } ]

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

theorem seekPrograms_length (slot : Slot) :
    (seekPrograms slot).length = 12 := by
  rfl

theorem slotPrograms_length (slot : Slot) :
    (slotPrograms slot).length = 20 := by
  simp [slotPrograms, seekPrograms_length]

theorem statePrograms_length :
    statePrograms.length = 124 := by
  rfl

theorem rulesAt_length (program : StateProgram) :
    (rulesAt program).length = 9 := by
  rfl

theorem rules_length :
    rules.length = 1116 := by
  change (statePrograms.flatMap rulesAt).length = 1116
  have materialized :
      ∀ programs : List StateProgram,
        (programs.flatMap rulesAt).length =
          9 * programs.length := by
    intro programs
    induction programs with
    | nil => rfl
    | cons program rest ih =>
        simp only [List.flatMap_cons, List.length_append,
          rulesAt_length, ih, List.length_cons, Nat.mul_succ]
        omega
  rw [materialized, statePrograms_length]

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

set_option maxRecDepth 1000000 in
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

set_option maxRecDepth 1000000 in
theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule rules acceptState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 1000000 in
theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules rejectState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 1000000 in
theorem no_rule_at_dead (symbol : WorkSymbol) :
    findWorkRule rules deadState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem dead_configuration_not_halted
    (slot : Slot) (tape : WorkTape) :
    (machineFor slot).isHalted
      { state := deadState, tape := tape } = false := by
  rfl

set_option maxRecDepth 1000000 in
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

/-! ### Frozen workspace endpoints and exact cost -/

abbrev LedgerFits :=
  TargetEmitterScratchAddSlot.LedgerFits

def selectedValue (slot : Slot)
    (registers : TargetEmitter.UnaryRegisters) : Nat :=
  TargetEmitterScratchAddSlot.selectedValue slot registers

def prefixWord (capacity : Nat) (slot : Slot)
    (registers : TargetEmitter.UnaryRegisters) : List WorkSymbol :=
  TargetEmitterScratchAddSlot.prefixWord capacity slot registers

def suffixWord (capacity : Nat) (slot : Slot)
    (registers : TargetEmitter.UnaryRegisters) : List WorkSymbol :=
  TargetEmitterScratchAddSlot.suffixWord capacity slot registers

def scratchWord (capacity scratch : Nat) : List WorkSymbol :=
  TargetEmitterScratchAddSlot.scratchWord capacity scratch

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

def equalConfiguration (_slot : Slot) (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft :
      List WorkSymbol) : WorkConfiguration :=
  configAtWord acceptState
    (sourceLeftBoundary ::
      (scratchWord capacity scratch ++
        ledgerBoundary ::
          (TargetEmitterLedger.slotBank capacity registers ++
            outsideLeft)))
    (sourceHead :: sourceTail ++ targetAndRight)

def lessConfiguration (_slot : Slot) (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft :
      List WorkSymbol) : WorkConfiguration :=
  configAtWord rejectState
    (sourceLeftBoundary ::
      (scratchWord capacity scratch ++
        ledgerBoundary ::
          (TargetEmitterLedger.slotBank capacity registers ++
            outsideLeft)))
    (sourceHead :: sourceTail ++ targetAndRight)

def pairSteps (capacity prefixLength : Nat) : Nat :=
  2 * capacity + 2 * prefixLength + 7

def finishSteps (capacity prefixLength scratch : Nat) : Nat :=
  2 * capacity + 2 * prefixLength + scratch + 8

def workSteps (slot : Slot) (capacity scratch : Nat) : Nat :=
  scratch * pairSteps capacity
      (slotCode slot * (capacity + 2)) +
    finishSteps capacity
      (slotCode slot * (capacity + 2)) scratch +
    2

theorem workSteps_evaluated (slot : Slot)
    (capacity scratch : Nat) :
    workSteps slot capacity scratch =
      scratch *
          (2 * capacity +
            2 * (slotCode slot * (capacity + 2)) + 7) +
        2 * capacity +
        2 * (slotCode slot * (capacity + 2)) +
        scratch + 10 := by
  unfold workSteps pairSteps finishSteps
  omega

def polynomialWorkBound (capacity scratch : Nat) : Nat :=
  scratch * (14 * capacity + 31) +
    14 * capacity + scratch + 34

theorem workSteps_le_polynomialWorkBound
    (slot : Slot) (capacity scratch : Nat) :
    workSteps slot capacity scratch ≤
      polynomialWorkBound capacity scratch := by
  have codeLe : slotCode slot ≤ 5 := by
    cases slot <;> decide
  have prefixLe :
      slotCode slot * (capacity + 2) ≤
        5 * (capacity + 2) :=
    Nat.mul_le_mul_right (capacity + 2) codeLe
  have pairLe :
      2 * capacity +
          2 * (slotCode slot * (capacity + 2)) + 7 ≤
        14 * capacity + 31 := by
    omega
  have scaled :=
    Nat.mul_le_mul_left scratch pairLe
  have finishLe :
      2 * capacity +
          2 * (slotCode slot * (capacity + 2)) +
          scratch + 10 ≤
        14 * capacity + scratch + 34 := by
    omega
  rw [workSteps_evaluated]
  unfold polynomialWorkBound
  omega

theorem equal_halted (slot : Slot) (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft :
      List WorkSymbol) :
    (machineFor slot).isHalted
      (equalConfiguration slot capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft) = true := by
  rfl

theorem less_halted (slot : Slot) (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft :
      List WorkSymbol) :
    (machineFor slot).isHalted
      (lessConfiguration slot capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft) = true := by
  rfl

end PNP.Concrete.LockedNAND.TargetEmitterScratchCompareSlot
