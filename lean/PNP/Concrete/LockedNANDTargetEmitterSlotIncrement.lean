/-
Copyright (c) 2026 PNP Labs.

Literal increment primitive for one of the six unary controller-ledger slots.
The executable table contains six entry paths.  It starts on the retained
source head, validates and crosses the nearest-first scratch record, counts
slot boundaries in finite control, moves the selected unary separator one
reserved blank outward, and returns to the same source head.  No rule knows a
slot value, capacity, raw circuit, or host-side schedule.
-/

import PNP.Concrete.LockedNANDTargetEmitterLedger
import PNP.Concrete.PipelineMachineSimulation

namespace PNP.Concrete.LockedNAND.TargetEmitterSlotIncrement

open PNP.Concrete

abbrev Slot := TargetEmitterLedger.Slot

def allSlots : List Slot :=
  TargetEmitterLedger.Slot.all

def slotCode (slot : Slot) : Nat :=
  TargetEmitterLedger.Slot.index slot

theorem slotCode_eq_ledger_index (slot : Slot) :
    slotCode slot = TargetEmitterLedger.Slot.index slot := by
  rfl

theorem slotCode_le_five (slot : Slot) :
    slotCode slot ≤ 5 := by
  cases slot <;> decide

def startState (slot : Slot) : Nat := 2000 + slotCode slot
def boundaryState (slot : Slot) : Nat := 2010 + slotCode slot
def scratchUnitsState (slot : Slot) : Nat := 2020 + slotCode slot
def scratchReserveState (slot : Slot) : Nat := 2030 + slotCode slot
def seekSlotState (remaining : Nat) : Nat := 2040 + remaining
def skipUnitsState (remaining : Nat) : Nat := 2050 + remaining
def skipReserveState (remaining : Nat) : Nat := 2060 + remaining
def selectedUnitsState : Nat := 2070
def writeSeparatorState : Nat := 2071
def returnLedgerState : Nat := 2072
def returnScratchState : Nat := 2073
def acceptState : Nat := 2074
def rejectState : Nat := 2075
def deadState : Nat := TargetEmitter.deadState

def unaryUnit : WorkSymbol := TargetEmitter.unaryUnit
def unarySeparator : WorkSymbol := TargetEmitter.unarySeparator
def cursorMarker : WorkSymbol := WorkSymbol.oneBlank
def sourceLeftBoundary : WorkSymbol :=
  TargetEmitter.sourceLeftBoundary
def ledgerBoundary : WorkSymbol :=
  TargetEmitterLedger.ledgerBoundary
def slotBoundary : WorkSymbol :=
  TargetEmitterLedger.slotBoundary

theorem ledgerBoundary_eq_sourceTargetBoundary :
    ledgerBoundary = TargetEmitter.sourceTargetBoundary := by
  rfl

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
    (boundaryState slot, symbol, .left)
  else
    deadAction symbol

def boundaryAction (slot : Slot) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = sourceLeftBoundary then
    (scratchUnitsState slot, symbol, .left)
  else
    deadAction symbol

def scratchUnitsAction (slot : Slot) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (scratchUnitsState slot, symbol, .left)
  else if symbol = unarySeparator then
    (scratchReserveState slot, symbol, .left)
  else
    deadAction symbol

def scratchReserveAction (slot : Slot) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.blank then
    (scratchReserveState slot, symbol, .left)
  else if symbol = ledgerBoundary then
    (seekSlotState (slotCode slot), symbol, .left)
  else
    deadAction symbol

def seekSlotAction (remaining : Nat) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = slotBoundary then
    if remaining = 0 then
      (selectedUnitsState, symbol, .left)
    else
      (skipUnitsState (remaining - 1), symbol, .left)
  else
    deadAction symbol

def skipUnitsAction (remaining : Nat) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (skipUnitsState remaining, symbol, .left)
  else if symbol = unarySeparator then
    (skipReserveState remaining, symbol, .left)
  else
    deadAction symbol

def skipReserveAction (remaining : Nat) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.blank then
    (skipReserveState remaining, symbol, .left)
  else if symbol = slotBoundary then
    if remaining = 0 then
      (selectedUnitsState, symbol, .left)
    else
      (skipUnitsState (remaining - 1), symbol, .left)
  else
    deadAction symbol

def selectedUnitsAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (selectedUnitsState, symbol, .left)
  else if symbol = unarySeparator then
    (writeSeparatorState, unaryUnit, .left)
  else
    deadAction symbol

def writeSeparatorAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.blank then
    (returnLedgerState, unarySeparator, .right)
  else
    deadAction symbol

def returnLedgerAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit ∨ symbol = unarySeparator ∨
      symbol = WorkSymbol.blank ∨ symbol = slotBoundary then
    (returnLedgerState, symbol, .right)
  else if symbol = ledgerBoundary then
    (returnScratchState, symbol, .right)
  else
    deadAction symbol

def returnScratchAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit ∨ symbol = unarySeparator ∨
      symbol = WorkSymbol.blank then
    (returnScratchState, symbol, .right)
  else if symbol = sourceLeftBoundary then
    (acceptState, symbol, .right)
  else
    deadAction symbol

def slotPrograms (slot : Slot) : List StateProgram :=
  [{ state := startState slot, action := sourceAction slot },
   { state := boundaryState slot, action := boundaryAction slot },
   { state := scratchUnitsState slot, action := scratchUnitsAction slot },
   { state := scratchReserveState slot,
     action := scratchReserveAction slot }]

def statePrograms : List StateProgram :=
  slotPrograms .inputCount ++
  slotPrograms .normalizedGateCount ++
  slotPrograms .carrierWidth ++
  slotPrograms .baseline ++
  slotPrograms .currentGate ++
  slotPrograms .outputIndex ++
  [{ state := seekSlotState 0, action := seekSlotAction 0 },
   { state := seekSlotState 1, action := seekSlotAction 1 },
   { state := seekSlotState 2, action := seekSlotAction 2 },
   { state := seekSlotState 3, action := seekSlotAction 3 },
   { state := seekSlotState 4, action := seekSlotAction 4 },
   { state := seekSlotState 5, action := seekSlotAction 5 },
   { state := skipUnitsState 0, action := skipUnitsAction 0 },
   { state := skipUnitsState 1, action := skipUnitsAction 1 },
   { state := skipUnitsState 2, action := skipUnitsAction 2 },
   { state := skipUnitsState 3, action := skipUnitsAction 3 },
   { state := skipUnitsState 4, action := skipUnitsAction 4 },
   { state := skipReserveState 0, action := skipReserveAction 0 },
   { state := skipReserveState 1, action := skipReserveAction 1 },
   { state := skipReserveState 2, action := skipReserveAction 2 },
   { state := skipReserveState 3, action := skipReserveAction 3 },
   { state := skipReserveState 4, action := skipReserveAction 4 },
   { state := selectedUnitsState, action := selectedUnitsAction },
   { state := writeSeparatorState, action := writeSeparatorAction },
   { state := returnLedgerState, action := returnLedgerAction },
   { state := returnScratchState, action := returnScratchAction }]

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

theorem slotPrograms_length (slot : Slot) :
    (slotPrograms slot).length = 4 := by
  rfl

theorem statePrograms_length :
    statePrograms.length = 44 := by
  rfl

theorem rulesAt_length (program : StateProgram) :
    (rulesAt program).length = 9 := by
  rfl

set_option maxRecDepth 200000 in
theorem rules_length :
    rules.length = 396 := by
  rfl

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
    (machineFor slot).startState ≠ (machineFor slot).acceptState := by
  cases slot <;> decide

theorem start_ne_reject (slot : Slot) :
    (machineFor slot).startState ≠ (machineFor slot).rejectState := by
  cases slot <;> decide

theorem accept_ne_reject (slot : Slot) :
    (machineFor slot).acceptState ≠ (machineFor slot).rejectState := by
  cases slot <;> decide

set_option maxRecDepth 200000 in
theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule rules acceptState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

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

/-! ### Six-slot nearest-first layout -/

structure SlotCell where
  value : Nat
  remaining : Nat
deriving Repr

def SlotCell.payload (cell : SlotCell) : List WorkSymbol :=
  List.replicate cell.value unaryUnit ++
    unarySeparator ::
      List.replicate cell.remaining WorkSymbol.blank

def SlotCell.word (cell : SlotCell) : List WorkSymbol :=
  slotBoundary :: cell.payload

theorem SlotCell.word_eq_ledger_slotWord (cell : SlotCell) :
    cell.word =
      TargetEmitterLedger.slotWord
        (cell.value + cell.remaining) cell.value := by
  unfold SlotCell.word SlotCell.payload TargetEmitterLedger.slotWord
  have subtraction :
      cell.value + cell.remaining - cell.value =
        cell.remaining := by
    omega
  rw [subtraction]
  unfold slotBoundary unaryUnit unarySeparator
    TargetEmitterLedger.slotSeparator
    TargetEmitterLedger.unarySeparator TargetEmitterLedger.cellBlank
    TargetEmitter.unaryWord
  simp [List.append_assoc]

def SlotCell.increment (cell : SlotCell) : SlotCell :=
  { value := cell.value + 1
    remaining := cell.remaining - 1 }

structure SlotBank where
  inputCount : SlotCell
  normalizedGateCount : SlotCell
  carrierWidth : SlotCell
  baseline : SlotCell
  currentGate : SlotCell
  outputIndex : SlotCell
deriving Repr

def cellsWord (cells : List SlotCell) : List WorkSymbol :=
  cells.flatMap SlotCell.word

def SlotBank.cells (bank : SlotBank) : List SlotCell :=
  [bank.inputCount, bank.normalizedGateCount, bank.carrierWidth,
    bank.baseline, bank.currentGate, bank.outputIndex]

def SlotBank.word (bank : SlotBank) : List WorkSymbol :=
  cellsWord bank.cells

def SlotBank.selected (slot : Slot) (bank : SlotBank) : SlotCell :=
  match slot with
  | .inputCount => bank.inputCount
  | .normalizedGateCount => bank.normalizedGateCount
  | .carrierWidth => bank.carrierWidth
  | .baseline => bank.baseline
  | .currentGate => bank.currentGate
  | .outputIndex => bank.outputIndex

def SlotBank.prefixCells (slot : Slot) (bank : SlotBank) :
    List SlotCell :=
  match slot with
  | .inputCount => []
  | .normalizedGateCount => [bank.inputCount]
  | .carrierWidth =>
      [bank.inputCount, bank.normalizedGateCount]
  | .baseline =>
      [bank.inputCount, bank.normalizedGateCount, bank.carrierWidth]
  | .currentGate =>
      [bank.inputCount, bank.normalizedGateCount, bank.carrierWidth,
        bank.baseline]
  | .outputIndex =>
      [bank.inputCount, bank.normalizedGateCount, bank.carrierWidth,
        bank.baseline, bank.currentGate]

def SlotBank.suffixCells (slot : Slot) (bank : SlotBank) :
    List SlotCell :=
  match slot with
  | .inputCount =>
      [bank.normalizedGateCount, bank.carrierWidth, bank.baseline,
        bank.currentGate, bank.outputIndex]
  | .normalizedGateCount =>
      [bank.carrierWidth, bank.baseline, bank.currentGate,
        bank.outputIndex]
  | .carrierWidth =>
      [bank.baseline, bank.currentGate, bank.outputIndex]
  | .baseline =>
      [bank.currentGate, bank.outputIndex]
  | .currentGate => [bank.outputIndex]
  | .outputIndex => []

def SlotBank.prefixWord (slot : Slot) (bank : SlotBank) :
    List WorkSymbol :=
  cellsWord (bank.prefixCells slot)

def SlotBank.suffixWord (slot : Slot) (bank : SlotBank) :
    List WorkSymbol :=
  cellsWord (bank.suffixCells slot)

def SlotBank.increment (slot : Slot) (bank : SlotBank) : SlotBank :=
  match slot with
  | .inputCount =>
      { bank with inputCount := bank.inputCount.increment }
  | .normalizedGateCount =>
      { bank with
        normalizedGateCount := bank.normalizedGateCount.increment }
  | .carrierWidth =>
      { bank with carrierWidth := bank.carrierWidth.increment }
  | .baseline =>
      { bank with baseline := bank.baseline.increment }
  | .currentGate =>
      { bank with currentGate := bank.currentGate.increment }
  | .outputIndex =>
      { bank with outputIndex := bank.outputIndex.increment }

theorem prefixCells_length (slot : Slot) (bank : SlotBank) :
    (bank.prefixCells slot).length = slotCode slot := by
  cases slot <;> rfl

theorem bankWord_decompose (slot : Slot) (bank : SlotBank) :
    bank.word =
      bank.prefixWord slot ++
        (bank.selected slot).word ++ bank.suffixWord slot := by
  cases slot <;>
    simp [SlotBank.word, cellsWord, SlotBank.cells, SlotBank.prefixWord,
      SlotBank.suffixWord, SlotBank.prefixCells, SlotBank.suffixCells,
      SlotBank.selected, List.append_assoc]

theorem increment_preserves_unselected_prefix
    (slot : Slot) (bank : SlotBank) :
    (bank.increment slot).prefixWord slot =
      bank.prefixWord slot := by
  cases slot <;> rfl

theorem increment_preserves_unselected_suffix
    (slot : Slot) (bank : SlotBank) :
    (bank.increment slot).suffixWord slot =
      bank.suffixWord slot := by
  cases slot <;> rfl

theorem increment_selected (slot : Slot) (bank : SlotBank) :
    (bank.increment slot).selected slot =
      (bank.selected slot).increment := by
  cases slot <;> rfl

def scratchWord (units reserve : Nat) : List WorkSymbol :=
  List.replicate units unaryUnit ++
    unarySeparator :: List.replicate reserve WorkSymbol.blank

def configAtWord (state : Nat)
    (left word : List WorkSymbol) : WorkConfiguration :=
  TargetEmitter.configAtWord state left word

def configAtLeftWord (state : Nat)
    (leftWord right : List WorkSymbol) : WorkConfiguration :=
  TargetEmitter.configAtLeftWord state leftWord right

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

private def pushLeft :
    List WorkSymbol → List WorkSymbol → List WorkSymbol
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
  | nil => rfl
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
  | nil => rfl
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

set_option maxRecDepth 200000 in
private theorem find_start_source (slot : Slot) (symbol : WorkSymbol)
    (allowed :
      TargetEmitter.PackedSymbol symbol ∨ symbol = cursorMarker) :
    findWorkRule rules (startState slot) symbol =
      some (literalRule (startState slot) symbol
        (boundaryState slot) symbol .left) := by
  rcases allowed with packed | cursor
  · cases slot <;> cases packed <;> decide
  · subst symbol
    cases slot <;> decide

set_option maxRecDepth 200000 in
private theorem find_boundary (slot : Slot) :
    findWorkRule rules (boundaryState slot) sourceLeftBoundary =
      some (literalRule (boundaryState slot) sourceLeftBoundary
        (scratchUnitsState slot) sourceLeftBoundary .left) := by
  cases slot <;> decide

set_option maxRecDepth 200000 in
private theorem find_scratch_unit (slot : Slot) :
    findWorkRule rules (scratchUnitsState slot) unaryUnit =
      some (literalRule (scratchUnitsState slot) unaryUnit
        (scratchUnitsState slot) unaryUnit .left) := by
  cases slot <;> decide

set_option maxRecDepth 200000 in
private theorem find_scratch_separator (slot : Slot) :
    findWorkRule rules (scratchUnitsState slot) unarySeparator =
      some (literalRule (scratchUnitsState slot) unarySeparator
        (scratchReserveState slot) unarySeparator .left) := by
  cases slot <;> decide

set_option maxRecDepth 200000 in
private theorem find_scratch_blank (slot : Slot) :
    findWorkRule rules (scratchReserveState slot) WorkSymbol.blank =
      some (literalRule (scratchReserveState slot) WorkSymbol.blank
        (scratchReserveState slot) WorkSymbol.blank .left) := by
  cases slot <;> decide

set_option maxRecDepth 200000 in
private theorem find_ledger_boundary (slot : Slot) :
    findWorkRule rules (scratchReserveState slot) ledgerBoundary =
      some (literalRule (scratchReserveState slot) ledgerBoundary
        (seekSlotState (slotCode slot)) ledgerBoundary .left) := by
  cases slot <;> decide

set_option maxRecDepth 200000 in
private theorem find_seek_skip_boundary (remaining : Nat)
    (positive : 0 < remaining) (remainingLe : remaining ≤ 5) :
    findWorkRule rules (seekSlotState remaining) slotBoundary =
      some (literalRule (seekSlotState remaining) slotBoundary
        (skipUnitsState (remaining - 1)) slotBoundary .left) := by
  have possibilities :
      remaining = 1 ∨ remaining = 2 ∨ remaining = 3 ∨
        remaining = 4 ∨ remaining = 5 := by
    omega
  rcases possibilities with first | second | third | fourth | fifth
  all_goals subst remaining
  all_goals decide

set_option maxRecDepth 200000 in
private theorem find_skip_unit (remaining : Nat)
    (remainingLe : remaining ≤ 4) :
    findWorkRule rules (skipUnitsState remaining) unaryUnit =
      some (literalRule (skipUnitsState remaining) unaryUnit
        (skipUnitsState remaining) unaryUnit .left) := by
  have possibilities :
      remaining = 0 ∨ remaining = 1 ∨ remaining = 2 ∨
        remaining = 3 ∨ remaining = 4 := by
    omega
  rcases possibilities with first | second | third | fourth | fifth
  all_goals subst remaining
  all_goals decide

set_option maxRecDepth 200000 in
private theorem find_skip_separator (remaining : Nat)
    (remainingLe : remaining ≤ 4) :
    findWorkRule rules (skipUnitsState remaining) unarySeparator =
      some (literalRule (skipUnitsState remaining) unarySeparator
        (skipReserveState remaining) unarySeparator .left) := by
  have possibilities :
      remaining = 0 ∨ remaining = 1 ∨ remaining = 2 ∨
        remaining = 3 ∨ remaining = 4 := by
    omega
  rcases possibilities with first | second | third | fourth | fifth
  all_goals subst remaining
  all_goals decide

set_option maxRecDepth 200000 in
private theorem find_skip_blank (remaining : Nat)
    (remainingLe : remaining ≤ 4) :
    findWorkRule rules (skipReserveState remaining) WorkSymbol.blank =
      some (literalRule (skipReserveState remaining) WorkSymbol.blank
        (skipReserveState remaining) WorkSymbol.blank .left) := by
  have possibilities :
      remaining = 0 ∨ remaining = 1 ∨ remaining = 2 ∨
        remaining = 3 ∨ remaining = 4 := by
    omega
  rcases possibilities with first | second | third | fourth | fifth
  all_goals subst remaining
  all_goals decide

set_option maxRecDepth 200000 in
private theorem find_skip_selected_boundary :
    findWorkRule rules (skipReserveState 0) slotBoundary =
      some (literalRule (skipReserveState 0) slotBoundary
        selectedUnitsState slotBoundary .left) := by
  decide

set_option maxRecDepth 200000 in
private theorem find_skip_next_boundary (remaining : Nat)
    (positive : 0 < remaining) (remainingLe : remaining ≤ 4) :
    findWorkRule rules (skipReserveState remaining) slotBoundary =
      some (literalRule (skipReserveState remaining) slotBoundary
        (skipUnitsState (remaining - 1)) slotBoundary .left) := by
  have possibilities :
      remaining = 1 ∨ remaining = 2 ∨ remaining = 3 ∨
        remaining = 4 := by
    omega
  rcases possibilities with first | second | third | fourth
  all_goals subst remaining
  all_goals decide

set_option maxRecDepth 200000 in
private theorem find_seek_selected_boundary :
    findWorkRule rules (seekSlotState 0) slotBoundary =
      some (literalRule (seekSlotState 0) slotBoundary
        selectedUnitsState slotBoundary .left) := by
  decide

set_option maxRecDepth 200000 in
private theorem find_selected_unit :
    findWorkRule rules selectedUnitsState unaryUnit =
      some (literalRule selectedUnitsState unaryUnit
        selectedUnitsState unaryUnit .left) := by
  decide

set_option maxRecDepth 200000 in
private theorem find_selected_separator :
    findWorkRule rules selectedUnitsState unarySeparator =
      some (literalRule selectedUnitsState unarySeparator
        writeSeparatorState unaryUnit .left) := by
  decide

set_option maxRecDepth 200000 in
private theorem find_write_blank :
    findWorkRule rules writeSeparatorState WorkSymbol.blank =
      some (literalRule writeSeparatorState WorkSymbol.blank
        returnLedgerState unarySeparator .right) := by
  decide

set_option maxRecDepth 200000 in
private theorem find_return_ledger_symbol (symbol : WorkSymbol)
    (allowed :
      symbol = unaryUnit ∨ symbol = unarySeparator ∨
        symbol = WorkSymbol.blank ∨ symbol = slotBoundary) :
    findWorkRule rules returnLedgerState symbol =
      some (literalRule returnLedgerState symbol
        returnLedgerState symbol .right) := by
  rcases allowed with unit | separator | blank | boundary
  · subst symbol; decide
  · subst symbol; decide
  · subst symbol; decide
  · subst symbol; decide

set_option maxRecDepth 200000 in
private theorem find_return_ledger_boundary :
    findWorkRule rules returnLedgerState ledgerBoundary =
      some (literalRule returnLedgerState ledgerBoundary
        returnScratchState ledgerBoundary .right) := by
  decide

set_option maxRecDepth 200000 in
private theorem find_return_scratch_symbol (symbol : WorkSymbol)
    (allowed :
      symbol = unaryUnit ∨ symbol = unarySeparator ∨
        symbol = WorkSymbol.blank) :
    findWorkRule rules returnScratchState symbol =
      some (literalRule returnScratchState symbol
        returnScratchState symbol .right) := by
  rcases allowed with unit | separator | blank
  · subst symbol; decide
  · subst symbol; decide
  · subst symbol; decide

set_option maxRecDepth 200000 in
private theorem find_return_source_boundary :
    findWorkRule rules returnScratchState sourceLeftBoundary =
      some (literalRule returnScratchState sourceLeftBoundary
        acceptState sourceLeftBoundary .right) := by
  decide

private theorem source_step (slot : Slot) (symbol : WorkSymbol)
    (allowed :
      TargetEmitter.PackedSymbol symbol ∨ symbol = cursorMarker)
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

private theorem seek_skip_boundary_step (slot : Slot)
    (remaining : Nat) (positive : 0 < remaining)
    (remainingLe : remaining ≤ 5)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (seekSlotState remaining)
          (slotBoundary :: left) right) =
      some (configAtLeftWord (skipUnitsState (remaining - 1))
        left (slotBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · have acceptNe :
        seekSlotState remaining ≠ acceptState := by
      unfold seekSlotState acceptState
      omega
    have rejectNe :
        seekSlotState remaining ≠ rejectState := by
      unfold seekSlotState rejectState
      omega
    simp [WorkMachine.isHalted, machineFor, configAtLeftWord,
      TargetEmitter.configAtLeftWord, acceptNe, rejectNe]
  · exact find_seek_skip_boundary remaining positive remainingLe

private theorem skip_unit_step (slot : Slot)
    (remaining : Nat) (remainingLe : remaining ≤ 4)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (skipUnitsState remaining)
          (unaryUnit :: left) right) =
      some (configAtLeftWord (skipUnitsState remaining)
        left (unaryUnit :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · have acceptNe :
        skipUnitsState remaining ≠ acceptState := by
      unfold skipUnitsState acceptState
      omega
    have rejectNe :
        skipUnitsState remaining ≠ rejectState := by
      unfold skipUnitsState rejectState
      omega
    simp [WorkMachine.isHalted, machineFor, configAtLeftWord,
      TargetEmitter.configAtLeftWord, acceptNe, rejectNe]
  · exact find_skip_unit remaining remainingLe

private theorem skip_separator_step (slot : Slot)
    (remaining : Nat) (remainingLe : remaining ≤ 4)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (skipUnitsState remaining)
          (unarySeparator :: left) right) =
      some (configAtLeftWord (skipReserveState remaining)
        left (unarySeparator :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · have acceptNe :
        skipUnitsState remaining ≠ acceptState := by
      unfold skipUnitsState acceptState
      omega
    have rejectNe :
        skipUnitsState remaining ≠ rejectState := by
      unfold skipUnitsState rejectState
      omega
    simp [WorkMachine.isHalted, machineFor, configAtLeftWord,
      TargetEmitter.configAtLeftWord, acceptNe, rejectNe]
  · exact find_skip_separator remaining remainingLe

private theorem skip_blank_step (slot : Slot)
    (remaining : Nat) (remainingLe : remaining ≤ 4)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (skipReserveState remaining)
          (WorkSymbol.blank :: left) right) =
      some (configAtLeftWord (skipReserveState remaining)
        left (WorkSymbol.blank :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · have acceptNe :
        skipReserveState remaining ≠ acceptState := by
      unfold skipReserveState acceptState
      omega
    have rejectNe :
        skipReserveState remaining ≠ rejectState := by
      unfold skipReserveState rejectState
      omega
    simp [WorkMachine.isHalted, machineFor, configAtLeftWord,
      TargetEmitter.configAtLeftWord, acceptNe, rejectNe]
  · exact find_skip_blank remaining remainingLe

private theorem skip_selected_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (skipReserveState 0)
          (slotBoundary :: left) right) =
      some (configAtLeftWord selectedUnitsState
        left (slotBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rfl
  · exact find_skip_selected_boundary

private theorem skip_next_boundary_step (slot : Slot)
    (remaining : Nat) (positive : 0 < remaining)
    (remainingLe : remaining ≤ 4)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (skipReserveState remaining)
          (slotBoundary :: left) right) =
      some (configAtLeftWord (skipUnitsState (remaining - 1))
        left (slotBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · have acceptNe :
        skipReserveState remaining ≠ acceptState := by
      unfold skipReserveState acceptState
      omega
    have rejectNe :
        skipReserveState remaining ≠ rejectState := by
      unfold skipReserveState rejectState
      omega
    simp [WorkMachine.isHalted, machineFor, configAtLeftWord,
      TargetEmitter.configAtLeftWord, acceptNe, rejectNe]
  · exact find_skip_next_boundary remaining positive remainingLe

private theorem seek_selected_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (seekSlotState 0)
          (slotBoundary :: left) right) =
      some (configAtLeftWord selectedUnitsState
        left (slotBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rfl
  · exact find_seek_selected_boundary

private theorem selected_unit_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord selectedUnitsState
          (unaryUnit :: left) right) =
      some (configAtLeftWord selectedUnitsState
        left (unaryUnit :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rfl
  · exact find_selected_unit

private theorem selected_separator_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord selectedUnitsState
          (unarySeparator :: left) right) =
      some (configAtLeftWord writeSeparatorState
        left (unaryUnit :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rfl
  · exact find_selected_separator

private theorem write_separator_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord writeSeparatorState
          (WorkSymbol.blank :: left) right) =
      some (configAtWord returnLedgerState
        (unarySeparator :: left) right) := by
  apply moveRightFromLeftWord_of_find slot
  · rfl
  · exact find_write_blank

private theorem return_ledger_symbol_step (slot : Slot)
    (symbol : WorkSymbol)
    (allowed :
      symbol = unaryUnit ∨ symbol = unarySeparator ∨
        symbol = WorkSymbol.blank ∨ symbol = slotBoundary)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord returnLedgerState left (symbol :: right)) =
      some (configAtWord returnLedgerState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find slot
  · rfl
  · exact find_return_ledger_symbol symbol allowed

private theorem return_ledger_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord returnLedgerState left
          (ledgerBoundary :: right)) =
      some (configAtWord returnScratchState
        (ledgerBoundary :: left) right) := by
  apply moveRightFromWord_of_find slot
  · rfl
  · exact find_return_ledger_boundary

private theorem return_scratch_symbol_step (slot : Slot)
    (symbol : WorkSymbol)
    (allowed :
      symbol = unaryUnit ∨ symbol = unarySeparator ∨
        symbol = WorkSymbol.blank)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord returnScratchState left (symbol :: right)) =
      some (configAtWord returnScratchState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find slot
  · rfl
  · exact find_return_scratch_symbol symbol allowed

private theorem return_source_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord returnScratchState left
          (sourceLeftBoundary :: right)) =
      some (configAtWord acceptState
        (sourceLeftBoundary :: left) right) := by
  apply moveRightFromWord_of_find slot
  · rfl
  · exact find_return_source_boundary

private def PayloadSymbol (symbol : WorkSymbol) : Prop :=
  symbol = unaryUnit ∨ symbol = unarySeparator ∨
    symbol = WorkSymbol.blank

private theorem slotPayload_allowed (cell : SlotCell) :
    ∀ symbol, symbol ∈ cell.payload → PayloadSymbol symbol := by
  intro symbol found
  unfold SlotCell.payload at found
  rw [List.mem_append] at found
  rcases found with inUnits | inTail
  · left
    exact List.eq_of_mem_replicate inUnits
  · cases inTail with
    | head => exact Or.inr (Or.inl rfl)
    | tail _ inBlanks =>
        exact Or.inr (Or.inr
          (List.eq_of_mem_replicate inBlanks))

private theorem scratchUnits_exact (slot : Slot) (count : Nat)
    (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) count
        (configAtLeftWord (scratchUnitsState slot)
          (List.replicate count unaryUnit ++ left) right) =
      some (configAtLeftWord (scratchUnitsState slot)
        left (List.replicate count unaryUnit ++ right)) := by
  have scanned := scanLeftExact slot (scratchUnitsState slot)
    (fun symbol => symbol = unaryUnit)
    (fun head leftTail rightSide equality => by
      subst head
      exact scratch_unit_step slot leftTail rightSide)
    (List.replicate count unaryUnit) left right (by simp)
  simpa using scanned

private theorem scratchBlanks_exact (slot : Slot) (count : Nat)
    (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) count
        (configAtLeftWord (scratchReserveState slot)
          (List.replicate count WorkSymbol.blank ++ left) right) =
      some (configAtLeftWord (scratchReserveState slot)
        left (List.replicate count WorkSymbol.blank ++ right)) := by
  have scanned := scanLeftExact slot (scratchReserveState slot)
    (fun symbol => symbol = WorkSymbol.blank)
    (fun head leftTail rightSide equality => by
      subst head
      exact scratch_blank_step slot leftTail rightSide)
    (List.replicate count WorkSymbol.blank) left right (by simp)
  simpa using scanned

private theorem skipUnits_exact (slot : Slot)
    (remaining : Nat) (remainingLe : remaining ≤ 4)
    (count : Nat) (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) count
        (configAtLeftWord (skipUnitsState remaining)
          (List.replicate count unaryUnit ++ left) right) =
      some (configAtLeftWord (skipUnitsState remaining)
        left (List.replicate count unaryUnit ++ right)) := by
  have scanned := scanLeftExact slot (skipUnitsState remaining)
    (fun symbol => symbol = unaryUnit)
    (fun head leftTail rightSide equality => by
      subst head
      exact skip_unit_step slot remaining remainingLe
        leftTail rightSide)
    (List.replicate count unaryUnit) left right (by simp)
  simpa using scanned

private theorem skipBlanks_exact (slot : Slot)
    (remaining : Nat) (remainingLe : remaining ≤ 4)
    (count : Nat) (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) count
        (configAtLeftWord (skipReserveState remaining)
          (List.replicate count WorkSymbol.blank ++ left) right) =
      some (configAtLeftWord (skipReserveState remaining)
        left (List.replicate count WorkSymbol.blank ++ right)) := by
  have scanned := scanLeftExact slot (skipReserveState remaining)
    (fun symbol => symbol = WorkSymbol.blank)
    (fun head leftTail rightSide equality => by
      subst head
      exact skip_blank_step slot remaining remainingLe
        leftTail rightSide)
    (List.replicate count WorkSymbol.blank) left right (by simp)
  simpa using scanned

private theorem skipCells_exact (slot : Slot)
    (cell : SlotCell) (rest : List SlotCell)
    (restLe : rest.length ≤ 4)
    (left right : List WorkSymbol) :
    workRunExact? (machineFor slot)
        ((cell.payload ++ cellsWord rest).length + 1)
        (configAtLeftWord (skipUnitsState rest.length)
          (cell.payload ++ cellsWord rest ++ slotBoundary :: left)
          right) =
      some (configAtLeftWord selectedUnitsState left
        (slotBoundary ::
          (cell.payload ++ cellsWord rest).reverse ++ right)) := by
  induction rest generalizing cell right with
  | nil =>
      let atSeparator :=
        configAtLeftWord (skipUnitsState 0)
          (unarySeparator ::
            List.replicate cell.remaining WorkSymbol.blank ++
              slotBoundary :: left)
          (List.replicate cell.value unaryUnit ++ right)
      let afterSeparator :=
        configAtLeftWord (skipReserveState 0)
          (List.replicate cell.remaining WorkSymbol.blank ++
            slotBoundary :: left)
          (unarySeparator ::
            List.replicate cell.value unaryUnit ++ right)
      let atBoundary :=
        configAtLeftWord (skipReserveState 0)
          (slotBoundary :: left)
          (List.replicate cell.remaining WorkSymbol.blank ++
            unarySeparator ::
              List.replicate cell.value unaryUnit ++ right)
      have hUnits :
          workRunExact? (machineFor slot) cell.value
              (configAtLeftWord (skipUnitsState 0)
                (cell.payload ++ slotBoundary :: left) right) =
            some atSeparator := by
        simpa [atSeparator, SlotCell.payload, List.append_assoc] using
          skipUnits_exact slot 0 (by omega) cell.value
            (unarySeparator ::
              List.replicate cell.remaining WorkSymbol.blank ++
                slotBoundary :: left)
            right
      have hSeparator :
          workRunExact? (machineFor slot) 1 atSeparator =
            some afterSeparator := by
        apply exactRun_one slot
        simpa [atSeparator, afterSeparator, List.append_assoc] using
          skip_separator_step slot 0 (by omega)
            (List.replicate cell.remaining WorkSymbol.blank ++
              slotBoundary :: left)
            (List.replicate cell.value unaryUnit ++ right)
      have hBlanks :
          workRunExact? (machineFor slot) cell.remaining
              afterSeparator =
            some atBoundary := by
        simpa [afterSeparator, atBoundary, List.append_assoc] using
          skipBlanks_exact slot 0 (by omega) cell.remaining
            (slotBoundary :: left)
            (unarySeparator ::
              List.replicate cell.value unaryUnit ++ right)
      have hBoundary :
          workRunExact? (machineFor slot) 1 atBoundary =
            some (configAtLeftWord selectedUnitsState left
              (slotBoundary ::
                List.replicate cell.remaining WorkSymbol.blank ++
                  unarySeparator ::
                    List.replicate cell.value unaryUnit ++ right)) := by
        apply exactRun_one slot
        simpa [atBoundary, List.append_assoc] using
          skip_selected_boundary_step slot left
            (List.replicate cell.remaining WorkSymbol.blank ++
              unarySeparator ::
                List.replicate cell.value unaryUnit ++ right)
      have h01 := exactRun_add slot cell.value 1 _ _ _
        hUnits hSeparator
      have h02 := exactRun_add slot (cell.value + 1)
        cell.remaining _ _ _ h01 hBlanks
      have complete := exactRun_add slot
        (cell.value + 1 + cell.remaining) 1 _ _ _
        h02 hBoundary
      have stepCount :
          cell.value + 1 + cell.remaining + 1 =
            (cell.payload ++ cellsWord []).length + 1 := by
        simp [SlotCell.payload, cellsWord]
        omega
      rw [stepCount] at complete
      simpa [SlotCell.payload, cellsWord, List.reverse_append,
        List.append_assoc] using complete
  | cons next tail ih =>
      have remainingLe : tail.length + 1 ≤ 4 := by
        simpa using restLe
      have tailLe : tail.length ≤ 4 := by
        omega
      let atSeparator :=
        configAtLeftWord (skipUnitsState (tail.length + 1))
          (unarySeparator ::
            List.replicate cell.remaining WorkSymbol.blank ++
              slotBoundary ::
                next.payload ++ cellsWord tail ++ slotBoundary :: left)
          (List.replicate cell.value unaryUnit ++ right)
      let afterSeparator :=
        configAtLeftWord (skipReserveState (tail.length + 1))
          (List.replicate cell.remaining WorkSymbol.blank ++
            slotBoundary ::
              next.payload ++ cellsWord tail ++ slotBoundary :: left)
          (unarySeparator ::
            List.replicate cell.value unaryUnit ++ right)
      let atBoundary :=
        configAtLeftWord (skipReserveState (tail.length + 1))
          (slotBoundary ::
            next.payload ++ cellsWord tail ++ slotBoundary :: left)
          (List.replicate cell.remaining WorkSymbol.blank ++
            unarySeparator ::
              List.replicate cell.value unaryUnit ++ right)
      let afterBoundary :=
        configAtLeftWord (skipUnitsState tail.length)
          (next.payload ++ cellsWord tail ++ slotBoundary :: left)
          (slotBoundary :: cell.payload.reverse ++ right)
      have hUnits :
          workRunExact? (machineFor slot) cell.value
              (configAtLeftWord (skipUnitsState (tail.length + 1))
                (cell.payload ++ cellsWord (next :: tail) ++
                  slotBoundary :: left) right) =
            some atSeparator := by
        simpa [atSeparator, SlotCell.payload, cellsWord,
          SlotCell.word, List.append_assoc] using
          skipUnits_exact slot (tail.length + 1) remainingLe
            cell.value
            (unarySeparator ::
              List.replicate cell.remaining WorkSymbol.blank ++
                slotBoundary ::
                  next.payload ++ cellsWord tail ++
                    slotBoundary :: left)
            right
      have hSeparator :
          workRunExact? (machineFor slot) 1 atSeparator =
            some afterSeparator := by
        apply exactRun_one slot
        simpa [atSeparator, afterSeparator, List.append_assoc] using
          skip_separator_step slot (tail.length + 1) remainingLe
            (List.replicate cell.remaining WorkSymbol.blank ++
              slotBoundary ::
                next.payload ++ cellsWord tail ++
                  slotBoundary :: left)
            (List.replicate cell.value unaryUnit ++ right)
      have hBlanks :
          workRunExact? (machineFor slot) cell.remaining
              afterSeparator =
            some atBoundary := by
        simpa [afterSeparator, atBoundary, List.append_assoc] using
          skipBlanks_exact slot (tail.length + 1) remainingLe
            cell.remaining
            (slotBoundary ::
              next.payload ++ cellsWord tail ++ slotBoundary :: left)
            (unarySeparator ::
              List.replicate cell.value unaryUnit ++ right)
      have hBoundary :
          workRunExact? (machineFor slot) 1 atBoundary =
            some afterBoundary := by
        apply exactRun_one slot
        have stepped :=
          skip_next_boundary_step slot (tail.length + 1)
            (by omega) remainingLe
            (next.payload ++ cellsWord tail ++ slotBoundary :: left)
            (List.replicate cell.remaining WorkSymbol.blank ++
              unarySeparator ::
                List.replicate cell.value unaryUnit ++ right)
        simpa [atBoundary, afterBoundary, SlotCell.payload,
          List.reverse_append, List.append_assoc] using stepped
      have hRest :
          workRunExact? (machineFor slot)
              ((next.payload ++ cellsWord tail).length + 1)
              afterBoundary =
            some (configAtLeftWord selectedUnitsState left
              (slotBoundary ::
                (next.payload ++ cellsWord tail).reverse ++
                  slotBoundary :: cell.payload.reverse ++ right)) := by
        simpa [afterBoundary, List.append_assoc] using
          ih next tailLe
            (slotBoundary :: cell.payload.reverse ++ right)
      have h01 := exactRun_add slot cell.value 1 _ _ _
        hUnits hSeparator
      have h02 := exactRun_add slot (cell.value + 1)
        cell.remaining _ _ _ h01 hBlanks
      have h03 := exactRun_add slot
        (cell.value + 1 + cell.remaining) 1 _ _ _
        h02 hBoundary
      have complete := exactRun_add slot
        (cell.value + 1 + cell.remaining + 1)
        ((next.payload ++ cellsWord tail).length + 1)
        _ _ _ h03 hRest
      have stepCount :
          cell.value + 1 + cell.remaining + 1 +
              ((next.payload ++ cellsWord tail).length + 1) =
            (cell.payload ++ cellsWord (next :: tail)).length + 1 := by
        simp [SlotCell.payload, cellsWord, SlotCell.word]
        omega
      rw [stepCount] at complete
      simpa [cellsWord, SlotCell.word, List.reverse_append,
        List.append_assoc] using complete

private theorem selectPrefix_exact (slot : Slot)
    (cells : List SlotCell) (cellsLe : cells.length ≤ 5)
    (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) ((cellsWord cells).length + 1)
        (configAtLeftWord (seekSlotState cells.length)
          (cellsWord cells ++ slotBoundary :: left) right) =
      some (configAtLeftWord selectedUnitsState left
        (slotBoundary :: (cellsWord cells).reverse ++ right)) := by
  cases cells with
  | nil =>
      apply exactRun_one slot
      simpa [cellsWord] using
        seek_selected_boundary_step slot left right
  | cons cell rest =>
      have positive : 0 < rest.length + 1 := by
        omega
      have remainingLe : rest.length + 1 ≤ 5 := by
        simpa using cellsLe
      have restLe : rest.length ≤ 4 := by
        omega
      let afterBoundary :=
        configAtLeftWord (skipUnitsState rest.length)
          (cell.payload ++ cellsWord rest ++ slotBoundary :: left)
          (slotBoundary :: right)
      have hBoundary :
          workRunExact? (machineFor slot) 1
              (configAtLeftWord (seekSlotState (rest.length + 1))
                (slotBoundary ::
                  cell.payload ++ cellsWord rest ++
                    slotBoundary :: left) right) =
            some afterBoundary := by
        apply exactRun_one slot
        simpa [afterBoundary, List.append_assoc] using
          seek_skip_boundary_step slot (rest.length + 1)
            positive remainingLe
            (cell.payload ++ cellsWord rest ++ slotBoundary :: left)
            right
      have hCells :
          workRunExact? (machineFor slot)
              ((cell.payload ++ cellsWord rest).length + 1)
              afterBoundary =
            some (configAtLeftWord selectedUnitsState left
              (slotBoundary ::
                (cell.payload ++ cellsWord rest).reverse ++
                  slotBoundary :: right)) := by
        simpa [afterBoundary, List.append_assoc] using
          skipCells_exact slot cell rest restLe left
            (slotBoundary :: right)
      have complete := exactRun_add slot 1
        ((cell.payload ++ cellsWord rest).length + 1)
        _ _ _ hBoundary hCells
      have stepCount :
          1 + ((cell.payload ++ cellsWord rest).length + 1) =
            (cellsWord (cell :: rest)).length + 1 := by
        simp [cellsWord, SlotCell.word]
        omega
      rw [stepCount] at complete
      simpa [cellsWord, SlotCell.word, List.reverse_append,
        List.append_assoc] using complete

private theorem selectedUnits_exact (slot : Slot) (count : Nat)
    (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) count
        (configAtLeftWord selectedUnitsState
          (List.replicate count unaryUnit ++ left) right) =
      some (configAtLeftWord selectedUnitsState left
        (List.replicate count unaryUnit ++ right)) := by
  have scanned := scanLeftExact slot selectedUnitsState
    (fun symbol => symbol = unaryUnit)
    (fun head leftTail rightSide equality => by
      subst head
      exact selected_unit_step slot leftTail rightSide)
    (List.replicate count unaryUnit) left right (by simp)
  simpa using scanned

private def LedgerReturnSymbol (symbol : WorkSymbol) : Prop :=
  PayloadSymbol symbol ∨ symbol = slotBoundary

private theorem slotWord_return_allowed (cell : SlotCell) :
    ∀ symbol, symbol ∈ cell.word → LedgerReturnSymbol symbol := by
  intro symbol found
  cases found with
  | head => exact Or.inr rfl
  | tail _ inPayload =>
      exact Or.inl (slotPayload_allowed cell symbol inPayload)

private theorem cellsWord_return_allowed (cells : List SlotCell) :
    ∀ symbol, symbol ∈ cellsWord cells →
      LedgerReturnSymbol symbol := by
  intro symbol found
  rcases List.mem_flatMap.mp found with
    ⟨cell, _cellMember, inWord⟩
  exact slotWord_return_allowed cell symbol inWord

private theorem returnLedgerWord_exact (slot : Slot)
    (word : List WorkSymbol)
    (allowed :
      ∀ symbol, symbol ∈ word → LedgerReturnSymbol symbol)
    (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) word.length
        (configAtWord returnLedgerState left (word ++ right)) =
      some (configAtWord returnLedgerState
        (word.reverse ++ left) right) := by
  exact scanRightExact slot returnLedgerState
    LedgerReturnSymbol
    (fun leftSide head suffix headAllowed =>
      return_ledger_symbol_step slot head
        (match headAllowed with
         | Or.inl payload =>
             match payload with
             | Or.inl unit => Or.inl unit
             | Or.inr rest =>
                 match rest with
                 | Or.inl separator => Or.inr (Or.inl separator)
                 | Or.inr blank =>
                     Or.inr (Or.inr (Or.inl blank))
         | Or.inr boundary =>
             Or.inr (Or.inr (Or.inr boundary)))
        leftSide suffix)
    word right left allowed

private theorem scratchWord_return_allowed
    (units reserve : Nat) :
    ∀ symbol, symbol ∈ (scratchWord units reserve).reverse →
      PayloadSymbol symbol := by
  intro symbol found
  rw [List.mem_reverse] at found
  unfold scratchWord at found
  rw [List.mem_append] at found
  rcases found with inUnits | inTail
  · exact Or.inl (List.eq_of_mem_replicate inUnits)
  · cases inTail with
    | head => exact Or.inr (Or.inl rfl)
    | tail _ inBlanks =>
        exact Or.inr (Or.inr
          (List.eq_of_mem_replicate inBlanks))

private theorem returnScratch_exact (slot : Slot)
    (units reserve : Nat) (left right : List WorkSymbol) :
    workRunExact? (machineFor slot)
        (scratchWord units reserve).length
        (configAtWord returnScratchState left
          ((scratchWord units reserve).reverse ++ right)) =
      some (configAtWord returnScratchState
        (scratchWord units reserve ++ left) right) := by
  have scanned := scanRightExact slot returnScratchState
    PayloadSymbol
    (fun leftSide head suffix allowed =>
      return_scratch_symbol_step slot head allowed leftSide suffix)
    (scratchWord units reserve).reverse right left
    (scratchWord_return_allowed units reserve)
  simpa using scanned

/-! ### Exact selected-slot trace -/

private def coreEntryConfiguration (slot : Slot)
    (scratchUnits scratchReserve : Nat)
    (priorCells : List SlotCell) (value remaining : Nat)
    (outerLeft : List WorkSymbol)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord (startState slot)
    (sourceLeftBoundary ::
      (scratchWord scratchUnits scratchReserve ++
        ledgerBoundary ::
          (cellsWord priorCells ++
            ({ value := value, remaining := remaining + 1 } :
              SlotCell).word ++ outerLeft)))
    (sourceHead :: sourceTail ++ targetAndRight)

private def coreFinalConfiguration (_slot : Slot)
    (scratchUnits scratchReserve : Nat)
    (priorCells : List SlotCell) (value remaining : Nat)
    (outerLeft : List WorkSymbol)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord acceptState
    (sourceLeftBoundary ::
      (scratchWord scratchUnits scratchReserve ++
        ledgerBoundary ::
          (cellsWord priorCells ++
            ({ value := value + 1, remaining := remaining } :
              SlotCell).word ++ outerLeft)))
    (sourceHead :: sourceTail ++ targetAndRight)

private def coreWorkSteps
    (scratchUnits scratchReserve : Nat)
    (priorCells : List SlotCell) (value : Nat) : Nat :=
  2 *
      (scratchUnits + scratchReserve +
        (cellsWord priorCells).length + value) +
    12

private theorem core_exact (slot : Slot)
    (scratchUnits scratchReserve : Nat)
    (priorCells : List SlotCell) (value remaining : Nat)
    (outerLeft : List WorkSymbol)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight : List WorkSymbol)
    (prefixLength : priorCells.length = slotCode slot)
    (sourceAllowed :
      TargetEmitter.PackedSymbol sourceHead ∨
        sourceHead = cursorMarker) :
    workRunExact? (machineFor slot)
        (coreWorkSteps scratchUnits scratchReserve priorCells value)
        (coreEntryConfiguration slot scratchUnits scratchReserve
          priorCells value remaining outerLeft sourceHead sourceTail
          targetAndRight) =
      some (coreFinalConfiguration slot scratchUnits scratchReserve
        priorCells value remaining outerLeft sourceHead sourceTail
        targetAndRight) := by
  let sourceWord := sourceHead :: sourceTail ++ targetAndRight
  let scratch := scratchWord scratchUnits scratchReserve
  let prefixWord := cellsWord priorCells
  let selectedBefore : SlotCell :=
    { value := value, remaining := remaining + 1 }
  let selectedAfter : SlotCell :=
    { value := value + 1, remaining := remaining }
  let afterSource :=
    configAtLeftWord (boundaryState slot)
      (sourceLeftBoundary ::
        scratch ++
          ledgerBoundary ::
            (prefixWord ++ selectedBefore.word ++ outerLeft))
      sourceWord
  let afterBoundary :=
    configAtLeftWord (scratchUnitsState slot)
      (scratch ++
        ledgerBoundary ::
          (prefixWord ++ selectedBefore.word ++ outerLeft))
      (sourceLeftBoundary :: sourceWord)
  let atScratchSeparator :=
    configAtLeftWord (scratchUnitsState slot)
      (unarySeparator ::
        List.replicate scratchReserve WorkSymbol.blank ++
          ledgerBoundary ::
            (prefixWord ++ selectedBefore.word ++ outerLeft))
      (List.replicate scratchUnits unaryUnit ++
        sourceLeftBoundary :: sourceWord)
  let afterScratchSeparator :=
    configAtLeftWord (scratchReserveState slot)
      (List.replicate scratchReserve WorkSymbol.blank ++
        ledgerBoundary ::
          (prefixWord ++ selectedBefore.word ++ outerLeft))
      (unarySeparator ::
        List.replicate scratchUnits unaryUnit ++
          sourceLeftBoundary :: sourceWord)
  let atLedger :=
    configAtLeftWord (scratchReserveState slot)
      (ledgerBoundary ::
        (prefixWord ++ selectedBefore.word ++ outerLeft))
      (scratch.reverse ++ sourceLeftBoundary :: sourceWord)
  let afterLedger :=
    configAtLeftWord (seekSlotState (slotCode slot))
      (prefixWord ++ selectedBefore.word ++ outerLeft)
      (ledgerBoundary :: scratch.reverse ++
        sourceLeftBoundary :: sourceWord)
  let afterSelectedBoundary :=
    configAtLeftWord selectedUnitsState
      (selectedBefore.payload ++ outerLeft)
      (slotBoundary :: prefixWord.reverse ++ ledgerBoundary ::
        scratch.reverse ++ sourceLeftBoundary :: sourceWord)
  let atSelectedSeparator :=
    configAtLeftWord selectedUnitsState
      (unarySeparator ::
        List.replicate (remaining + 1) WorkSymbol.blank ++ outerLeft)
      (List.replicate value unaryUnit ++
        slotBoundary :: prefixWord.reverse ++ ledgerBoundary ::
          scratch.reverse ++ sourceLeftBoundary :: sourceWord)
  let atBlank :=
    configAtLeftWord writeSeparatorState
      (List.replicate (remaining + 1) WorkSymbol.blank ++ outerLeft)
      (unaryUnit :: List.replicate value unaryUnit ++
        slotBoundary :: prefixWord.reverse ++ ledgerBoundary ::
          scratch.reverse ++ sourceLeftBoundary :: sourceWord)
  let returnWord :=
    List.replicate (value + 1) unaryUnit ++
      slotBoundary :: prefixWord.reverse
  let returning :=
    configAtWord returnLedgerState
      (unarySeparator ::
        List.replicate remaining WorkSymbol.blank ++ outerLeft)
      (returnWord ++ ledgerBoundary :: scratch.reverse ++
        sourceLeftBoundary :: sourceWord)
  let atReturnLedger :=
    configAtWord returnLedgerState
      (prefixWord ++ selectedAfter.word ++ outerLeft)
      (ledgerBoundary :: scratch.reverse ++
        sourceLeftBoundary :: sourceWord)
  let atReturnScratch :=
    configAtWord returnScratchState
      (ledgerBoundary ::
        prefixWord ++ selectedAfter.word ++ outerLeft)
      (scratch.reverse ++ sourceLeftBoundary :: sourceWord)
  let atSourceBoundary :=
    configAtWord returnScratchState
      (scratch ++ ledgerBoundary ::
        prefixWord ++ selectedAfter.word ++ outerLeft)
      (sourceLeftBoundary :: sourceWord)
  have hSource :
      workRunExact? (machineFor slot) 1
          (coreEntryConfiguration slot scratchUnits scratchReserve
            priorCells value remaining outerLeft sourceHead sourceTail
            targetAndRight) =
        some afterSource := by
    apply exactRun_one slot
    simpa [coreEntryConfiguration, afterSource, sourceWord, scratch,
      prefixWord, selectedBefore, List.append_assoc] using
      source_step slot sourceHead sourceAllowed
        (sourceLeftBoundary ::
          scratch ++ ledgerBoundary ::
            (prefixWord ++ selectedBefore.word ++ outerLeft))
        (sourceTail ++ targetAndRight)
  have hBoundary :
      workRunExact? (machineFor slot) 1 afterSource =
        some afterBoundary := by
    apply exactRun_one slot
    simpa [afterSource, afterBoundary, List.append_assoc] using
      boundary_step slot
        (scratch ++ ledgerBoundary ::
          (prefixWord ++ selectedBefore.word ++ outerLeft))
        sourceWord
  have hScratchUnits :
      workRunExact? (machineFor slot) scratchUnits afterBoundary =
        some atScratchSeparator := by
    simpa [afterBoundary, atScratchSeparator, scratch,
      scratchWord, List.append_assoc] using
      scratchUnits_exact slot scratchUnits
        (unarySeparator ::
          List.replicate scratchReserve WorkSymbol.blank ++
            ledgerBoundary ::
              (prefixWord ++ selectedBefore.word ++ outerLeft))
        (sourceLeftBoundary :: sourceWord)
  have hScratchSeparator :
      workRunExact? (machineFor slot) 1 atScratchSeparator =
        some afterScratchSeparator := by
    apply exactRun_one slot
    simpa [atScratchSeparator, afterScratchSeparator,
      List.append_assoc] using
      scratch_separator_step slot
        (List.replicate scratchReserve WorkSymbol.blank ++
          ledgerBoundary ::
            (prefixWord ++ selectedBefore.word ++ outerLeft))
        (List.replicate scratchUnits unaryUnit ++
          sourceLeftBoundary :: sourceWord)
  have hScratchReserve :
      workRunExact? (machineFor slot) scratchReserve
          afterScratchSeparator =
        some atLedger := by
    have scanned :=
      scratchBlanks_exact slot scratchReserve
        (ledgerBoundary ::
          (prefixWord ++ selectedBefore.word ++ outerLeft))
        (unarySeparator ::
          List.replicate scratchUnits unaryUnit ++
            sourceLeftBoundary :: sourceWord)
    simpa [afterScratchSeparator, atLedger, scratch,
      scratchWord, List.reverse_append, List.append_assoc] using scanned
  have hLedger :
      workRunExact? (machineFor slot) 1 atLedger =
        some afterLedger := by
    apply exactRun_one slot
    simpa [atLedger, afterLedger, List.append_assoc] using
      ledger_boundary_step slot
        (prefixWord ++ selectedBefore.word ++ outerLeft)
        (scratch.reverse ++ sourceLeftBoundary :: sourceWord)
  have hSelect :
      workRunExact? (machineFor slot) (prefixWord.length + 1)
          afterLedger =
        some afterSelectedBoundary := by
    have prefixLe : priorCells.length ≤ 5 := by
      rw [prefixLength]
      exact slotCode_le_five slot
    have selected := selectPrefix_exact slot priorCells prefixLe
      (selectedBefore.payload ++ outerLeft)
      (ledgerBoundary :: scratch.reverse ++
        sourceLeftBoundary :: sourceWord)
    simpa [afterLedger, afterSelectedBoundary, prefixWord,
      prefixLength, selectedBefore, SlotCell.word,
      List.append_assoc] using selected
  have hSelectedUnits :
      workRunExact? (machineFor slot) value
          afterSelectedBoundary =
        some atSelectedSeparator := by
    have scanned := selectedUnits_exact slot value
      (unarySeparator ::
        List.replicate (remaining + 1) WorkSymbol.blank ++ outerLeft)
      (slotBoundary :: prefixWord.reverse ++ ledgerBoundary ::
        scratch.reverse ++ sourceLeftBoundary :: sourceWord)
    simpa [afterSelectedBoundary, atSelectedSeparator,
      selectedBefore, SlotCell.payload, List.append_assoc] using scanned
  have hSelectedSeparator :
      workRunExact? (machineFor slot) 1 atSelectedSeparator =
        some atBlank := by
    apply exactRun_one slot
    simpa [atSelectedSeparator, atBlank, List.append_assoc] using
      selected_separator_step slot
        (List.replicate (remaining + 1) WorkSymbol.blank ++ outerLeft)
        (List.replicate value unaryUnit ++
          slotBoundary :: prefixWord.reverse ++ ledgerBoundary ::
            scratch.reverse ++ sourceLeftBoundary :: sourceWord)
  have hWrite :
      workRunExact? (machineFor slot) 1 atBlank =
        some returning := by
    apply exactRun_one slot
    have written := write_separator_step slot
      (List.replicate remaining WorkSymbol.blank ++ outerLeft)
      (unaryUnit :: List.replicate value unaryUnit ++
        slotBoundary :: prefixWord.reverse ++ ledgerBoundary ::
          scratch.reverse ++ sourceLeftBoundary :: sourceWord)
    simpa [atBlank, returning, returnWord,
      List.replicate_succ, Nat.add_comm, List.append_assoc] using written
  have returnAllowed :
      ∀ symbol, symbol ∈ returnWord →
        LedgerReturnSymbol symbol := by
    intro symbol found
    unfold returnWord at found
    rw [List.mem_append] at found
    rcases found with inUnits | inRest
    · exact Or.inl (Or.inl
        (List.eq_of_mem_replicate inUnits))
    · cases inRest with
      | head => exact Or.inr rfl
      | tail _ inPrefixReverse =>
          exact cellsWord_return_allowed priorCells symbol
            (List.mem_reverse.mp inPrefixReverse)
  have hReturnLedger :
      workRunExact? (machineFor slot) returnWord.length returning =
        some atReturnLedger := by
    have scanned := returnLedgerWord_exact slot returnWord
      returnAllowed
      (unarySeparator ::
        List.replicate remaining WorkSymbol.blank ++ outerLeft)
      (ledgerBoundary :: scratch.reverse ++
        sourceLeftBoundary :: sourceWord)
    simpa [returning, atReturnLedger, returnWord, prefixWord,
      selectedAfter, SlotCell.word, SlotCell.payload,
      List.reverse_append, List.append_assoc] using scanned
  have hReturnLedgerBoundary :
      workRunExact? (machineFor slot) 1 atReturnLedger =
        some atReturnScratch := by
    apply exactRun_one slot
    simpa [atReturnLedger, atReturnScratch, List.append_assoc] using
      return_ledger_boundary_step slot
        (prefixWord ++ selectedAfter.word ++ outerLeft)
        (scratch.reverse ++ sourceLeftBoundary :: sourceWord)
  have hReturnScratch :
      workRunExact? (machineFor slot) scratch.length atReturnScratch =
        some atSourceBoundary := by
    have scanned := returnScratch_exact slot
      scratchUnits scratchReserve
      (ledgerBoundary ::
        prefixWord ++ selectedAfter.word ++ outerLeft)
      (sourceLeftBoundary :: sourceWord)
    simpa [atReturnScratch, atSourceBoundary, scratch,
      List.append_assoc] using scanned
  have hReturnSourceBoundary :
      workRunExact? (machineFor slot) 1 atSourceBoundary =
        some (coreFinalConfiguration slot scratchUnits scratchReserve
          priorCells value remaining outerLeft sourceHead sourceTail
          targetAndRight) := by
    apply exactRun_one slot
    simpa [atSourceBoundary, coreFinalConfiguration, sourceWord,
      scratch, prefixWord, selectedAfter, List.append_assoc] using
      return_source_boundary_step slot
        (scratch ++ ledgerBoundary ::
          prefixWord ++ selectedAfter.word ++ outerLeft)
        sourceWord
  have h01 := exactRun_add slot 1 1 _ _ _
    hSource hBoundary
  have h02 := exactRun_add slot 2 scratchUnits _ _ _
    h01 hScratchUnits
  have h03 := exactRun_add slot (2 + scratchUnits) 1 _ _ _
    h02 hScratchSeparator
  have h04 := exactRun_add slot
    (2 + scratchUnits + 1) scratchReserve _ _ _
    h03 hScratchReserve
  have h05 := exactRun_add slot
    (2 + scratchUnits + 1 + scratchReserve) 1 _ _ _
    h04 hLedger
  have h06 := exactRun_add slot
    (2 + scratchUnits + 1 + scratchReserve + 1)
    (prefixWord.length + 1) _ _ _ h05 hSelect
  have h08 := exactRun_add slot
    (2 + scratchUnits + 1 + scratchReserve + 1 +
      prefixWord.length + 1) value _ _ _ h06 hSelectedUnits
  have h09 := exactRun_add slot
    (2 + scratchUnits + 1 + scratchReserve + 1 +
      prefixWord.length + 1 + value) 1 _ _ _
    h08 hSelectedSeparator
  have h10 := exactRun_add slot
    (2 + scratchUnits + 1 + scratchReserve + 1 +
      prefixWord.length + 1 + value + 1) 1 _ _ _ h09 hWrite
  have h11 := exactRun_add slot
    (2 + scratchUnits + 1 + scratchReserve + 1 +
      prefixWord.length + 1 + value + 1 + 1)
    returnWord.length _ _ _ h10 hReturnLedger
  have h12 := exactRun_add slot
    (2 + scratchUnits + 1 + scratchReserve + 1 +
      prefixWord.length + 1 + value + 1 + 1 +
        returnWord.length) 1 _ _ _ h11 hReturnLedgerBoundary
  have h13 := exactRun_add slot
    (2 + scratchUnits + 1 + scratchReserve + 1 +
      prefixWord.length + 1 + value + 1 + 1 +
        returnWord.length + 1)
    scratch.length _ _ _ h12 hReturnScratch
  have complete := exactRun_add slot
    (2 + scratchUnits + 1 + scratchReserve + 1 +
      prefixWord.length + 1 + value + 1 + 1 +
        returnWord.length + 1 + scratch.length)
    1 _ _ _ h13 hReturnSourceBoundary
  have returnWordLength :
      returnWord.length = value + prefixWord.length + 2 := by
    simp [returnWord]
    omega
  have scratchLength :
      scratch.length = scratchUnits + scratchReserve + 1 := by
    simp [scratch, scratchWord]
    omega
  have steps :
      2 + scratchUnits + 1 + scratchReserve + 1 +
          prefixWord.length + 1 + value + 1 + 1 +
          returnWord.length + 1 + scratch.length + 1 =
        coreWorkSteps scratchUnits scratchReserve priorCells value := by
    rw [returnWordLength, scratchLength]
    unfold coreWorkSteps prefixWord
    omega
  rw [steps] at complete
  exact complete

/-! ### Public six-slot endpoint -/

def entryConfiguration (slot : Slot)
    (scratchUnits scratchReserve : Nat) (bank : SlotBank)
    (outsideLeft : List WorkSymbol)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord (startState slot)
    (sourceLeftBoundary ::
      (scratchWord scratchUnits scratchReserve ++
        ledgerBoundary :: (bank.word ++ outsideLeft)))
    (sourceHead :: sourceTail ++ targetAndRight)

def finalConfiguration (slot : Slot)
    (scratchUnits scratchReserve : Nat) (bank : SlotBank)
    (outsideLeft : List WorkSymbol)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord acceptState
    (sourceLeftBoundary ::
      (scratchWord scratchUnits scratchReserve ++
        ledgerBoundary ::
          ((bank.increment slot).word ++ outsideLeft)))
    (sourceHead :: sourceTail ++ targetAndRight)

def workSteps (slot : Slot)
    (scratchUnits scratchReserve : Nat)
    (bank : SlotBank) : Nat :=
  2 *
      (scratchUnits + scratchReserve +
        (bank.prefixWord slot).length +
        (bank.selected slot).value) +
    12

theorem workSteps_evaluated (slot : Slot)
    (scratchUnits scratchReserve : Nat) (bank : SlotBank) :
    workSteps slot scratchUnits scratchReserve bank =
      2 * scratchUnits + 2 * scratchReserve +
        2 * (bank.prefixWord slot).length +
        2 * (bank.selected slot).value + 12 := by
  unfold workSteps
  omega

theorem prefixWord_length_le_bankWord
    (slot : Slot) (bank : SlotBank) :
    (bank.prefixWord slot).length ≤ bank.word.length := by
  have decomposition := congrArg List.length
    (bankWord_decompose slot bank)
  simp only [List.length_append] at decomposition
  omega

def polynomialWorkBound (slot : Slot)
    (scratchUnits scratchReserve : Nat) (bank : SlotBank) : Nat :=
  2 *
      (scratchUnits + scratchReserve + bank.word.length +
        (bank.selected slot).value) +
    12

theorem workSteps_le_polynomialWorkBound (slot : Slot)
    (scratchUnits scratchReserve : Nat) (bank : SlotBank) :
    workSteps slot scratchUnits scratchReserve bank ≤
      polynomialWorkBound slot scratchUnits scratchReserve bank := by
  unfold workSteps polynomialWorkBound
  have prefixLe := prefixWord_length_le_bankWord slot bank
  omega

/-- Exact bounded slot increment.  Positivity of the selected blank remainder
is the capacity precondition; the table itself observes the blank before
writing and therefore fails closed if the precondition is false on tape. -/
theorem exact (slot : Slot)
    (scratchUnits scratchReserve : Nat) (bank : SlotBank)
    (outsideLeft : List WorkSymbol)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight : List WorkSymbol)
    (capacityAvailable : 0 < (bank.selected slot).remaining)
    (sourceAllowed :
      TargetEmitter.PackedSymbol sourceHead ∨
        sourceHead = cursorMarker) :
    workRunExact? (machineFor slot)
        (workSteps slot scratchUnits scratchReserve bank)
        (entryConfiguration slot scratchUnits scratchReserve bank
          outsideLeft sourceHead sourceTail targetAndRight) =
      some (finalConfiguration slot scratchUnits scratchReserve bank
        outsideLeft sourceHead sourceTail targetAndRight) := by
  let selected := bank.selected slot
  let remaining := selected.remaining - 1
  change 0 < selected.remaining at capacityAvailable
  have remainingEq :
      selected.remaining = remaining + 1 := by
    unfold remaining
    omega
  have core := core_exact slot scratchUnits scratchReserve
    (bank.prefixCells slot) selected.value remaining
    (bank.suffixWord slot ++ outsideLeft)
    sourceHead sourceTail targetAndRight
    (prefixCells_length slot bank) sourceAllowed
  have entryEq :
      coreEntryConfiguration slot scratchUnits scratchReserve
          (bank.prefixCells slot) selected.value remaining
          (bank.suffixWord slot ++ outsideLeft)
          sourceHead sourceTail targetAndRight =
        entryConfiguration slot scratchUnits scratchReserve bank
          outsideLeft sourceHead sourceTail targetAndRight := by
    unfold coreEntryConfiguration entryConfiguration
    rw [bankWord_decompose slot bank]
    simp [selected, remainingEq, SlotCell.word, SlotCell.payload,
      SlotBank.prefixWord, List.append_assoc]
  have finalEq :
      coreFinalConfiguration slot scratchUnits scratchReserve
          (bank.prefixCells slot) selected.value remaining
          (bank.suffixWord slot ++ outsideLeft)
          sourceHead sourceTail targetAndRight =
        finalConfiguration slot scratchUnits scratchReserve bank
          outsideLeft sourceHead sourceTail targetAndRight := by
    unfold coreFinalConfiguration finalConfiguration
    rw [bankWord_decompose slot (bank.increment slot)]
    rw [increment_preserves_unselected_prefix,
      increment_preserves_unselected_suffix, increment_selected]
    simp [selected, remaining, SlotCell.increment,
      SlotCell.word, SlotCell.payload, SlotBank.prefixWord,
      List.append_assoc]
  have stepsEq :
      coreWorkSteps scratchUnits scratchReserve
          (bank.prefixCells slot) selected.value =
        workSteps slot scratchUnits scratchReserve bank := by
    rfl
  rw [stepsEq, entryEq, finalEq] at core
  exact core

theorem final_halted (slot : Slot)
    (scratchUnits scratchReserve : Nat) (bank : SlotBank)
    (outsideLeft : List WorkSymbol)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight : List WorkSymbol) :
    (machineFor slot).isHalted
      (finalConfiguration slot scratchUnits scratchReserve bank
        outsideLeft sourceHead sourceTail targetAndRight) = true := by
  rfl

theorem final_source_preserved (slot : Slot)
    (scratchUnits scratchReserve : Nat) (bank : SlotBank)
    (outsideLeft : List WorkSymbol)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight : List WorkSymbol) :
    let final :=
      finalConfiguration slot scratchUnits scratchReserve bank
        outsideLeft sourceHead sourceTail targetAndRight
    final.tape.head :: final.tape.right =
      sourceHead :: sourceTail ++ targetAndRight := by
  rfl

theorem final_left_workspace (slot : Slot)
    (scratchUnits scratchReserve : Nat) (bank : SlotBank)
    (outsideLeft : List WorkSymbol)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight : List WorkSymbol) :
    (finalConfiguration slot scratchUnits scratchReserve bank
      outsideLeft sourceHead sourceTail targetAndRight).tape.left =
        sourceLeftBoundary ::
          (scratchWord scratchUnits scratchReserve ++
            ledgerBoundary ::
              ((bank.increment slot).word ++ outsideLeft)) := by
  rfl

theorem selected_value_incremented (slot : Slot) (bank : SlotBank) :
    ((bank.increment slot).selected slot).value =
      (bank.selected slot).value + 1 := by
  rw [increment_selected]
  rfl

theorem selected_remaining_decremented
    (slot : Slot) (bank : SlotBank) :
    ((bank.increment slot).selected slot).remaining =
      (bank.selected slot).remaining - 1 := by
  rw [increment_selected]
  rfl

/-! ### Fail-closed malformed layouts and exhausted capacity -/

set_option maxRecDepth 200000 in
private theorem find_scratch_units_malformed (slot : Slot)
    (symbol : WorkSymbol)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    findWorkRule rules (scratchUnitsState slot) symbol =
      some (literalRule (scratchUnitsState slot) symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases slot <;> cases first <;> cases second
  all_goals first
    | exact (notUnit rfl).elim
    | exact (notSeparator rfl).elim
    | decide

set_option maxRecDepth 200000 in
private theorem find_scratch_reserve_malformed (slot : Slot)
    (symbol : WorkSymbol)
    (notBlank : symbol ≠ WorkSymbol.blank)
    (notLedger : symbol ≠ ledgerBoundary) :
    findWorkRule rules (scratchReserveState slot) symbol =
      some (literalRule (scratchReserveState slot) symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases slot <;> cases first <;> cases second
  all_goals first
    | exact (notBlank rfl).elim
    | exact (notLedger rfl).elim
    | decide

set_option maxRecDepth 200000 in
private theorem find_seek_malformed (remaining : Nat)
    (symbol : WorkSymbol) (remainingLe : remaining ≤ 5)
    (notBoundary : symbol ≠ slotBoundary) :
    findWorkRule rules (seekSlotState remaining) symbol =
      some (literalRule (seekSlotState remaining) symbol
        deadState symbol .stay) := by
  have possibilities :
      remaining = 0 ∨ remaining = 1 ∨ remaining = 2 ∨
        remaining = 3 ∨ remaining = 4 ∨ remaining = 5 := by
    omega
  rcases possibilities with
    first | second | third | fourth | fifth | sixth
  all_goals subst remaining
  all_goals rcases symbol with ⟨left, right⟩
  all_goals cases left <;> cases right
  all_goals first
    | exact (notBoundary rfl).elim
    | decide

set_option maxRecDepth 200000 in
private theorem find_skip_units_malformed (remaining : Nat)
    (symbol : WorkSymbol) (remainingLe : remaining ≤ 4)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    findWorkRule rules (skipUnitsState remaining) symbol =
      some (literalRule (skipUnitsState remaining) symbol
        deadState symbol .stay) := by
  have possibilities :
      remaining = 0 ∨ remaining = 1 ∨ remaining = 2 ∨
        remaining = 3 ∨ remaining = 4 := by
    omega
  rcases possibilities with first | second | third | fourth | fifth
  all_goals subst remaining
  all_goals rcases symbol with ⟨left, right⟩
  all_goals cases left <;> cases right
  all_goals first
    | exact (notUnit rfl).elim
    | exact (notSeparator rfl).elim
    | decide

set_option maxRecDepth 200000 in
private theorem find_skip_reserve_malformed (remaining : Nat)
    (symbol : WorkSymbol) (remainingLe : remaining ≤ 4)
    (notBlank : symbol ≠ WorkSymbol.blank)
    (notBoundary : symbol ≠ slotBoundary) :
    findWorkRule rules (skipReserveState remaining) symbol =
      some (literalRule (skipReserveState remaining) symbol
        deadState symbol .stay) := by
  have possibilities :
      remaining = 0 ∨ remaining = 1 ∨ remaining = 2 ∨
        remaining = 3 ∨ remaining = 4 := by
    omega
  rcases possibilities with first | second | third | fourth | fifth
  all_goals subst remaining
  all_goals rcases symbol with ⟨left, right⟩
  all_goals cases left <;> cases right
  all_goals first
    | exact (notBlank rfl).elim
    | exact (notBoundary rfl).elim
    | decide

set_option maxRecDepth 200000 in
private theorem find_selected_malformed (symbol : WorkSymbol)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    findWorkRule rules selectedUnitsState symbol =
      some (literalRule selectedUnitsState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  all_goals first
    | exact (notUnit rfl).elim
    | exact (notSeparator rfl).elim
    | decide

set_option maxRecDepth 200000 in
private theorem find_write_occupied (symbol : WorkSymbol)
    (occupied : symbol ≠ WorkSymbol.blank) :
    findWorkRule rules writeSeparatorState symbol =
      some (literalRule writeSeparatorState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · exact (occupied rfl).elim
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

/-- A malformed unary scratch payload fails before reaching the ledger. -/
theorem malformed_scratch_units_enters_dead (slot : Slot)
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    workStep? (machineFor slot)
        (configAtLeftWord (scratchUnitsState slot)
          (symbol :: left) right) =
      some (configAtLeftWord deadState
        (symbol :: left) right) := by
  exact left_dead_step slot (scratchUnitsState slot)
    symbol left right (by cases slot <;> rfl)
    (find_scratch_units_malformed slot symbol
      notUnit notSeparator)

/-- Scratch reserve scanning accepts only blanks and the pinned ledger
boundary. -/
theorem malformed_scratch_reserve_enters_dead (slot : Slot)
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notBlank : symbol ≠ WorkSymbol.blank)
    (notLedger : symbol ≠ ledgerBoundary) :
    workStep? (machineFor slot)
        (configAtLeftWord (scratchReserveState slot)
          (symbol :: left) right) =
      some (configAtLeftWord deadState
        (symbol :: left) right) := by
  exact left_dead_step slot (scratchReserveState slot)
    symbol left right (by cases slot <;> rfl)
    (find_scratch_reserve_malformed slot symbol
      notBlank notLedger)

/-- Before a slot is selected, the finite selector accepts only a canonical
slot boundary.  Any payload symbol at that phase witnesses a malformed slot
bank and enters the dead state. -/
theorem malformed_slot_boundary_enters_dead (slot : Slot)
    (remaining : Nat) (symbol : WorkSymbol)
    (left right : List WorkSymbol)
    (remainingLe : remaining ≤ 5)
    (notBoundary : symbol ≠ slotBoundary) :
    workStep? (machineFor slot)
        (configAtLeftWord (seekSlotState remaining)
          (symbol :: left) right) =
      some (configAtLeftWord deadState
        (symbol :: left) right) := by
  apply left_dead_step slot (seekSlotState remaining)
    symbol left right
  · have acceptNe :
        seekSlotState remaining ≠ acceptState := by
      unfold seekSlotState acceptState
      omega
    have rejectNe :
        seekSlotState remaining ≠ rejectState := by
      unfold seekSlotState rejectState
      omega
    simp [WorkMachine.isHalted, machineFor, configAtLeftWord,
      TargetEmitter.configAtLeftWord, acceptNe, rejectNe]
  · exact find_seek_malformed remaining symbol
      remainingLe notBoundary

/-- A skipped slot must have a unary run immediately after its boundary,
followed by exactly one separator. -/
theorem malformed_skipped_units_enters_dead (slot : Slot)
    (remaining : Nat) (symbol : WorkSymbol)
    (left right : List WorkSymbol)
    (remainingLe : remaining ≤ 4)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    workStep? (machineFor slot)
        (configAtLeftWord (skipUnitsState remaining)
          (symbol :: left) right) =
      some (configAtLeftWord deadState
        (symbol :: left) right) := by
  apply left_dead_step slot (skipUnitsState remaining)
    symbol left right
  · have acceptNe :
        skipUnitsState remaining ≠ acceptState := by
      unfold skipUnitsState acceptState
      omega
    have rejectNe :
        skipUnitsState remaining ≠ rejectState := by
      unfold skipUnitsState rejectState
      omega
    simp [WorkMachine.isHalted, machineFor, configAtLeftWord,
      TargetEmitter.configAtLeftWord, acceptNe, rejectNe]
  · exact find_skip_units_malformed remaining symbol
      remainingLe notUnit notSeparator

/-- After a skipped slot's separator, only reserved blanks and the next slot
boundary are canonical. -/
theorem malformed_skipped_reserve_enters_dead (slot : Slot)
    (remaining : Nat) (symbol : WorkSymbol)
    (left right : List WorkSymbol)
    (remainingLe : remaining ≤ 4)
    (notBlank : symbol ≠ WorkSymbol.blank)
    (notBoundary : symbol ≠ slotBoundary) :
    workStep? (machineFor slot)
        (configAtLeftWord (skipReserveState remaining)
          (symbol :: left) right) =
      some (configAtLeftWord deadState
        (symbol :: left) right) := by
  apply left_dead_step slot (skipReserveState remaining)
    symbol left right
  · have acceptNe :
        skipReserveState remaining ≠ acceptState := by
      unfold skipReserveState acceptState
      omega
    have rejectNe :
        skipReserveState remaining ≠ rejectState := by
      unfold skipReserveState rejectState
      omega
    simp [WorkMachine.isHalted, machineFor, configAtLeftWord,
      TargetEmitter.configAtLeftWord, acceptNe, rejectNe]
  · exact find_skip_reserve_malformed remaining symbol
      remainingLe notBlank notBoundary

/-- The selected unary payload contains only units followed by its separator;
any other observed symbol enters the dead state. -/
theorem malformed_selected_payload_enters_dead (slot : Slot)
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    workStep? (machineFor slot)
        (configAtLeftWord selectedUnitsState
          (symbol :: left) right) =
      some (configAtLeftWord deadState
        (symbol :: left) right) := by
  exact left_dead_step slot selectedUnitsState
    symbol left right (by rfl)
    (find_selected_malformed symbol notUnit notSeparator)

/-- The separator moves only into a literal blank.  Zero remaining capacity,
or any occupied cell after the separator, is observed without overwrite and
enters the ruleless dead state. -/
theorem exhausted_capacity_enters_dead (slot : Slot)
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (occupied : symbol ≠ WorkSymbol.blank) :
    workStep? (machineFor slot)
        (configAtLeftWord writeSeparatorState
          (symbol :: left) right) =
      some (configAtLeftWord deadState
        (symbol :: left) right) := by
  exact left_dead_step slot writeSeparatorState
    symbol left right (by rfl)
    (find_write_occupied symbol occupied)

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

end PNP.Concrete.LockedNAND.TargetEmitterSlotIncrement
