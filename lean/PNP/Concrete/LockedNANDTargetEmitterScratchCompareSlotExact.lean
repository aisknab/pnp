/-
Copyright (c) 2026 PNP Labs.

Exact traces for the literal scratch/ledger comparison controller.
-/

import PNP.Concrete.LockedNANDTargetEmitterScratchCompareSlot
import PNP.Concrete.PipelineMachineSimulation
import PNP.Concrete.TapeBlankEquivalence

namespace PNP.Concrete.LockedNAND.TargetEmitterScratchCompareSlot

open PNP.Concrete

private def literalRule (source : Nat) (read : WorkSymbol)
    (target : Nat) (write : WorkSymbol) (move : HeadMove) :
    WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := write
    move := move }

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

def SourceAllowed (symbol : WorkSymbol) : Prop :=
  TargetEmitter.PackedSymbol symbol ∨ symbol = cursorMarker

def ScratchPayload (symbol : WorkSymbol) : Prop :=
  symbol = unaryUnit ∨ symbol = unarySeparator ∨
    symbol = WorkSymbol.blank

def SlotPayload (symbol : WorkSymbol) : Prop :=
  symbol = unaryUnit ∨ symbol = unarySeparator ∨
    symbol = WorkSymbol.blank ∨ symbol = selectedMark

private theorem remaining_cases (remaining : Nat)
    (remainingLe : remaining ≤ 5) :
    remaining = 0 ∨ remaining = 1 ∨ remaining = 2 ∨
      remaining = 3 ∨ remaining = 4 ∨ remaining = 5 := by
  omega

set_option maxRecDepth 1000000 in
private theorem find_start_source (slot : Slot)
    (symbol : WorkSymbol) (allowed : SourceAllowed symbol) :
    findWorkRule rules (startState slot) symbol =
      some (literalRule (startState slot) symbol
        (startState slot) symbol .left) := by
  rcases allowed with packed | cursor
  · cases slot <;> cases packed <;> decide
  · subst symbol
    cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_start_boundary (slot : Slot) :
    findWorkRule rules (startState slot) sourceLeftBoundary =
      some (literalRule (startState slot) sourceLeftBoundary
        (scratchState slot) sourceLeftBoundary .left) := by
  cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_scratch_unit (slot : Slot) :
    findWorkRule rules (scratchState slot) unaryUnit =
      some (literalRule (scratchState slot) unaryUnit
        (seekLedgerState slot) scratchMark .left) := by
  cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_scratch_separator (slot : Slot) :
    findWorkRule rules (scratchState slot) unarySeparator =
      some (literalRule (scratchState slot) unarySeparator
        (compareSeekLedgerState slot) unarySeparator .left) := by
  cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_seek_ledger_payload (slot : Slot)
    (symbol : WorkSymbol) (allowed : ScratchPayload symbol) :
    findWorkRule rules (seekLedgerState slot) symbol =
      some (literalRule (seekLedgerState slot) symbol
        (seekLedgerState slot) symbol .left) := by
  rcases allowed with unit | separator | blank
  all_goals subst symbol
  all_goals cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_seek_ledger_boundary (slot : Slot) :
    findWorkRule rules (seekLedgerState slot) ledgerBoundary =
      some (literalRule (seekLedgerState slot) ledgerBoundary
        (pairSeekSlotState slot (slotCode slot))
        ledgerBoundary .left) := by
  cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_pair_seek_payload (slot : Slot)
    (remaining : Nat) (symbol : WorkSymbol)
    (remainingLe : remaining ≤ 5)
    (allowed : SlotPayload symbol) :
    findWorkRule rules (pairSeekSlotState slot remaining) symbol =
      some (literalRule (pairSeekSlotState slot remaining) symbol
        (pairSeekSlotState slot remaining) symbol .left) := by
  rcases allowed with unit | separator | blank | mark
  all_goals subst symbol
  all_goals
    rcases remaining_cases remaining remainingLe with
      first | second | third | fourth | fifth | sixth
  all_goals subst remaining
  all_goals cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_pair_seek_boundary_positive (slot : Slot)
    (remaining : Nat) (positive : 0 < remaining)
    (remainingLe : remaining ≤ 5) :
    findWorkRule rules (pairSeekSlotState slot remaining) slotBoundary =
      some (literalRule (pairSeekSlotState slot remaining) slotBoundary
        (pairSeekSlotState slot (remaining - 1))
        slotBoundary .left) := by
  rcases remaining_cases remaining remainingLe with
    first | second | third | fourth | fifth | sixth
  · subst remaining
    contradiction
  all_goals subst remaining
  all_goals cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_pair_selected_boundary (slot : Slot) :
    findWorkRule rules (pairSeekSlotState slot 0) slotBoundary =
      some (literalRule (pairSeekSlotState slot 0) slotBoundary
        (selectedState slot) slotBoundary .left) := by
  cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_selected_mark (slot : Slot) :
    findWorkRule rules (selectedState slot) selectedMark =
      some (literalRule (selectedState slot) selectedMark
        (selectedState slot) selectedMark .left) := by
  cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_selected_unit (slot : Slot) :
    findWorkRule rules (selectedState slot) unaryUnit =
      some (literalRule (selectedState slot) unaryUnit
        (returnLedgerState slot) selectedMark .right) := by
  cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_return_ledger_payload (slot : Slot)
    (symbol : WorkSymbol) (allowed : ledgerPayload symbol) :
    findWorkRule rules (returnLedgerState slot) symbol =
      some (literalRule (returnLedgerState slot) symbol
        (returnLedgerState slot) symbol .right) := by
  rcases allowed with unit | separator | blank | boundary | mark
  all_goals subst symbol
  all_goals cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_return_ledger_boundary (slot : Slot) :
    findWorkRule rules (returnLedgerState slot) ledgerBoundary =
      some (literalRule (returnLedgerState slot) ledgerBoundary
        (returnScratchState slot) ledgerBoundary .right) := by
  cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_return_scratch_payload (slot : Slot)
    (symbol : WorkSymbol) (allowed : ScratchPayload symbol) :
    findWorkRule rules (returnScratchState slot) symbol =
      some (literalRule (returnScratchState slot) symbol
        (returnScratchState slot) symbol .right) := by
  rcases allowed with unit | separator | blank
  all_goals subst symbol
  all_goals cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_return_scratch_mark (slot : Slot) :
    findWorkRule rules (returnScratchState slot) scratchMark =
      some (literalRule (returnScratchState slot) scratchMark
        (scratchState slot) unaryUnit .left) := by
  cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_compare_seek_ledger_payload (slot : Slot)
    (symbol : WorkSymbol) (allowed : ScratchPayload symbol) :
    findWorkRule rules (compareSeekLedgerState slot) symbol =
      some (literalRule (compareSeekLedgerState slot) symbol
        (compareSeekLedgerState slot) symbol .left) := by
  rcases allowed with unit | separator | blank
  all_goals subst symbol
  all_goals cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_compare_seek_ledger_boundary (slot : Slot) :
    findWorkRule rules (compareSeekLedgerState slot) ledgerBoundary =
      some (literalRule (compareSeekLedgerState slot) ledgerBoundary
        (compareSeekSlotState slot (slotCode slot))
        ledgerBoundary .left) := by
  cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_compare_seek_payload (slot : Slot)
    (remaining : Nat) (symbol : WorkSymbol)
    (remainingLe : remaining ≤ 5)
    (allowed : SlotPayload symbol) :
    findWorkRule rules (compareSeekSlotState slot remaining) symbol =
      some (literalRule (compareSeekSlotState slot remaining) symbol
        (compareSeekSlotState slot remaining) symbol .left) := by
  rcases allowed with unit | separator | blank | mark
  all_goals subst symbol
  all_goals
    rcases remaining_cases remaining remainingLe with
      first | second | third | fourth | fifth | sixth
  all_goals subst remaining
  all_goals cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_compare_seek_boundary_positive (slot : Slot)
    (remaining : Nat) (positive : 0 < remaining)
    (remainingLe : remaining ≤ 5) :
    findWorkRule rules
        (compareSeekSlotState slot remaining) slotBoundary =
      some (literalRule
        (compareSeekSlotState slot remaining) slotBoundary
        (compareSeekSlotState slot (remaining - 1))
        slotBoundary .left) := by
  rcases remaining_cases remaining remainingLe with
    first | second | third | fourth | fifth | sixth
  · subst remaining
    contradiction
  all_goals subst remaining
  all_goals cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_compare_selected_boundary (slot : Slot) :
    findWorkRule rules
        (compareSeekSlotState slot 0) slotBoundary =
      some (literalRule
        (compareSeekSlotState slot 0) slotBoundary
        (compareSelectedState slot) slotBoundary .left) := by
  cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_compare_selected_mark (slot : Slot) :
    findWorkRule rules (compareSelectedState slot) selectedMark =
      some (literalRule (compareSelectedState slot) selectedMark
        (compareSelectedState slot) selectedMark .left) := by
  cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_compare_selected_unit (slot : Slot) :
    findWorkRule rules (compareSelectedState slot) unaryUnit =
      some (literalRule (compareSelectedState slot) unaryUnit
        restoreLessLedgerState unaryUnit .right) := by
  cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_compare_selected_separator (slot : Slot) :
    findWorkRule rules (compareSelectedState slot) unarySeparator =
      some (literalRule (compareSelectedState slot) unarySeparator
        restoreEqualLedgerState unarySeparator .right) := by
  cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_restore_ledger_mark (equal : Bool) :
    let state :=
      if equal then restoreEqualLedgerState
      else restoreLessLedgerState
    findWorkRule rules state selectedMark =
      some (literalRule state selectedMark state unaryUnit .right) := by
  cases equal <;> decide

set_option maxRecDepth 1000000 in
private theorem find_restore_ledger_payload (equal : Bool)
    (symbol : WorkSymbol)
    (allowed :
      symbol = unaryUnit ∨ symbol = unarySeparator ∨
        symbol = WorkSymbol.blank ∨ symbol = slotBoundary) :
    let state :=
      if equal then restoreEqualLedgerState
      else restoreLessLedgerState
    findWorkRule rules state symbol =
      some (literalRule state symbol state symbol .right) := by
  rcases allowed with unit | separator | blank | boundary
  all_goals subst symbol
  all_goals cases equal <;> decide

set_option maxRecDepth 1000000 in
private theorem find_restore_ledger_boundary (equal : Bool) :
    let state :=
      if equal then restoreEqualLedgerState
      else restoreLessLedgerState
    let target :=
      if equal then restoreEqualScratchState
      else restoreLessScratchState
    findWorkRule rules state ledgerBoundary =
      some (literalRule state ledgerBoundary target
        ledgerBoundary .right) := by
  cases equal <;> decide

set_option maxRecDepth 1000000 in
private theorem find_restore_scratch_payload (equal : Bool)
    (symbol : WorkSymbol) (allowed : ScratchPayload symbol) :
    let state :=
      if equal then restoreEqualScratchState
      else restoreLessScratchState
    findWorkRule rules state symbol =
      some (literalRule state symbol state symbol .right) := by
  rcases allowed with unit | separator | blank
  all_goals subst symbol
  all_goals cases equal <;> decide

set_option maxRecDepth 1000000 in
private theorem find_restore_source_boundary (equal : Bool) :
    let state :=
      if equal then restoreEqualScratchState
      else restoreLessScratchState
    let target := if equal then acceptState else rejectState
    findWorkRule rules state sourceLeftBoundary =
      some (literalRule state sourceLeftBoundary target
        sourceLeftBoundary .right) := by
  cases equal <;> decide

/-! ### Literal transition lemmas -/

private theorem start_source_step (slot : Slot)
    (symbol : WorkSymbol) (allowed : SourceAllowed symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord (startState slot) left (symbol :: right)) =
      some (configAtLeftWord (startState slot) left
        (symbol :: right)) := by
  apply moveLeftFromWord_of_find slot
  · cases slot <;> rfl
  · exact find_start_source slot symbol allowed

private theorem start_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (startState slot)
          (sourceLeftBoundary :: left) right) =
      some (configAtLeftWord (scratchState slot) left
        (sourceLeftBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_start_boundary slot

private theorem scratch_unit_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (scratchState slot)
          (unaryUnit :: left) right) =
      some (configAtLeftWord (seekLedgerState slot) left
        (scratchMark :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_scratch_unit slot

private theorem scratch_separator_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (scratchState slot)
          (unarySeparator :: left) right) =
      some (configAtLeftWord (compareSeekLedgerState slot) left
        (unarySeparator :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_scratch_separator slot

private theorem seek_ledger_payload_step (slot : Slot)
    (symbol : WorkSymbol) (allowed : ScratchPayload symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (seekLedgerState slot)
          (symbol :: left) right) =
      some (configAtLeftWord (seekLedgerState slot) left
        (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_seek_ledger_payload slot symbol allowed

private theorem seek_ledger_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (seekLedgerState slot)
          (ledgerBoundary :: left) right) =
      some
        (configAtLeftWord
          (pairSeekSlotState slot (slotCode slot))
          left (ledgerBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_seek_ledger_boundary slot

private theorem pair_seek_payload_step (slot : Slot)
    (remaining : Nat) (remainingLe : remaining ≤ 5)
    (symbol : WorkSymbol) (allowed : SlotPayload symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (pairSeekSlotState slot remaining)
          (symbol :: left) right) =
      some
        (configAtLeftWord (pairSeekSlotState slot remaining)
          left (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rcases remaining_cases remaining remainingLe with
      first | second | third | fourth | fifth | sixth
    all_goals subst remaining
    all_goals cases slot <;> rfl
  · exact find_pair_seek_payload slot remaining symbol
      remainingLe allowed

private theorem pair_seek_boundary_positive_step (slot : Slot)
    (remaining : Nat) (positive : 0 < remaining)
    (remainingLe : remaining ≤ 5)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (pairSeekSlotState slot remaining)
          (slotBoundary :: left) right) =
      some
        (configAtLeftWord
          (pairSeekSlotState slot (remaining - 1))
          left (slotBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rcases remaining_cases remaining remainingLe with
      first | second | third | fourth | fifth | sixth
    all_goals subst remaining
    all_goals cases slot <;> rfl
  · exact find_pair_seek_boundary_positive slot remaining
      positive remainingLe

private theorem pair_selected_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (pairSeekSlotState slot 0)
          (slotBoundary :: left) right) =
      some
        (configAtLeftWord (selectedState slot) left
          (slotBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_pair_selected_boundary slot

private theorem selected_mark_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (selectedState slot)
          (selectedMark :: left) right) =
      some
        (configAtLeftWord (selectedState slot) left
          (selectedMark :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_selected_mark slot

private theorem selected_unit_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (selectedState slot)
          (unaryUnit :: left) right) =
      some
        (configAtWord (returnLedgerState slot)
          (selectedMark :: left) right) := by
  apply moveRightFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_selected_unit slot

private theorem return_ledger_payload_step (slot : Slot)
    (symbol : WorkSymbol) (allowed : ledgerPayload symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord (returnLedgerState slot)
          left (symbol :: right)) =
      some
        (configAtWord (returnLedgerState slot)
          (symbol :: left) right) := by
  apply moveRightFromWord_of_find slot
  · cases slot <;> rfl
  · exact find_return_ledger_payload slot symbol allowed

private theorem return_ledger_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord (returnLedgerState slot)
          left (ledgerBoundary :: right)) =
      some
        (configAtWord (returnScratchState slot)
          (ledgerBoundary :: left) right) := by
  apply moveRightFromWord_of_find slot
  · cases slot <;> rfl
  · exact find_return_ledger_boundary slot

private theorem return_scratch_payload_step (slot : Slot)
    (symbol : WorkSymbol) (allowed : ScratchPayload symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord (returnScratchState slot)
          left (symbol :: right)) =
      some
        (configAtWord (returnScratchState slot)
          (symbol :: left) right) := by
  apply moveRightFromWord_of_find slot
  · cases slot <;> rfl
  · exact find_return_scratch_payload slot symbol allowed

private theorem return_scratch_mark_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtWord (returnScratchState slot)
          left (scratchMark :: right)) =
      some
        (configAtLeftWord (scratchState slot) left
          (unaryUnit :: right)) := by
  apply moveLeftFromWord_of_find slot
  · cases slot <;> rfl
  · exact find_return_scratch_mark slot

private theorem compare_seek_ledger_payload_step (slot : Slot)
    (symbol : WorkSymbol) (allowed : ScratchPayload symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (compareSeekLedgerState slot)
          (symbol :: left) right) =
      some
        (configAtLeftWord (compareSeekLedgerState slot) left
          (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_compare_seek_ledger_payload slot symbol allowed

private theorem compare_seek_ledger_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (compareSeekLedgerState slot)
          (ledgerBoundary :: left) right) =
      some
        (configAtLeftWord
          (compareSeekSlotState slot (slotCode slot))
          left (ledgerBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_compare_seek_ledger_boundary slot

private theorem compare_seek_payload_step (slot : Slot)
    (remaining : Nat) (remainingLe : remaining ≤ 5)
    (symbol : WorkSymbol) (allowed : SlotPayload symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (compareSeekSlotState slot remaining)
          (symbol :: left) right) =
      some
        (configAtLeftWord (compareSeekSlotState slot remaining)
          left (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rcases remaining_cases remaining remainingLe with
      first | second | third | fourth | fifth | sixth
    all_goals subst remaining
    all_goals cases slot <;> rfl
  · exact find_compare_seek_payload slot remaining symbol
      remainingLe allowed

private theorem compare_seek_boundary_positive_step (slot : Slot)
    (remaining : Nat) (positive : 0 < remaining)
    (remainingLe : remaining ≤ 5)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (compareSeekSlotState slot remaining)
          (slotBoundary :: left) right) =
      some
        (configAtLeftWord
          (compareSeekSlotState slot (remaining - 1))
          left (slotBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · rcases remaining_cases remaining remainingLe with
      first | second | third | fourth | fifth | sixth
    all_goals subst remaining
    all_goals cases slot <;> rfl
  · exact find_compare_seek_boundary_positive slot remaining
      positive remainingLe

private theorem compare_selected_boundary_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (compareSeekSlotState slot 0)
          (slotBoundary :: left) right) =
      some
        (configAtLeftWord (compareSelectedState slot) left
          (slotBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_compare_selected_boundary slot

private theorem compare_selected_mark_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (compareSelectedState slot)
          (selectedMark :: left) right) =
      some
        (configAtLeftWord (compareSelectedState slot) left
          (selectedMark :: right)) := by
  apply moveLeftFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_compare_selected_mark slot

private theorem compare_selected_unit_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (compareSelectedState slot)
          (unaryUnit :: left) right) =
      some
        (configAtWord restoreLessLedgerState
          (unaryUnit :: left) right) := by
  apply moveRightFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_compare_selected_unit slot

private theorem compare_selected_separator_step (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (compareSelectedState slot)
          (unarySeparator :: left) right) =
      some
        (configAtWord restoreEqualLedgerState
          (unarySeparator :: left) right) := by
  apply moveRightFromLeftWord_of_find slot
  · cases slot <;> rfl
  · exact find_compare_selected_separator slot

private theorem restore_ledger_mark_step (slot : Slot)
    (equal : Bool) (left right : List WorkSymbol) :
    let state :=
      if equal then restoreEqualLedgerState
      else restoreLessLedgerState
    workStep? (machineFor slot)
        (configAtWord state left (selectedMark :: right)) =
      some
        (configAtWord state (unaryUnit :: left) right) := by
  dsimp only
  apply moveRightFromWord_of_find slot
  · cases slot <;> cases equal <;> rfl
  · exact find_restore_ledger_mark equal

private theorem restore_ledger_payload_step (slot : Slot)
    (equal : Bool) (symbol : WorkSymbol)
    (allowed :
      symbol = unaryUnit ∨ symbol = unarySeparator ∨
        symbol = WorkSymbol.blank ∨ symbol = slotBoundary)
    (left right : List WorkSymbol) :
    let state :=
      if equal then restoreEqualLedgerState
      else restoreLessLedgerState
    workStep? (machineFor slot)
        (configAtWord state left (symbol :: right)) =
      some
        (configAtWord state (symbol :: left) right) := by
  dsimp only
  apply moveRightFromWord_of_find slot
  · cases slot <;> cases equal <;> rfl
  · exact find_restore_ledger_payload equal symbol allowed

private theorem restore_ledger_boundary_step (slot : Slot)
    (equal : Bool) (left right : List WorkSymbol) :
    let state :=
      if equal then restoreEqualLedgerState
      else restoreLessLedgerState
    let target :=
      if equal then restoreEqualScratchState
      else restoreLessScratchState
    workStep? (machineFor slot)
        (configAtWord state left (ledgerBoundary :: right)) =
      some
        (configAtWord target (ledgerBoundary :: left) right) := by
  dsimp only
  apply moveRightFromWord_of_find slot
  · cases slot <;> cases equal <;> rfl
  · exact find_restore_ledger_boundary equal

private theorem restore_scratch_payload_step (slot : Slot)
    (equal : Bool) (symbol : WorkSymbol)
    (allowed : ScratchPayload symbol)
    (left right : List WorkSymbol) :
    let state :=
      if equal then restoreEqualScratchState
      else restoreLessScratchState
    workStep? (machineFor slot)
        (configAtWord state left (symbol :: right)) =
      some
        (configAtWord state (symbol :: left) right) := by
  dsimp only
  apply moveRightFromWord_of_find slot
  · cases slot <;> cases equal <;> rfl
  · exact find_restore_scratch_payload equal symbol allowed

private theorem restore_source_boundary_step (slot : Slot)
    (equal : Bool) (left right : List WorkSymbol) :
    let state :=
      if equal then restoreEqualScratchState
      else restoreLessScratchState
    let target := if equal then acceptState else rejectState
    workStep? (machineFor slot)
        (configAtWord state left (sourceLeftBoundary :: right)) =
      some
        (configAtWord target
          (sourceLeftBoundary :: left) right) := by
  dsimp only
  apply moveRightFromWord_of_find slot
  · cases slot <;> cases equal <;> rfl
  · exact find_restore_source_boundary equal

/-! ### Canonical words and reusable scans -/

private def valuesWord (capacity : Nat)
    (values : List Nat) : List WorkSymbol :=
  TargetEmitterScratchAddSlot.valuesWord capacity values

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

private theorem slotPayload_basic_allowed
    (capacity value : Nat) :
    ∀ symbol, symbol ∈ slotPayload capacity value →
      symbol = unaryUnit ∨ symbol = unarySeparator ∨
        symbol = WorkSymbol.blank := by
  intro symbol member
  unfold slotPayload at member
  rw [List.mem_append] at member
  rcases member with fromUnits | fromTail
  · exact Or.inl (List.eq_of_mem_replicate fromUnits)
  · cases fromTail with
    | head =>
        exact Or.inr (Or.inl rfl)
    | tail _ fromBlanks =>
        exact Or.inr (Or.inr
          (List.eq_of_mem_replicate fromBlanks))

private theorem slotPayload_allowed
    (capacity value : Nat) :
    ∀ symbol, symbol ∈ slotPayload capacity value →
      SlotPayload symbol := by
  intro symbol member
  rcases slotPayload_basic_allowed capacity value symbol member with
    unit | separator | blank
  · exact Or.inl unit
  · exact Or.inr (Or.inl separator)
  · exact Or.inr (Or.inr (Or.inl blank))

private theorem valuesWord_ledger_allowed
    (capacity : Nat) (values : List Nat) :
    ∀ symbol, symbol ∈ valuesWord capacity values →
      ledgerPayload symbol := by
  intro symbol member
  rcases List.mem_flatMap.mp member with
    ⟨value, _valueMember, symbolMember⟩
  rw [slotWord_eq] at symbolMember
  cases symbolMember with
  | head =>
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | tail _ payloadMember =>
      rcases slotPayload_basic_allowed capacity value symbol
          payloadMember with unit | separator | blank
      · exact Or.inl unit
      · exact Or.inr (Or.inl separator)
      · exact Or.inr (Or.inr (Or.inl blank))

private theorem scratchWord_allowed
    (capacity scratch : Nat) :
    ∀ symbol, symbol ∈ scratchWord capacity scratch →
      ScratchPayload symbol := by
  intro symbol member
  unfold scratchWord TargetEmitterScratchAddSlot.scratchWord at member
  rw [List.mem_append] at member
  rcases member with fromUnits | fromTail
  · exact Or.inl (List.eq_of_mem_replicate fromUnits)
  · cases fromTail with
    | head =>
        exact Or.inr (Or.inl rfl)
    | tail _ fromBlanks =>
        exact Or.inr (Or.inr
          (List.eq_of_mem_replicate fromBlanks))

private def slotSeekState (compare : Bool)
    (slot : Slot) (remaining : Nat) : Nat :=
  if compare then compareSeekSlotState slot remaining
  else pairSeekSlotState slot remaining

private def slotSelectedState (compare : Bool)
    (slot : Slot) : Nat :=
  if compare then compareSelectedState slot
  else selectedState slot

private theorem slot_seek_payload_step (slot : Slot)
    (compare : Bool) (remaining : Nat)
    (remainingLe : remaining ≤ 5)
    (symbol : WorkSymbol) (allowed : SlotPayload symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord
          (slotSeekState compare slot remaining)
          (symbol :: left) right) =
      some
        (configAtLeftWord
          (slotSeekState compare slot remaining)
          left (symbol :: right)) := by
  cases compare
  · simpa [slotSeekState] using
      pair_seek_payload_step slot remaining remainingLe
        symbol allowed left right
  · simpa [slotSeekState] using
      compare_seek_payload_step slot remaining remainingLe
        symbol allowed left right

private theorem slot_seek_boundary_positive_step (slot : Slot)
    (compare : Bool) (remaining : Nat)
    (positive : 0 < remaining)
    (remainingLe : remaining ≤ 5)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord
          (slotSeekState compare slot remaining)
          (slotBoundary :: left) right) =
      some
        (configAtLeftWord
          (slotSeekState compare slot (remaining - 1))
          left (slotBoundary :: right)) := by
  cases compare
  · simpa [slotSeekState] using
      pair_seek_boundary_positive_step slot remaining
        positive remainingLe left right
  · simpa [slotSeekState] using
      compare_seek_boundary_positive_step slot remaining
        positive remainingLe left right

private theorem slot_selected_boundary_step (slot : Slot)
    (compare : Bool) (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (slotSeekState compare slot 0)
          (slotBoundary :: left) right) =
      some
        (configAtLeftWord (slotSelectedState compare slot)
          left (slotBoundary :: right)) := by
  cases compare
  · simpa [slotSeekState, slotSelectedState] using
      pair_selected_boundary_step slot left right
  · simpa [slotSeekState, slotSelectedState] using
      compare_selected_boundary_step slot left right

private theorem slot_seek_payload_exact (slot : Slot)
    (compare : Bool) (remaining : Nat)
    (remainingLe : remaining ≤ 5)
    (capacity value : Nat)
    (left right : List WorkSymbol) :
    workRunExact? (machineFor slot)
        (slotPayload capacity value).length
        (configAtLeftWord
          (slotSeekState compare slot remaining)
          (slotPayload capacity value ++ left) right) =
      some
        (configAtLeftWord
          (slotSeekState compare slot remaining)
          left ((slotPayload capacity value).reverse ++ right)) := by
  exact scanLeftExact slot
    (slotSeekState compare slot remaining)
    SlotPayload
    (fun head leftTail rightSide allowed =>
      slot_seek_payload_step slot compare remaining remainingLe
        head allowed leftTail rightSide)
    (slotPayload capacity value) left right
    (slotPayload_allowed capacity value)

private theorem slot_seek_prefix_exact (slot : Slot)
    (compare : Bool) (capacity : Nat)
    (priorValues : List Nat)
    (valuesLe : priorValues.length ≤ 5)
    (left right : List WorkSymbol) :
    workRunExact? (machineFor slot)
        (valuesWord capacity priorValues).length
        (configAtLeftWord
          (slotSeekState compare slot priorValues.length)
          (valuesWord capacity priorValues ++ left) right) =
      some
        (configAtLeftWord (slotSeekState compare slot 0)
          left ((valuesWord capacity priorValues).reverse ++ right)) := by
  induction priorValues generalizing right with
  | nil =>
      rfl
  | cons value rest inductionHypothesis =>
      have positive : 0 < rest.length + 1 := by omega
      have remainingLe : rest.length + 1 ≤ 5 := by
        simpa using valuesLe
      have restLe : rest.length ≤ 5 := by omega
      let afterBoundary :=
        configAtLeftWord
          (slotSeekState compare slot rest.length)
          (slotPayload capacity value ++
            valuesWord capacity rest ++ left)
          (slotBoundary :: right)
      let afterPayload :=
        configAtLeftWord
          (slotSeekState compare slot rest.length)
          (valuesWord capacity rest ++ left)
          ((slotPayload capacity value).reverse ++
            slotBoundary :: right)
      have hBoundary :=
        exactRun_one slot _ _
          (slot_seek_boundary_positive_step slot compare
            (rest.length + 1) positive remainingLe
            (slotPayload capacity value ++
              valuesWord capacity rest ++ left)
            right)
      have hBoundaryCanonical :
          workRunExact? (machineFor slot) 1
              (configAtLeftWord
                (slotSeekState compare slot (rest.length + 1))
                (slotBoundary :: slotPayload capacity value ++
                  valuesWord capacity rest ++ left) right) =
            some afterBoundary := by
        simpa [afterBoundary, List.append_assoc] using hBoundary
      have hPayload :
          workRunExact? (machineFor slot)
              (slotPayload capacity value).length afterBoundary =
            some afterPayload := by
        simpa [afterBoundary, afterPayload, List.append_assoc] using
          slot_seek_payload_exact slot compare rest.length restLe
            capacity value (valuesWord capacity rest ++ left)
            (slotBoundary :: right)
      have hRest :
          workRunExact? (machineFor slot)
              (valuesWord capacity rest).length afterPayload =
            some
              (configAtLeftWord
                (slotSeekState compare slot 0) left
                ((valuesWord capacity rest).reverse ++
                  (slotPayload capacity value).reverse ++
                    slotBoundary :: right)) := by
        simpa [afterPayload, List.append_assoc] using
          inductionHypothesis restLe
            ((slotPayload capacity value).reverse ++
              slotBoundary :: right)
      have first := exactRun_add slot 1
        (slotPayload capacity value).length
        _ _ _ hBoundaryCanonical hPayload
      have complete := exactRun_add slot
        (1 + (slotPayload capacity value).length)
        (valuesWord capacity rest).length
        _ _ _ first hRest
      have steps :
          1 + (slotPayload capacity value).length +
              (valuesWord capacity rest).length =
            (valuesWord capacity (value :: rest)).length := by
        simp [valuesWord,
          TargetEmitterScratchAddSlot.valuesWord, slotWord_eq]
        omega
      rw [steps] at complete
      simpa [valuesWord,
        TargetEmitterScratchAddSlot.valuesWord,
        slotWord_eq, List.reverse_append,
        List.append_assoc] using complete

private def scratchPayloadWord
    (units blanks : Nat) : List WorkSymbol :=
  List.replicate units unaryUnit ++
    unarySeparator ::
      List.replicate blanks WorkSymbol.blank

private theorem scratchPayloadWord_allowed
    (units blanks : Nat) :
    ∀ symbol, symbol ∈ scratchPayloadWord units blanks →
      ScratchPayload symbol := by
  intro symbol member
  unfold scratchPayloadWord at member
  rw [List.mem_append] at member
  rcases member with fromUnits | fromTail
  · exact Or.inl (List.eq_of_mem_replicate fromUnits)
  · cases fromTail with
    | head =>
        exact Or.inr (Or.inl rfl)
    | tail _ fromBlanks =>
        exact Or.inr (Or.inr
          (List.eq_of_mem_replicate fromBlanks))

private def seekLedgerScanState
    (compare : Bool) (slot : Slot) : Nat :=
  if compare then compareSeekLedgerState slot
  else seekLedgerState slot

private theorem seek_ledger_scan_step (slot : Slot)
    (compare : Bool) (symbol : WorkSymbol)
    (allowed : ScratchPayload symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (seekLedgerScanState compare slot)
          (symbol :: left) right) =
      some
        (configAtLeftWord (seekLedgerScanState compare slot)
          left (symbol :: right)) := by
  cases compare
  · simpa [seekLedgerScanState] using
      seek_ledger_payload_step slot symbol allowed left right
  · simpa [seekLedgerScanState] using
      compare_seek_ledger_payload_step slot symbol allowed left right

private theorem seek_ledger_scan_boundary_step (slot : Slot)
    (compare : Bool) (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (seekLedgerScanState compare slot)
          (ledgerBoundary :: left) right) =
      some
        (configAtLeftWord
          (slotSeekState compare slot (slotCode slot))
          left (ledgerBoundary :: right)) := by
  cases compare
  · simpa [seekLedgerScanState, slotSeekState] using
      seek_ledger_boundary_step slot left right
  · simpa [seekLedgerScanState, slotSeekState] using
      compare_seek_ledger_boundary_step slot left right

private theorem seek_ledger_scan_exact (slot : Slot)
    (compare : Bool) (units blanks : Nat)
    (left right : List WorkSymbol) :
    workRunExact? (machineFor slot)
        (scratchPayloadWord units blanks).length
        (configAtLeftWord (seekLedgerScanState compare slot)
          (scratchPayloadWord units blanks ++ left) right) =
      some
        (configAtLeftWord (seekLedgerScanState compare slot)
          left ((scratchPayloadWord units blanks).reverse ++ right)) := by
  exact scanLeftExact slot
    (seekLedgerScanState compare slot)
    ScratchPayload
    (fun head leftTail rightSide allowed =>
      seek_ledger_scan_step slot compare head allowed
        leftTail rightSide)
    (scratchPayloadWord units blanks) left right
    (scratchPayloadWord_allowed units blanks)

private theorem selected_marks_exact (slot : Slot)
    (compare : Bool) (count : Nat)
    (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) count
        (configAtLeftWord (slotSelectedState compare slot)
          (List.replicate count selectedMark ++ left) right) =
      some
        (configAtLeftWord (slotSelectedState compare slot)
          left (List.replicate count selectedMark ++ right)) := by
  have scanned := scanLeftExact slot
    (slotSelectedState compare slot)
    (fun symbol => symbol = selectedMark)
    (fun head leftTail rightSide equality => by
      subst head
      cases compare
      · simpa [slotSelectedState] using
          selected_mark_step slot leftTail rightSide
      · simpa [slotSelectedState] using
          compare_selected_mark_step slot leftTail rightSide)
    (List.replicate count selectedMark) left right (by simp)
  simpa using scanned

private theorem return_ledger_word_exact (slot : Slot)
    (word suffix left : List WorkSymbol)
    (allowed :
      ∀ symbol, symbol ∈ word → ledgerPayload symbol) :
    workRunExact? (machineFor slot) word.length
        (configAtWord (returnLedgerState slot) left
          (word ++ suffix)) =
      some
        (configAtWord (returnLedgerState slot)
          (word.reverse ++ left) suffix) := by
  exact scanRightExact slot (returnLedgerState slot)
    ledgerPayload
    (fun leftSide head rightSide headAllowed =>
      return_ledger_payload_step slot head headAllowed
        leftSide rightSide)
    word suffix left allowed

private theorem return_scratch_word_exact (slot : Slot)
    (word suffix left : List WorkSymbol)
    (allowed :
      ∀ symbol, symbol ∈ word → ScratchPayload symbol) :
    workRunExact? (machineFor slot) word.length
        (configAtWord (returnScratchState slot) left
          (word ++ suffix)) =
      some
        (configAtWord (returnScratchState slot)
          (word.reverse ++ left) suffix) := by
  exact scanRightExact slot (returnScratchState slot)
    ScratchPayload
    (fun leftSide head rightSide headAllowed =>
      return_scratch_payload_step slot head headAllowed
        leftSide rightSide)
    word suffix left allowed

private theorem replicate_append_self_cons
    (count : Nat) (symbol : WorkSymbol)
    (tail : List WorkSymbol) :
    List.replicate count symbol ++ symbol :: tail =
      List.replicate (count + 1) symbol ++ tail := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons symbol) inductionHypothesis

private theorem replicate_succ_append {α : Type}
    (count : Nat) (item : α) :
    List.replicate (count + 1) item =
      List.replicate count item ++ [item] := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      change
        item :: List.replicate (count + 1) item =
          item :: (List.replicate count item ++ [item])
      rw [inductionHypothesis]

private theorem restore_marks_exact (slot : Slot)
    (equal : Bool) (count : Nat)
    (left right : List WorkSymbol) :
    let state :=
      if equal then restoreEqualLedgerState
      else restoreLessLedgerState
    workRunExact? (machineFor slot) count
        (configAtWord state left
          (List.replicate count selectedMark ++ right)) =
      some
        (configAtWord state
          (List.replicate count unaryUnit ++ left) right) := by
  dsimp only
  induction count generalizing left with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      change
        (match workStep? (machineFor slot)
          (configAtWord
            (if equal then restoreEqualLedgerState
              else restoreLessLedgerState)
            left
            (selectedMark ::
              List.replicate count selectedMark ++ right)) with
         | none => none
         | some next =>
             workRunExact? (machineFor slot) count next) = _
      simp only [List.cons_append]
      have hStep := restore_ledger_mark_step slot equal left
        (List.replicate count selectedMark ++ right)
      dsimp only at hStep
      rw [hStep]
      have restored :=
        inductionHypothesis (unaryUnit :: left)
      rw [replicate_append_self_cons count unaryUnit left]
        at restored
      simpa only [List.replicate_succ,
        List.cons_append] using restored

private theorem valuesWord_restore_allowed
    (capacity : Nat) (values : List Nat) :
    ∀ symbol, symbol ∈ valuesWord capacity values →
      symbol = unaryUnit ∨ symbol = unarySeparator ∨
        symbol = WorkSymbol.blank ∨ symbol = slotBoundary := by
  intro symbol member
  rcases List.mem_flatMap.mp member with
    ⟨value, _valueMember, symbolMember⟩
  rw [slotWord_eq] at symbolMember
  cases symbolMember with
  | head =>
      exact Or.inr (Or.inr (Or.inr rfl))
  | tail _ payloadMember =>
      rcases slotPayload_basic_allowed capacity value symbol
          payloadMember with unit | separator | blank
      · exact Or.inl unit
      · exact Or.inr (Or.inl separator)
      · exact Or.inr (Or.inr (Or.inl blank))

private theorem restore_ledger_word_exact (slot : Slot)
    (equal : Bool) (word suffix left : List WorkSymbol)
    (allowed :
      ∀ symbol, symbol ∈ word →
        symbol = unaryUnit ∨ symbol = unarySeparator ∨
          symbol = WorkSymbol.blank ∨ symbol = slotBoundary) :
    let state :=
      if equal then restoreEqualLedgerState
      else restoreLessLedgerState
    workRunExact? (machineFor slot) word.length
        (configAtWord state left (word ++ suffix)) =
      some
        (configAtWord state
          (word.reverse ++ left) suffix) := by
  dsimp only
  exact scanRightExact slot
    (if equal then restoreEqualLedgerState
      else restoreLessLedgerState)
    (fun symbol =>
      symbol = unaryUnit ∨ symbol = unarySeparator ∨
        symbol = WorkSymbol.blank ∨ symbol = slotBoundary)
    (fun leftSide head rightSide headAllowed =>
      restore_ledger_payload_step slot equal head
        headAllowed leftSide rightSide)
    word suffix left allowed

private theorem restore_scratch_word_exact (slot : Slot)
    (equal : Bool) (word suffix left : List WorkSymbol)
    (allowed :
      ∀ symbol, symbol ∈ word → ScratchPayload symbol) :
    let state :=
      if equal then restoreEqualScratchState
      else restoreLessScratchState
    workRunExact? (machineFor slot) word.length
        (configAtWord state left (word ++ suffix)) =
      some
        (configAtWord state
          (word.reverse ++ left) suffix) := by
  dsimp only
  exact scanRightExact slot
    (if equal then restoreEqualScratchState
      else restoreLessScratchState)
    ScratchPayload
    (fun leftSide head rightSide headAllowed =>
      restore_scratch_payload_step slot equal head
        headAllowed leftSide rightSide)
    word suffix left allowed

/-! ### Canonical comparison configurations -/

private def selectedPayload (capacity processed remaining : Nat) :
    List WorkSymbol :=
  List.replicate processed selectedMark ++
    List.replicate remaining unaryUnit ++
      unarySeparator ::
        List.replicate (capacity - (processed + remaining))
          WorkSymbol.blank

private def loopConfiguration (slot : Slot)
    (capacity processed scratchRemaining selectedRemaining : Nat)
    (priorWord outerLeft sourceWord : List WorkSymbol) :
    WorkConfiguration :=
  configAtLeftWord (scratchState slot)
    (List.replicate scratchRemaining unaryUnit ++
      unarySeparator ::
        List.replicate
            (capacity - (processed + scratchRemaining))
            WorkSymbol.blank ++
          ledgerBoundary ::
            (priorWord ++ slotBoundary ::
              selectedPayload capacity processed selectedRemaining ++
                outerLeft))
    (List.replicate processed unaryUnit ++
      sourceLeftBoundary :: sourceWord)

private theorem scratchWord_length_of_le
    (capacity scratch : Nat) (bounded : scratch ≤ capacity) :
    (scratchWord capacity scratch).length = capacity + 1 := by
  simp [scratchWord, TargetEmitterScratchAddSlot.scratchWord]
  omega

private theorem slotPayload_length_of_le
    (capacity value : Nat) (bounded : value ≤ capacity) :
    (slotPayload capacity value).length = capacity + 1 := by
  simp [slotPayload]
  omega

private theorem initial_exact (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (allowed : SourceAllowed sourceHead) :
    workRunExact? (machineFor slot) 2
        (entryConfiguration slot capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) =
      some
        (loopConfiguration slot capacity 0 scratch
          (selectedValue slot registers)
          (prefixWord capacity slot registers)
          (suffixWord capacity slot registers ++ outsideLeft)
          (sourceHead :: sourceTail ++ targetAndRight)) := by
  let afterSource :=
    configAtLeftWord (startState slot)
      (sourceLeftBoundary ::
        scratchWord capacity scratch ++
          ledgerBoundary ::
            (TargetEmitterLedger.slotBank capacity registers ++
              outsideLeft))
      (sourceHead :: sourceTail ++ targetAndRight)
  have hSource :
      workRunExact? (machineFor slot) 1
          (entryConfiguration slot capacity scratch registers
            sourceHead sourceTail targetAndRight outsideLeft) =
        some afterSource := by
    apply exactRun_one slot
    simpa [entryConfiguration, afterSource,
      List.append_assoc] using
      start_source_step slot sourceHead allowed
        (sourceLeftBoundary ::
          scratchWord capacity scratch ++
            ledgerBoundary ::
              (TargetEmitterLedger.slotBank capacity registers ++
                outsideLeft))
        (sourceTail ++ targetAndRight)
  have hBoundary :
      workRunExact? (machineFor slot) 1 afterSource =
        some
          (configAtLeftWord (scratchState slot)
            (scratchWord capacity scratch ++
              ledgerBoundary ::
                (TargetEmitterLedger.slotBank capacity registers ++
                  outsideLeft))
            (sourceLeftBoundary ::
              sourceHead :: sourceTail ++ targetAndRight)) := by
    apply exactRun_one slot
    simpa [afterSource] using
      start_boundary_step slot
        (scratchWord capacity scratch ++
          ledgerBoundary ::
            (TargetEmitterLedger.slotBank capacity registers ++
              outsideLeft))
        (sourceHead :: sourceTail ++ targetAndRight)
  have complete := exactRun_add slot 1 1 _ _ _
    hSource hBoundary
  rw [TargetEmitterScratchAddSlot.slotBank_decompose
    capacity slot registers] at complete
  simpa [loopConfiguration, scratchWord,
    TargetEmitterScratchAddSlot.scratchWord, selectedPayload,
    slotWord_eq, slotPayload, prefixWord, suffixWord,
    selectedValue, unaryUnit, unarySeparator,
    TargetEmitterScratchAddSlot.unaryUnit,
    TargetEmitterScratchAddSlot.unarySeparator,
    List.append_assoc] using complete

/-! ### One scratch/slot pairing cycle -/

private theorem cycle_exact (slot : Slot)
    (capacity processed scratchRemaining selectedRemaining : Nat)
    (priorValues : List Nat)
    (outerLeft sourceWord : List WorkSymbol)
    (priorLength :
      priorValues.length = slotCode slot)
    (scratchFits :
      processed + (scratchRemaining + 1) ≤ capacity)
    (selectedFits :
      processed + (selectedRemaining + 1) ≤ capacity) :
    workRunExact? (machineFor slot)
        (pairSteps capacity
          (valuesWord capacity priorValues).length)
        (loopConfiguration slot capacity processed
          (scratchRemaining + 1) (selectedRemaining + 1)
          (valuesWord capacity priorValues) outerLeft sourceWord) =
      some
        (loopConfiguration slot capacity (processed + 1)
          scratchRemaining selectedRemaining
          (valuesWord capacity priorValues) outerLeft sourceWord) := by
  let priorWord := valuesWord capacity priorValues
  let scratchTail :=
    scratchPayloadWord scratchRemaining
      (capacity - (processed + (scratchRemaining + 1)))
  let selectedTail :=
    List.replicate selectedRemaining unaryUnit ++
      unarySeparator ::
        List.replicate
            (capacity - (processed + (selectedRemaining + 1)))
            WorkSymbol.blank ++
          outerLeft
  let afterScratch :=
    configAtLeftWord (seekLedgerState slot)
      (scratchTail ++ ledgerBoundary ::
        (priorWord ++ slotBoundary ::
          List.replicate processed selectedMark ++
            unaryUnit :: selectedTail))
      (scratchMark :: List.replicate processed unaryUnit ++
        sourceLeftBoundary :: sourceWord)
  let atLedger :=
    configAtLeftWord (seekLedgerState slot)
      (ledgerBoundary ::
        (priorWord ++ slotBoundary ::
          List.replicate processed selectedMark ++
            unaryUnit :: selectedTail))
      (scratchTail.reverse ++ scratchMark ::
        List.replicate processed unaryUnit ++
          sourceLeftBoundary :: sourceWord)
  let afterLedger :=
    configAtLeftWord
      (pairSeekSlotState slot (slotCode slot))
      (priorWord ++ slotBoundary ::
        List.replicate processed selectedMark ++
          unaryUnit :: selectedTail)
      (ledgerBoundary :: scratchTail.reverse ++ scratchMark ::
        List.replicate processed unaryUnit ++
          sourceLeftBoundary :: sourceWord)
  let atSelectedBoundary :=
    configAtLeftWord (pairSeekSlotState slot 0)
      (slotBoundary ::
        List.replicate processed selectedMark ++
          unaryUnit :: selectedTail)
      (priorWord.reverse ++ ledgerBoundary ::
        scratchTail.reverse ++ scratchMark ::
          List.replicate processed unaryUnit ++
            sourceLeftBoundary :: sourceWord)
  let atSelected :=
    configAtLeftWord (selectedState slot)
      (List.replicate processed selectedMark ++
        unaryUnit :: selectedTail)
      (slotBoundary :: priorWord.reverse ++ ledgerBoundary ::
        scratchTail.reverse ++ scratchMark ::
          List.replicate processed unaryUnit ++
            sourceLeftBoundary :: sourceWord)
  let atUnit :=
    configAtLeftWord (selectedState slot)
      (unaryUnit :: selectedTail)
      (List.replicate processed selectedMark ++
        slotBoundary :: priorWord.reverse ++ ledgerBoundary ::
          scratchTail.reverse ++ scratchMark ::
            List.replicate processed unaryUnit ++
              sourceLeftBoundary :: sourceWord)
  let returningLedger :=
    configAtWord (returnLedgerState slot)
      (selectedMark :: selectedTail)
      (List.replicate processed selectedMark ++
        slotBoundary :: priorWord.reverse ++ ledgerBoundary ::
          scratchTail.reverse ++ scratchMark ::
            List.replicate processed unaryUnit ++
              sourceLeftBoundary :: sourceWord)
  let returnWord :=
    List.replicate processed selectedMark ++
      slotBoundary :: priorWord.reverse
  let atLedgerReturn :=
    configAtWord (returnLedgerState slot)
      (priorWord ++ slotBoundary ::
        List.replicate (processed + 1) selectedMark ++
          selectedTail)
      (ledgerBoundary :: scratchTail.reverse ++ scratchMark ::
        List.replicate processed unaryUnit ++
          sourceLeftBoundary :: sourceWord)
  let returningScratch :=
    configAtWord (returnScratchState slot)
      (ledgerBoundary :: priorWord ++ slotBoundary ::
        List.replicate (processed + 1) selectedMark ++
          selectedTail)
      (scratchTail.reverse ++ scratchMark ::
        List.replicate processed unaryUnit ++
          sourceLeftBoundary :: sourceWord)
  let atScratchMark :=
    configAtWord (returnScratchState slot)
      (scratchTail ++ ledgerBoundary :: priorWord ++
        slotBoundary ::
          List.replicate (processed + 1) selectedMark ++
            selectedTail)
      (scratchMark :: List.replicate processed unaryUnit ++
        sourceLeftBoundary :: sourceWord)
  have hScratch :
      workRunExact? (machineFor slot) 1
          (loopConfiguration slot capacity processed
            (scratchRemaining + 1) (selectedRemaining + 1)
            priorWord outerLeft sourceWord) =
        some afterScratch := by
    apply exactRun_one slot
    simpa [loopConfiguration, afterScratch, scratchTail,
      scratchPayloadWord, selectedPayload, selectedTail, priorWord,
      List.replicate_succ, List.append_assoc] using
      scratch_unit_step slot
        (scratchTail ++ ledgerBoundary ::
          (priorWord ++ slotBoundary ::
            List.replicate processed selectedMark ++
              unaryUnit :: selectedTail))
        (List.replicate processed unaryUnit ++
          sourceLeftBoundary :: sourceWord)
  have hSeek :
      workRunExact? (machineFor slot) scratchTail.length
          afterScratch =
        some atLedger := by
    simpa [afterScratch, atLedger, scratchTail,
      seekLedgerScanState] using
      seek_ledger_scan_exact slot false scratchRemaining
        (capacity - (processed + (scratchRemaining + 1)))
        (ledgerBoundary ::
          (priorWord ++ slotBoundary ::
            List.replicate processed selectedMark ++
              unaryUnit :: selectedTail))
        (scratchMark :: List.replicate processed unaryUnit ++
          sourceLeftBoundary :: sourceWord)
  have hLedger :
      workRunExact? (machineFor slot) 1 atLedger =
        some afterLedger := by
    apply exactRun_one slot
    simpa [atLedger, afterLedger] using
      seek_ledger_boundary_step slot
        (priorWord ++ slotBoundary ::
          List.replicate processed selectedMark ++
            unaryUnit :: selectedTail)
        (scratchTail.reverse ++ scratchMark ::
          List.replicate processed unaryUnit ++
            sourceLeftBoundary :: sourceWord)
  have priorLe : priorValues.length ≤ 5 := by
    rw [priorLength]
    exact TargetEmitterScratchAddSlot.slotCode_le_five slot
  have hPrefix :
      workRunExact? (machineFor slot) priorWord.length
          afterLedger =
        some atSelectedBoundary := by
    simpa [afterLedger, atSelectedBoundary, priorWord,
      slotSeekState, priorLength, List.append_assoc] using
      slot_seek_prefix_exact slot false capacity priorValues priorLe
        (slotBoundary ::
          List.replicate processed selectedMark ++
            unaryUnit :: selectedTail)
        (ledgerBoundary :: scratchTail.reverse ++ scratchMark ::
          List.replicate processed unaryUnit ++
            sourceLeftBoundary :: sourceWord)
  have hSelectedBoundary :
      workRunExact? (machineFor slot) 1 atSelectedBoundary =
        some atSelected := by
    apply exactRun_one slot
    simpa [atSelectedBoundary, atSelected,
      slotSeekState, slotSelectedState] using
      slot_selected_boundary_step slot false
        (List.replicate processed selectedMark ++
          unaryUnit :: selectedTail)
        (priorWord.reverse ++ ledgerBoundary ::
          scratchTail.reverse ++ scratchMark ::
            List.replicate processed unaryUnit ++
              sourceLeftBoundary :: sourceWord)
  have hMarks :
      workRunExact? (machineFor slot) processed atSelected =
        some atUnit := by
    simpa [atSelected, atUnit, slotSelectedState,
      List.append_assoc] using
      selected_marks_exact slot false processed
        (unaryUnit :: selectedTail)
        (slotBoundary :: priorWord.reverse ++ ledgerBoundary ::
          scratchTail.reverse ++ scratchMark ::
            List.replicate processed unaryUnit ++
              sourceLeftBoundary :: sourceWord)
  have hUnit :
      workRunExact? (machineFor slot) 1 atUnit =
        some returningLedger := by
    apply exactRun_one slot
    simpa [atUnit, returningLedger] using
      selected_unit_step slot selectedTail
        (List.replicate processed selectedMark ++
          slotBoundary :: priorWord.reverse ++ ledgerBoundary ::
            scratchTail.reverse ++ scratchMark ::
              List.replicate processed unaryUnit ++
                sourceLeftBoundary :: sourceWord)
  have returnAllowed :
      ∀ symbol, symbol ∈ returnWord → ledgerPayload symbol := by
    intro symbol member
    unfold returnWord at member
    rw [List.mem_append] at member
    rcases member with fromMarks | fromRest
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (List.eq_of_mem_replicate fromMarks))))
    · cases fromRest with
      | head =>
          exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | tail _ fromPrior =>
          exact valuesWord_ledger_allowed capacity priorValues symbol
            (List.mem_reverse.mp fromPrior)
  have hReturnLedger :
      workRunExact? (machineFor slot) returnWord.length
          returningLedger =
        some atLedgerReturn := by
    have scanned :=
      return_ledger_word_exact slot returnWord
        (ledgerBoundary :: scratchTail.reverse ++ scratchMark ::
          List.replicate processed unaryUnit ++
            sourceLeftBoundary :: sourceWord)
        (selectedMark :: selectedTail) returnAllowed
    simpa [returningLedger, atLedgerReturn, returnWord,
      priorWord, List.reverse_append,
      replicate_succ_append, List.append_assoc] using scanned
  have hReturnBoundary :
      workRunExact? (machineFor slot) 1 atLedgerReturn =
        some returningScratch := by
    apply exactRun_one slot
    simpa [atLedgerReturn, returningScratch] using
      return_ledger_boundary_step slot
        (priorWord ++ slotBoundary ::
          List.replicate (processed + 1) selectedMark ++
            selectedTail)
        (scratchTail.reverse ++ scratchMark ::
          List.replicate processed unaryUnit ++
            sourceLeftBoundary :: sourceWord)
  have scratchAllowed :
      ∀ symbol, symbol ∈ scratchTail.reverse →
        ScratchPayload symbol := by
    intro symbol member
    exact scratchPayloadWord_allowed scratchRemaining
      (capacity - (processed + (scratchRemaining + 1)))
      symbol (List.mem_reverse.mp member)
  have hReturnScratch :
      workRunExact? (machineFor slot) scratchTail.length
          returningScratch =
        some atScratchMark := by
    have scanned :=
      return_scratch_word_exact slot scratchTail.reverse
        (scratchMark :: List.replicate processed unaryUnit ++
          sourceLeftBoundary :: sourceWord)
        (ledgerBoundary :: priorWord ++ slotBoundary ::
          List.replicate (processed + 1) selectedMark ++
            selectedTail)
        scratchAllowed
    simpa [returningScratch, atScratchMark,
      List.append_assoc] using scanned
  have hScratchMark :
      workRunExact? (machineFor slot) 1 atScratchMark =
        some
          (loopConfiguration slot capacity (processed + 1)
            scratchRemaining selectedRemaining priorWord
            outerLeft sourceWord) := by
    apply exactRun_one slot
    have step :=
      return_scratch_mark_step slot
        (scratchTail ++ ledgerBoundary :: priorWord ++
          slotBoundary ::
            List.replicate (processed + 1) selectedMark ++
              selectedTail)
        (List.replicate processed unaryUnit ++
          sourceLeftBoundary :: sourceWord)
    have scratchReserve :
        capacity - (processed + (scratchRemaining + 1)) =
          capacity - ((processed + 1) + scratchRemaining) := by
      omega
    have selectedReserve :
        capacity - (processed + (selectedRemaining + 1)) =
          capacity - ((processed + 1) + selectedRemaining) := by
      omega
    simpa [atScratchMark, loopConfiguration, scratchTail,
      scratchPayloadWord,
      selectedPayload, selectedTail, priorWord, scratchReserve,
      selectedReserve, List.replicate_succ,
      List.append_assoc] using step
  have h01 := exactRun_add slot 1 scratchTail.length
    _ _ _ hScratch hSeek
  have h02 := exactRun_add slot (1 + scratchTail.length) 1
    _ _ _ h01 hLedger
  have h03 := exactRun_add slot
    (1 + scratchTail.length + 1) priorWord.length
    _ _ _ h02 hPrefix
  have h04 := exactRun_add slot
    (1 + scratchTail.length + 1 + priorWord.length) 1
    _ _ _ h03 hSelectedBoundary
  have h05 := exactRun_add slot
    (1 + scratchTail.length + 1 + priorWord.length + 1)
    processed _ _ _ h04 hMarks
  have h06 := exactRun_add slot
    (1 + scratchTail.length + 1 + priorWord.length + 1 +
      processed) 1 _ _ _ h05 hUnit
  have h07 := exactRun_add slot
    (1 + scratchTail.length + 1 + priorWord.length + 1 +
      processed + 1) returnWord.length _ _ _
    h06 hReturnLedger
  have h08 := exactRun_add slot
    (1 + scratchTail.length + 1 + priorWord.length + 1 +
      processed + 1 + returnWord.length) 1 _ _ _
    h07 hReturnBoundary
  have h09 := exactRun_add slot
    (1 + scratchTail.length + 1 + priorWord.length + 1 +
      processed + 1 + returnWord.length + 1)
    scratchTail.length _ _ _ h08 hReturnScratch
  have complete := exactRun_add slot
    (1 + scratchTail.length + 1 + priorWord.length + 1 +
      processed + 1 + returnWord.length + 1 +
      scratchTail.length) 1 _ _ _ h09 hScratchMark
  have scratchLength :
      scratchTail.length = capacity - processed := by
    simp [scratchTail, scratchPayloadWord]
    omega
  have returnLength :
      returnWord.length =
        processed + 1 + priorWord.length := by
    simp [returnWord]
    omega
  have steps :
      1 + scratchTail.length + 1 + priorWord.length + 1 +
          processed + 1 + returnWord.length + 1 +
          scratchTail.length + 1 =
        pairSteps capacity priorWord.length := by
    rw [scratchLength, returnLength]
    unfold pairSteps
    omega
  rw [steps] at complete
  simpa [priorWord] using complete

/-! ### Finish after every scratch unit has been paired -/

private theorem seek_ledger_blanks_exact (slot : Slot)
    (count : Nat) (left right : List WorkSymbol) :
    workRunExact? (machineFor slot) count
        (configAtLeftWord (compareSeekLedgerState slot)
          (List.replicate count WorkSymbol.blank ++ left) right) =
      some
        (configAtLeftWord (compareSeekLedgerState slot)
          left (List.replicate count WorkSymbol.blank ++ right)) := by
  have scanned := scanLeftExact slot
    (compareSeekLedgerState slot)
    (fun symbol => symbol = WorkSymbol.blank)
    (fun head leftTail rightSide equality => by
      subst head
      exact compare_seek_ledger_payload_step slot
        WorkSymbol.blank (Or.inr (Or.inr rfl))
        leftTail rightSide)
    (List.replicate count WorkSymbol.blank)
    left right (by simp)
  simpa using scanned

private def outcomeSymbol (equal : Bool) : WorkSymbol :=
  if equal then unarySeparator else unaryUnit

private def outcomeTail (equal : Bool)
    (capacity processed extra : Nat)
    (outerLeft : List WorkSymbol) : List WorkSymbol :=
  if equal then
    List.replicate (capacity - processed) WorkSymbol.blank ++
      outerLeft
  else
    List.replicate extra unaryUnit ++
      unarySeparator ::
        List.replicate
            (capacity - (processed + (extra + 1)))
            WorkSymbol.blank ++
          outerLeft

private def remainingValue (equal : Bool) (extra : Nat) : Nat :=
  if equal then 0 else extra + 1

private def finishedConfiguration (equal : Bool)
    (capacity processed extra : Nat)
    (priorWord outerLeft sourceWord : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord
    (if equal then acceptState else rejectState)
    (sourceLeftBoundary ::
      scratchWord capacity processed ++ ledgerBoundary ::
        (priorWord ++ slotBoundary ::
          List.replicate processed unaryUnit ++
            outcomeSymbol equal ::
              outcomeTail equal capacity processed extra outerLeft))
    sourceWord

private theorem finish_exact (slot : Slot)
    (equal : Bool) (capacity processed extra : Nat)
    (priorValues : List Nat)
    (outerLeft sourceWord : List WorkSymbol)
    (priorLength :
      priorValues.length = slotCode slot)
    (scratchFits : processed ≤ capacity) :
    workRunExact? (machineFor slot)
        (finishSteps capacity
          (valuesWord capacity priorValues).length processed)
        (loopConfiguration slot capacity processed 0
          (remainingValue equal extra)
          (valuesWord capacity priorValues) outerLeft sourceWord) =
      some
        (finishedConfiguration equal capacity processed extra
          (valuesWord capacity priorValues) outerLeft sourceWord) := by
  let priorWord := valuesWord capacity priorValues
  let scratchReserve :=
    List.replicate (capacity - processed) WorkSymbol.blank
  let scratchW := scratchWord capacity processed
  let selectedRest :=
    outcomeSymbol equal ::
      outcomeTail equal capacity processed extra outerLeft
  let afterScratchSeparator :=
    configAtLeftWord (compareSeekLedgerState slot)
      (scratchReserve ++ ledgerBoundary ::
        (priorWord ++ slotBoundary ::
          List.replicate processed selectedMark ++ selectedRest))
      (unarySeparator :: List.replicate processed unaryUnit ++
        sourceLeftBoundary :: sourceWord)
  let atLedger :=
    configAtLeftWord (compareSeekLedgerState slot)
      (ledgerBoundary ::
        (priorWord ++ slotBoundary ::
          List.replicate processed selectedMark ++ selectedRest))
      (scratchReserve ++ unarySeparator ::
        List.replicate processed unaryUnit ++
          sourceLeftBoundary :: sourceWord)
  let afterLedger :=
    configAtLeftWord
      (compareSeekSlotState slot (slotCode slot))
      (priorWord ++ slotBoundary ::
        List.replicate processed selectedMark ++ selectedRest)
      (ledgerBoundary :: scratchReserve ++ unarySeparator ::
        List.replicate processed unaryUnit ++
          sourceLeftBoundary :: sourceWord)
  let atSelectedBoundary :=
    configAtLeftWord (compareSeekSlotState slot 0)
      (slotBoundary ::
        List.replicate processed selectedMark ++ selectedRest)
      (priorWord.reverse ++ ledgerBoundary ::
        scratchReserve ++ unarySeparator ::
          List.replicate processed unaryUnit ++
            sourceLeftBoundary :: sourceWord)
  let atSelected :=
    configAtLeftWord (compareSelectedState slot)
      (List.replicate processed selectedMark ++ selectedRest)
      (slotBoundary :: priorWord.reverse ++ ledgerBoundary ::
        scratchReserve ++ unarySeparator ::
          List.replicate processed unaryUnit ++
            sourceLeftBoundary :: sourceWord)
  let atOutcome :=
    configAtLeftWord (compareSelectedState slot) selectedRest
      (List.replicate processed selectedMark ++
        slotBoundary :: priorWord.reverse ++ ledgerBoundary ::
          scratchReserve ++ unarySeparator ::
            List.replicate processed unaryUnit ++
              sourceLeftBoundary :: sourceWord)
  let restoringLedger :=
    configAtWord
      (if equal then restoreEqualLedgerState
        else restoreLessLedgerState)
      selectedRest
      (List.replicate processed selectedMark ++
        slotBoundary :: priorWord.reverse ++ ledgerBoundary ::
          scratchReserve ++ unarySeparator ::
            List.replicate processed unaryUnit ++
              sourceLeftBoundary :: sourceWord)
  let afterMarks :=
    configAtWord
      (if equal then restoreEqualLedgerState
        else restoreLessLedgerState)
      (List.replicate processed unaryUnit ++ selectedRest)
      (slotBoundary :: priorWord.reverse ++ ledgerBoundary ::
        scratchReserve ++ unarySeparator ::
          List.replicate processed unaryUnit ++
            sourceLeftBoundary :: sourceWord)
  let restoreWord := slotBoundary :: priorWord.reverse
  let atLedgerRestore :=
    configAtWord
      (if equal then restoreEqualLedgerState
        else restoreLessLedgerState)
      (priorWord ++ slotBoundary ::
        List.replicate processed unaryUnit ++ selectedRest)
      (ledgerBoundary :: scratchReserve ++ unarySeparator ::
        List.replicate processed unaryUnit ++
          sourceLeftBoundary :: sourceWord)
  let restoringScratch :=
    configAtWord
      (if equal then restoreEqualScratchState
        else restoreLessScratchState)
      (ledgerBoundary :: priorWord ++ slotBoundary ::
        List.replicate processed unaryUnit ++ selectedRest)
      (scratchW.reverse ++ sourceLeftBoundary :: sourceWord)
  let atSourceBoundary :=
    configAtWord
      (if equal then restoreEqualScratchState
        else restoreLessScratchState)
      (scratchW ++ ledgerBoundary :: priorWord ++ slotBoundary ::
        List.replicate processed unaryUnit ++ selectedRest)
      (sourceLeftBoundary :: sourceWord)
  have hScratchSeparator :
      workRunExact? (machineFor slot) 1
          (loopConfiguration slot capacity processed 0
            (remainingValue equal extra) priorWord
            outerLeft sourceWord) =
        some afterScratchSeparator := by
    apply exactRun_one slot
    cases equal <;>
      simpa [loopConfiguration, afterScratchSeparator,
        remainingValue,
        selectedPayload, selectedRest, outcomeSymbol, outcomeTail,
        scratchReserve, priorWord, List.replicate_succ,
        List.append_assoc] using
        scratch_separator_step slot
          (scratchReserve ++ ledgerBoundary ::
            (priorWord ++ slotBoundary ::
              List.replicate processed selectedMark ++
                selectedRest))
          (List.replicate processed unaryUnit ++
            sourceLeftBoundary :: sourceWord)
  have hBlanks :
      workRunExact? (machineFor slot) scratchReserve.length
          afterScratchSeparator =
        some atLedger := by
    simpa [afterScratchSeparator, atLedger, scratchReserve,
      List.append_assoc] using
      seek_ledger_blanks_exact slot (capacity - processed)
        (ledgerBoundary ::
          (priorWord ++ slotBoundary ::
            List.replicate processed selectedMark ++ selectedRest))
        (unarySeparator :: List.replicate processed unaryUnit ++
          sourceLeftBoundary :: sourceWord)
  have hLedger :
      workRunExact? (machineFor slot) 1 atLedger =
        some afterLedger := by
    apply exactRun_one slot
    simpa [atLedger, afterLedger] using
      compare_seek_ledger_boundary_step slot
        (priorWord ++ slotBoundary ::
          List.replicate processed selectedMark ++ selectedRest)
        (scratchReserve ++ unarySeparator ::
          List.replicate processed unaryUnit ++
            sourceLeftBoundary :: sourceWord)
  have priorLe : priorValues.length ≤ 5 := by
    rw [priorLength]
    exact TargetEmitterScratchAddSlot.slotCode_le_five slot
  have hPrefix :
      workRunExact? (machineFor slot) priorWord.length
          afterLedger =
        some atSelectedBoundary := by
    simpa [afterLedger, atSelectedBoundary, priorWord,
      slotSeekState, priorLength, List.append_assoc] using
      slot_seek_prefix_exact slot true capacity priorValues priorLe
        (slotBoundary ::
          List.replicate processed selectedMark ++ selectedRest)
        (ledgerBoundary :: scratchReserve ++ unarySeparator ::
          List.replicate processed unaryUnit ++
            sourceLeftBoundary :: sourceWord)
  have hSelectedBoundary :
      workRunExact? (machineFor slot) 1 atSelectedBoundary =
        some atSelected := by
    apply exactRun_one slot
    simpa [atSelectedBoundary, atSelected,
      slotSeekState, slotSelectedState] using
      slot_selected_boundary_step slot true
        (List.replicate processed selectedMark ++ selectedRest)
        (priorWord.reverse ++ ledgerBoundary ::
          scratchReserve ++ unarySeparator ::
            List.replicate processed unaryUnit ++
              sourceLeftBoundary :: sourceWord)
  have hMarks :
      workRunExact? (machineFor slot) processed atSelected =
        some atOutcome := by
    simpa [atSelected, atOutcome, slotSelectedState,
      List.append_assoc] using
      selected_marks_exact slot true processed selectedRest
        (slotBoundary :: priorWord.reverse ++ ledgerBoundary ::
          scratchReserve ++ unarySeparator ::
            List.replicate processed unaryUnit ++
              sourceLeftBoundary :: sourceWord)
  have hOutcome :
      workRunExact? (machineFor slot) 1 atOutcome =
        some restoringLedger := by
    apply exactRun_one slot
    cases equal
    · simpa [atOutcome, restoringLedger, selectedRest,
        outcomeSymbol, outcomeTail] using
        compare_selected_unit_step slot
          (outcomeTail false capacity processed extra outerLeft)
          (List.replicate processed selectedMark ++
            slotBoundary :: priorWord.reverse ++ ledgerBoundary ::
              scratchReserve ++ unarySeparator ::
                List.replicate processed unaryUnit ++
                  sourceLeftBoundary :: sourceWord)
    · simpa [atOutcome, restoringLedger, selectedRest,
        outcomeSymbol, outcomeTail] using
        compare_selected_separator_step slot
          (outcomeTail true capacity processed extra outerLeft)
          (List.replicate processed selectedMark ++
            slotBoundary :: priorWord.reverse ++ ledgerBoundary ::
              scratchReserve ++ unarySeparator ::
                List.replicate processed unaryUnit ++
                  sourceLeftBoundary :: sourceWord)
  have hRestoreMarks :
      workRunExact? (machineFor slot) processed restoringLedger =
        some afterMarks := by
    simpa [restoringLedger, afterMarks, selectedRest] using
      restore_marks_exact slot equal processed selectedRest
        (slotBoundary :: priorWord.reverse ++ ledgerBoundary ::
          scratchReserve ++ unarySeparator ::
            List.replicate processed unaryUnit ++
              sourceLeftBoundary :: sourceWord)
  have restoreAllowed :
      ∀ symbol, symbol ∈ restoreWord →
        symbol = unaryUnit ∨ symbol = unarySeparator ∨
          symbol = WorkSymbol.blank ∨ symbol = slotBoundary := by
    intro symbol member
    unfold restoreWord at member
    cases member with
    | head =>
        exact Or.inr (Or.inr (Or.inr rfl))
    | tail _ fromPrior =>
        exact valuesWord_restore_allowed capacity priorValues
          symbol (List.mem_reverse.mp fromPrior)
  have hRestoreLedger :
      workRunExact? (machineFor slot) restoreWord.length afterMarks =
        some atLedgerRestore := by
    have scanned :=
      restore_ledger_word_exact slot equal restoreWord
        (ledgerBoundary :: scratchReserve ++ unarySeparator ::
          List.replicate processed unaryUnit ++
            sourceLeftBoundary :: sourceWord)
        (List.replicate processed unaryUnit ++ selectedRest)
        restoreAllowed
    simpa [afterMarks, atLedgerRestore, restoreWord,
      priorWord, List.reverse_append,
      List.append_assoc] using scanned
  have hRestoreBoundary :
      workRunExact? (machineFor slot) 1 atLedgerRestore =
        some restoringScratch := by
    apply exactRun_one slot
    have step :=
      restore_ledger_boundary_step slot equal
        (priorWord ++ slotBoundary ::
          List.replicate processed unaryUnit ++ selectedRest)
        (scratchReserve ++ unarySeparator ::
          List.replicate processed unaryUnit ++
            sourceLeftBoundary :: sourceWord)
    simpa [atLedgerRestore, restoringScratch, scratchW,
      scratchWord, TargetEmitterScratchAddSlot.scratchWord,
      scratchReserve, unaryUnit, unarySeparator,
      TargetEmitterScratchAddSlot.unaryUnit,
      TargetEmitterScratchAddSlot.unarySeparator,
      List.reverse_append, List.append_assoc] using step
  have scratchAllowed :
      ∀ symbol, symbol ∈ scratchW.reverse →
        ScratchPayload symbol := by
    intro symbol member
    exact scratchWord_allowed capacity processed symbol
      (List.mem_reverse.mp member)
  have hRestoreScratch :
      workRunExact? (machineFor slot) scratchW.length
          restoringScratch =
        some atSourceBoundary := by
    have scanned :=
      restore_scratch_word_exact slot equal scratchW.reverse
        (sourceLeftBoundary :: sourceWord)
        (ledgerBoundary :: priorWord ++ slotBoundary ::
          List.replicate processed unaryUnit ++ selectedRest)
        scratchAllowed
    simpa [restoringScratch, atSourceBoundary,
      List.append_assoc] using scanned
  have hSourceBoundary :
      workRunExact? (machineFor slot) 1 atSourceBoundary =
        some
          (finishedConfiguration equal capacity processed extra
            priorWord outerLeft sourceWord) := by
    apply exactRun_one slot
    have step :=
      restore_source_boundary_step slot equal
        (scratchW ++ ledgerBoundary :: priorWord ++ slotBoundary ::
          List.replicate processed unaryUnit ++ selectedRest)
        sourceWord
    simpa [atSourceBoundary, finishedConfiguration,
      selectedRest, scratchW, priorWord] using step
  have h01 := exactRun_add slot 1 scratchReserve.length
    _ _ _ hScratchSeparator hBlanks
  have h02 := exactRun_add slot
    (1 + scratchReserve.length) 1 _ _ _ h01 hLedger
  have h03 := exactRun_add slot
    (1 + scratchReserve.length + 1) priorWord.length
    _ _ _ h02 hPrefix
  have h04 := exactRun_add slot
    (1 + scratchReserve.length + 1 + priorWord.length) 1
    _ _ _ h03 hSelectedBoundary
  have h05 := exactRun_add slot
    (1 + scratchReserve.length + 1 + priorWord.length + 1)
    processed _ _ _ h04 hMarks
  have h06 := exactRun_add slot
    (1 + scratchReserve.length + 1 + priorWord.length + 1 +
      processed) 1 _ _ _ h05 hOutcome
  have h07 := exactRun_add slot
    (1 + scratchReserve.length + 1 + priorWord.length + 1 +
      processed + 1) processed _ _ _ h06 hRestoreMarks
  have h08 := exactRun_add slot
    (1 + scratchReserve.length + 1 + priorWord.length + 1 +
      processed + 1 + processed) restoreWord.length _ _ _
    h07 hRestoreLedger
  have h09 := exactRun_add slot
    (1 + scratchReserve.length + 1 + priorWord.length + 1 +
      processed + 1 + processed + restoreWord.length) 1 _ _ _
    h08 hRestoreBoundary
  have h10 := exactRun_add slot
    (1 + scratchReserve.length + 1 + priorWord.length + 1 +
      processed + 1 + processed + restoreWord.length + 1)
    scratchW.length _ _ _ h09 hRestoreScratch
  have complete := exactRun_add slot
    (1 + scratchReserve.length + 1 + priorWord.length + 1 +
      processed + 1 + processed + restoreWord.length + 1 +
      scratchW.length) 1 _ _ _ h10 hSourceBoundary
  have reserveLength :
      scratchReserve.length = capacity - processed := by
    simp [scratchReserve]
  have restoreLength :
      restoreWord.length = priorWord.length + 1 := by
    simp [restoreWord]
  have scratchLength :
      scratchW.length = capacity + 1 :=
    scratchWord_length_of_le capacity processed scratchFits
  have steps :
      1 + scratchReserve.length + 1 + priorWord.length + 1 +
          processed + 1 + processed + restoreWord.length + 1 +
          scratchW.length + 1 =
        finishSteps capacity priorWord.length processed := by
    rw [reserveLength, restoreLength, scratchLength]
    unfold finishSteps
    omega
  rw [steps] at complete
  simpa [priorWord] using complete

/-! ### Complete comparison trace -/

private def processSteps (capacity prefixLength processed : Nat) :
    Nat → Nat
  | 0 =>
      finishSteps capacity prefixLength processed
  | remaining + 1 =>
      pairSteps capacity prefixLength +
        processSteps capacity prefixLength (processed + 1) remaining

private theorem processSteps_evaluated
    (capacity prefixLength processed remaining : Nat) :
    processSteps capacity prefixLength processed remaining =
      remaining * pairSteps capacity prefixLength +
        finishSteps capacity prefixLength (processed + remaining) := by
  induction remaining generalizing processed with
  | zero =>
      simp [processSteps]
  | succ remaining inductionHypothesis =>
      simp only [processSteps]
      rw [inductionHypothesis (processed + 1)]
      simp only [Nat.succ_mul]
      unfold finishSteps
      omega

private theorem process_exact (slot : Slot)
    (equal : Bool) (capacity processed remaining extra : Nat)
    (priorValues : List Nat)
    (outerLeft sourceWord : List WorkSymbol)
    (priorLength :
      priorValues.length = slotCode slot)
    (scratchFits : processed + remaining ≤ capacity)
    (selectedFits :
      processed + (remaining + remainingValue equal extra) ≤
        capacity) :
    workRunExact? (machineFor slot)
        (processSteps capacity
          (valuesWord capacity priorValues).length
          processed remaining)
        (loopConfiguration slot capacity processed remaining
          (remaining + remainingValue equal extra)
          (valuesWord capacity priorValues) outerLeft sourceWord) =
      some
        (finishedConfiguration equal capacity
          (processed + remaining) extra
          (valuesWord capacity priorValues) outerLeft sourceWord) := by
  induction remaining generalizing processed with
  | zero =>
      simpa [processSteps] using
        finish_exact slot equal capacity processed extra
          priorValues outerLeft sourceWord priorLength scratchFits
  | succ remaining inductionHypothesis =>
      have scratchCycleFits :
          processed + (remaining + 1) ≤ capacity := by
        omega
      have selectedCycleFits :
          processed +
              ((remaining + remainingValue equal extra) + 1) ≤
            capacity := by
        omega
      have hCycle :=
        cycle_exact slot capacity processed remaining
          (remaining + remainingValue equal extra)
          priorValues outerLeft sourceWord priorLength
          scratchCycleFits selectedCycleFits
      have scratchRestFits :
          (processed + 1) + remaining ≤ capacity := by
        omega
      have selectedRestFits :
          (processed + 1) +
              (remaining + remainingValue equal extra) ≤
            capacity := by
        omega
      have hRest :=
        inductionHypothesis (processed + 1)
          scratchRestFits selectedRestFits
      have complete := exactRun_add slot
        (pairSteps capacity
          (valuesWord capacity priorValues).length)
        (processSteps capacity
          (valuesWord capacity priorValues).length
          (processed + 1) remaining)
        _ _ _ hCycle hRest
      have selectedShape :
          (remaining + 1) + remainingValue equal extra =
            (remaining + remainingValue equal extra) + 1 := by
        omega
      have processedShape :
          processed + 1 + remaining =
            processed + (remaining + 1) := by
        omega
      simpa [processSteps, selectedShape,
        processedShape] using complete

private theorem core_exact (slot : Slot)
    (equal : Bool) (capacity scratch extra : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (selectedShape :
      selectedValue slot registers =
        scratch + remainingValue equal extra)
    (allowed : SourceAllowed sourceHead) :
    workRunExact? (machineFor slot)
        (workSteps slot capacity scratch)
        (entryConfiguration slot capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) =
      some
        (finishedConfiguration equal capacity scratch extra
          (prefixWord capacity slot registers)
          (suffixWord capacity slot registers ++ outsideLeft)
          (sourceHead :: sourceTail ++ targetAndRight)) := by
  let priorValues :=
    TargetEmitterScratchAddSlot.prefixValues slot registers
  let outerLeft :=
    suffixWord capacity slot registers ++ outsideLeft
  let sourceWord :=
    sourceHead :: sourceTail ++ targetAndRight
  have hInitial :=
    initial_exact slot capacity scratch registers sourceHead
      sourceTail targetAndRight outsideLeft allowed
  have scratchFits : scratch ≤ capacity := by
    have selectedLe :
        selectedValue slot registers ≤ capacity := by
      simpa [selectedValue] using
        TargetEmitterScratchAddSlot.selectedValue_le capacity slot
          registers fits
    omega
  have selectedFits :
      scratch + remainingValue equal extra ≤ capacity := by
    rw [← selectedShape]
    exact TargetEmitterScratchAddSlot.selectedValue_le
      capacity slot registers fits
  have hProcess :=
    process_exact slot equal capacity 0 scratch extra
      priorValues outerLeft sourceWord
      (TargetEmitterScratchAddSlot.prefixValues_length
        slot registers)
      (by simpa using scratchFits)
      (by simpa using selectedFits)
  have priorWordEq :
      valuesWord capacity priorValues =
        prefixWord capacity slot registers := by
    rfl
  have initialTargetEq :
      loopConfiguration slot capacity 0 scratch
          (selectedValue slot registers)
          (prefixWord capacity slot registers)
          outerLeft sourceWord =
        loopConfiguration slot capacity 0 scratch
          (scratch + remainingValue equal extra)
          (valuesWord capacity priorValues)
          outerLeft sourceWord := by
    rw [priorWordEq, selectedShape]
  rw [initialTargetEq] at hInitial
  have complete := exactRun_add slot 2
    (processSteps capacity
      (valuesWord capacity priorValues).length 0 scratch)
    _ _ _ hInitial hProcess
  have evaluated :=
    processSteps_evaluated capacity
      (valuesWord capacity priorValues).length 0 scratch
  have prefixLength :
      (prefixWord capacity slot registers).length =
        slotCode slot * (capacity + 2) := by
    simpa [prefixWord, slotCode,
      TargetEmitterScratchAddSlot.slotCode] using
      TargetEmitterScratchAddSlot.prefixWord_length
        capacity slot registers fits
  have steps :
      2 +
          processSteps capacity
            (valuesWord capacity priorValues).length 0 scratch =
        workSteps slot capacity scratch := by
    rw [evaluated, priorWordEq, prefixLength]
    unfold workSteps
    simp only [Nat.zero_add]
    omega
  rw [steps] at complete
  simpa [priorWordEq, outerLeft, sourceWord] using complete

private theorem replicate_add {α : Type}
    (first second : Nat) (item : α) :
    List.replicate (first + second) item =
      List.replicate first item ++
        List.replicate second item := by
  induction first with
  | zero =>
      simp
  | succ first inductionHypothesis =>
      rw [show first + 1 + second =
        (first + second) + 1 by omega]
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons item) inductionHypothesis

private theorem cons_replicate_append_commute
    (count : Nat) (item : WorkSymbol)
    (tail : List WorkSymbol) :
    item :: (List.replicate count item ++ tail) =
      List.replicate count item ++ item :: tail := by
  calc
    item :: (List.replicate count item ++ tail) =
        List.replicate (count + 1) item ++ tail := by
      rfl
    _ = List.replicate count item ++ item :: tail :=
      (replicate_append_self_cons count item tail).symm

private theorem finished_equal_eq (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (equal : selectedValue slot registers = scratch) :
    finishedConfiguration true capacity scratch 0
        (prefixWord capacity slot registers)
        (suffixWord capacity slot registers ++ outsideLeft)
        (sourceHead :: sourceTail ++ targetAndRight) =
      equalConfiguration slot capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft := by
  have equal' :
      TargetEmitterScratchAddSlot.selectedValue slot registers =
        scratch := by
    simpa [selectedValue] using equal
  unfold finishedConfiguration equalConfiguration
  rw [TargetEmitterScratchAddSlot.slotBank_decompose
    capacity slot registers]
  simp [outcomeSymbol, outcomeTail, slotWord_eq, slotPayload,
    equal',
    scratchWord, TargetEmitterScratchAddSlot.scratchWord,
    unaryUnit, unarySeparator,
    TargetEmitterScratchAddSlot.unaryUnit,
    TargetEmitterScratchAddSlot.unarySeparator,
    prefixWord, suffixWord, List.append_assoc]

private theorem finished_less_eq (slot : Slot)
    (capacity scratch extra : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (shape :
      selectedValue slot registers = scratch + (extra + 1)) :
    finishedConfiguration false capacity scratch extra
        (prefixWord capacity slot registers)
        (suffixWord capacity slot registers ++ outsideLeft)
        (sourceHead :: sourceTail ++ targetAndRight) =
      lessConfiguration slot capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft := by
  have shape' :
      TargetEmitterScratchAddSlot.selectedValue slot registers =
        scratch + (extra + 1) := by
    simpa [selectedValue] using shape
  unfold finishedConfiguration lessConfiguration
  rw [TargetEmitterScratchAddSlot.slotBank_decompose
    capacity slot registers]
  simp [outcomeSymbol, outcomeTail, slotWord_eq, slotPayload,
    shape', replicate_add, scratchWord,
    TargetEmitterScratchAddSlot.scratchWord,
    unaryUnit, unarySeparator,
    TargetEmitterScratchAddSlot.unaryUnit,
    TargetEmitterScratchAddSlot.unarySeparator,
    prefixWord, suffixWord, List.append_assoc]
  rw [cons_replicate_append_commute]

/-! ### Public exact endpoints and preservation -/

/-- If scratch equals the selected slot, the literal controller reaches its
accept endpoint in exactly the frozen number of work steps. -/
theorem equal_exact (slot : Slot) (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (equal : scratch = selectedValue slot registers)
    (allowed : SourceAllowed sourceHead) :
    workRunExact? (machineFor slot)
        (workSteps slot capacity scratch)
        (entryConfiguration slot capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) =
      some
        (equalConfiguration slot capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) := by
  have traced :=
    core_exact slot true capacity scratch 0 registers
      sourceHead sourceTail targetAndRight outsideLeft fits
      (by simpa [remainingValue] using equal.symm)
      allowed
  rw [finished_equal_eq slot capacity scratch registers
    sourceHead sourceTail targetAndRight outsideLeft equal.symm]
    at traced
  exact traced

/-- If scratch is strictly below the selected slot, the literal controller
reaches its reject endpoint in exactly the same frozen schedule and restores
the complete workspace. -/
theorem less_exact (slot : Slot) (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (less : scratch < selectedValue slot registers)
    (allowed : SourceAllowed sourceHead) :
    workRunExact? (machineFor slot)
        (workSteps slot capacity scratch)
        (entryConfiguration slot capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) =
      some
        (lessConfiguration slot capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) := by
  let extra :=
    selectedValue slot registers - (scratch + 1)
  have shape :
      selectedValue slot registers = scratch + (extra + 1) := by
    unfold extra
    omega
  have traced :=
    core_exact slot false capacity scratch extra registers
      sourceHead sourceTail targetAndRight outsideLeft fits
      (by simpa [remainingValue] using shape)
      allowed
  rw [finished_less_eq slot capacity scratch extra registers
    sourceHead sourceTail targetAndRight outsideLeft shape] at traced
  exact traced

theorem equal_tape_preserved (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    (equalConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft).tape =
    (entryConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft).tape := by
  rfl

theorem less_tape_preserved (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    (lessConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft).tape =
    (entryConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft).tape := by
  rfl

theorem equal_source_and_right_preserved (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    let final :=
      equalConfiguration slot capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft
    final.tape.head :: final.tape.right =
      sourceHead :: sourceTail ++ targetAndRight := by
  rfl

theorem less_source_and_right_preserved (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    let final :=
      lessConfiguration slot capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft
    final.tape.head :: final.tape.right =
      sourceHead :: sourceTail ++ targetAndRight := by
  rfl

theorem equal_left_workspace_preserved (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    (equalConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft).tape.left =
        sourceLeftBoundary ::
          scratchWord capacity scratch ++ ledgerBoundary ::
            (TargetEmitterLedger.slotBank capacity registers ++
              outsideLeft) := by
  rfl

theorem less_left_workspace_preserved (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol) :
    (lessConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft).tape.left =
        sourceLeftBoundary ::
          scratchWord capacity scratch ++ ledgerBoundary ::
            (TargetEmitterLedger.slotBank capacity registers ++
              outsideLeft) := by
  rfl

/-! ### Bounded work execution and compiled execution -/

theorem workRun_bounded_equal (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (equal : scratch = selectedValue slot registers)
    (allowed : SourceAllowed sourceHead) :
    workRun (machineFor slot)
        (polynomialWorkBound capacity scratch)
        (entryConfiguration slot capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) =
      equalConfiguration slot capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft := by
  exact workRun_of_workRunExact_halted_le
    (machineFor slot) (workSteps slot capacity scratch)
    (polynomialWorkBound capacity scratch)
    (entryConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (equalConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (equal_exact slot capacity scratch registers sourceHead
      sourceTail targetAndRight outsideLeft fits equal allowed)
    (equal_halted slot capacity scratch registers sourceHead
      sourceTail targetAndRight outsideLeft)
    (workSteps_le_polynomialWorkBound slot capacity scratch)

theorem workRun_bounded_less (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (less : scratch < selectedValue slot registers)
    (allowed : SourceAllowed sourceHead) :
    workRun (machineFor slot)
        (polynomialWorkBound capacity scratch)
        (entryConfiguration slot capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) =
      lessConfiguration slot capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft := by
  exact workRun_of_workRunExact_halted_le
    (machineFor slot) (workSteps slot capacity scratch)
    (polynomialWorkBound capacity scratch)
    (entryConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (lessConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (less_exact slot capacity scratch registers sourceHead
      sourceTail targetAndRight outsideLeft fits less allowed)
    (less_halted slot capacity scratch registers sourceHead
      sourceTail targetAndRight outsideLeft)
    (workSteps_le_polynomialWorkBound slot capacity scratch)

theorem workRun_bounded_equal_accepts (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (equal : scratch = selectedValue slot registers)
    (allowed : SourceAllowed sourceHead) :
    (workRun (machineFor slot)
      (polynomialWorkBound capacity scratch)
      (entryConfiguration slot capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft)).state =
        (machineFor slot).acceptState := by
  rw [workRun_bounded_equal slot capacity scratch registers
    sourceHead sourceTail targetAndRight outsideLeft
    fits equal allowed]
  rfl

theorem workRun_bounded_less_rejects (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (less : scratch < selectedValue slot registers)
    (allowed : SourceAllowed sourceHead) :
    (workRun (machineFor slot)
      (polynomialWorkBound capacity scratch)
      (entryConfiguration slot capacity scratch registers
        sourceHead sourceTail targetAndRight outsideLeft)).state =
        (machineFor slot).rejectState := by
  rw [workRun_bounded_less slot capacity scratch registers
    sourceHead sourceTail targetAndRight outsideLeft
    fits less allowed]
  rfl

def rawTimeBound (capacity scratch : Nat) : Nat :=
  6 * polynomialWorkBound capacity scratch

theorem six_workSteps_le_rawTimeBound (slot : Slot)
    (capacity scratch : Nat) :
    6 * workSteps slot capacity scratch ≤
      rawTimeBound capacity scratch := by
  unfold rawTimeBound
  exact Nat.mul_le_mul_left 6
    (workSteps_le_polynomialWorkBound slot capacity scratch)

theorem run_compiled_equal_exact (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (equal : scratch = selectedValue slot registers)
    (allowed : SourceAllowed sourceHead) :
    run (compiledMachineFor slot)
        (6 * workSteps slot capacity scratch)
        (encodeWorkConfiguration
          (entryConfiguration slot capacity scratch registers
            sourceHead sourceTail targetAndRight outsideLeft)) =
      encodeWorkConfiguration
        (equalConfiguration slot capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) := by
  exact run_compileWorkMachine_mul_of_workRunExact
    (machineFor slot) (workSteps slot capacity scratch)
    (entryConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (equalConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (equal_exact slot capacity scratch registers sourceHead
      sourceTail targetAndRight outsideLeft fits equal allowed)

theorem run_compiled_less_exact (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (less : scratch < selectedValue slot registers)
    (allowed : SourceAllowed sourceHead) :
    run (compiledMachineFor slot)
        (6 * workSteps slot capacity scratch)
        (encodeWorkConfiguration
          (entryConfiguration slot capacity scratch registers
            sourceHead sourceTail targetAndRight outsideLeft)) =
      encodeWorkConfiguration
        (lessConfiguration slot capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) := by
  exact run_compileWorkMachine_mul_of_workRunExact
    (machineFor slot) (workSteps slot capacity scratch)
    (entryConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (lessConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (less_exact slot capacity scratch registers sourceHead
      sourceTail targetAndRight outsideLeft fits less allowed)

theorem run_compiled_equal_bounded (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (equal : scratch = selectedValue slot registers)
    (allowed : SourceAllowed sourceHead) :
    run (compiledMachineFor slot)
        (rawTimeBound capacity scratch)
        (encodeWorkConfiguration
          (entryConfiguration slot capacity scratch registers
            sourceHead sourceTail targetAndRight outsideLeft)) =
      encodeWorkConfiguration
        (equalConfiguration slot capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le
    (machineFor slot) (workSteps slot capacity scratch)
    (rawTimeBound capacity scratch)
    (entryConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (equalConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (equal_exact slot capacity scratch registers sourceHead
      sourceTail targetAndRight outsideLeft fits equal allowed)
    (equal_halted slot capacity scratch registers sourceHead
      sourceTail targetAndRight outsideLeft)
    (six_workSteps_le_rawTimeBound slot capacity scratch)

theorem run_compiled_less_bounded (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (less : scratch < selectedValue slot registers)
    (allowed : SourceAllowed sourceHead) :
    run (compiledMachineFor slot)
        (rawTimeBound capacity scratch)
        (encodeWorkConfiguration
          (entryConfiguration slot capacity scratch registers
            sourceHead sourceTail targetAndRight outsideLeft)) =
      encodeWorkConfiguration
        (lessConfiguration slot capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le
    (machineFor slot) (workSteps slot capacity scratch)
    (rawTimeBound capacity scratch)
    (entryConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (lessConfiguration slot capacity scratch registers
      sourceHead sourceTail targetAndRight outsideLeft)
    (less_exact slot capacity scratch registers sourceHead
      sourceTail targetAndRight outsideLeft fits less allowed)
    (less_halted slot capacity scratch registers sourceHead
      sourceTail targetAndRight outsideLeft)
    (six_workSteps_le_rawTimeBound slot capacity scratch)

theorem run_compiled_equal_blankEquivalent (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (equal : scratch = selectedValue slot registers)
    (allowed : SourceAllowed sourceHead)
    (initial : Configuration)
    (equivalent :
      Configuration.BlankEquivalent initial
        (encodeWorkConfiguration
          (entryConfiguration slot capacity scratch registers
            sourceHead sourceTail targetAndRight outsideLeft))) :
    Configuration.BlankEquivalent
      (run (compiledMachineFor slot)
        (rawTimeBound capacity scratch) initial)
      (encodeWorkConfiguration
        (equalConfiguration slot capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft)) := by
  have transported :=
    run_blankEquivalent (compiledMachineFor slot)
      (rawTimeBound capacity scratch) equivalent
  rw [run_compiled_equal_bounded slot capacity scratch registers
    sourceHead sourceTail targetAndRight outsideLeft fits equal
    allowed] at transported
  exact transported

theorem run_compiled_less_blankEquivalent (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight outsideLeft : List WorkSymbol)
    (fits : LedgerFits capacity registers)
    (less : scratch < selectedValue slot registers)
    (allowed : SourceAllowed sourceHead)
    (initial : Configuration)
    (equivalent :
      Configuration.BlankEquivalent initial
        (encodeWorkConfiguration
          (entryConfiguration slot capacity scratch registers
            sourceHead sourceTail targetAndRight outsideLeft))) :
    Configuration.BlankEquivalent
      (run (compiledMachineFor slot)
        (rawTimeBound capacity scratch) initial)
      (encodeWorkConfiguration
        (lessConfiguration slot capacity scratch registers
          sourceHead sourceTail targetAndRight outsideLeft)) := by
  have transported :=
    run_blankEquivalent (compiledMachineFor slot)
      (rawTimeBound capacity scratch) equivalent
  rw [run_compiled_less_bounded slot capacity scratch registers
    sourceHead sourceTail targetAndRight outsideLeft fits less
    allowed] at transported
  exact transported

/-! ### Fail-closed malformed workspaces -/

set_option maxRecDepth 1000000 in
private theorem find_scratch_malformed (slot : Slot)
    (symbol : WorkSymbol)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    findWorkRule rules (scratchState slot) symbol =
      some (literalRule (scratchState slot) symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · cases slot <;> decide
  · cases slot <;> decide
  · cases slot <;> decide
  · exact (notUnit rfl).elim
  · cases slot <;> decide
  · cases slot <;> decide
  · exact (notSeparator rfl).elim
  · cases slot <;> decide
  · cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_selected_malformed (slot : Slot)
    (symbol : WorkSymbol)
    (notMark : symbol ≠ selectedMark)
    (notUnit : symbol ≠ unaryUnit) :
    findWorkRule rules (selectedState slot) symbol =
      some (literalRule (selectedState slot) symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · cases slot <;> decide
  · cases slot <;> decide
  · cases slot <;> decide
  · exact (notUnit rfl).elim
  · cases slot <;> decide
  · cases slot <;> decide
  · cases slot <;> decide
  · exact (notMark rfl).elim
  · cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_compare_malformed (slot : Slot)
    (symbol : WorkSymbol)
    (notMark : symbol ≠ selectedMark)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    findWorkRule rules (compareSelectedState slot) symbol =
      some (literalRule (compareSelectedState slot) symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · cases slot <;> decide
  · cases slot <;> decide
  · cases slot <;> decide
  · exact (notUnit rfl).elim
  · cases slot <;> decide
  · cases slot <;> decide
  · exact (notSeparator rfl).elim
  · exact (notMark rfl).elim
  · cases slot <;> decide

set_option maxRecDepth 1000000 in
private theorem find_return_scratch_malformed (slot : Slot)
    (symbol : WorkSymbol)
    (notPayload : ¬ ScratchPayload symbol)
    (notMark : symbol ≠ scratchMark) :
    findWorkRule rules (returnScratchState slot) symbol =
      some (literalRule (returnScratchState slot) symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · exact (notPayload (Or.inr (Or.inr rfl))).elim
  · cases slot <;> decide
  · cases slot <;> decide
  · exact (notPayload (Or.inl rfl)).elim
  · exact (notMark rfl).elim
  · cases slot <;> decide
  · exact (notPayload (Or.inr (Or.inl rfl))).elim
  · cases slot <;> decide
  · cases slot <;> decide

private theorem stayFromLeftWord_of_find (slot : Slot)
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
      some
        (configAtLeftWord deadState (symbol :: left) right) := by
  calc
    workStep? (machineFor slot)
        (configAtLeftWord state (symbol :: left) right) =
      some
        (applyWorkRule
          (literalRule state symbol deadState symbol .stay)
          (configAtLeftWord state (symbol :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some
        (configAtLeftWord deadState (symbol :: left) right) := by
      rfl

private theorem stayFromWord_of_find (slot : Slot)
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
      some
        (configAtWord deadState left (symbol :: right)) := by
  calc
    workStep? (machineFor slot)
        (configAtWord state left (symbol :: right)) =
      some
        (applyWorkRule
          (literalRule state symbol deadState symbol .stay)
          (configAtWord state left (symbol :: right))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some
        (configAtWord deadState left (symbol :: right)) := by
      rfl

/-- Scratch accepts only its unary units and separator.  Every other
observed symbol is preserved while the controller enters the ruleless dead
state. -/
theorem malformed_scratch_enters_dead (slot : Slot)
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    workStep? (machineFor slot)
        (configAtLeftWord (scratchState slot)
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState (symbol :: left) right) := by
  exact stayFromLeftWord_of_find slot (scratchState slot)
    symbol left right (by cases slot <;> rfl)
    (find_scratch_malformed slot symbol notUnit notSeparator)

/-- Pairing cannot pass the selected slot's separator.  This is the local
fail-closed witness for the excluded case `selected < scratch`. -/
theorem exhausted_selected_enters_dead (slot : Slot)
    (left right : List WorkSymbol) :
    workStep? (machineFor slot)
        (configAtLeftWord (selectedState slot)
          (unarySeparator :: left) right) =
      some
        (configAtLeftWord deadState
          (unarySeparator :: left) right) := by
  exact stayFromLeftWord_of_find slot (selectedState slot)
    unarySeparator left right (by cases slot <;> rfl)
    (find_selected_malformed slot unarySeparator
      (by decide) (by decide))

theorem malformed_selected_enters_dead (slot : Slot)
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notMark : symbol ≠ selectedMark)
    (notUnit : symbol ≠ unaryUnit) :
    workStep? (machineFor slot)
        (configAtLeftWord (selectedState slot)
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState (symbol :: left) right) := by
  exact stayFromLeftWord_of_find slot (selectedState slot)
    symbol left right (by cases slot <;> rfl)
    (find_selected_malformed slot symbol notMark notUnit)

theorem malformed_compare_enters_dead (slot : Slot)
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notMark : symbol ≠ selectedMark)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    workStep? (machineFor slot)
        (configAtLeftWord (compareSelectedState slot)
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState (symbol :: left) right) := by
  exact stayFromLeftWord_of_find slot (compareSelectedState slot)
    symbol left right (by cases slot <;> rfl)
    (find_compare_malformed slot symbol notMark notUnit
      notSeparator)

theorem malformed_return_scratch_enters_dead (slot : Slot)
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notPayload : ¬ ScratchPayload symbol)
    (notMark : symbol ≠ scratchMark) :
    workStep? (machineFor slot)
        (configAtWord (returnScratchState slot) left
          (symbol :: right)) =
      some
        (configAtWord deadState left (symbol :: right)) := by
  exact stayFromWord_of_find slot (returnScratchState slot)
    symbol left right (by cases slot <;> rfl)
    (find_return_scratch_malformed slot symbol
      notPayload notMark)

end PNP.Concrete.LockedNAND.TargetEmitterScratchCompareSlot
