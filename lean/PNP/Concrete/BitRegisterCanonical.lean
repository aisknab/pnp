/-
Copyright (c) 2026 PNP Labs.

Canonical boundary-to-boundary register mutation machines. Every operation
starts and finishes at the explicit left boundary, so the finite program
compiler can compose operations without supplying an input-dependent cursor.
The exact traces include navigation, bridges, the full suffix and blank slack.
-/

import PNP.Concrete.BitRegisterClear

namespace PNP.Concrete.BitRegister.Operation

open TapePrimitive Mutation WorkMachineProgramGraph
open PipelineStateNamespace

theorem insert_wellFormed (bit : Bool) : ProgramWellFormed (insert bit) := by
  cases bit <;>
    refine ⟨?_, noRuleAt_of_all _ _ (by decide), noRuleAt_of_all _ _ (by decide), by decide⟩ <;>
    unfold QueryDistinct <;> decide

theorem pop_wellFormed : ProgramWellFormed pop :=
  ⟨WorkMachineProgramGraph.rules_pairwise _ popGraph_wellFormed,
    noRuleAt_globalAccept _, noRuleAt_globalReject _, machine_accept_ne_reject _⟩

theorem home_cursor_run (before : List BitString) (bits : BitString) (after : List Cell)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? home ((fieldCells before).length + 2)
      ⟨home.startState, cursor before bits after outside slack⟩ =
    some ⟨home.acceptState, atBoundary before bits after outside slack⟩ := by
  cases bits with
  | nil => exact home_run (fieldCells before) .separator outside (after.map Cell.symbol ++ tail slack)
  | cons bit rest =>
      have h := home_run (fieldCells before) (bitCell bit) outside (content rest after slack)
      cases bit <;> exact h

theorem insert_register_run (before : List BitString) (bit : Bool) (bits : BitString)
    (after : List Cell) (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (insert bit) (2 * (bits.length + 1 + after.length) + 3)
      ⟨(insert bit).startState, cursor before bits after outside slack⟩ =
    some ⟨(insert bit).acceptState, cursor before (bit :: bits) after outside (slack - 1)⟩ := by
  have hStart : (insert bit).startState = 0 := rfl
  have hAccept : (insert bit).acceptState = 1 := rfl
  rw [hStart, hAccept]
  cases bits with
  | nil =>
      have h := insert_run bit .separator after
        (reverseOnto (fieldWord before) (WorkSymbol.blankZero :: outside)) slack
      simpa only [cursor, content, List.length_nil, List.map_nil, List.nil_append,
        List.map_cons, List.cons_append, Cell.symbol, Nat.zero_add, Nat.add_comm 1] using h
  | cons head rest =>
      have h := insert_run bit (bitCell head) (bitCells rest ++ .separator :: after)
        (reverseOnto (fieldWord before) (WorkSymbol.blankZero :: outside)) slack
      have hLength : (bitCells rest ++ .separator :: after).length + 1 =
          (head :: rest).length + 1 + after.length := by
        simp only [List.length_append, bitCells_length, List.length_cons]
        omega
      rw [hLength] at h
      cases head <;>
        simpa only [cursor, content, List.map_cons, List.map_append, bitCells_symbols,
          List.cons_append, List.append_assoc, bitCell, Cell.symbol] using h

def pushFront (bit : Bool) : WorkMachine := WorkMachineChain.machine (insert bit) home

theorem pushFront_wellFormed (bit : Bool) : ProgramWellFormed (pushFront bit) :=
  chain_wellFormed (insert bit) home (insert_wellFormed bit) home_wellFormed

def pushFrontSteps (before : List BitString) (bits : BitString) (after : List Cell) : Nat :=
  2 * (bits.length + 1 + after.length) + (fieldCells before).length + 6

theorem pushFront_run (before : List BitString) (bit : Bool) (bits : BitString)
    (after : List Cell) (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (pushFront bit) (pushFrontSteps before bits after)
      ⟨(pushFront bit).startState, cursor before bits after outside slack⟩ =
    some ⟨(pushFront bit).acceptState, atBoundary before (bit :: bits) after outside (slack - 1)⟩ := by
  have h := WorkMachineChain.workRunExact (insert bit) home
    (2 * (bits.length + 1 + after.length) + 3) ((fieldCells before).length + 2)
    _ _ _ (insert_register_run before bit bits after outside slack) rfl
    (home_cursor_run before (bit :: bits) after outside (slack - 1))
  have hSteps : 2 * (bits.length + 1 + after.length) + 3 + 1 + ((fieldCells before).length + 2) =
      pushFrontSteps before bits after := by unfold pushFrontSteps; omega
  rw [hSteps] at h
  exact h

def pushAt (index : Nat) (bit : Bool) : WorkMachine :=
  WorkMachineChain.machine (seekFromBoundary index) (pushFront bit)

def popAt (index : Nat) : WorkMachine :=
  WorkMachineChain.machine (seekFromBoundary index) pop

def clearAt (index : Nat) : WorkMachine :=
  WorkMachineChain.machine (seekFromBoundary index) (clear index)

theorem pushAt_wellFormed (index : Nat) (bit : Bool) : ProgramWellFormed (pushAt index bit) :=
  chain_wellFormed _ _ (seekFromBoundary_wellFormed index) (pushFront_wellFormed bit)

theorem popAt_wellFormed (index : Nat) : ProgramWellFormed (popAt index) :=
  chain_wellFormed _ _ (seekFromBoundary_wellFormed index) pop_wellFormed

theorem clearAt_wellFormed (index : Nat) : ProgramWellFormed (clearAt index) :=
  chain_wellFormed _ _ (seekFromBoundary_wellFormed index) (clear_wellFormed index)

def pushAtSteps (before : List BitString) (bits : BitString) (after : List Cell) : Nat :=
  3 + seekSteps before + pushFrontSteps before bits after

def popAtSteps (before : List BitString) (bits : BitString) (after : List Cell) : Nat :=
  3 + seekSteps before + popSteps before bits after

def clearAtSteps (before : List BitString) (bits : BitString) (after : List Cell) : Nat :=
  3 + seekSteps before + clearSteps before bits after

theorem pushAt_run (before : List BitString) (bit : Bool) (bits : BitString)
    (after : List Cell) (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (pushAt before.length bit) (pushAtSteps before bits after)
      ⟨(pushAt before.length bit).startState, atBoundary before bits after outside slack⟩ =
    some ⟨(pushAt before.length bit).acceptState,
      atBoundary before (bit :: bits) after outside (slack - 1)⟩ := by
  have h := WorkMachineChain.workRunExact (seekFromBoundary before.length) (pushFront bit)
    (2 + seekSteps before) (pushFrontSteps before bits after) _ _ _
    (seekFromBoundary_run before outside (content bits after slack)) rfl
    (pushFront_run before bit bits after outside slack)
  have hSteps : 2 + seekSteps before + 1 + pushFrontSteps before bits after =
      pushAtSteps before bits after := by unfold pushAtSteps; omega
  rw [hSteps] at h
  exact h

theorem popAt_run (before : List BitString) (bits : BitString)
    (after : List Cell) (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (popAt before.length) (popAtSteps before bits after)
      ⟨(popAt before.length).startState, atBoundary before bits after outside slack⟩ =
    some ⟨(popAt before.length).acceptState,
      atBoundary before bits.tail after outside (popSlack bits slack)⟩ := by
  have h := WorkMachineChain.workRunExact (seekFromBoundary before.length) pop
    (2 + seekSteps before) (popSteps before bits after) _ _ _
    (seekFromBoundary_run before outside (content bits after slack)) rfl
    (pop_run before bits after outside slack)
  have hSteps : 2 + seekSteps before + 1 + popSteps before bits after =
      popAtSteps before bits after := by unfold popAtSteps; omega
  rw [hSteps] at h
  exact h

theorem clearAt_run (before : List BitString) (bits : BitString)
    (after : List Cell) (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (clearAt before.length) (clearAtSteps before bits after)
      ⟨(clearAt before.length).startState, atBoundary before bits after outside slack⟩ =
    some ⟨(clearAt before.length).acceptState,
      atBoundary before [] after outside (slack + bits.length)⟩ := by
  have h := WorkMachineChain.workRunExact (seekFromBoundary before.length) (clear before.length)
    (2 + seekSteps before) (clearSteps before bits after) _ _ _
    (seekFromBoundary_run before outside (content bits after slack)) rfl
    (clear_run before bits after outside slack)
  have hSteps : 2 + seekSteps before + 1 + clearSteps before bits after =
      clearAtSteps before bits after := by unfold clearAtSteps; omega
  rw [hSteps] at h
  exact h

theorem pushAt_raw_run (before : List BitString) (bit : Bool) (bits : BitString)
    (after : List Cell) (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (pushAt before.length bit))
      (6 * pushAtSteps before bits after)
      (encodeWorkConfiguration ⟨(pushAt before.length bit).startState,
        atBoundary before bits after outside slack⟩) =
    encodeWorkConfiguration ⟨(pushAt before.length bit).acceptState,
      atBoundary before (bit :: bits) after outside (slack - 1)⟩ :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (pushAt_run before bit bits after outside slack)

theorem popAt_raw_run (before : List BitString) (bits : BitString)
    (after : List Cell) (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (popAt before.length))
      (6 * popAtSteps before bits after)
      (encodeWorkConfiguration ⟨(popAt before.length).startState,
        atBoundary before bits after outside slack⟩) =
    encodeWorkConfiguration ⟨(popAt before.length).acceptState,
      atBoundary before bits.tail after outside (popSlack bits slack)⟩ :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (popAt_run before bits after outside slack)

theorem clearAt_raw_run (before : List BitString) (bits : BitString)
    (after : List Cell) (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (clearAt before.length))
      (6 * clearAtSteps before bits after)
      (encodeWorkConfiguration ⟨(clearAt before.length).startState,
        atBoundary before bits after outside slack⟩) =
    encodeWorkConfiguration ⟨(clearAt before.length).acceptState,
      atBoundary before [] after outside (slack + bits.length)⟩ :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (clearAt_run before bits after outside slack)

theorem pushAtSteps_le (before : List BitString) (bits : BitString) (after : List Cell) :
    pushAtSteps before bits after ≤ 3 * bankSpan before bits after + 2 := by
  have hFields := fieldCells_length_ge before
  simp only [pushAtSteps, seekSteps, fieldWord_length, pushFrontSteps, bankSpan]
  omega

theorem popAtSteps_le (before : List BitString) (bits : BitString) (after : List Cell) :
    popAtSteps before bits after ≤ 4 * bankSpan before bits after := by
  have hFields := fieldCells_length_ge before
  cases bits <;>
    simp only [popAtSteps, seekSteps, fieldWord_length, popSteps, bankSpan,
      List.length_nil, List.length_cons] <;> omega

theorem clearAtSteps_le (before : List BitString) (bits : BitString) (after : List Cell) :
    clearAtSteps before bits after ≤
      9 * bankSpan before bits after * bankSpan before bits after +
        15 * bankSpan before bits after + 8 := by
  have hClear := clearSteps_le_polynomial before bits after
  have hFields := fieldCells_length_ge before
  have hPrefix : (fieldCells before).length + before.length ≤ 2 * bankSpan before bits after := by
    unfold bankSpan; omega
  simp only [clearAtSteps, seekSteps, fieldWord_length]
  omega

end PNP.Concrete.BitRegister.Operation
