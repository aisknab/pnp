/-
Copyright (c) 2026 PNP Labs.

A uniform polynomial source-step bound for the closed frontend. Store-growth
bounds account for every intermediate field, including accumulated output, and
the gate-loop bound accounts for all malformed-input paths.
-/

import PNP.Concrete.NANDFrontendClosed

namespace PNP.Concrete.NANDFrontend

open BitRegister

theorem registers_fields_bounded (r : Registers) (bound : Nat) (h : r.store.Bounded bound) :
    r.input.length ≤ bound ∧ r.inputs.length ≤ bound ∧ r.width.length ≤ bound ∧
      r.gate.length ≤ bound ∧ r.reversed.length ≤ bound :=
  ⟨Store.get_length_le r.store 0 h, Store.get_length_le r.store 1 h,
    Store.get_length_le r.store 2 h, Store.get_length_le r.store 3 h,
    Store.get_length_le r.store 7 h⟩

theorem registers_bounded_of_run (p : Program 9) (fuel start stop bound : Nat) (r s : Registers)
    (execution : BitRegister.run p fuel (r.state start) = s.state stop)
    (bounded : r.store.Bounded bound) :
    s.store.Bounded (bound + fuel) := by
  have h := BitRegister.run_bounded p fuel (r.state start) bounded
  rw [execution] at h
  exact h

def headerBudget (bound : Nat) : Nat := 6 * bound + 19

def constantsBudget (bound : Nat) : Nat := 24 * (bound + headerBudget bound) + 58

def preLoopBound (bound : Nat) : Nat := bound + headerBudget bound + constantsBudget bound

def traversalBudget (bound : Nat) : Nat :=
  128 * (preLoopBound bound + 1) * (3 * preLoopBound bound + 1)

def outputBudget (bound : Nat) : Nat :=
  256 * (4 * (preLoopBound bound + traversalBudget bound) + 1)

def frontendBudget (bound : Nat) : Nat :=
  headerBudget bound + constantsBudget bound + traversalBudget bound + outputBudget bound + 3

theorem frontendFuel_bound (r : Registers) (bound : Nat) (bounded : r.store.Bounded bound) :
    frontendFuel r ≤ frontendBudget bound := by
  have ps := program_segments
  have initialBound := registers_fields_bounded r bound bounded
  have hb : (headerResult r).fuel ≤ headerBudget bound := by
    have h := header_result_bound r
    unfold headerBudget
    omega
  have headerStore := registers_bounded_of_run program (headerResult r).fuel 0
    (readerExit (headerResult r).valid 113 666) bound r (headerResult r).state
    (header_result_run program 0 113 666 r ps.1) bounded
  have headerStore' : (headerResult r).state.store.Bounded (bound + headerBudget bound) :=
    Store.bounded_mono headerStore (Nat.add_le_add_left hb bound)
  have headerFields := registers_fields_bounded (headerResult r).state _ headerStore'
  have cb : constantsFuel (headerResult r).state ≤ constantsBudget bound := by
    unfold constantsFuel constantsBudget
    omega
  have constantsStore := registers_bounded_of_run program (constantsFuel (headerResult r).state)
    113 177 (bound + headerBudget bound) (headerResult r).state (initialized r)
    (constants_run program 113 177 (headerResult r).state ps.2.1) headerStore'
  have constantsStore' : (initialized r).store.Bounded (preLoopBound bound) :=
    Store.bounded_mono constantsStore (Nat.add_le_add_left cb (bound + headerBudget bound))
  have constantsFields := registers_fields_bounded (initialized r) _ constantsStore'
  have lb : (afterTraversal r).fuel ≤ traversalBudget bound := by
    have h := gateLoop_result_bound (initialized r)
    have left : 128 * ((initialized r).input.length + 1) ≤ 128 * (preLoopBound bound + 1) :=
      Nat.mul_le_mul_left 128 (Nat.succ_le_succ constantsFields.1)
    have right : loopPotential (initialized r) ≤ 3 * preLoopBound bound + 1 := by
      unfold loopPotential
      omega
    exact Nat.le_trans h (Nat.mul_le_mul left right)
  have loopStore := registers_bounded_of_run program (afterTraversal r).fuel 177
    (readerExit (afterTraversal r).valid 492 666) (preLoopBound bound) (initialized r) (afterTraversal r).state
    (gateLoop_result_run program 177 492 666 (initialized r) ps.2.2.1) constantsStore'
  have loopStore' : (afterTraversal r).state.store.Bounded (preLoopBound bound + traversalBudget bound) :=
    Store.bounded_mono loopStore (Nat.add_le_add_left lb (preLoopBound bound))
  have loopFields := registers_fields_bounded (afterTraversal r).state _ loopStore'
  have ob : (outputResult (afterTraversal r).state).fuel ≤ outputBudget bound := by
    have h := output_result_bound (afterTraversal r).state
    unfold outputBudget
    omega
  unfold frontendFuel frontendBudget
  cases hh : (headerResult r).valid <;> cases hl : (afterTraversal r).valid <;>
    cases ho : (outputResult (afterTraversal r).state).valid <;>
      simp only [frontendResult, hh, hl, ho, readerExit] <;> omega

theorem initial_registers_bounded (input : BitString) :
    (initialRegisters input).store.Bounded input.length :=
  ⟨Nat.le_refl _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, True.intro⟩

theorem frontend_input_bound (input : BitString) :
    frontendFuel (initialRegisters input) ≤ frontendBudget input.length :=
  frontendFuel_bound (initialRegisters input) input.length (initial_registers_bounded input)

end PNP.Concrete.NANDFrontend
