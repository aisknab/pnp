/-
Copyright (c) 2026 PNP Labs.

The complete gate loop terminates on every raw input, not only canonical
circuits. Every successful iteration consumes input and increases the current
gate index by one. Their joint potential gives a quadratic source-step bound.
-/

import PNP.Concrete.NANDFrontendGateResult

namespace PNP.Concrete.NANDFrontend

open BitRegister

def gateLoopResult (r : Registers) : BlockResult :=
  match r.input with
  | [] => ⟨1, r, false⟩
  | true :: _ =>
      let marker := matchScan LockedNAND.Token.programEnd.bits r.input
      ⟨1 + marker.fuel, {r with input := marker.rest}, marker.valid⟩
  | false :: _ =>
      match h : (gateReadResult r).valid with
      | false => ⟨1 + (gateReadResult r).fuel, (gateReadResult r).state, false⟩
      | true =>
          let tail := gateLoopResult (gateReadResult r).state
          ⟨1 + ((gateReadResult r).fuel + tail.fuel), tail.state, tail.valid⟩
termination_by r.input.length
decreasing_by exact (gateRead_result_progress r h).1

theorem gateLoopResult_empty (r : Registers) (empty : r.input = []) :
    gateLoopResult r = ⟨1, r, false⟩ := by
  rw [gateLoopResult, empty]

theorem gateLoopResult_end (r : Registers) (tail : BitString) (input : r.input = true :: tail) :
    gateLoopResult r =
      ⟨1 + (matchScan LockedNAND.Token.programEnd.bits r.input).fuel,
        {r with input := (matchScan LockedNAND.Token.programEnd.bits r.input).rest},
        (matchScan LockedNAND.Token.programEnd.bits r.input).valid⟩ := by
  rw [gateLoopResult, input]

theorem gateLoopResult_failure (r : Registers) (tail : BitString) (input : r.input = false :: tail)
    (invalid : (gateReadResult r).valid = false) :
    gateLoopResult r = ⟨1 + (gateReadResult r).fuel, (gateReadResult r).state, false⟩ := by
  rw [gateLoopResult, input, invalid]

theorem gateLoopResult_continue (r : Registers) (tail : BitString) (input : r.input = false :: tail)
    (valid : (gateReadResult r).valid = true) :
    gateLoopResult r =
      ⟨1 + ((gateReadResult r).fuel + (gateLoopResult (gateReadResult r).state).fuel),
        (gateLoopResult (gateReadResult r).state).state,
        (gateLoopResult (gateReadResult r).state).valid⟩ := by
  rw [gateLoopResult, input, valid]

theorem gateLoop_result_run (program : Program 9) (base next failure : Nat) (r : Registers)
    (placed : Segment program base (gateLoopCode base next failure)) :
    BitRegister.run program (gateLoopResult r).fuel (r.state base) =
      (gateLoopResult r).state.state (readerExit (gateLoopResult r).valid next failure) := by
  have ps := gateLoop_segments program base next failure placed
  match hi : r.input with
  | [] =>
      rw [gateLoopResult_empty r hi]
      simp only [BitRegister.run, BitRegister.step, Registers.state, ps.1,
        Instruction.execute, Instruction.nextControl, Instruction.update,
        Registers.store, Store.get, Store.indexCases, hi, readerExit]
  | true :: tail =>
      rw [gateLoopResult_end r tail hi]
      have firstStep : BitRegister.run program 1 (r.state base) = r.state (base + 303) := by
        simp only [BitRegister.run, BitRegister.step, Registers.state, ps.1,
          Instruction.execute, Instruction.nextControl, Instruction.update,
          Registers.store, Store.get, Store.indexCases, hi]
      rw [BitRegister.run_add, firstStep]
      exact marker_run program (base + 303) .programEnd next failure r r.input ps.2.2
  | false :: tail =>
      have firstStep : BitRegister.run program 1 (r.state base) = r.state (base + 1) := by
        simp only [BitRegister.run, BitRegister.step, Registers.state, ps.1,
          Instruction.execute, Instruction.nextControl, Instruction.update,
          Registers.store, Store.get, Store.indexCases, hi]
      have body := gateRead_result_run program (base + 1) base failure r ps.2.1
      cases valid : (gateReadResult r).valid with
      | false =>
          rw [gateLoopResult_failure r tail hi valid]
          rw [BitRegister.run_add, firstStep]
          simpa only [valid, readerExit] using body
      | true =>
          rw [gateLoopResult_continue r tail hi valid]
          simp only [valid, readerExit] at body
          rw [BitRegister.run_add, firstStep, BitRegister.run_add, body]
          exact gateLoop_result_run program base next failure (gateReadResult r).state placed
termination_by r.input.length
decreasing_by exact (gateRead_result_progress r valid).1

def loopPotential (r : Registers) : Nat :=
  r.inputs.length + r.gate.length + r.input.length + 1

def loopBudget (r : Registers) : Nat :=
  128 * (r.input.length + 1) * loopPotential r

theorem loopPotential_positive (r : Registers) : 1 ≤ loopPotential r := by
  unfold loopPotential
  omega

theorem loopBudget_minimum (r : Registers) : 128 * loopPotential r ≤ loopBudget r := by
  have factor : 128 ≤ 128 * (r.input.length + 1) := by omega
  exact Nat.mul_le_mul_right (loopPotential r) factor

theorem loopBudget_step (r next : Registers)
    (shorter : next.input.length < r.input.length)
    (smaller : loopPotential next ≤ loopPotential r) :
    128 * loopPotential r + loopBudget next ≤ loopBudget r := by
  have lengthBound : next.input.length + 1 ≤ r.input.length := by omega
  have h := Nat.mul_le_mul (Nat.mul_le_mul_left 128 lengthBound) smaller
  change loopBudget next ≤ 128 * r.input.length * loopPotential r at h
  have equal : loopBudget r = 128 * r.input.length * loopPotential r + 128 * loopPotential r := by
    simp only [loopBudget, Nat.mul_add, Nat.mul_one, Nat.add_mul]
  rw [equal]
  omega

theorem gateRead_result_potential (r : Registers) (valid : (gateReadResult r).valid = true) :
    loopPotential (gateReadResult r).state ≤ loopPotential r := by
  have h := gateRead_result_progress r valid
  unfold loopPotential
  rw [h.2.1, h.2.2]
  omega

theorem gateLoop_result_bound (r : Registers) : (gateLoopResult r).fuel ≤ loopBudget r := by
  have minimum := loopBudget_minimum r
  have positive := loopPotential_positive r
  match hi : r.input with
  | [] =>
      rw [gateLoopResult_empty r hi]
      change 1 ≤ loopBudget r
      omega
  | true :: tail =>
      rw [gateLoopResult_end r tail hi]
      have h := (matchScan_bounds LockedNAND.Token.programEnd.bits r.input).1
      change (matchScan LockedNAND.Token.programEnd.bits r.input).fuel ≤ 8 at h
      change 1 + (matchScan LockedNAND.Token.programEnd.bits r.input).fuel ≤ loopBudget r
      omega
  | false :: tail =>
      have perIteration := gateRead_result_bound r
      change (gateReadResult r).fuel ≤ 127 * loopPotential r at perIteration
      cases valid : (gateReadResult r).valid with
      | false =>
          rw [gateLoopResult_failure r tail hi valid]
          change 1 + (gateReadResult r).fuel ≤ loopBudget r
          omega
      | true =>
          rw [gateLoopResult_continue r tail hi valid]
          have ih := gateLoop_result_bound (gateReadResult r).state
          have decrease := gateRead_result_progress r valid
          have potential := gateRead_result_potential r valid
          have stepBound := loopBudget_step r (gateReadResult r).state decrease.1 potential
          change 1 + ((gateReadResult r).fuel + (gateLoopResult (gateReadResult r).state).fuel) ≤ loopBudget r
          omega
termination_by r.input.length
decreasing_by exact (gateRead_result_progress r valid).1

end PNP.Concrete.NANDFrontend
