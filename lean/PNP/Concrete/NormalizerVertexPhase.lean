/-
Copyright (c) 2026 PNP Labs.

Read one encoded count and construct its complete tagged range. This phase
preserves the unread suffix and accumulated output. Its running-time bound
depends only on the new input length, not on the old buffer length.
-/

import PNP.Concrete.NormalizerVertexHeader

namespace PNP.Concrete.NormalizerBlocks.SearchVertices

open BitRegister Occurrence

def phase (tag : Bool) : Block 9 :=
  .seq reset (.seq TableInit.header (.seq prepare (loop tag)))
def phaseStarted (r : Registers) : Registers := prepared (readBuffered r.input r.excess)
def phaseResult (tag : Bool) (r : Registers) : Registers := (whole tag (phaseStarted r)).state
def phaseSteps (tag : Bool) (r : Registers) : Nat :=
  7 + (TableInit.headerFuel r.input + (2 + (whole tag (phaseStarted r)).fuel))

theorem phase_exec (tag : Bool) (r : Registers) :
    Exec (phase tag) r.store (phaseSteps tag r) (phaseResult tag r).store :=
  Exec.seq (reset_exec r) (Exec.seq (buffered_header_exec r.input r.excess)
    (Exec.seq (prepare_exec (readBuffered r.input r.excess)) (whole_exec tag (phaseStarted r))))

theorem phase_input (tag : Bool) (r : Registers) :
    (phaseResult tag r).input = (TableInit.readCount r.input).state.input :=
  whole_input tag (phaseStarted r)

theorem phase_input_bound (tag : Bool) (r : Registers) :
    (phaseResult tag r).input.length ≤ r.input.length := by
  rw [phase_input]
  exact Occurrence.header_input_bound r.input (TableInit.seeded r.input)

theorem phase_excess (tag : Bool) (r : Registers) :
    (phaseResult tag r).excess =
      (rangeBits tag (TableInit.readCount r.input).state.target.length 0).reverse ++ r.excess :=
  whole_excess tag (phaseStarted r)

def phaseBudget : NatPolynomial := .add (.linear 4 16) (.mul (.linear 20 37) (.linear 5 6))

theorem phaseBudget_eval (size : Nat) :
    phaseBudget.eval size = 4 * size + 16 + (20 * size + 37) * (5 * size + 6) := rfl

theorem phaseSteps_bound (tag : Bool) (r : Registers) :
    phaseSteps tag r ≤ phaseBudget.eval r.input.length := by
  have header := TableInit.headerFuel_bound r.input
  have count := TableInit.count_length_bound r.input
  have loop := whole_fuel_bound tag (phaseStarted r)
  change (whole tag (phaseStarted r)).fuel ≤
    (4 * (0 + (TableInit.readCount r.input).state.target.length) + 13) *
      (TableInit.readCount r.input).state.target.length + 1 at loop
  have factor : 4 * (0 + (TableInit.readCount r.input).state.target.length) + 13 ≤
      20 * r.input.length + 37 := by omega
  have product := Nat.mul_le_mul factor count
  rw [phaseBudget_eval]
  simp only [phaseSteps]
  omega

theorem phaseBudget_mono {first second : Nat} (bound : first ≤ second) :
    phaseBudget.eval first ≤ phaseBudget.eval second := by
  have left : 20 * first + 37 ≤ 20 * second + 37 := by omega
  have right : 5 * first + 6 ≤ 5 * second + 6 := by omega
  have product := Nat.mul_le_mul left right
  rw [phaseBudget_eval, phaseBudget_eval]
  omega

theorem phase_canonical_input (tag : Bool) (count : Nat) (suffix : BitString) (r : Registers)
    (input : r.input = TableInit.encodeCount count suffix) :
    (phaseResult tag r).input = suffix := by
  rw [phase_input, input, BatchPacket.header_canonical]
  rfl

theorem phase_canonical_excess (tag : Bool) (count : Nat) (suffix : BitString) (r : Registers)
    (input : r.input = TableInit.encodeCount count suffix) :
    (phaseResult tag r).excess = (rangeBits tag count 0).reverse ++ r.excess := by
  rw [phase_excess, input, BatchPacket.header_canonical]
  simp only [TableInit.canonicalHeader, List.length_replicate]

end PNP.Concrete.NormalizerBlocks.SearchVertices
