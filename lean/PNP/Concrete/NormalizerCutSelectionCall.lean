/-
Copyright (c) 2026 PNP Labs.

Call the complete selector inside a larger protected machine. The count and
trace are already present in registers; this interface neither reparses a
packet nor assumes that scratch registers are empty. It exposes an all-state
polynomial bound so the caller can account for the complete construction.
-/
import PNP.Concrete.NormalizerCutSelectionPolynomial

namespace PNP.Concrete.NormalizerBlocks.CutSelection
open BitRegister

def callFront (tag : Bool) : Block 24 := .seq (start tag) (loop tag)
def callScanned (tag : Bool) (r : State) : State := (whole tag (started tag r)).state
def callFrontSteps (tag : Bool) (r : State) : Nat := 6 + (whole tag (started tag r)).fuel
theorem callFront_exec (tag : Bool) (r : State) :
    Exec (callFront tag) r.store (callFrontSteps tag r) (callScanned tag r).store :=
  Exec.seq (start_exec tag r) (whole_exec tag (started tag r))

def callFrontBound : NatPolynomial :=
  .add (.constant 7)
    (.mul (.add (.mul (.linear 28 81) (.linear 1 1)) (.linear 4 21)) (.linear 1 0))
theorem callFrontBound_eval (bound : Nat) :
    callFrontBound.eval bound = 7 + ((28 * bound + 81) * (bound + 1) + 4 * bound + 21) * bound := by
  change 7 + ((28 * bound + 81) * (1 * bound + 1) + (4 * bound + 21)) * (1 * bound + 0) = _
  simp only [Nat.one_mul, Nat.add_zero, Nat.add_assoc]

theorem callFrontSteps_bound (tag : Bool) (r : State) (bound : Nat)
    (bounded : r.store.Bounded bound) :
    callFrontSteps tag r ≤ callFrontBound.eval bound := by
  have inputSize := Store.get_length_le r.store (0 : Fin 24) bounded
  have countSize := Store.get_length_le r.store (1 : Fin 24) bounded
  change r.registers.input.length ≤ bound at inputSize
  change r.registers.target.length ≤ bound at countSize
  have loopBound := whole_fuel_bound tag (started tag r)
  change (whole tag (started tag r)).fuel ≤
    (stepBound r.registers.input.length (0 + r.registers.target.length) + 1) *
      r.registers.target.length + 1 at loopBound
  have product := Nat.mul_le_mul
    (show 28 * r.registers.input.length + 81 ≤ 28 * bound + 81 by omega)
    (show r.registers.input.length + 1 ≤ bound + 1 by omega)
  have factor : stepBound r.registers.input.length (0 + r.registers.target.length) + 1 ≤
      (28 * bound + 81) * (bound + 1) + 4 * bound + 21 := by
    unfold stepBound
    omega
  have loopProduct := Nat.mul_le_mul factor countSize
  rw [callFrontBound_eval]
  unfold callFrontSteps
  omega

def call (tag : Bool) : Block 24 := .seq (callFront tag) finish
def called (tag : Bool) (r : State) : State := finished (callScanned tag r)
def callSteps (tag : Bool) (r : State) : Nat :=
  callFrontSteps tag r + finishFuel (callScanned tag r)
def callBound : NatPolynomial :=
  .add (.mul (.constant 5) callFrontBound) (.linear 4 13)
theorem callBound_eval (bound : Nat) :
    callBound.eval bound = 5 * callFrontBound.eval bound + (4 * bound + 13) := rfl
theorem call_exec (tag : Bool) (r : State) :
    Exec (call tag) r.store (callSteps tag r) (called tag r).store :=
  Exec.seq (callFront_exec tag r) (finish_exec (callScanned tag r))

theorem callSteps_bound (tag : Bool) (r : State) (bound : Nat)
    (bounded : r.store.Bounded bound) : callSteps tag r ≤ callBound.eval bound := by
  have scannedBound := (callFront_exec tag r).bounded bound bounded
  have bufferSize := Store.get_length_le (callScanned tag r).store (23 : Fin 24) scannedBound
  change (callScanned tag r).buffer.length ≤ bound + callFrontSteps tag r at bufferSize
  have front := callFrontSteps_bound tag r bound bounded
  rw [callBound_eval]
  unfold callSteps finishFuel
  omega

theorem called_canonical (tag : Bool) (r : State) (count : Nat) (trace : List TraceData.Row)
    (countRead : r.registers.target = List.replicate count true)
    (traceRead : r.registers.input = TraceData.encode trace) :
    (called tag r).registers.output = SearchVertices.encodeVertices (selected tag trace count 0) := by
  have buffer := whole_buffer tag (started tag r) 0 trace rfl
    (by cases tag <;> rfl) traceRead
  change (callScanned tag r).buffer =
    (selectedBits tag trace r.registers.target.length 0).reverse ++ [] at buffer
  rw [countRead, List.length_replicate, List.append_nil] at buffer
  rw [called, finished_output, buffer, List.reverse_reverse]
  exact (UnseenData.encoded_prefix (selected tag trace count 0)).symm

end PNP.Concrete.NormalizerBlocks.CutSelection
