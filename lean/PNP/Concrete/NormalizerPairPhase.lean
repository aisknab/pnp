/-
Copyright (c) 2026 PNP Labs.

Reusable path-to-update phase. Output is reversed exactly once into the
batch updater's raw pair format. No prefilled buffer is trusted.
-/
import PNP.Concrete.NormalizerPairCanonical

namespace PNP.Concrete.NormalizerBlocks.PathPairs
open BitRegister

def resetBuffer : Block 12 := .action (.clear 11)
def bufferReset (r : State) : State := {r with buffer := []}
theorem resetBuffer_exec (r : State) : Exec resetBuffer r.store 1 (bufferReset r).store := .action _ _

def prepareOutput : Block 12 := .seq (.action (.copy 3 11)) (.action (.clear 8))
def outputPrepared (r : State) : State := r.withCore {r.core with excess := r.buffer, output := []}
theorem prepareOutput_exec (r : State) : Exec prepareOutput r.store 2 (outputPrepared r).store :=
  Exec.seq (.action _ _) (.action _ _)
def reverseOutput : Block 12 := liftCore ClauseQuery.reverseLoop
def outputReversed (r : State) : State := r.withCore {r.core with excess := [], output := r.core.excess.reverse ++ r.core.output}
theorem reverseOutput_exec (r : State) :
    Exec reverseOutput r.store (4 * r.core.excess.length + 1) (outputReversed r).store :=
  liftCore_exec _ r _ _ (ClauseQuery.reverse_exec r.core r.core.excess)
def finish : Block 12 := .seq prepareOutput reverseOutput
def finished (r : State) : State := outputReversed (outputPrepared r)
def finishFuel (r : State) : Nat := 4 * r.buffer.length + 3
theorem finish_exec (r : State) : Exec finish r.store (finishFuel r) (finished r).store := by
  have checked := Exec.seq (prepareOutput_exec r) (reverseOutput_exec (outputPrepared r))
  change Exec finish r.store (2 + (4 * r.buffer.length + 1)) (finished r).store at checked
  have cost : 2 + (4 * r.buffer.length + 1) = finishFuel r := by unfold finishFuel; omega
  rw [cost] at checked
  exact checked
theorem finished_output (r : State) : (finished r).core.output = r.buffer.reverse := by
  change r.buffer.reverse ++ [] = _
  rw [List.append_nil]

def front : Block 12 := .seq resetBuffer loop
def frontResult (r : State) : State := (whole (bufferReset r)).state
def frontFuel (r : State) : Nat := 1 + (whole (bufferReset r)).fuel
theorem front_exec (r : State) : Exec front r.store (frontFuel r) (frontResult r).store :=
  Exec.seq (resetBuffer_exec r) (whole_exec (bufferReset r))
theorem frontFuel_bound (r : State) :
    frontFuel r ≤ (64 * r.pending.length + 129) * (r.pending.length + 1) + 2 := by
  have checked := whole_fuel_bound (bufferReset r)
  change (whole (bufferReset r)).fuel ≤ (64 * r.pending.length + 129) * (r.pending.length + 1) + 1 at checked
  unfold frontFuel
  omega

def phase : Block 12 := .seq front finish
def phaseResult (r : State) : State := finished (frontResult r)
def phaseFuel (r : State) : Nat := frontFuel r + finishFuel (frontResult r)
theorem phase_exec (r : State) : Exec phase r.store (phaseFuel r) (phaseResult r).store :=
  Exec.seq (front_exec r) (finish_exec (frontResult r))
theorem phaseFuel_bound (r : State) (bound : Nat) (checked : r.store.Bounded bound) :
    phaseFuel r ≤ 4 * bound + 5 * ((64 * r.pending.length + 129) * (r.pending.length + 1)) + 13 := by
  have frontSize := (front_exec r).bounded bound checked
  have buffer : (frontResult r).buffer.length ≤ bound + frontFuel r :=
    (frontResult r).store.get_length_le 11 frontSize
  have steps := frontFuel_bound r
  unfold phaseFuel finishFuel
  omega

theorem phase_canonical (r : State) (xs : List CNFLiteral) (pending : r.pending = PathData.encode xs) :
    (phaseResult r).core.output = TableBatch.encodeUpdates (value xs) := by
  change (finished (frontResult r)).core.output = _
  rw [finished_output]
  have buffer := whole_buffer (bufferReset r) xs pending
  change (frontResult r).buffer = (TableBatch.encodeUpdates (value xs)).reverse ++ [] at buffer
  rw [buffer, List.append_nil, List.reverse_reverse]

end PNP.Concrete.NormalizerBlocks.PathPairs
