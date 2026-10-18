import PNP.Concrete.ResidualReduction.SourceFamilyReductionLoop

/-! Emit the accumulated canonical family only when every row succeeded.
Failure emits only the absent marker. All family scratch is cleared in either
case while the external suffix and computed tail parameters are preserved. -/

namespace PNP.Concrete.ResidualReduction.SourceFamilyReductionOutput
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceRowReductionState (work parameters emptyData)
open PNP.Concrete.ResidualReduction.SourceFamilyReductionState

def bytes (accumulator : BitString) (flag : Bool) : BitString :=
  if flag then true :: accumulator.reverse else [false]
def emittedState {n : Nat} (t : TailForm n) (suffix accumulator : BitString)
    (flag : Bool) (count : BitString) : Store 23 :=
  full (SourceRowReductionState.full {work n suffix with output := bytes accumulator flag}
    (parameters t) (emptyData t [])) ⟨[],accumulator,[flag],count⟩
def success : Block 23 := .seq (.action (.copy 3 20)) <|
  .seq (core ClauseQuery.reverseLoop) (.action (.push 8 true))

theorem success_exec {n : Nat} (t : TailForm n) (suffix accumulator count : BitString) :
    Exec success (done t suffix accumulator true count) (4 * accumulator.length + 3)
      (emittedState t suffix accumulator true count) := by
  let before := work n suffix
  let d := emptyData t []
  let s : Saved := ⟨[],accumulator,[true],count⟩
  let loaded := {before with excess := accumulator}
  let reversed := {before with output := accumulator.reverse}
  have load : Exec (.action (.copy (3 : Fin 23) 20)) (done t suffix accumulator true count) 1
      (full (SourceRowReductionState.full loaded (parameters t) d) s) := .action _ _
  have reverse : Exec ClauseQuery.reverseLoop loaded.store (4 * accumulator.length + 1) reversed.store := by
    simpa only [loaded,reversed,before,work,List.append_nil] using ClauseQuery.reverse_exec before accumulator
  have tag : Exec (.action (.push (8 : Fin 23) true))
      (full (SourceRowReductionState.full reversed (parameters t) d) s) 1
      (emittedState t suffix accumulator true count) := .action _ _
  have cost : 4 * accumulator.length + 3 = 1 + ((4 * accumulator.length + 1) + 1) := by omega
  simpa only [success,cost] using Exec.seq load (Exec.seq (core_exec reverse (parameters t) d s) tag)

def emit : Block 23 := .branch 21 .skip (.action (.push 8 false)) success
def emitFuel (accumulator : BitString) : Bool → Nat
  | false => 2
  | true => 1 + (4 * accumulator.length + 3)

theorem emit_exec {n : Nat} (t : TailForm n) (suffix accumulator : BitString)
    (flag : Bool) (count : BitString) :
    Exec emit (done t suffix accumulator flag count) (emitFuel accumulator flag)
      (emittedState t suffix accumulator flag count) := by
  cases flag with
  | false => exact Exec.zero rfl (.action _ _)
  | true => exact Exec.one rfl (success_exec t suffix accumulator count)

def block : Block 23 := .seq emit cleanup
def fuel (accumulator : BitString) (flag : Bool) : Nat := emitFuel accumulator flag + 4

theorem block_exec {n : Nat} (t : TailForm n) (suffix accumulator : BitString)
    (flag : Bool) (count : BitString) :
    Exec block (done t suffix accumulator flag count) (fuel accumulator flag)
      (finished t suffix (bytes accumulator flag)) :=
  Exec.seq (emit_exec t suffix accumulator flag count)
    (cleanup_exec {work n suffix with output := bytes accumulator flag}
      (parameters t) (emptyData t []) ⟨[],accumulator,[flag],count⟩)

theorem fuel_bound (accumulator : BitString) (flag : Bool) :
    fuel accumulator flag ≤ 4 * accumulator.length + 8 := by
  cases flag <;> simp only [fuel,emitFuel] <;> omega

end PNP.Concrete.ResidualReduction.SourceFamilyReductionOutput
