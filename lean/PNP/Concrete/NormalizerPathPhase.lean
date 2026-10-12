/-
Copyright (c) 2026 PNP Labs.

Reusable closed path phase. It clears any supplied answer and path buffer,
reconstructs from the actual trace, and serializes the result. Formula
and matching registers are preserved for the enclosing search machine.
-/
import PNP.Concrete.NormalizerPathPack

namespace PNP.Concrete.NormalizerBlocks.TracePath
open BitRegister

def resetPath : Block 23 := .seq (lift ParentQuery.defaultAnswer) (.action (.clear (Frame.frameIndex 21 (0 : Fin 2))))
def pathReset (r : State) : State := {r.withCore (ParentQuery.defaulted r.core) with buffer := []}
theorem resetPath_exec (r : State) : Exec resetPath r.store 3 (pathReset r).store := by
  have default := lift_exec ParentQuery.defaultAnswer r 2 (ParentQuery.defaulted r.core) (ParentQuery.defaultAnswer_exec r.core)
  have clear : Exec (.action (.clear (Frame.frameIndex 21 (0 : Fin 2))))
      (r.withCore (ParentQuery.defaulted r.core)).store 1 (pathReset r).store := by
    have checked := Exec.action (.clear (Frame.frameIndex 21 (0 : Fin 2))) (r.withCore (ParentQuery.defaulted r.core)).store
    simpa only [Action.update, Action.instruction, Instruction.update, State.store, Frame.set_frame,
      State.frame, pathReset, State.withCore, Store.set, Store.indexCases] using checked
  exact Exec.seq default clear

def front : Block 23 := .seq resetPath loop
def frontResult (r : State) : State := (whole (pathReset r)).state
def frontFuel (r : State) : Nat := 3 + (whole (pathReset r)).fuel
theorem front_exec (r : State) : Exec front r.store (frontFuel r) (frontResult r).store :=
  Exec.seq (resetPath_exec r) (whole_exec (pathReset r))

def phase : Block 23 := .seq front finish
def phaseResult (r : State) : State := finished (frontResult r)
def phaseFuel (r : State) : Nat := frontFuel r + finishFuel (frontResult r)
theorem phase_exec (r : State) : Exec phase r.store (phaseFuel r) (phaseResult r).store :=
  Exec.seq (front_exec r) (finish_exec (frontResult r))

theorem frontFuel_bound (r : State) :
    frontFuel r ≤ (47 * r.core.pending.length + 125) * (r.core.pending.length + 1) + 4 := by
  have checked := whole_fuel_bound (pathReset r)
  change (whole (pathReset r)).fuel ≤ (47 * r.core.pending.length + 125) * (r.core.pending.length + 1) + 1 at checked
  unfold frontFuel
  omega

theorem phaseFuel_bound (r : State) (bound : Nat) (bounded : r.store.Bounded bound) :
    phaseFuel r ≤ 4 * bound + 5 * ((47 * r.core.pending.length + 125) * (r.core.pending.length + 1) + 4) + 5 := by
  have frontBound := (front_exec r).bounded bound bounded
  have buffer := Store.get_length_le (frontResult r).store (21 : Fin 23) frontBound
  change (frontResult r).buffer.length ≤ bound + frontFuel r at buffer
  have finishBound := finishFuel_bound (frontResult r)
  have first := frontFuel_bound r
  unfold phaseFuel
  omega

theorem phase_preserves (r : State) :
    (phaseResult r).core.graph.core.formula = r.core.graph.core.formula ∧
      (phaseResult r).core.graph.core.matching = r.core.graph.core.matching := by
  have first := scan_preserves ((pathReset r).core.pending.length + 1) (pathReset r)
  have second := finished_preserves (frontResult r)
  exact ⟨second.1.trans first.1, second.2.trans first.2⟩

theorem phase_canonical (r : State) (target : CNFLiteral) (trace : List TraceData.Row)
    (indexRead : r.core.targetIndex = List.replicate target.variableIndex true)
    (tagRead : ForwardEdge.present r.core.targetTag = target.positive)
    (traceRead : r.core.pending = TraceData.encode trace) :
    (phaseResult r).registers.output = PathData.answer (value trace target) := by
  rw [phaseResult, finished_output]
  exact whole_canonical (pathReset r) target trace indexRead tagRead traceRead rfl rfl

end PNP.Concrete.NormalizerBlocks.TracePath
