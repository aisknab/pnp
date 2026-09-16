/-
Copyright (c) 2026 PNP Labs.

Execute an arbitrary finite raw-stage sequence against its actual changing
descendants. A failed later stage rejects the complete program. Every receipt
retains the existing stage execution, and totals sum its actual charges and
removals rather than the lengths of a newly defined ownership ledger.

Intermediate stages may expand. This does not generate a successful global
strategy, transport open obligations between local histories or prove a
polynomial bound on intermediate size or total runtime.
-/

import PNP.NANDWireDescendantStage

namespace PNP.DirectWire.WireDescendantHistory

variable {inputs outputs : Nat}

/-- The result of executing all stages, with no supplied intermediate circuit
in the raw program input. Each next stage uses the preceding computed result. -/
inductive CompiledRun :
    (source : Implementation inputs outputs) → List RawStage → Type where
  | nil (source : Implementation inputs outputs) : CompiledRun source []
  | cons {source : Implementation inputs outputs} {stage : RawStage} {stages : List RawStage}
      (first : StageCompilation source stage)
      (rest : CompiledRun first.result stages) : CompiledRun source (stage :: stages)

namespace CompiledRun

variable {source : Implementation inputs outputs} {stages : List RawStage}

def result {source : Implementation inputs outputs} {stages : List RawStage} : CompiledRun source stages → Implementation inputs outputs
  | .nil source => source
  | .cons _ rest => rest.result

/-- Sum charges of the actual existing stage executions, even if an allocation
is removed by a later stage. -/
def chargedCount {source : Implementation inputs outputs} {stages : List RawStage} : CompiledRun source stages → Nat
  | .nil _ => 0
  | .cons first rest => first.chargedCount + rest.chargedCount

def removedCount {source : Implementation inputs outputs} {stages : List RawStage} : CompiledRun source stages → Nat
  | .nil _ => 0
  | .cons first rest => first.removedCount + rest.removedCount

theorem semantics (run : CompiledRun source stages)
    (valuation : Valuation inputs) (output : Fin outputs) :
    run.result.candidate.semantics valuation output =
      source.candidate.semantics valuation output := by
  induction run with
  | nil source => rfl
  | cons first rest ih =>
      exact ih.trans (first.semantics valuation output)

/-- Exact accounting for the entire actual execution. No per-stage strict gain
is assumed, and this scalar identity is not a replacement for physical origins. -/
theorem gate_balance (run : CompiledRun source stages) :
    run.result.gateCount + run.removedCount = source.gateCount + run.chargedCount := by
  induction run with
  | nil source => rfl
  | cons first rest ih =>
      have firstBalance := first.gate_balance
      simp only [result, removedCount, chargedCount]
      omega

end CompiledRun

/-- Public source-only interpreter: the source and finite raw stages are the
only inputs. Bounds and histories are checked against each actual descendant. -/
def compile :
    (source : Implementation inputs outputs) → (stages : List RawStage) →
      Option (CompiledRun source stages)
  | source, [] => some (.nil source)
  | source, stage :: stages =>
      match compileStage source stage with
      | none => none
      | some first => (compile first.result stages).map fun rest => .cons first rest

theorem compile_nil (source : Implementation inputs outputs) :
    compile source [] = some (.nil source) := rfl

theorem compile_cons (source : Implementation inputs outputs)
    (stage : RawStage) (stages : List RawStage) :
    compile source (stage :: stages) =
      match compileStage source stage with
      | none => none
      | some first => (compile first.result stages).map fun rest => .cons first rest := rfl

theorem compile_stage_none (source : Implementation inputs outputs)
    (stage : RawStage) (stages : List RawStage)
    (rejected : compileStage source stage = none) :
    compile source (stage :: stages) = none := by
  rw [compile_cons, rejected]

/-- A successful prefix cannot hide a failed tail or return a partial receipt. -/
theorem compile_tail_none (source : Implementation inputs outputs)
    (stage : RawStage) (stages : List RawStage)
    (first : StageCompilation source stage)
    (firstAt : compileStage source stage = some first)
    (rejected : compile first.result stages = none) :
    compile source (stage :: stages) = none := by
  rw [compile_cons, firstAt]
  dsimp only
  rw [rejected]
  rfl

theorem compile_cons_some (source : Implementation inputs outputs)
    (stage : RawStage) (stages : List RawStage)
    (first : StageCompilation source stage)
    (rest : CompiledRun first.result stages)
    (firstAt : compileStage source stage = some first)
    (restAt : compile first.result stages = some rest) :
    compile source (stage :: stages) = some (.cons first rest) := by
  rw [compile_cons, firstAt]
  dsimp only
  rw [restAt]
  rfl

/-- The returned receipt identifies the complete semantically sound execution,
not a separately supplied result checked by exhaustive truth-table comparison. -/
theorem compile_sound (source : Implementation inputs outputs) (stages : List RawStage)
    (run : CompiledRun source stages) (_accepted : compile source stages = some run) :
    (∀ valuation output, run.result.candidate.semantics valuation output =
      source.candidate.semantics valuation output) ∧
      run.result.gateCount + run.removedCount = source.gateCount + run.chargedCount :=
  ⟨run.semantics, run.gate_balance⟩

end PNP.DirectWire.WireDescendantHistory
