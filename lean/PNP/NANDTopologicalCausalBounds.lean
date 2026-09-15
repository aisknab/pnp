/-
Copyright (c) 2026 PNP Labs.

Dependency-level bounds for the actual raw NAND topological compiler.
The state invariant follows every physically emitted gate. Boolean soundness
alone is insufficient; the success premise binds the theorem to the computed
compiler output. Splice callers must derive the graph caps from actual source
programs. This is not a global route or a polynomial-time PCCMin theorem.
-/

import PNP.NANDTopologicalCompiler
import PNP.NANDCausalBounds

namespace PNP.DirectWire.RawNandCausalBound

def GraphBounds {inputs nodes : Nat} (graph : RawNandGraph inputs nodes)
    (labels : Fin inputs → Nat) (caps : Fin nodes → Nat) : Prop :=
  ∀ node, max (CausalBound.source (graph.gate node).left labels caps)
      (CausalBound.source (graph.gate node).right labels caps) ≤ caps node

def StateBounds {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}
    (state : RawNandCompilationState graph)
    (labels : Fin inputs → Nat) (caps : Fin nodes → Nat) : Prop :=
  ∀ node index, state.position node = some index →
    CausalBound.levels state.program labels index ≤ caps node

theorem initial_bounds {inputs nodes : Nat} (graph : RawNandGraph inputs nodes)
    (labels : Fin inputs → Nat) (caps : Fin nodes → Nat) :
    StateBounds (RawNandCompilationState.initial graph) labels caps := by
  intro node index placed
  cases placed

theorem readSource_bound {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}
    (state : RawNandCompilationState graph)
    (labels : Fin inputs → Nat) (caps : Fin nodes → Nat)
    (checked : StateBounds state labels caps)
    (source : Source inputs nodes) (translated : Source inputs state.count)
    (found : state.readSource source = some translated) :
    CausalBound.source translated labels (CausalBound.levels state.program labels) ≤
      CausalBound.source source labels caps := by
  cases source with
  | input index => cases found; exact Nat.le_refl _
  | constant value => cases found; exact Nat.le_refl _
  | gate node =>
      cases placed : state.position node with
      | none =>
          simp only [RawNandCompilationState.readSource, placed, Option.map_none] at found
          cases found
      | some index =>
          simp only [RawNandCompilationState.readSource, placed, Option.map_some,
            Option.some.injEq] at found
          subst translated
          exact checked node index placed

theorem readGate_bound {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}
    (state : RawNandCompilationState graph)
    (labels : Fin inputs → Nat) (caps : Fin nodes → Nat)
    (bounded : GraphBounds graph labels caps) (checked : StateBounds state labels caps)
    (node : Fin nodes) (translated : Gate inputs state.count)
    (found : state.readGate node = some translated) :
    max (CausalBound.source translated.left labels (CausalBound.levels state.program labels))
      (CausalBound.source translated.right labels (CausalBound.levels state.program labels)) ≤
      caps node := by
  cases leftAt : state.readSource (graph.gate node).left with
  | none => simp only [RawNandCompilationState.readGate, leftAt] at found; cases found
  | some left =>
      cases rightAt : state.readSource (graph.gate node).right with
      | none =>
          simp only [RawNandCompilationState.readGate, leftAt, rightAt] at found
          cases found
      | some right =>
          simp only [RawNandCompilationState.readGate, leftAt, rightAt,
            Option.some.injEq] at found
          subst translated
          have leftBound := readSource_bound state labels caps checked _ _ leftAt
          have rightBound := readSource_bound state labels caps checked _ _ rightAt
          have nodeBound := bounded node
          change max (CausalBound.source left labels (CausalBound.levels state.program labels))
            (CausalBound.source right labels (CausalBound.levels state.program labels)) ≤ _
          omega

theorem apply_bounds {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}
    {state : RawNandCompilationState graph} (step : RawNandReadyStep state)
    (labels : Fin inputs → Nat) (caps : Fin nodes → Nat)
    (bounded : GraphBounds graph labels caps) (checked : StateBounds state labels caps) :
    StateBounds step.apply labels caps := by
  change ∀ (node : Fin nodes) (index : Fin (state.count + 1)),
    (if node = step.node then some (Fin.last state.count)
      else (state.position node).map Fin.castSucc) = some index →
    CausalBound.levels (state.program.snoc step.gate) labels index ≤ caps node
  intro node index placed
  split at placed
  · rename_i same
    have sameIndex := Option.some.inj placed
    subst index
    rw [CausalBound.levels_snoc_last, same]
    exact readGate_bound state labels caps bounded checked step.node step.gate step.compiled
  · rename_i _different
    cases oldAt : state.position node with
    | none => simp only [oldAt, Option.map_none] at placed; cases placed
    | some oldIndex =>
        simp only [oldAt, Option.map_some, Option.some.injEq] at placed
        subst index
        rw [CausalBound.levels_snoc_castSucc]
        exact checked node oldIndex oldAt

theorem run_bounds {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}
    (state : RawNandCompilationState graph)
    (labels : Fin inputs → Nat) (caps : Fin nodes → Nat)
    (bounded : GraphBounds graph labels caps) (checked : StateBounds state labels caps) :
    StateBounds (runRawNandCompilation state).state labels caps := by
  rw [runRawNandCompilation]
  split
  · exact checked
  · rename_i step found
    exact run_bounds step.apply labels caps bounded (apply_bounds step labels caps bounded checked)
termination_by state.remaining.length
decreasing_by exact RawNandReadyStep.apply_remaining_lt _

theorem finish_bounds {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}
    (state : RawNandCompilationState graph) (complete : state.remaining = [])
    (labels : Fin inputs → Nat) (caps : Fin nodes → Nat)
    (checked : StateBounds state labels caps) (node : Fin nodes) :
    CausalBound.levels (state.finish complete).program labels
        ((state.finish complete).position node) ≤ caps node :=
  checked node _ (state.finish_position complete node)

theorem compile_bounds {inputs nodes : Nat} (graph : RawNandGraph inputs nodes)
    (compiled : CompiledRawNandGraph graph)
    (accepted : compileRawNandGraph graph = some compiled)
    (labels : Fin inputs → Nat) (caps : Fin nodes → Nat)
    (bounded : GraphBounds graph labels caps) (node : Fin nodes) :
    CausalBound.levels compiled.program labels (compiled.position node) ≤ caps node := by
  let stop := runRawNandCompilation (RawNandCompilationState.initial graph)
  have checked := run_bounds (RawNandCompilationState.initial graph) labels caps bounded
    (initial_bounds graph labels caps)
  change (if complete : stop.state.remaining = [] then
    some (stop.state.finish complete) else none) = some compiled at accepted
  split at accepted
  · rename_i complete
    cases accepted
    exact finish_bounds stop.state complete labels caps checked node
  · cases accepted

theorem translateSource_bound {inputs nodes : Nat} (graph : RawNandGraph inputs nodes)
    (compiled : CompiledRawNandGraph graph)
    (accepted : compileRawNandGraph graph = some compiled)
    (labels : Fin inputs → Nat) (caps : Fin nodes → Nat)
    (bounded : GraphBounds graph labels caps) (source : Source inputs nodes) :
    CausalBound.source (compiled.translateSource source) labels
        (CausalBound.levels compiled.program labels) ≤ CausalBound.source source labels caps := by
  cases source with
  | input index => exact Nat.le_refl _
  | constant value => exact Nat.le_refl _
  | gate node => exact compile_bounds graph compiled accepted labels caps bounded node

theorem candidate_bound {inputs nodes outputs : Nat} (graph : RawNandGraph inputs nodes)
    (compiled : CompiledRawNandGraph graph)
    (accepted : compileRawNandGraph graph = some compiled)
    (labels : Fin inputs → Nat) (caps : Fin nodes → Nat)
    (bounded : GraphBounds graph labels caps)
    (word : DirectWireWord inputs nodes outputs) (output : Fin outputs) :
    CausalBound.outputLevel (compiled.candidate word) labels output ≤
      CausalBound.source (word.source output) labels caps := by
  unfold CompiledRawNandGraph.candidate CausalBound.outputLevel
  rw [Candidate.ofDirectWireWord_pointwise]
  exact translateSource_bound graph compiled accepted labels caps bounded (word.source output)

end PNP.DirectWire.RawNandCausalBound
