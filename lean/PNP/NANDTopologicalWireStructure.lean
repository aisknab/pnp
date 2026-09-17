/-
Copyright (c) 2026 PNP Labs.

Literal source-pair fidelity of the actual topological NAND compiler.
An accepted compiler result preserves both input wires at every actual emitted
gate, not merely Boolean outputs or a bound on dependencies.

This is the structural prerequisite for arbitrary-support transport under
reordering. It does not yet prove that support transport, full manuscript
profiles, all normalization rules, global ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDCompiledGateProvenance
import PNP.ResidualTerminalSupportExtraction

namespace PNP.DirectWire.RawNandWireStructure

private def weakenGate {inputs gates : Nat} (gate : Gate inputs gates) :
    Gate inputs (gates + 1) :=
  ⟨gate.left.weakenGates 1, gate.right.weakenGates 1⟩

private theorem sources_before {inputs gates : Nat} (program : Program inputs gates)
    (gate : Gate inputs gates) (index : Fin gates) :
    (program.snoc gate).terminalGateSources index.castSucc =
      ((program.terminalGateSources index).1.weakenGates 1,
        (program.terminalGateSources index).2.weakenGates 1) := by
  change (if within : index.castSucc.val < gates then
    let pair := program.terminalGateSources ⟨index.castSucc.val, within⟩
    (pair.1.weakenGates 1, pair.2.weakenGates 1)
    else (gate.left.weakenGates 1, gate.right.weakenGates 1)) = _
  split
  · rfl
  · rename_i outside
    exact False.elim (outside index.isLt)

private theorem sources_last {inputs gates : Nat} (program : Program inputs gates)
    (gate : Gate inputs gates) :
    (program.snoc gate).terminalGateSources (Fin.last gates) =
      (gate.left.weakenGates 1, gate.right.weakenGates 1) := by
  change (if within : (Fin.last gates).val < gates then
    let pair := program.terminalGateSources ⟨(Fin.last gates).val, within⟩
    (pair.1.weakenGates 1, pair.2.weakenGates 1)
    else (gate.left.weakenGates 1, gate.right.weakenGates 1)) = _
  split
  · rename_i impossible
    exact False.elim (Nat.lt_irrefl gates impossible)
  · rfl

/-- Every placed raw node has exactly its translated two physical source wires. -/
def StateFaithful {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}
    (state : RawNandCompilationState graph) : Prop :=
  ∀ node index, state.position node = some index →
    state.readGate node = some
      ⟨(state.program.terminalGateSources index).1,
        (state.program.terminalGateSources index).2⟩

theorem initial_faithful {inputs nodes : Nat} (graph : RawNandGraph inputs nodes) :
    StateFaithful (RawNandCompilationState.initial graph) := by
  intro node index placed
  cases placed

private theorem readSource_after {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}
    {state : RawNandCompilationState graph} (step : RawNandReadyStep state)
    (wire : Source inputs nodes) (translated : Source inputs state.count)
    (found : state.readSource wire = some translated) :
    step.apply.readSource wire = some (translated.weakenGates 1) := by
  cases wire with
  | input index => cases found; rfl
  | constant value => cases found; rfl
  | gate node =>
      cases placed : state.position node with
      | none =>
          simp only [RawNandCompilationState.readSource, placed, Option.map_none] at found
          cases found
      | some index =>
          simp only [RawNandCompilationState.readSource, placed, Option.map_some,
            Option.some.injEq] at found
          subst translated
          have different : node ≠ step.node := by
            intro same
            subst node
            have pending := (state.pending step.node).mp step.member
            rw [pending] at placed
            cases placed
          change ((if node = step.node then some (Fin.last state.count)
            else (state.position node).map Fin.castSucc).map Source.gate) =
              some ((Source.gate index).weakenGates 1)
          rw [if_neg different, placed]
          rfl

private theorem readGate_after {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}
    {state : RawNandCompilationState graph} (step : RawNandReadyStep state)
    (node : Fin nodes) (translated : Gate inputs state.count)
    (found : state.readGate node = some translated) :
    step.apply.readGate node = some (weakenGate translated) := by
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
          simp only [RawNandCompilationState.readGate,
            readSource_after step _ _ leftAt, readSource_after step _ _ rightAt]
          rfl

theorem apply_faithful {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}
    {state : RawNandCompilationState graph} (step : RawNandReadyStep state)
    (checked : StateFaithful state) : StateFaithful step.apply := by
  change ∀ (node : Fin nodes) (index : Fin (state.count + 1)),
    (if node = step.node then some (Fin.last state.count)
      else (state.position node).map Fin.castSucc) = some index →
    step.apply.readGate node = some
      ⟨((state.program.snoc step.gate).terminalGateSources index).1,
        ((state.program.snoc step.gate).terminalGateSources index).2⟩
  intro node index placed
  by_cases same : node = step.node
  · subst node
    rw [if_pos rfl] at placed
    have sameIndex := Option.some.inj placed
    subst index
    change step.apply.readGate step.node = some
      ⟨((state.program.snoc step.gate).terminalGateSources (Fin.last state.count)).1,
        ((state.program.snoc step.gate).terminalGateSources (Fin.last state.count)).2⟩
    rw [sources_last]
    exact readGate_after step step.node step.gate step.compiled
  · simp only [if_neg same] at placed
    cases oldAt : state.position node with
    | none => simp only [oldAt, Option.map_none] at placed; cases placed
    | some oldIndex =>
        rw [oldAt] at placed
        have sameIndex := Option.some.inj placed
        subst index
        change step.apply.readGate node = some
          ⟨((state.program.snoc step.gate).terminalGateSources oldIndex.castSucc).1,
            ((state.program.snoc step.gate).terminalGateSources oldIndex.castSucc).2⟩
        rw [sources_before]
        exact readGate_after step node _ (checked node oldIndex oldAt)

theorem run_faithful {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}
    (state : RawNandCompilationState graph) (checked : StateFaithful state) :
    StateFaithful (runRawNandCompilation state).state := by
  rw [runRawNandCompilation]
  split
  · exact checked
  · rename_i step found
    exact run_faithful step.apply (apply_faithful step checked)
termination_by state.remaining.length
decreasing_by exact RawNandReadyStep.apply_remaining_lt _

private theorem finish_readSource {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}
    (state : RawNandCompilationState graph) (complete : state.remaining = [])
    (wire : Source inputs nodes) :
    state.readSource wire = some ((state.finish complete).translateSource wire) := by
  cases wire with
  | input index => rfl
  | constant value => rfl
  | gate node =>
      change (state.position node).map Source.gate =
        some (.gate ((state.finish complete).position node))
      rw [state.finish_position complete node]
      rfl

theorem finish_sources {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}
    (state : RawNandCompilationState graph) (complete : state.remaining = [])
    (checked : StateFaithful state) (node : Fin nodes) :
    (state.finish complete).program.terminalGateSources
        ((state.finish complete).position node) =
      ((state.finish complete).translateSource (graph.gate node).left,
        (state.finish complete).translateSource (graph.gate node).right) := by
  have actual := checked node _ (state.finish_position complete node)
  rw [RawNandCompilationState.readGate,
    finish_readSource state complete (graph.gate node).left,
    finish_readSource state complete (graph.gate node).right] at actual
  simp only [Option.some.injEq] at actual
  exact Prod.ext (congrArg Gate.left actual).symm (congrArg Gate.right actual).symm

/-- The success equation binds source fidelity to the actual compiler, not an
arbitrary semantically equivalent object inhabiting its result structure. -/
theorem compile_sources {inputs nodes : Nat} (graph : RawNandGraph inputs nodes)
    (compiled : CompiledRawNandGraph graph)
    (accepted : compileRawNandGraph graph = some compiled) (node : Fin nodes) :
    compiled.program.terminalGateSources (compiled.position node) =
      (compiled.translateSource (graph.gate node).left,
        compiled.translateSource (graph.gate node).right) := by
  let stop := runRawNandCompilation (RawNandCompilationState.initial graph)
  have checked := run_faithful (RawNandCompilationState.initial graph) (initial_faithful graph)
  change (if complete : stop.state.remaining = [] then
    some (stop.state.finish complete) else none) = some compiled at accepted
  split at accepted
  · rename_i complete
    cases accepted
    exact finish_sources stop.state complete checked node
  · cases accepted

/-- The actual inverse placement map recovers the source pair at every physical
position, including positions whose raw identifiers were not topological. -/
theorem physicalOrigin_sources {inputs nodes : Nat} (graph : RawNandGraph inputs nodes)
    (compiled : CompiledRawNandGraph graph)
    (accepted : compileRawNandGraph graph = some compiled) (position : Fin compiled.count) :
    compiled.program.terminalGateSources position =
      (compiled.translateSource (graph.gate (compiled.physicalOrigin position)).left,
        compiled.translateSource (graph.gate (compiled.physicalOrigin position)).right) := by
  have actual := compile_sources graph compiled accepted (compiled.physicalOrigin position)
  rw [compiled.position_physicalOrigin] at actual
  exact actual

end PNP.DirectWire.RawNandWireStructure
