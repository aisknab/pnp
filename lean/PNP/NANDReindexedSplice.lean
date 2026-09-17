/-
Copyright (c) 2026 PNP Labs.

Exact raw-splice transport through the computed structural reindexer. Retained
exterior nodes follow their canonical port bijection; replacement nodes retain
their coordinates. Literal gate sources and ordered outputs are mapped exactly,
so dependencies, well-foundedness and compiler acceptance agree in both directions.

No compatibility premise is needed for the raw graph correspondence. In
particular, a cyclic offered splice remains rejected; this does not assert that
every semantically compatible replacement is acyclic. Full manuscript profiles,
materializers and the remaining normalization rules are separate obligations.
-/

import PNP.NANDReindexedReplacement

namespace PNP.DirectWire.StructuralReindexing

variable {inputs gates outputs profileWidth replacementGates : Nat}
variable (original : Candidate inputs gates outputs) (relabeling : GateRenaming gates)
variable (records : List
  (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))

/-- Actual exterior ownership changes position; every replacement gate stays itself. -/
def spliceForward :
    Fin ((ArbitrarySupportSplice.exterior
      (backwardRecords original.program relabeling records)).length + replacementGates) →
    Fin ((ArbitrarySupportSplice.exterior records).length + replacementGates) :=
  splitFin
    (fun outside => Fin.castAdd replacementGates
      ((exteriorPorts original relabeling records).forward outside))
    (fun inside => Fin.natAdd (ArbitrarySupportSplice.exterior records).length inside)

def spliceBackward :
    Fin ((ArbitrarySupportSplice.exterior records).length + replacementGates) →
    Fin ((ArbitrarySupportSplice.exterior
      (backwardRecords original.program relabeling records)).length + replacementGates) :=
  splitFin
    (fun outside => Fin.castAdd replacementGates
      ((exteriorPorts original relabeling records).backward outside))
    (fun inside => Fin.natAdd (ArbitrarySupportSplice.exterior
      (backwardRecords original.program relabeling records)).length inside)

theorem spliceForward_exterior
    (outside : Fin (ArbitrarySupportSplice.exterior
      (backwardRecords original.program relabeling records)).length) :
    spliceForward original relabeling records (Fin.castAdd replacementGates outside) =
      Fin.castAdd replacementGates ((exteriorPorts original relabeling records).forward outside) := by
  unfold spliceForward
  exact splitFin_left _ _ outside

theorem spliceForward_replacement (inside : Fin replacementGates) :
    spliceForward original relabeling records
        (Fin.natAdd (ArbitrarySupportSplice.exterior
          (backwardRecords original.program relabeling records)).length inside) =
      Fin.natAdd (ArbitrarySupportSplice.exterior records).length inside := by
  unfold spliceForward
  exact splitFin_right _ _ inside

theorem spliceBackward_exterior
    (outside : Fin (ArbitrarySupportSplice.exterior records).length) :
    spliceBackward original relabeling records (Fin.castAdd replacementGates outside) =
      Fin.castAdd replacementGates ((exteriorPorts original relabeling records).backward outside) := by
  unfold spliceBackward
  exact splitFin_left _ _ outside

theorem spliceBackward_replacement (inside : Fin replacementGates) :
    spliceBackward original relabeling records
        (Fin.natAdd (ArbitrarySupportSplice.exterior records).length inside) =
      Fin.natAdd (ArbitrarySupportSplice.exterior
        (backwardRecords original.program relabeling records)).length inside := by
  unfold spliceBackward
  exact splitFin_right _ _ inside

theorem splice_backward_forward
    (node : Fin ((ArbitrarySupportSplice.exterior
      (backwardRecords original.program relabeling records)).length + replacementGates)) :
    spliceBackward original relabeling records (spliceForward original relabeling records node) =
      node := by
  rcases finSum_decompose node with ⟨outside, rfl⟩ | ⟨inside, rfl⟩
  · rw [spliceForward_exterior, spliceBackward_exterior,
      (exteriorPorts original relabeling records).backward_forward]
  · rw [spliceForward_replacement, spliceBackward_replacement]

theorem splice_forward_backward
    (node : Fin ((ArbitrarySupportSplice.exterior records).length + replacementGates)) :
    spliceForward original relabeling records (spliceBackward original relabeling records node) =
      node := by
  rcases finSum_decompose node with ⟨outside, rfl⟩ | ⟨inside, rfl⟩
  · rw [spliceBackward_exterior, spliceForward_exterior,
      (exteriorPorts original relabeling records).forward_backward]
  · rw [spliceBackward_replacement, spliceForward_replacement]

private theorem splice_source_roundtrip
    (source : Source inputs ((ArbitrarySupportSplice.exterior
      (backwardRecords original.program relabeling records)).length + replacementGates)) :
    sourceMap (spliceBackward original relabeling records)
      (sourceMap (spliceForward original relabeling records) source) = source := by
  cases source with
  | input index => rfl
  | constant value => rfl
  | gate node => exact congrArg Source.gate (splice_backward_forward original relabeling records node)

private theorem splice_source_injective :
    Function.Injective (sourceMap (inputs := inputs)
      (spliceForward (replacementGates := replacementGates) original relabeling records)) := by
  intro left right same
  have recovered := congrArg (sourceMap (spliceBackward original relabeling records)) same
  rw [splice_source_roundtrip, splice_source_roundtrip] at recovered
  exact recovered

/-- Every actual boundary port reconnects to the corresponding primary or exterior wire. -/
theorem splice_boundarySource_forward
    (port : Fin (terminalBoundaryPorts original.program
      (backwardRecords original.program relabeling records)).length) :
    sourceMap (spliceForward (replacementGates := replacementGates) original relabeling records)
        (ArbitrarySupportSplice.boundarySource original
          (backwardRecords original.program relabeling records) port) =
      ArbitrarySupportSplice.boundarySource (result original relabeling) records
        ((boundaryPorts original relabeling records).forward port) := by
  cases atPort : (terminalBoundaryPorts original.program
      (backwardRecords original.program relabeling records)).get port with
  | input input =>
      have nextAt : (terminalBoundaryPorts (result original relabeling).program records).get
          ((boundaryPorts original relabeling records).forward port) = .input input := by
        rw [(boundaryPorts original relabeling records).forward_get, atPort]
        rfl
      rw [ArbitrarySupportSplice.boundarySource_input original
        (backwardRecords original.program relabeling records) port input atPort,
        ArbitrarySupportSplice.boundarySource_input (result original relabeling) records
          ((boundaryPorts original relabeling records).forward port) input nextAt]
      rfl
  | gate producer =>
      have member : TerminalSupportWire.gate producer ∈ terminalBoundaryPorts original.program
          (backwardRecords original.program relabeling records) := by
        rw [← atPort]
        exact List.get_mem _ _
      have unselected : terminalGateSelected
          (backwardRecords original.program relabeling records) producer = false :=
        (terminalWireExternal_eq_true_iff _ (.gate producer)).mp
          ((terminalBoundaryWire_eq_true_iff original.program _ (.gate producer)).mp
            ((mem_terminalBoundaryPorts_iff original.program _ (.gate producer)).mp member)).1
      obtain ⟨index, bound, found⟩ := List.mem_iff_getElem.mp
        ((ArbitrarySupportSplice.mem_exterior_iff
          (backwardRecords original.program relabeling records) producer).mpr unselected)
      let outside : Fin (ArbitrarySupportSplice.exterior
          (backwardRecords original.program relabeling records)).length := ⟨index, bound⟩
      have oldGet : (ArbitrarySupportSplice.exterior
          (backwardRecords original.program relabeling records)).get outside = producer := found
      have oldAt : (terminalBoundaryPorts original.program
          (backwardRecords original.program relabeling records)).get port =
            .gate ((ArbitrarySupportSplice.exterior
              (backwardRecords original.program relabeling records)).get outside) := by
        rw [oldGet]
        exact atPort
      have nextAt : (terminalBoundaryPorts (result original relabeling).program records).get
          ((boundaryPorts original relabeling records).forward port) =
            .gate ((ArbitrarySupportSplice.exterior records).get
              ((exteriorPorts original relabeling records).forward outside)) := by
        rw [(boundaryPorts original relabeling records).forward_get, atPort,
          (exteriorPorts original relabeling records).forward_get, oldGet]
        rfl
      rw [ArbitrarySupportSplice.boundarySource_gate original
        (backwardRecords original.program relabeling records) port outside oldAt,
        ArbitrarySupportSplice.boundarySource_gate (result original relabeling) records
          ((boundaryPorts original relabeling records).forward port)
          ((exteriorPorts original relabeling records).forward outside) nextAt]
      exact congrArg Source.gate (spliceForward_exterior original relabeling records outside)

/-- Input rewiring and unchanged replacement indices commute with literal binding. -/
theorem splice_replacementSource_forward
    (source : Source
      (terminalBoundaryPorts (result original relabeling).program records).length replacementGates) :
    sourceMap (spliceForward original relabeling records)
        (ArbitrarySupportSplice.replacementSource original
          (backwardRecords original.program relabeling records)
          (source.renameInputs (boundaryPorts original relabeling records).backward)) =
      ArbitrarySupportSplice.replacementSource (result original relabeling) records source := by
  cases source with
  | input port =>
      have same := splice_boundarySource_forward (replacementGates := replacementGates)
        original relabeling records ((boundaryPorts original relabeling records).backward port)
      rw [(boundaryPorts original relabeling records).forward_backward] at same
      exact same
  | constant value => rfl
  | gate node => exact congrArg Source.gate (spliceForward_replacement original relabeling records node)

variable (offered : Candidate
  (terminalBoundaryPorts (result original relabeling).program records).length replacementGates
  (terminalInterfacePorts (result original relabeling) records).length)

private theorem splice_originalSource_forward (source : Source inputs gates)
    (oldVisible : ArbitrarySupportSplice.Visible original
      (backwardRecords original.program relabeling records) source)
    (newVisible : ArbitrarySupportSplice.Visible (result original relabeling) records
      (sourceMap (forwardGate original.program relabeling) source)) :
    sourceMap (spliceForward original relabeling records)
        (ArbitrarySupportSplice.originalSource original
          (backwardRecords original.program relabeling records)
          (pullReplacement original relabeling records offered) source oldVisible) =
      ArbitrarySupportSplice.originalSource (result original relabeling) records offered
        (sourceMap (forwardGate original.program relabeling) source) newVisible := by
  cases source with
  | input index => rfl
  | constant value => rfl
  | gate producer =>
      cases selected : terminalGateSelected
          (backwardRecords original.program relabeling records) producer with
      | false =>
          obtain ⟨index, bound, found⟩ := List.mem_iff_getElem.mp
            ((ArbitrarySupportSplice.mem_exterior_iff
              (backwardRecords original.program relabeling records) producer).mpr selected)
          let outside : Fin (ArbitrarySupportSplice.exterior
              (backwardRecords original.program relabeling records)).length := ⟨index, bound⟩
          have oldGet : (ArbitrarySupportSplice.exterior
              (backwardRecords original.program relabeling records)).get outside = producer := found
          subst producer
          have nextGet := (exteriorPorts original relabeling records).forward_get outside
          have nextEquation := ArbitrarySupportSplice.originalSource_exterior
            (result original relabeling) records offered
            ((exteriorPorts original relabeling records).forward outside)
            (by rw [nextGet]; exact newVisible)
          simp only [nextGet] at nextEquation
          have oldEquation := ArbitrarySupportSplice.originalSource_exterior original
            (backwardRecords original.program relabeling records)
            (pullReplacement original relabeling records offered) outside oldVisible
          exact (congrArg (sourceMap (spliceForward original relabeling records)) oldEquation).trans
            ((congrArg Source.gate
              (spliceForward_exterior original relabeling records outside)).trans nextEquation.symm)
      | true =>
          obtain ⟨index, bound, found⟩ := List.mem_iff_getElem.mp
            (oldVisible producer rfl selected)
          let port : Fin (terminalInterfacePorts original
              (backwardRecords original.program relabeling records)).length := ⟨index, bound⟩
          have oldGet : (terminalInterfacePorts original
              (backwardRecords original.program relabeling records)).get port = producer := found
          subst producer
          have nextGet := (interfacePorts original relabeling records).forward_get port
          have nextEquation := ArbitrarySupportSplice.originalSource_interface
            (result original relabeling) records offered
            ((interfacePorts original relabeling records).forward port)
            (by rw [nextGet]; exact newVisible)
          simp only [nextGet] at nextEquation
          have oldEquation := ArbitrarySupportSplice.originalSource_interface original
            (backwardRecords original.program relabeling records)
            (pullReplacement original relabeling records offered) port oldVisible
          have wordEquation := congrArg
            (fun (wire : Source (terminalBoundaryPorts original.program
                (backwardRecords original.program relabeling records)).length replacementGates) =>
              sourceMap (spliceForward original relabeling records)
                (ArbitrarySupportSplice.replacementSource original
                  (backwardRecords original.program relabeling records) wire))
            (pullReplacement_output_source original relabeling records offered port)
          exact (congrArg (sourceMap (spliceForward original relabeling records)) oldEquation).trans
            (wordEquation.trans ((splice_replacementSource_forward original relabeling records
              (offered.directWireWord.source
                ((interfacePorts original relabeling records).forward port))).trans nextEquation.symm))

/-- Every raw gate keeps exactly its two sources under the computed node correspondence. -/
theorem splice_sources
    (node : Fin ((ArbitrarySupportSplice.exterior
      (backwardRecords original.program relabeling records)).length + replacementGates)) :
    (((ArbitrarySupportSplice.graph (result original relabeling) records offered).gate
        (spliceForward original relabeling records node)).left,
      ((ArbitrarySupportSplice.graph (result original relabeling) records offered).gate
        (spliceForward original relabeling records node)).right) =
      (sourceMap (spliceForward original relabeling records)
        ((ArbitrarySupportSplice.graph original
          (backwardRecords original.program relabeling records)
          (pullReplacement original relabeling records offered)).gate node).left,
       sourceMap (spliceForward original relabeling records)
        ((ArbitrarySupportSplice.graph original
          (backwardRecords original.program relabeling records)
          (pullReplacement original relabeling records offered)).gate node).right) := by
  rcases finSum_decompose node with ⟨outside, rfl⟩ | ⟨inside, rfl⟩
  · rw [spliceForward_exterior]
    simp only [ArbitrarySupportSplice.graph, splitFin_left, ArbitrarySupportSplice.exteriorGate,
      (exteriorPorts original relabeling records).forward_get, result_sources]
    apply Prod.ext
    · exact (splice_originalSource_forward original relabeling records offered _ _ _).symm
    · exact (splice_originalSource_forward original relabeling records offered _ _ _).symm
  · rw [spliceForward_replacement]
    simp only [ArbitrarySupportSplice.graph, splitFin_right, ArbitrarySupportSplice.replacementGate,
      pullReplacement_gate_sources]
    apply Prod.ext
    · exact (splice_replacementSource_forward original relabeling records _).symm
    · exact (splice_replacementSource_forward original relabeling records _).symm

/-- Ordered global outputs, including aliases and constants, follow the same literal map. -/
theorem splice_output_source (output : Fin outputs) :
    (ArbitrarySupportSplice.word (result original relabeling) records offered).source output =
      sourceMap (spliceForward original relabeling records)
        ((ArbitrarySupportSplice.word original
          (backwardRecords original.program relabeling records)
          (pullReplacement original relabeling records offered)).source output) := by
  simp only [ArbitrarySupportSplice.word, result_output_source]
  exact (splice_originalSource_forward original relabeling records offered _ _ _).symm

/-- Neither an edge nor its direction can be added or lost by the raw transport. -/
theorem splice_dependencies
    (producer consumer : Fin ((ArbitrarySupportSplice.exterior
      (backwardRecords original.program relabeling records)).length + replacementGates)) :
    (ArbitrarySupportSplice.graph original
      (backwardRecords original.program relabeling records)
      (pullReplacement original relabeling records offered)).Depends producer consumer ↔
    (ArbitrarySupportSplice.graph (result original relabeling) records offered).Depends
      (spliceForward original relabeling records producer)
      (spliceForward original relabeling records consumer) := by
  have same := splice_sources original relabeling records offered consumer
  have leftSame := congrArg Prod.fst same
  have rightSame := congrArg Prod.snd same
  dsimp only at leftSame rightSame
  unfold RawNandGraph.Depends
  rw [leftSame, rightSame]
  constructor
  · intro edge
    rcases edge with left | right
    · exact Or.inl (congrArg (sourceMap (spliceForward original relabeling records)) left)
    · exact Or.inr (congrArg (sourceMap (spliceForward original relabeling records)) right)
  · intro edge
    rcases edge with left | right
    · exact Or.inl (splice_source_injective original relabeling records left)
    · exact Or.inr (splice_source_injective original relabeling records right)

private theorem accessible_pullback {alpha beta : Type}
    (mapping : alpha → beta) {before : alpha → alpha → Prop} {after : beta → beta → Prop}
    (preserves : ∀ {left right}, before left right → after (mapping left) (mapping right))
    {node : beta} (accessible : Acc after node) :
    ∀ prior, mapping prior = node → Acc before prior := by
  induction accessible with
  | intro node _predecessors ih =>
      intro prior same
      apply Acc.intro
      intro child edge
      apply ih (mapping child) ?_ child rfl
      rw [← same]
      exact preserves edge

/-- Acyclicity is equivalent for the two actual raw graphs, including nonconvex supports. -/
theorem splice_wellFounded_iff :
    WellFounded (ArbitrarySupportSplice.graph original
      (backwardRecords original.program relabeling records)
      (pullReplacement original relabeling records offered)).Depends ↔
    WellFounded (ArbitrarySupportSplice.graph (result original relabeling) records offered).Depends := by
  constructor
  · intro prior
    have preserves : ∀ {left right},
        (ArbitrarySupportSplice.graph (result original relabeling) records offered).Depends left right →
        (ArbitrarySupportSplice.graph original
          (backwardRecords original.program relabeling records)
          (pullReplacement original relabeling records offered)).Depends
            (spliceBackward original relabeling records left)
            (spliceBackward original relabeling records right) := by
      intro left right edge
      apply (splice_dependencies original relabeling records offered _ _).mpr
      simpa only [splice_forward_backward] using edge
    exact ⟨fun node => accessible_pullback (spliceBackward original relabeling records)
      preserves (prior.apply _) node rfl⟩
  · intro descendant
    exact ⟨fun node => accessible_pullback (spliceForward original relabeling records)
      (fun {left right} edge =>
        (splice_dependencies original relabeling records offered left right).mp edge)
      (descendant.apply _) node rfl⟩

/-- The actual compilers succeed together; no successful order or result is supplied. -/
theorem splice_compile_success_iff :
    (∃ checked, ArbitrarySupportSplice.compile original
      (backwardRecords original.program relabeling records)
      (pullReplacement original relabeling records offered) = some checked) ↔
    (∃ checked, ArbitrarySupportSplice.compile (result original relabeling) records offered =
      some checked) := by
  rw [ArbitrarySupportSplice.compile_success_iff, ArbitrarySupportSplice.compile_success_iff]
  exact splice_wellFounded_iff original relabeling records offered

/-- Cyclic raw replacements are rejected on both sides rather than silently repaired. -/
theorem splice_compile_failure_iff :
    ArbitrarySupportSplice.compile original
      (backwardRecords original.program relabeling records)
      (pullReplacement original relabeling records offered) = none ↔
    ArbitrarySupportSplice.compile (result original relabeling) records offered = none := by
  rw [ArbitrarySupportSplice.compile_failure_iff, ArbitrarySupportSplice.compile_failure_iff]
  constructor
  · intro prior cyclic
    exact prior ((splice_wellFounded_iff original relabeling records offered).mpr cyclic)
  · intro descendant cyclic
    exact descendant ((splice_wellFounded_iff original relabeling records offered).mp cyclic)

end PNP.DirectWire.StructuralReindexing
