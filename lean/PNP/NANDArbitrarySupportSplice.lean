/-
Copyright (c) 2026 PNP Labs.

Literal arbitrary-support replacement from actual physical ports. The raw
graph retains each exterior gate exactly once and binds every selected output
to the replacement's corresponding interface port. Topological order is
computed, not supplied. Cyclic wiring is not a direct-wire implementation.

This is physical substitution, not full-profile compatibility, complete
Package E, unconditional ZeroSlack, or polynomial PCCMin.
-/

import PNP.NANDTopologicalCompiler
import PNP.NANDTopologicalCausalBounds
import PNP.ResidualTerminalSaturatedSupportContext
import PNP.NANDNormalizationCausalBounds

namespace PNP
namespace DirectWire
namespace ArbitrarySupportSplice

private def locate {alpha : Type} [DecidableEq alpha] (item : alpha) :
    (items : List alpha) → item ∈ items →
      {index : Fin items.length // items.get index = item}
  | [], member => False.elim (by cases member)
  | head :: tail, member =>
      if same : item = head then
        ⟨⟨0, Nat.zero_lt_succ _⟩, by subst item; rfl⟩
      else
        let found := locate item tail ((List.mem_cons.mp member).resolve_left same)
        ⟨found.1.succ, found.2⟩

private def memberIndex {alpha : Type} [DecidableEq alpha]
    {item : alpha} {items : List alpha} (member : item ∈ items) :
    Fin items.length := (locate item items member).1

private theorem get_memberIndex {alpha : Type} [DecidableEq alpha]
    {item : alpha} {items : List alpha} (member : item ∈ items) :
    items.get (memberIndex member) = item := (locate item items member).2

private theorem index_cases {width : Nat} (index : Fin (width + 1)) :
    (∃ earlier : Fin width, index = earlier.castSucc) ∨ index = Fin.last width := by
  if within : index.val < width then
    exact Or.inl ⟨⟨index.val, within⟩, Fin.ext rfl⟩
  else
    apply Or.inr
    apply Fin.ext
    have upper := index.isLt
    change index.val = width
    omega

private theorem sources_earlier {inputs gates : Nat}
    (initial : Program inputs gates) (gate : Gate inputs gates) (index : Fin gates) :
    (initial.snoc gate).terminalGateSources index.castSucc =
      ((initial.terminalGateSources index).1.weakenGates 1,
        (initial.terminalGateSources index).2.weakenGates 1) := by
  change (if within : index.castSucc.val < gates then
    let pair := initial.terminalGateSources ⟨index.castSucc.val, within⟩
    (pair.1.weakenGates 1, pair.2.weakenGates 1)
    else (gate.left.weakenGates 1, gate.right.weakenGates 1)) = _
  split
  · rfl
  · rename_i outside
    exact False.elim (outside index.isLt)

private theorem sources_last {inputs gates : Nat}
    (initial : Program inputs gates) (gate : Gate inputs gates) :
    (initial.snoc gate).terminalGateSources (Fin.last gates) =
      (gate.left.weakenGates 1, gate.right.weakenGates 1) := by
  change (if within : (Fin.last gates).val < gates then
    let pair := initial.terminalGateSources ⟨(Fin.last gates).val, within⟩
    (pair.1.weakenGates 1, pair.2.weakenGates 1)
    else (gate.left.weakenGates 1, gate.right.weakenGates 1)) = _
  split
  · rename_i impossible
    exact False.elim (Nat.lt_irrefl gates impossible)
  · rfl

private theorem weaken_eval {inputs gates : Nat}
    (program : Program inputs gates) (gate : Gate inputs gates)
    (source : Source inputs gates) (input : Valuation inputs) :
    (source.weakenGates 1).eval input ((program.snoc gate).eval input) =
      source.eval input (program.eval input) := by
  cases source with
  | input index => rfl
  | constant value => rfl
  | gate index => exact Program.eval_snoc_castSucc program gate input index

theorem sources_eval {inputs gates : Nat}
    (program : Program inputs gates) (input : Valuation inputs) (index : Fin gates) :
    boolNand
      ((program.terminalGateSources index).1.eval input (program.eval input))
      ((program.terminalGateSources index).2.eval input (program.eval input)) =
        program.eval input index := by
  induction program with
  | empty => exact Fin.elim0 index
  | @snoc gates initial gate ih =>
      rcases index_cases index with ⟨earlier, rfl⟩ | rfl
      · rw [sources_earlier, weaken_eval, weaken_eval, ih,
          Program.eval_snoc_castSucc]
      · rw [sources_last, weaken_eval, weaken_eval, Program.eval_snoc_last]
        rfl

private theorem weaken_gate {inputs gates : Nat}
    (source : Source inputs gates) (producer : Fin (gates + 1))
    (same : source.weakenGates 1 = .gate producer) :
    ∃ earlier : Fin gates, source = .gate earlier ∧ producer = earlier.castSucc := by
  cases source with
  | input index => cases same
  | constant value => cases same
  | gate earlier =>
      have indices : earlier.castSucc = producer := Source.gate.inj same
      exact ⟨earlier, rfl, indices.symm⟩

theorem sources_ordered {inputs gates : Nat}
    (program : Program inputs gates) (consumer producer : Fin gates)
    (edge : (program.terminalGateSources consumer).1 = .gate producer ∨
      (program.terminalGateSources consumer).2 = .gate producer) :
    producer.val < consumer.val := by
  induction program with
  | empty => exact Fin.elim0 consumer
  | @snoc gates initial gate ih =>
      rcases index_cases consumer with ⟨earlier, rfl⟩ | rfl
      · rw [sources_earlier] at edge
        rcases edge with leftAt | rightAt
        · obtain ⟨prior, original, rfl⟩ := weaken_gate _ producer leftAt
          exact ih earlier prior (Or.inl original)
        · obtain ⟨prior, original, rfl⟩ := weaken_gate _ producer rightAt
          exact ih earlier prior (Or.inr original)
      · rw [sources_last] at edge
        rcases edge with leftAt | rightAt
        · obtain ⟨prior, _original, rfl⟩ := weaken_gate _ producer leftAt
          exact prior.isLt
        · obtain ⟨prior, _original, rfl⟩ := weaken_gate _ producer rightAt
          exact prior.isLt

variable {inputs gates outputs profileWidth replacementGates : Nat}

/-- The actual original gate coordinates outside the selected support. -/
def exterior
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (Fin gates) :=
  terminalSelectedGateIndices (fun gate => !(terminalGateSelected records gate))

theorem mem_exterior_iff
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates) :
    gate ∈ exterior records ↔ terminalGateSelected records gate = false := by
  rw [exterior, mem_terminalSelectedGateIndices_iff]
  cases terminalGateSelected records gate <;> decide

private theorem exteriorGet_unselected
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (index : Fin (exterior records).length) :
    terminalGateSelected records ((exterior records).get index) = false :=
  (mem_exterior_iff records _).1 (List.get_mem _ _)

variable (candidate : Candidate inputs gates outputs)
variable (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))

private theorem boundaryGate_unselected (gate : Fin gates)
    (member : TerminalSupportWire.gate gate ∈
      terminalBoundaryPorts candidate.program records) :
    terminalGateSelected records gate = false :=
  (terminalWireExternal_eq_true_iff records (.gate gate)).1
    ((terminalBoundaryWire_eq_true_iff candidate.program records (.gate gate)).1
      ((mem_terminalBoundaryPorts_iff candidate.program records (.gate gate)).1 member)).1

/-- Bind an actual incoming boundary port to its primary input or exterior gate. -/
def boundarySource (port : Fin (terminalBoundaryPorts candidate.program records).length) :
    Source inputs ((exterior records).length + replacementGates) :=
  match found : (terminalBoundaryPorts candidate.program records).get port with
  | .input index => .input index
  | .gate gate =>
      .gate (Fin.castAdd replacementGates (memberIndex
        ((mem_exterior_iff records gate).2
          (boundaryGate_unselected candidate records gate
            (by rw [← found]; exact List.get_mem _ _)))))

/-- Bind every replacement source through the computed original boundary. -/
def replacementSource :
    Source (terminalBoundaryPorts candidate.program records).length replacementGates →
      Source inputs ((exterior records).length + replacementGates)
  | .input port => boundarySource candidate records port
  | .constant value => .constant value
  | .gate index => .gate (Fin.natAdd (exterior records).length index)

variable (replacement : Candidate
  (terminalBoundaryPorts candidate.program records).length replacementGates
  (terminalInterfacePorts candidate records).length)

/-- Only selected gate references require an actual outgoing interface port. -/
def Visible (source : Source inputs gates) : Prop :=
  ∀ gate, source = .gate gate → terminalGateSelected records gate = true →
    gate ∈ terminalInterfacePorts candidate records

/-- Rebind a complete-program source, with no unresolved-source fallback. -/
def originalSource : (source : Source inputs gates) →
    Visible candidate records source →
      Source inputs ((exterior records).length + replacementGates)
  | .input index, _visible => .input index
  | .constant value, _visible => .constant value
  | .gate gate, visible =>
      if selected : terminalGateSelected records gate = true then
        replacementSource candidate records
          (replacement.directWireWord.source
            (memberIndex (visible gate rfl selected)))
      else
        .gate (Fin.castAdd replacementGates (memberIndex
          ((mem_exterior_iff records gate).2 (by
            cases value : terminalGateSelected records gate with
            | false => rfl
            | true => exact False.elim (selected value)))))

theorem exteriorSource_visible (consumer : Fin gates)
    (outside : terminalGateSelected records consumer = false)
    (source : Source inputs gates)
    (occurs : (candidate.program.terminalGateSources consumer).1 = source ∨
      (candidate.program.terminalGateSources consumer).2 = source) :
    Visible candidate records source := by
  intro producer sourceAt selected
  apply (mem_terminalInterfacePorts_iff candidate records producer).2
  apply (terminalInterfaceGate_eq_true_iff candidate records producer).2
  refine ⟨selected, Or.inl ?_⟩
  apply (terminalGateHasExternalConsumer_eq_true_iff
    candidate.program records producer).2
  refine ⟨consumer, mem_allFin consumer, outside, ?_⟩
  change
    (decide ((candidate.program.terminalGateSources consumer).1.terminalSupportWire? =
      some (.gate producer)) ||
    decide ((candidate.program.terminalGateSources consumer).2.terminalSupportWire? =
      some (.gate producer))) = true
  simp only [Bool.or_eq_true]
  rcases occurs with leftAt | rightAt
  · exact Or.inl (decide_eq_true (by rw [leftAt, sourceAt]; rfl))
  · exact Or.inr (decide_eq_true (by rw [rightAt, sourceAt]; rfl))

theorem output_visible (output : Fin outputs) :
    Visible candidate records (candidate.directWireWord.source output) := by
  intro producer sourceAt selected
  apply (mem_terminalInterfacePorts_iff candidate records producer).2
  apply (terminalInterfaceGate_eq_true_iff candidate records producer).2
  exact ⟨selected, Or.inr
    ((terminalGateIsGlobalOutput_eq_true_iff candidate.directWireWord producer).2
      ⟨output, sourceAt⟩)⟩

/-- One retained exterior gate, with selected producers replaced at exact ports. -/
def exteriorGate (index : Fin (exterior records).length) :
    Gate inputs ((exterior records).length + replacementGates) :=
  let original := (exterior records).get index
  let pair := candidate.program.terminalGateSources original
  ⟨originalSource candidate records replacement pair.1
      (exteriorSource_visible candidate records original
        (exteriorGet_unselected records index) pair.1 (Or.inl rfl)),
    originalSource candidate records replacement pair.2
      (exteriorSource_visible candidate records original
        (exteriorGet_unselected records index) pair.2 (Or.inr rfl))⟩

/-- One replacement gate, with all its input and gate references physically bound. -/
def replacementGate (index : Fin replacementGates) :
    Gate inputs ((exterior records).length + replacementGates) :=
  let pair := replacement.program.terminalGateSources index
  ⟨replacementSource candidate records pair.1,
    replacementSource candidate records pair.2⟩

/-- Literal splice data, with no caller-supplied graph, order, frame or maps. -/
def graph : RawNandGraph inputs ((exterior records).length + replacementGates) :=
  ⟨splitFin (exteriorGate candidate records replacement)
    (replacementGate candidate records replacement)⟩

/-- Every ordered original output is rebound; repeated and constant outputs remain. -/
def word : DirectWireWord inputs ((exterior records).length + replacementGates) outputs :=
  ⟨fun output => originalSource candidate records replacement
    (candidate.directWireWord.source output) (output_visible candidate records output)⟩

/-- The executable constructor derives its order or rejects a cyclic literal splice. -/
def compile : Option (CompiledRawNandGraph (graph candidate records replacement)) :=
  compileRawNandGraph (graph candidate records replacement)

/-- A successful compile yields the actual reconnected whole candidate. -/
def result (compiled : CompiledRawNandGraph (graph candidate records replacement)) :
    Candidate inputs compiled.count outputs :=
  compiled.candidate (word candidate records replacement)

theorem result_gateCount
    (compiled : CompiledRawNandGraph (graph candidate records replacement)) :
    (result candidate records replacement compiled).toImplementation.gateCount =
      (exterior records).length + replacementGates :=
  compiled.candidate_gateCount (word candidate records replacement)

theorem compile_success_iff :
    (∃ compiled, compile candidate records replacement = some compiled) ↔
      WellFounded (graph candidate records replacement).Depends :=
  compileRawNandGraph_success_iff (graph candidate records replacement)

theorem compile_failure_iff :
    compile candidate records replacement = none ↔
      ¬WellFounded (graph candidate records replacement).Depends :=
  compileRawNandGraph_failure_iff (graph candidate records replacement)

/-- Values for every literal graph node, derived from the two actual executions. -/
def values (input : Valuation inputs) :
    Valuation ((exterior records).length + replacementGates) :=
  splitFin
    (fun index => candidate.program.eval input ((exterior records).get index))
    (replacement.program.eval (terminalInducedBoundaryValuation candidate records input))

private theorem boundarySource_eval
    (port : Fin (terminalBoundaryPorts candidate.program records).length)
    (input : Valuation inputs) :
    (boundarySource (replacementGates := replacementGates) candidate records port).eval
      input (values candidate records replacement input) =
        terminalInducedBoundaryValuation candidate records input port := by
  unfold boundarySource
  split
  · rename_i index found
    change input index = _
    unfold terminalInducedBoundaryValuation
    rw [found]
    rfl
  · rename_i gate found
    dsimp only [Source.eval, values]
    rw [splitFin_left, get_memberIndex]
    unfold terminalInducedBoundaryValuation
    rw [found]
    rfl

theorem replacementSource_eval
    (source : Source (terminalBoundaryPorts candidate.program records).length
      replacementGates) (input : Valuation inputs) :
    (replacementSource candidate records source).eval input
      (values candidate records replacement input) =
        source.eval (terminalInducedBoundaryValuation candidate records input)
          (replacement.program.eval
            (terminalInducedBoundaryValuation candidate records input)) := by
  cases source with
  | input port => exact boundarySource_eval candidate records replacement port input
  | constant value => rfl
  | gate index =>
      change values candidate records replacement input
        (Fin.natAdd (exterior records).length index) = _
      unfold values
      rw [splitFin_right]
      rfl

theorem originalSource_eval
    (equivalent : replacement.semantics =
      (extractTerminalSupport candidate records).extractedCandidate.semantics)
    (source : Source inputs gates) (visible : Visible candidate records source)
    (input : Valuation inputs) :
    (originalSource candidate records replacement source visible).eval input
      (values candidate records replacement input) =
        source.eval input (candidate.program.eval input) := by
  cases source with
  | input index => rfl
  | constant value => rfl
  | gate gate =>
      simp only [originalSource]
      split
      · rename_i selected
        rw [replacementSource_eval]
        let port := memberIndex (visible gate rfl selected)
        change replacement.semantics
          (terminalInducedBoundaryValuation candidate records input) port =
            candidate.program.eval input gate
        rw [equivalent, extractTerminalSupport_induced, get_memberIndex]
      · dsimp only [Source.eval, values]
        rw [splitFin_left, get_memberIndex]

/-- Every physical NAND equation is satisfied, not merely the final output tuple. -/
theorem values_solution
    (equivalent : replacement.semantics =
      (extractTerminalSupport candidate records).extractedCandidate.semantics)
    (input : Valuation inputs) :
    (graph candidate records replacement).Solution input
      (values candidate records replacement input) := by
  intro node
  rcases finSum_decompose node with ⟨outside, rfl⟩ | ⟨inside, rfl⟩
  · dsimp only [values, graph]
    rw [splitFin_left, splitFin_left]
    change candidate.program.eval input ((exterior records).get outside) =
      (exteriorGate candidate records replacement outside).eval input
        (values candidate records replacement input)
    unfold exteriorGate Gate.eval
    dsimp only
    rw [originalSource_eval candidate records replacement equivalent,
      originalSource_eval candidate records replacement equivalent]
    exact (sources_eval candidate.program input ((exterior records).get outside)).symm
  · dsimp only [values, graph]
    rw [splitFin_right, splitFin_right]
    change replacement.program.eval
      (terminalInducedBoundaryValuation candidate records input) inside =
        (replacementGate candidate records replacement inside).eval input
          (values candidate records replacement input)
    unfold replacementGate Gate.eval
    dsimp only
    rw [replacementSource_eval, replacementSource_eval]
    exact (sources_eval replacement.program
      (terminalInducedBoundaryValuation candidate records input) inside).symm

/-- Any accepted literal splice preserves all ordered original outputs. -/
theorem result_semantics
    (equivalent : replacement.semantics =
      (extractTerminalSupport candidate records).extractedCandidate.semantics)
    (compiled : CompiledRawNandGraph (graph candidate records replacement))
    (input : Valuation inputs) (output : Fin outputs) :
    (result candidate records replacement compiled).semantics input output =
      candidate.semantics input output := by
  unfold result
  rw [compiled.candidate_semantics _ input (values candidate records replacement input)
    (values_solution candidate records replacement equivalent input)]
  exact originalSource_eval candidate records replacement equivalent
    (candidate.directWireWord.source output) (output_visible candidate records output) input

private theorem selection_partition
    {gates : Nat} (selected : Fin gates → Bool) :
    (terminalSelectedGateIndices selected).length +
      (terminalSelectedGateIndices fun gate => !(selected gate)).length = gates := by
  induction gates with
  | zero => rfl
  | succ gates ih =>
      have earlier := ih (fun gate => selected gate.castSucc)
      cases lastValue : selected (Fin.last gates) <;>
        simp only [terminalSelectedGateIndices, lastValue, Bool.not_false,
          Bool.not_true, Bool.false_eq_true, if_false, if_true, List.length_append,
          List.length_map, List.length_cons, List.length_nil]
      · omega
      · omega

/-- Actual extracted support and actual retained exterior partition the old gates. -/
theorem exterior_accounting :
    (extractTerminalSupport candidate records).gateCount +
      (exterior records).length = gates := by
  rw [extractTerminalSupport_gateCount]
  exact selection_partition (terminalGateSelected records)

/-- All replacement gates are counted, even when the replacement is larger. -/
theorem result_exact_accounting
    (compiled : CompiledRawNandGraph (graph candidate records replacement)) :
    (result candidate records replacement compiled).toImplementation.gateCount +
      (extractTerminalSupport candidate records).gateCount =
        gates + replacementGates := by
  rw [result_gateCount]
  have partition := exterior_accounting candidate records
  omega

/-- A strict local physical saving becomes a strict saving in an accepted splice. -/
theorem result_strict_gain
    (smaller : replacementGates < (extractTerminalSupport candidate records).gateCount)
    (compiled : CompiledRawNandGraph (graph candidate records replacement)) :
    (result candidate records replacement compiled).toImplementation.gateCount < gates := by
  have exactCount := result_exact_accounting candidate records replacement compiled
  omega

/-- Primary-only physical boundary, derived by production predecessor closure. -/
def PrimaryBoundary : Prop :=
  ∀ wire, wire ∈ terminalBoundaryPorts candidate.program records →
    ∃ index : Fin inputs, wire = TerminalSupportWire.input index

/-- Replacement nodes precede exterior nodes, whose original ordering is retained. -/
def rank : Fin ((exterior records).length + replacementGates) → Nat :=
  splitFin (fun index => replacementGates + ((exterior records).get index).val)
    (fun index => index.val)

private theorem boundarySource_not_gate
    (primary : PrimaryBoundary candidate records)
    (port : Fin (terminalBoundaryPorts candidate.program records).length)
    (node : Fin ((exterior records).length + replacementGates))
    (same : boundarySource candidate records port = .gate node) : False := by
  unfold boundarySource at same
  split at same
  · cases same
  · rename_i gate found
    obtain ⟨index, impossible⟩ := primary (.gate gate)
      (by rw [← found]; exact List.get_mem _ _)
    cases impossible

private theorem replacementSource_rank_lt
    (primary : PrimaryBoundary candidate records)
    (source : Source (terminalBoundaryPorts candidate.program records).length
      replacementGates) (limit : Nat)
    (bounded : ∀ index, source = .gate index → index.val < limit)
    (node : Fin ((exterior records).length + replacementGates))
    (same : replacementSource candidate records source = .gate node) :
    rank records node < limit := by
  cases source with
  | input port =>
      exact False.elim (boundarySource_not_gate candidate records primary port node same)
  | constant value => cases same
  | gate index =>
      have mapped : Fin.natAdd (exterior records).length index = node :=
        Source.gate.inj same
      rw [← mapped, rank, splitFin_right]
      exact bounded index rfl

private theorem originalSource_rank_lt
    (primary : PrimaryBoundary candidate records)
    (source : Source inputs gates) (visible : Visible candidate records source)
    (consumer : Fin gates)
    (bounded : ∀ producer, source = .gate producer → producer.val < consumer.val)
    (node : Fin ((exterior records).length + replacementGates))
    (same : originalSource candidate records replacement source visible = .gate node) :
    rank records node < replacementGates + consumer.val := by
  cases source with
  | input index => cases same
  | constant value => cases same
  | gate producer =>
      simp only [originalSource] at same
      split at same
      · apply replacementSource_rank_lt candidate records primary _ _
          (fun index _isSource => ?_) node same
        have within := index.isLt
        omega
      · have mapped := Source.gate.inj same
        rw [← mapped, rank, splitFin_left, get_memberIndex]
        have earlier := bounded producer rfl
        omega

/-- Every actual dependency decreases the derived rank under a primary-only boundary. -/
theorem graph_rank_decreases
    (primary : PrimaryBoundary candidate records)
    (producer consumer : Fin ((exterior records).length + replacementGates))
    (edge : (graph candidate records replacement).Depends producer consumer) :
    rank records producer < rank records consumer := by
  rcases finSum_decompose consumer with ⟨outside, rfl⟩ | ⟨inside, rfl⟩
  · have consumerRank : rank (replacementGates := replacementGates) records
        (Fin.castAdd replacementGates outside) =
          replacementGates + ((exterior records).get outside).val := by
      unfold rank
      rw [splitFin_left]
    rw [consumerRank]
    dsimp only [RawNandGraph.Depends, graph] at edge
    simp only [splitFin_left] at edge
    rcases edge with leftAt | rightAt
    · exact originalSource_rank_lt candidate records replacement primary _ _
        ((exterior records).get outside)
        (fun prior atSource => sources_ordered candidate.program _ prior (Or.inl atSource))
        producer leftAt
    · exact originalSource_rank_lt candidate records replacement primary _ _
        ((exterior records).get outside)
        (fun prior atSource => sources_ordered candidate.program _ prior (Or.inr atSource))
        producer rightAt
  · have consumerRank : rank (replacementGates := replacementGates) records
        (Fin.natAdd (exterior records).length inside) = inside.val := by
      unfold rank
      rw [splitFin_right]
    rw [consumerRank]
    dsimp only [RawNandGraph.Depends, graph] at edge
    simp only [splitFin_right] at edge
    rcases edge with leftAt | rightAt
    · exact replacementSource_rank_lt candidate records primary _ inside.val
        (fun prior atSource => sources_ordered replacement.program inside prior
          (Or.inl atSource)) producer leftAt
    · exact replacementSource_rank_lt candidate records primary _ inside.val
        (fun prior atSource => sources_ordered replacement.program inside prior
          (Or.inr atSource)) producer rightAt

private theorem rank_accessible {nodes : Nat} (relation : Fin nodes → Fin nodes → Prop)
    (nodeRank : Fin nodes → Nat)
    (decreases : ∀ producer consumer, relation producer consumer →
      nodeRank producer < nodeRank consumer) (node : Fin nodes) :
    Acc relation node :=
  Acc.intro node (fun producer _edge => rank_accessible relation nodeRank decreases producer)
termination_by nodeRank node
decreasing_by exact decreases _ _ _edge

theorem graph_wellFounded_of_primaryBoundary
    (primary : PrimaryBoundary candidate records) :
    WellFounded (graph candidate records replacement).Depends :=
  ⟨fun node => rank_accessible _ (rank records)
    (graph_rank_decreases candidate records replacement primary) node⟩

/-- Actual production saturation derives acyclicity; no order proof is an input. -/
theorem production_compiles
    (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (replacement : Candidate
      (terminalBoundaryPorts candidate.program
        (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)).length
      replacementGates
      (terminalInterfacePorts candidate
        (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)).length) :
    ∃ compiled, compile candidate
      (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)
      replacement = some compiled := by
  apply (compile_success_iff candidate _ replacement).2
  apply graph_wellFounded_of_primaryBoundary candidate _ replacement
  intro wire member
  exact terminalCandidateSaturate_boundary_isInput candidate model seed wire member

/-- On production supports, both independently computed physical constructors agree
    in size and complete output semantics; no new credit is assigned to the old frame. -/
theorem production_agreement
    (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (replacement : Candidate
      (terminalBoundaryPorts candidate.program
        (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)).length
      replacementGates
      (terminalInterfacePorts candidate
        (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)).length)
    (equivalent : replacement.semantics =
      (extractTerminalSupport candidate (terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed)).extractedCandidate.semantics)
    (compiled : CompiledRawNandGraph (graph candidate (terminalSaturateRecords
      (terminalCandidateSaturationSystem candidate model) seed) replacement)) :
    let records := terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed
    let oldResult := (terminalCandidateSaturatePhysicalContext candidate model seed).plug replacement
    (result candidate records replacement compiled).toImplementation.gateCount =
      oldResult.toImplementation.gateCount ∧
    ∀ input output, (result candidate records replacement compiled).semantics input output =
      oldResult.semantics input output := by
  dsimp only
  let records := terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed
  have newAccounting := result_exact_accounting candidate records replacement compiled
  have oldAccounting := terminalCandidateSaturatePhysicalContext_size candidate model seed replacement
  have charges := terminalCandidateSaturatePhysicalCharges_size candidate model seed
  change (extractTerminalSupport candidate records).gateCount =
    (terminalSaturatePhysicalCharges
      (terminalCandidateSaturationSystem candidate model) seed).length at charges
  rw [Program.size_eq_gateCount, ← charges] at oldAccounting
  change ((terminalCandidateSaturatePhysicalContext candidate model seed).plug
    replacement).toImplementation.gateCount +
      (extractTerminalSupport candidate records).gateCount = gates + replacementGates at oldAccounting
  constructor
  · exact Nat.add_right_cancel (newAccounting.trans oldAccounting.symm)
  · intro input output
    have oldSemantics := terminalCandidateSaturatePhysicalContext_replace_equivalent
      candidate model seed replacement (fun boundary port =>
        congrFun (congrFun equivalent boundary) port) input output
    exact (result_semantics candidate records replacement equivalent compiled input output).trans
      oldSemantics.symm

/-- Place the optional replacement gate just after its sole external input.
    Retained original gates keep their original relative order. -/
private def singleGateRank (boundaryGate : Fin gates) :
    Fin ((exterior records).length + replacementGates) → Nat :=
  splitFin (fun index => 2 * ((exterior records).get index).val)
    (fun _ => 2 * boundaryGate.val + 1)

private theorem singleGateBoundarySource_rank
    (boundaryGate : Fin gates)
    (single : terminalBoundaryPorts candidate.program records = [.gate boundaryGate])
    (port : Fin (terminalBoundaryPorts candidate.program records).length)
    (node : Fin ((exterior records).length + replacementGates))
    (same : boundarySource candidate records port = .gate node) :
    singleGateRank records boundaryGate node = 2 * boundaryGate.val := by
  have atPort : (terminalBoundaryPorts candidate.program records).get port =
      .gate boundaryGate := by
    apply List.mem_singleton.mp
    rw [← single]
    exact List.get_mem _ _
  unfold boundarySource at same
  split at same
  · rename_i index found
    have impossible := found.symm.trans atPort
    cases impossible
  · rename_i original found
    have equal : original = boundaryGate :=
      TerminalSupportWire.gate.inj (found.symm.trans atPort)
    have mapped := Source.gate.inj same
    rw [← mapped, singleGateRank, splitFin_left, get_memberIndex, equal]

private theorem singleGateReplacementSource_rank_bound
    (boundaryGate : Fin gates)
    (single : terminalBoundaryPorts candidate.program records = [.gate boundaryGate])
    (source : Source (terminalBoundaryPorts candidate.program records).length replacementGates)
    (node : Fin ((exterior records).length + replacementGates))
    (same : replacementSource candidate records source = .gate node) :
    singleGateRank records boundaryGate node < 2 * boundaryGate.val + 2 := by
  cases source with
  | input port =>
      have value := singleGateBoundarySource_rank candidate records boundaryGate
        single port node same
      omega
  | constant value => cases same
  | gate index =>
      have mapped := Source.gate.inj same
      rw [← mapped, singleGateRank, splitFin_right]
      omega

private theorem singleGateOriginalSource_rank_lt
    (boundaryGate : Fin gates)
    (single : terminalBoundaryPorts candidate.program records = [.gate boundaryGate])
    (early : ∀ port : Fin (terminalInterfacePorts candidate records).length,
      ((terminalInterfacePorts candidate records).get port).val < boundaryGate.val →
        ∃ value, replacement.directWireWord.source port = .constant value)
    (source : Source inputs gates) (visible : Visible candidate records source)
    (consumer : Fin gates)
    (bounded : ∀ producer, source = .gate producer → producer.val < consumer.val)
    (node : Fin ((exterior records).length + replacementGates))
    (same : originalSource candidate records replacement source visible = .gate node) :
    singleGateRank records boundaryGate node < 2 * consumer.val := by
  cases source with
  | input index => cases same
  | constant value => cases same
  | gate producer =>
      simp only [originalSource] at same
      split at same
      · rename_i selected
        by_cases before : producer.val < boundaryGate.val
        · obtain ⟨value, literal⟩ := early (memberIndex (visible producer rfl selected))
            (by rw [get_memberIndex]; exact before)
          rw [literal] at same
          cases same
        · have sourceBound := singleGateReplacementSource_rank_bound candidate records
            boundaryGate single _ node same
          have earlier := bounded producer rfl
          omega
      · have mapped := Source.gate.inj same
        rw [← mapped, singleGateRank, splitFin_left, get_memberIndex]
        have earlier := bounded producer rfl
        omega

private theorem singleGateReplacementSource_rank_lt
    (boundaryGate : Fin gates)
    (single : terminalBoundaryPorts candidate.program records = [.gate boundaryGate])
    (small : replacementGates ≤ 1)
    (source : Source (terminalBoundaryPorts candidate.program records).length replacementGates)
    (consumer : Fin replacementGates)
    (bounded : ∀ producer, source = .gate producer → producer.val < consumer.val)
    (node : Fin ((exterior records).length + replacementGates))
    (same : replacementSource candidate records source = .gate node) :
    singleGateRank records boundaryGate node < 2 * boundaryGate.val + 1 := by
  cases source with
  | input port =>
      have value := singleGateBoundarySource_rank candidate records boundaryGate
        single port node same
      omega
  | constant value => cases same
  | gate producer =>
      have earlier := bounded producer rfl
      have within := consumer.isLt
      omega

private theorem singleGateGraph_rank_decreases
    (boundaryGate : Fin gates)
    (single : terminalBoundaryPorts candidate.program records = [.gate boundaryGate])
    (small : replacementGates ≤ 1)
    (early : ∀ port : Fin (terminalInterfacePorts candidate records).length,
      ((terminalInterfacePorts candidate records).get port).val < boundaryGate.val →
        ∃ value, replacement.directWireWord.source port = .constant value)
    (producer consumer : Fin ((exterior records).length + replacementGates))
    (edge : (graph candidate records replacement).Depends producer consumer) :
    singleGateRank records boundaryGate producer <
      singleGateRank records boundaryGate consumer := by
  rcases finSum_decompose consumer with ⟨outside, rfl⟩ | ⟨inside, rfl⟩
  · have consumerRank : singleGateRank (replacementGates := replacementGates)
        records boundaryGate (Fin.castAdd replacementGates outside) =
          2 * ((exterior records).get outside).val := by
      unfold singleGateRank
      rw [splitFin_left]
    rw [consumerRank]
    dsimp only [RawNandGraph.Depends, graph] at edge
    simp only [splitFin_left] at edge
    rcases edge with leftAt | rightAt
    · exact singleGateOriginalSource_rank_lt candidate records replacement
        boundaryGate single early _ _ ((exterior records).get outside)
        (fun prior atSource => sources_ordered candidate.program _ prior (Or.inl atSource))
        producer leftAt
    · exact singleGateOriginalSource_rank_lt candidate records replacement
        boundaryGate single early _ _ ((exterior records).get outside)
        (fun prior atSource => sources_ordered candidate.program _ prior (Or.inr atSource))
        producer rightAt
  · have consumerRank : singleGateRank (replacementGates := replacementGates)
        records boundaryGate (Fin.natAdd (exterior records).length inside) =
          2 * boundaryGate.val + 1 := by
      unfold singleGateRank
      rw [splitFin_right]
    rw [consumerRank]
    dsimp only [RawNandGraph.Depends, graph] at edge
    simp only [splitFin_right] at edge
    rcases edge with leftAt | rightAt
    · exact singleGateReplacementSource_rank_lt candidate records boundaryGate single
        small _ inside
        (fun prior atSource => sources_ordered replacement.program inside prior (Or.inl atSource))
        producer leftAt
    · exact singleGateReplacementSource_rank_lt candidate records boundaryGate single
        small _ inside
        (fun prior atSource => sources_ordered replacement.program inside prior (Or.inr atSource))
        producer rightAt

/-- A zero/one-gate replacement is acyclic across a sole external gate when
    every earlier frontier observation is represented by a literal constant.
    Source-derived unary realization establishes this condition by prefix
    causality; no caller-supplied graph or ordering is needed there. -/
theorem graph_wellFounded_of_singleGateBoundary
    (boundaryGate : Fin gates)
    (single : terminalBoundaryPorts candidate.program records = [.gate boundaryGate])
    (small : replacementGates ≤ 1)
    (early : ∀ port : Fin (terminalInterfacePorts candidate records).length,
      ((terminalInterfacePorts candidate records).get port).val < boundaryGate.val →
        ∃ value, replacement.directWireWord.source port = .constant value) :
    WellFounded (graph candidate records replacement).Depends :=
  ⟨fun node => rank_accessible _ (singleGateRank records boundaryGate)
    (singleGateGraph_rank_decreases candidate records replacement boundaryGate
      single small early) node⟩

/-- Original physical input positions, with primary inputs placed before every gate. -/
def causalBoundaryLabels :
    Fin (terminalBoundaryPorts candidate.program records).length → Nat :=
  terminalBoundaryCausalLabels candidate records (fun _ => 0) (fun index => index.val + 1)

/-- A numeric dependency bound, derived from extraction and actual history transport
in the complete construction. Boolean equivalence alone does not imply it. -/
def CausalInterfaceBound : Prop :=
  ∀ port, CausalBound.outputLevel replacement (causalBoundaryLabels candidate records) port ≤
    ((terminalInterfacePorts candidate records).get port).val + 1

/-- Original causal position followed by a local slot; the stride fits every
replacement gate and puts each exterior producer before its replacement consumers. -/
def causalRank : Fin ((exterior records).length + replacementGates) → Nat :=
  splitFin
    (fun index => (((exterior records).get index).val + 1) * (replacementGates + 1))
    (fun index => CausalBound.levels replacement.program
      (causalBoundaryLabels candidate records) index * (replacementGates + 1) +
        (index.val + 1))

private theorem boundarySource_causal_rank
    (port : Fin (terminalBoundaryPorts candidate.program records).length)
    (node : Fin ((exterior records).length + replacementGates))
    (same : boundarySource candidate records port = .gate node) :
    causalRank candidate records replacement node =
      causalBoundaryLabels candidate records port * (replacementGates + 1) := by
  unfold boundarySource at same
  split at same
  · cases same
  · rename_i gate found
    have mapped := Source.gate.inj same
    rw [← mapped, causalRank, splitFin_left, get_memberIndex]
    unfold causalBoundaryLabels terminalBoundaryCausalLabels
    rw [found]
    rfl

private theorem replacementSource_causal_rank_le
    (wire : Source (terminalBoundaryPorts candidate.program records).length
      replacementGates)
    (node : Fin ((exterior records).length + replacementGates))
    (same : replacementSource candidate records wire = .gate node) :
    causalRank candidate records replacement node ≤
      CausalBound.source wire (causalBoundaryLabels candidate records)
        (CausalBound.levels replacement.program (causalBoundaryLabels candidate records)) *
          (replacementGates + 1) + replacementGates := by
  cases wire with
  | input port =>
      rw [boundarySource_causal_rank candidate records replacement port node same]
      exact Nat.le_add_right _ _
  | constant value => cases same
  | gate index =>
      have mapped : Fin.natAdd (exterior records).length index = node :=
        Source.gate.inj same
      rw [← mapped, causalRank, splitFin_right]
      simp only [CausalBound.source]
      have within := index.isLt
      omega

private theorem replacementSource_causal_rank_lt
    (wire : Source (terminalBoundaryPorts candidate.program records).length
      replacementGates) (consumer : Fin replacementGates)
    (levelBound : CausalBound.source wire (causalBoundaryLabels candidate records)
      (CausalBound.levels replacement.program (causalBoundaryLabels candidate records)) ≤
        CausalBound.levels replacement.program (causalBoundaryLabels candidate records) consumer)
    (earlier : ∀ prior, wire = .gate prior → prior.val < consumer.val)
    (node : Fin ((exterior records).length + replacementGates))
    (same : replacementSource candidate records wire = .gate node) :
    causalRank candidate records replacement node <
      CausalBound.levels replacement.program (causalBoundaryLabels candidate records) consumer *
        (replacementGates + 1) + (consumer.val + 1) := by
  have scaled := Nat.mul_le_mul_right (replacementGates + 1) levelBound
  cases wire with
  | input port =>
      rw [boundarySource_causal_rank candidate records replacement port node same]
      change causalBoundaryLabels candidate records port * (replacementGates + 1) ≤ _ at scaled
      omega
  | constant value => cases same
  | gate index =>
      have mapped : Fin.natAdd (exterior records).length index = node :=
        Source.gate.inj same
      rw [← mapped, causalRank, splitFin_right]
      have before := earlier index rfl
      change CausalBound.levels replacement.program
        (causalBoundaryLabels candidate records) index * (replacementGates + 1) ≤ _ at scaled
      omega

private theorem originalSource_causal_rank_lt
    (interfaceBound : CausalInterfaceBound candidate records replacement)
    (wire : Source inputs gates) (visible : Visible candidate records wire)
    (consumer : Fin gates)
    (earlier : ∀ producer, wire = .gate producer → producer.val < consumer.val)
    (node : Fin ((exterior records).length + replacementGates))
    (same : originalSource candidate records replacement wire visible = .gate node) :
    causalRank candidate records replacement node <
      (consumer.val + 1) * (replacementGates + 1) := by
  have expanded : (consumer.val + 1) * (replacementGates + 1) =
      consumer.val * (replacementGates + 1) + (replacementGates + 1) := by
    simp only [Nat.add_mul, Nat.one_mul]
  rw [expanded]
  cases wire with
  | input index => cases same
  | constant value => cases same
  | gate producer =>
      have before := earlier producer rfl
      simp only [originalSource] at same
      split at same
      · rename_i selected
        have portBound := interfaceBound (memberIndex (visible producer rfl selected))
        rw [get_memberIndex] at portBound
        have through := replacementSource_causal_rank_le candidate records replacement
          (replacement.directWireWord.source
            (memberIndex (visible producer rfl selected))) node same
        have levelBound : CausalBound.outputLevel replacement
            (causalBoundaryLabels candidate records)
            (memberIndex (visible producer rfl selected)) ≤ consumer.val := by
          omega
        have scaled := Nat.mul_le_mul_right (replacementGates + 1) levelBound
        unfold CausalBound.outputLevel at scaled
        omega
      · have mapped := Source.gate.inj same
        rw [← mapped, causalRank, splitFin_left, get_memberIndex]
        have bounded : producer.val + 1 ≤ consumer.val := by omega
        have scaled := Nat.mul_le_mul_right (replacementGates + 1) bounded
        omega

/-- Every literal dependency decreases the source-derived causal order. -/
theorem graph_causal_rank_decreases
    (interfaceBound : CausalInterfaceBound candidate records replacement)
    (producer consumer : Fin ((exterior records).length + replacementGates))
    (edge : (graph candidate records replacement).Depends producer consumer) :
    causalRank candidate records replacement producer <
      causalRank candidate records replacement consumer := by
  rcases finSum_decompose consumer with ⟨outside, rfl⟩ | ⟨inside, rfl⟩
  · have consumerRank : causalRank candidate records replacement
        (Fin.castAdd replacementGates outside) =
          (((exterior records).get outside).val + 1) * (replacementGates + 1) := by
      unfold causalRank
      rw [splitFin_left]
    rw [consumerRank]
    dsimp only [RawNandGraph.Depends, graph] at edge
    simp only [splitFin_left] at edge
    rcases edge with leftAt | rightAt
    · exact originalSource_causal_rank_lt candidate records replacement interfaceBound _ _
        ((exterior records).get outside)
        (fun prior atSource => sources_ordered candidate.program _ prior (Or.inl atSource))
        producer leftAt
    · exact originalSource_causal_rank_lt candidate records replacement interfaceBound _ _
        ((exterior records).get outside)
        (fun prior atSource => sources_ordered candidate.program _ prior (Or.inr atSource))
        producer rightAt
  · have consumerRank : causalRank candidate records replacement
        (Fin.natAdd (exterior records).length inside) =
          CausalBound.levels replacement.program (causalBoundaryLabels candidate records) inside *
            (replacementGates + 1) + (inside.val + 1) := by
      unfold causalRank
      rw [splitFin_right]
    rw [consumerRank]
    dsimp only [RawNandGraph.Depends, graph] at edge
    simp only [splitFin_right] at edge
    have levels := CausalBound.terminal_sources_level replacement.program
      (causalBoundaryLabels candidate records) inside
    rcases edge with leftAt | rightAt
    · apply replacementSource_causal_rank_lt candidate records replacement _ inside ?_
        (fun prior atSource => sources_ordered replacement.program inside prior
          (Or.inl atSource)) producer leftAt
      omega
    · apply replacementSource_causal_rank_lt candidate records replacement _ inside ?_
        (fun prior atSource => sources_ordered replacement.program inside prior
          (Or.inr atSource)) producer rightAt
      omega

theorem graph_wellFounded_of_causalInterfaceBound
    (interfaceBound : CausalInterfaceBound candidate records replacement) :
    WellFounded (graph candidate records replacement).Depends :=
  ⟨fun node => rank_accessible _ (causalRank candidate records replacement)
    (graph_causal_rank_decreases candidate records replacement interfaceBound) node⟩

/-- The existing compiler computes an order whenever actual causal bounds hold.
The history construction derives these bounds rather than requesting a certificate. -/
theorem compile_of_causalInterfaceBound
    (interfaceBound : CausalInterfaceBound candidate records replacement) :
    ∃ compiled, compile candidate records replacement = some compiled :=
  (compile_success_iff candidate records replacement).2
    (graph_wellFounded_of_causalInterfaceBound candidate records replacement interfaceBound)

variable (labels : Fin inputs → Nat)

/-- Labels of the actual original wires entering the selected support. -/
def dependencyBoundaryLabels :
    Fin (terminalBoundaryPorts candidate.program records).length → Nat :=
  terminalBoundaryCausalLabels candidate records labels
    (CausalBound.levels candidate.program labels)

/-- Actual source-program levels for the exterior and replacement nodes. -/
def dependencyCaps : Fin ((exterior records).length + replacementGates) → Nat :=
  splitFin
    (fun index => CausalBound.levels candidate.program labels ((exterior records).get index))
    (CausalBound.levels replacement.program (dependencyBoundaryLabels candidate records labels))

/-- An intermediate proof predicate, derived by the concrete R7 constructor. -/
def DependencyInterfaceBound : Prop :=
  ∀ port, CausalBound.outputLevel replacement (dependencyBoundaryLabels candidate records labels)
      port ≤ CausalBound.levels candidate.program labels
        ((terminalInterfacePorts candidate records).get port)

private theorem dependencyCaps_left (index : Fin (exterior records).length) :
    dependencyCaps candidate records replacement labels (Fin.castAdd replacementGates index) =
      CausalBound.levels candidate.program labels ((exterior records).get index) := by
  unfold dependencyCaps
  rw [splitFin_left]

private theorem dependencyCaps_right (index : Fin replacementGates) :
    dependencyCaps candidate records replacement labels
        (Fin.natAdd (exterior records).length index) =
      CausalBound.levels replacement.program
        (dependencyBoundaryLabels candidate records labels) index := by
  unfold dependencyCaps
  rw [splitFin_right]

private theorem boundarySource_dependency_level
    (port : Fin (terminalBoundaryPorts candidate.program records).length) :
    CausalBound.source
        (boundarySource (replacementGates := replacementGates) candidate records port)
        labels (dependencyCaps candidate records replacement labels) =
      dependencyBoundaryLabels candidate records labels port := by
  unfold boundarySource
  split
  · rename_i index found
    change labels index = _
    unfold dependencyBoundaryLabels terminalBoundaryCausalLabels
    rw [found]
    rfl
  · rename_i gate found
    dsimp only [CausalBound.source]
    rw [dependencyCaps_left, get_memberIndex]
    unfold dependencyBoundaryLabels terminalBoundaryCausalLabels
    rw [found]
    rfl

private theorem replacementSource_dependency_level
    (source : Source (terminalBoundaryPorts candidate.program records).length replacementGates) :
    CausalBound.source (replacementSource candidate records source) labels
        (dependencyCaps candidate records replacement labels) =
      CausalBound.source source (dependencyBoundaryLabels candidate records labels)
        (CausalBound.levels replacement.program (dependencyBoundaryLabels candidate records labels)) := by
  cases source with
  | input port => exact boundarySource_dependency_level candidate records replacement labels port
  | constant value => rfl
  | gate index => exact dependencyCaps_right candidate records replacement labels index

private theorem originalSource_dependency_bound
    (interfaceBound : DependencyInterfaceBound candidate records replacement labels)
    (source : Source inputs gates) (visible : Visible candidate records source) :
    CausalBound.source (originalSource candidate records replacement source visible) labels
        (dependencyCaps candidate records replacement labels) ≤
      CausalBound.source source labels (CausalBound.levels candidate.program labels) := by
  cases source with
  | input index => exact Nat.le_refl _
  | constant value => exact Nat.le_refl _
  | gate gate =>
      simp only [originalSource]
      split
      · rename_i selected
        rw [replacementSource_dependency_level]
        have bounded := interfaceBound (memberIndex (visible gate rfl selected))
        rw [get_memberIndex] at bounded
        exact bounded
      · dsimp only [CausalBound.source]
        rw [dependencyCaps_left, get_memberIndex]
        exact Nat.le_refl _

/-- Every actual splice gate respects the source-derived dependency caps. -/
theorem graph_dependency_bounds
    (interfaceBound : DependencyInterfaceBound candidate records replacement labels) :
    RawNandCausalBound.GraphBounds (graph candidate records replacement) labels
      (dependencyCaps candidate records replacement labels) := by
  intro node
  rcases finSum_decompose node with ⟨outside, rfl⟩ | ⟨inside, rfl⟩
  · dsimp only [graph]
    rw [splitFin_left, dependencyCaps_left]
    unfold exteriorGate
    dsimp only
    let original := (exterior records).get outside
    let pair := candidate.program.terminalGateSources original
    have leftBound := originalSource_dependency_bound candidate records replacement labels
      interfaceBound pair.1 (exteriorSource_visible candidate records original
        (exteriorGet_unselected records outside) pair.1 (Or.inl rfl))
    have rightBound := originalSource_dependency_bound candidate records replacement labels
      interfaceBound pair.2 (exteriorSource_visible candidate records original
        (exteriorGet_unselected records outside) pair.2 (Or.inr rfl))
    have exactLevel := CausalBound.terminal_sources_level candidate.program labels original
    change max (CausalBound.source (originalSource candidate records replacement pair.1 _) labels
      (dependencyCaps candidate records replacement labels))
      (CausalBound.source (originalSource candidate records replacement pair.2 _) labels
        (dependencyCaps candidate records replacement labels)) ≤
      CausalBound.levels candidate.program labels original
    dsimp only [pair] at leftBound rightBound ⊢
    omega
  · dsimp only [graph]
    rw [splitFin_right, dependencyCaps_right]
    unfold replacementGate
    dsimp only
    rw [replacementSource_dependency_level, replacementSource_dependency_level,
      CausalBound.terminal_sources_level]
    exact Nat.le_refl _

/-- Bounds follow the actual accepted compiler result, not Boolean equivalence. -/
theorem result_output_dependency_bound
    (interfaceBound : DependencyInterfaceBound candidate records replacement labels)
    (compiled : CompiledRawNandGraph (graph candidate records replacement))
    (accepted : compile candidate records replacement = some compiled)
    (output : Fin outputs) :
    CausalBound.outputLevel (result candidate records replacement compiled) labels output ≤
      CausalBound.outputLevel candidate labels output :=
  Nat.le_trans
    (RawNandCausalBound.candidate_bound (graph candidate records replacement) compiled accepted
      labels (dependencyCaps candidate records replacement labels)
      (graph_dependency_bounds candidate records replacement labels interfaceBound)
      (word candidate records replacement) output)
    (originalSource_dependency_bound candidate records replacement labels interfaceBound
      (candidate.directWireWord.source output) (output_visible candidate records output))

end ArbitrarySupportSplice
end DirectWire
end PNP
