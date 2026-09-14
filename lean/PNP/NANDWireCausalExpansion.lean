/-
Copyright (c) 2026 PNP Labs.

Source-ordered physical expansion of an arbitrary computational support.
Every copied NAND gate is owned by an exact retained-producer/local-gate pair.
This is not complete Package E, unrestricted saving transport, or a runtime bound.
-/

import PNP.NANDWireCarrier
import PNP.NANDWireObligationRestoration

namespace PNP
namespace DirectWire
namespace WireCausalExpansion

private def copyNode {owners width : Nat} (owner : Fin owners) (gate : Fin width) :
    Fin (owners * width) :=
  ⟨owner.val * width + gate.val, by
    have upper := Nat.mul_le_mul_right width (Nat.succ_le_of_lt owner.isLt)
    rw [Nat.succ_mul] at upper
    have localBound := gate.isLt
    omega⟩

private theorem copyWidth_pos {owners width : Nat} (node : Fin (owners * width)) :
    0 < width := by
  apply Nat.pos_of_ne_zero
  intro absent
  have sizeZero : owners * width = 0 := by rw [absent, Nat.mul_zero]
  exact Nat.not_lt_zero node.val
    (Nat.lt_of_lt_of_le node.isLt (Nat.le_of_eq sizeZero))

private def copyOwner {owners width : Nat} (node : Fin (owners * width)) : Fin owners :=
  ⟨node.val / width, (Nat.div_lt_iff_lt_mul (copyWidth_pos node)).2 node.isLt⟩

private def copyGate {owners width : Nat} (node : Fin (owners * width)) : Fin width :=
  ⟨node.val % width, Nat.mod_lt node.val (copyWidth_pos node)⟩

private theorem copyOwner_copyNode {owners width : Nat}
    (owner : Fin owners) (gate : Fin width) :
    copyOwner (copyNode owner gate) = owner := by
  apply Fin.ext
  change (owner.val * width + gate.val) / width = owner.val
  apply Nat.div_eq_of_lt_le
  · exact Nat.le_add_right _ _
  · rw [Nat.succ_mul]
    exact Nat.add_lt_add_left gate.isLt _

private theorem copyGate_copyNode {owners width : Nat}
    (owner : Fin owners) (gate : Fin width) :
    copyGate (copyNode owner gate) = gate := by
  apply Fin.ext
  exact Nat.mul_add_mod_of_lt gate.isLt

private theorem copyNode_decompose {owners width : Nat}
    (node : Fin (owners * width)) :
    copyNode (copyOwner node) (copyGate node) = node := by
  apply Fin.ext
  change (node.val / width) * width + node.val % width = node.val
  rw [Nat.mul_comm, Nat.add_comm, Nat.mod_add_div]

private theorem copyNode_injective {owners width : Nat}
    (leftOwner rightOwner : Fin owners) (leftGate rightGate : Fin width)
    (same : copyNode leftOwner leftGate = copyNode rightOwner rightGate) :
    leftOwner = rightOwner ∧ leftGate = rightGate := by
  constructor
  · have ownersEqual := congrArg (copyOwner (owners := owners) (width := width)) same
    simpa only [copyOwner_copyNode] using ownersEqual
  · have gatesEqual := congrArg (copyGate (owners := owners) (width := width)) same
    simpa only [copyGate_copyNode] using gatesEqual

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
    {item : alpha} {items : List alpha} (member : item ∈ items) : Fin items.length :=
  (locate item items member).1

private theorem get_memberIndex {alpha : Type} [DecidableEq alpha]
    {item : alpha} {items : List alpha} (member : item ∈ items) :
    items.get (memberIndex member) = item := (locate item items member).2

variable {inputs gates outputs profileWidth replacementGates : Nat}
variable (candidate : Candidate inputs gates outputs)
variable (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))

/-- Every exterior gate is retained once, with one whole copy per interface producer. -/
def nodeCount (replacementGates : Nat) : Nat :=
  (ArbitrarySupportSplice.exterior records).length +
    (terminalInterfacePorts candidate records).length * replacementGates

private theorem exteriorGet_unselected
    (index : Fin (ArbitrarySupportSplice.exterior records).length) :
    terminalGateSelected records
      ((ArbitrarySupportSplice.exterior records).get index) = false :=
  (ArbitrarySupportSplice.mem_exterior_iff records _).1 (List.get_mem _ _)

private theorem boundaryGate_unselected (gate : Fin gates)
    (member : TerminalSupportWire.gate gate ∈
      terminalBoundaryPorts candidate.program records) :
    terminalGateSelected records gate = false :=
  (terminalWireExternal_eq_true_iff records (.gate gate)).1
    ((terminalBoundaryWire_eq_true_iff candidate.program records (.gate gate)).1
      ((mem_terminalBoundaryPorts_iff candidate.program records (.gate gate)).1 member)).1

private theorem interfaceGet_selected
    (owner : Fin (terminalInterfacePorts candidate records).length) :
    terminalGateSelected records ((terminalInterfacePorts candidate records).get owner) = true :=
  ((terminalInterfaceGate_eq_true_iff candidate records _).1
    ((mem_terminalInterfacePorts_iff candidate records _).1 (List.get_mem _ _))).1

/-- Only gate-valued boundary ports strictly before this copy's anchor are connected.
Later boundary gates are deliberately masked, never treated as unresolved names. -/
def boundarySource
    (owner : Fin (terminalInterfacePorts candidate records).length)
    (port : Fin (terminalBoundaryPorts candidate.program records).length) :
    Source inputs (nodeCount candidate records replacementGates) :=
  match found : (terminalBoundaryPorts candidate.program records).get port with
  | .input index => .input index
  | .gate gate =>
      if gate.val < ((terminalInterfacePorts candidate records).get owner).val then
        .gate (Fin.castAdd
          ((terminalInterfacePorts candidate records).length * replacementGates)
          (memberIndex ((ArbitrarySupportSplice.mem_exterior_iff records gate).2
            (boundaryGate_unselected candidate records gate
              (by rw [← found]; exact List.get_mem _ _)))))
      else .constant false

/-- Every internal reference remains in the same physically owned replacement copy. -/
def replacementSource
    (owner : Fin (terminalInterfacePorts candidate records).length) :
    Source (terminalBoundaryPorts candidate.program records).length replacementGates →
      Source inputs (nodeCount candidate records replacementGates)
  | .input port => boundarySource candidate records owner port
  | .constant value => .constant value
  | .gate index =>
      .gate (Fin.natAdd (ArbitrarySupportSplice.exterior records).length
        (copyNode owner index))

variable (replacement : Candidate
  (terminalBoundaryPorts candidate.program records).length replacementGates
  (terminalInterfacePorts candidate records).length)

/-- Reconnect a retained selected producer through its own copy's exact output. -/
def originalSource : (source : Source inputs gates) →
    ArbitrarySupportSplice.Visible candidate records source →
      Source inputs (nodeCount candidate records replacementGates)
  | .input index, _visible => .input index
  | .constant value, _visible => .constant value
  | .gate gate, visible =>
      if selected : terminalGateSelected records gate = true then
        let owner := memberIndex (visible gate rfl selected)
        replacementSource candidate records owner (replacement.directWireWord.source owner)
      else
        .gate (Fin.castAdd
          ((terminalInterfacePorts candidate records).length * replacementGates)
          (memberIndex ((ArbitrarySupportSplice.mem_exterior_iff records gate).2 (by
            cases value : terminalGateSelected records gate with
            | false => rfl
            | true => exact False.elim (selected value)))))

/-- Actual original exterior gates, with every source resolved from the support. -/
def exteriorGate (index : Fin (ArbitrarySupportSplice.exterior records).length) :
    Gate inputs (nodeCount candidate records replacementGates) :=
  let original := (ArbitrarySupportSplice.exterior records).get index
  let pair := candidate.program.terminalGateSources original
  ⟨originalSource candidate records replacement pair.1
      (ArbitrarySupportSplice.exteriorSource_visible candidate records original
        (exteriorGet_unselected records index) pair.1 (Or.inl rfl)),
    originalSource candidate records replacement pair.2
      (ArbitrarySupportSplice.exteriorSource_visible candidate records original
        (exteriorGet_unselected records index) pair.2 (Or.inr rfl))⟩

/-- A physical gate belongs to one exact retained producer and local gate index. -/
def replacementGate
    (owner : Fin (terminalInterfacePorts candidate records).length)
    (index : Fin replacementGates) :
    Gate inputs (nodeCount candidate records replacementGates) :=
  let pair := replacement.program.terminalGateSources index
  ⟨replacementSource candidate records owner pair.1,
    replacementSource candidate records owner pair.2⟩

/-- The fully resolved source-ordered graph. No external rank or order is supplied. -/
def graph : RawNandGraph inputs (nodeCount candidate records replacementGates) :=
  ⟨splitFin (exteriorGate candidate records replacement)
    (fun node => replacementGate candidate records replacement
      (copyOwner node) (copyGate node))⟩

/-- Preserve the original ordered observation tuple, including repeated sources. -/
def word : DirectWireWord inputs (nodeCount candidate records replacementGates) outputs :=
  ⟨fun output => originalSource candidate records replacement
    (candidate.directWireWord.source output)
    (ArbitrarySupportSplice.output_visible candidate records output)⟩

/-- The original producer's block and the copied gate's own position determine rank. -/
def rank (node : Fin (nodeCount candidate records replacementGates)) : Nat :=
  splitFin
    (fun outside => (replacementGates + 1) *
      ((ArbitrarySupportSplice.exterior records).get outside).val + replacementGates)
    (fun copied => (replacementGates + 1) *
      ((terminalInterfacePorts candidate records).get
        (copyOwner (width := replacementGates) copied)).val +
      (copyGate (owners := (terminalInterfacePorts candidate records).length)
        (width := replacementGates) copied).val) node

private theorem block_lt (width earlier later : Nat) (before : earlier < later) :
    (width + 1) * earlier + width < (width + 1) * later := by
  have scaled := Nat.mul_le_mul_left (width + 1) (Nat.succ_le_of_lt before)
  rw [Nat.mul_succ] at scaled
  omega

private theorem boundarySource_rank_lt
    (owner : Fin (terminalInterfacePorts candidate records).length)
    (port : Fin (terminalBoundaryPorts candidate.program records).length)
    (node : Fin (nodeCount candidate records replacementGates))
    (same : boundarySource candidate records owner port = .gate node) :
    rank candidate records node <
      (replacementGates + 1) * ((terminalInterfacePorts candidate records).get owner).val := by
  unfold boundarySource at same
  split at same
  · cases same
  · rename_i gate found
    split at same
    · rename_i before
      have mapped := Source.gate.inj same
      rw [← mapped, rank, splitFin_left, get_memberIndex]
      exact block_lt replacementGates gate.val
        ((terminalInterfacePorts candidate records).get owner).val before
    · cases same

private theorem replacementSource_rank_lt
    (owner : Fin (terminalInterfacePorts candidate records).length)
    (source : Source (terminalBoundaryPorts candidate.program records).length replacementGates)
    (limit : Nat)
    (bounded : ∀ index, source = .gate index → index.val < limit)
    (node : Fin (nodeCount candidate records replacementGates))
    (same : replacementSource candidate records owner source = .gate node) :
    rank candidate records node <
      (replacementGates + 1) * ((terminalInterfacePorts candidate records).get owner).val + limit := by
  cases source with
  | input port =>
      exact Nat.lt_of_lt_of_le
        (boundarySource_rank_lt candidate records owner port node same)
        (Nat.le_add_right _ _)
  | constant value => cases same
  | gate index =>
      have mapped : Fin.natAdd (ArbitrarySupportSplice.exterior records).length
          (copyNode owner index) = node := Source.gate.inj same
      rw [← mapped, rank, splitFin_right, copyOwner_copyNode, copyGate_copyNode]
      exact Nat.add_lt_add_left (bounded index rfl) _

private theorem originalSource_rank_lt
    (source : Source inputs gates)
    (visible : ArbitrarySupportSplice.Visible candidate records source)
    (consumer : Fin gates)
    (bounded : ∀ producer, source = .gate producer → producer.val < consumer.val)
    (node : Fin (nodeCount candidate records replacementGates))
    (same : originalSource candidate records replacement source visible = .gate node) :
    rank candidate records node < (replacementGates + 1) * consumer.val + replacementGates := by
  cases source with
  | input index => cases same
  | constant value => cases same
  | gate producer =>
      simp only [originalSource] at same
      split at same
      · rename_i selected
        have lower := replacementSource_rank_lt candidate records
          (memberIndex (visible producer rfl selected))
          (replacement.directWireWord.source (memberIndex (visible producer rfl selected)))
          replacementGates (fun index _atSource => index.isLt) node same
        rw [get_memberIndex] at lower
        have before := block_lt replacementGates producer.val consumer.val (bounded producer rfl)
        omega
      · have mapped := Source.gate.inj same
        rw [← mapped, rank, splitFin_left, get_memberIndex]
        exact Nat.lt_of_lt_of_le
          (block_lt replacementGates producer.val consumer.val (bounded producer rfl))
          (Nat.le_add_right _ _)

/-- Every actual producer precedes its consumer in the source-derived rank. -/
theorem graph_rank_decreases
    (producer consumer : Fin (nodeCount candidate records replacementGates))
    (edge : (graph candidate records replacement).Depends producer consumer) :
    rank candidate records producer < rank candidate records consumer := by
  rcases finSum_decompose consumer with ⟨outside, rfl⟩ | ⟨inside, rfl⟩
  · have consumerRank : rank (replacementGates := replacementGates) candidate records
        (Fin.castAdd ((terminalInterfacePorts candidate records).length * replacementGates)
          outside) =
        (replacementGates + 1) *
          ((ArbitrarySupportSplice.exterior records).get outside).val + replacementGates := by
      unfold rank
      rw [splitFin_left]
    rw [consumerRank]
    dsimp only [RawNandGraph.Depends, graph] at edge
    simp only [splitFin_left] at edge
    rcases edge with leftAt | rightAt
    · exact originalSource_rank_lt candidate records replacement _ _
        ((ArbitrarySupportSplice.exterior records).get outside)
        (fun prior atSource => ArbitrarySupportSplice.sources_ordered
          candidate.program _ prior (Or.inl atSource)) producer leftAt
    · exact originalSource_rank_lt candidate records replacement _ _
        ((ArbitrarySupportSplice.exterior records).get outside)
        (fun prior atSource => ArbitrarySupportSplice.sources_ordered
          candidate.program _ prior (Or.inr atSource)) producer rightAt
  · let owner := copyOwner
      (owners := (terminalInterfacePorts candidate records).length)
      (width := replacementGates) inside
    let localGate := copyGate
      (owners := (terminalInterfacePorts candidate records).length)
      (width := replacementGates) inside
    have consumerRank : rank candidate records
        (Fin.natAdd (ArbitrarySupportSplice.exterior records).length inside) =
        (replacementGates + 1) * ((terminalInterfacePorts candidate records).get owner).val +
          localGate.val := by
      unfold rank
      rw [splitFin_right]
    rw [consumerRank]
    dsimp only [RawNandGraph.Depends, graph] at edge
    simp only [splitFin_right] at edge
    rcases edge with leftAt | rightAt
    · exact replacementSource_rank_lt candidate records owner _ localGate.val
        (fun prior atSource => ArbitrarySupportSplice.sources_ordered
          replacement.program localGate prior (Or.inl atSource)) producer leftAt
    · exact replacementSource_rank_lt candidate records owner _ localGate.val
        (fun prior atSource => ArbitrarySupportSplice.sources_ordered
          replacement.program localGate prior (Or.inr atSource)) producer rightAt

private theorem rank_accessible {nodes : Nat} (relation : Fin nodes → Fin nodes → Prop)
    (nodeRank : Fin nodes → Nat)
    (decreases : ∀ producer consumer, relation producer consumer →
      nodeRank producer < nodeRank consumer) (node : Fin nodes) :
    Acc relation node :=
  Acc.intro node (fun producer _edge => rank_accessible relation nodeRank decreases producer)
termination_by nodeRank node
decreasing_by exact decreases _ _ _edge

/-- Acyclicity follows from actual sources at arbitrary support and replacement widths. -/
theorem graph_wellFounded : WellFounded (graph candidate records replacement).Depends :=
  ⟨fun node => rank_accessible _ (rank candidate records)
    (graph_rank_decreases candidate records replacement) node⟩

/-- Use the existing executable raw-graph compiler, not a supplied schedule. -/
def compile : Option (CompiledRawNandGraph (graph candidate records replacement)) :=
  compileRawNandGraph (graph candidate records replacement)

theorem compile_success :
    ∃ built, compile candidate records replacement = some built :=
  (compileRawNandGraph_success_iff (graph candidate records replacement)).2
    (graph_wellFounded candidate records replacement)

/-- Obtain the actual computed result; the rejected branch is formally impossible. -/
def compiled : CompiledRawNandGraph (graph candidate records replacement) :=
  match found : compile candidate records replacement with
  | some built => built
  | none => False.elim
      (((compileRawNandGraph_failure_iff (graph candidate records replacement)).1 found)
        (graph_wellFounded candidate records replacement))

theorem compiled_spec :
    compile candidate records replacement = some (compiled candidate records replacement) := by
  unfold compiled
  split
  · assumption
  · rename_i missing
    exact False.elim
      (((compileRawNandGraph_failure_iff (graph candidate records replacement)).1 missing)
        (graph_wellFounded candidate records replacement))

/-- The complete ordered original word, rebound through the actual compiled positions. -/
def expanded : Implementation inputs outputs :=
  ((compiled candidate records replacement).candidate
    (word candidate records replacement)).toImplementation

/-- Every physical exterior and copy gate is included in the actual executable result. -/
theorem expanded_gateCount :
    (expanded candidate records replacement).gateCount =
      nodeCount candidate records replacementGates :=
  (compiled candidate records replacement).candidate_gateCount
    (word candidate records replacement)

/-- Mask only later gate-valued boundary ports for one retained producer.
Primary inputs and all earlier boundary values remain unchanged. -/
def maskedBoundary
    (owner : Fin (terminalInterfacePorts candidate records).length)
    (valuation : Valuation (terminalBoundaryPorts candidate.program records).length) :
    Valuation (terminalBoundaryPorts candidate.program records).length :=
  fun port =>
    match (terminalBoundaryPorts candidate.program records).get port with
    | .input _ => valuation port
    | .gate gate =>
        if gate.val < ((terminalInterfacePorts candidate records).get owner).val
        then valuation port else false

private theorem maskedBoundary_agreement
    (owner : Fin (terminalInterfacePorts candidate records).length)
    (valuation : Valuation (terminalBoundaryPorts candidate.program records).length)
    (port : Fin (terminalBoundaryPorts candidate.program records).length)
    (before : (match (terminalBoundaryPorts candidate.program records).get port with
      | .input _ => True
      | .gate gate =>
          gate.val < ((terminalInterfacePorts candidate records).get owner).val + 1)) :
    maskedBoundary candidate records owner valuation port = valuation port := by
  unfold maskedBoundary
  split
  · rfl
  · rename_i gate found
    rw [found] at before
    have distinct : gate ≠ (terminalInterfacePorts candidate records).get owner := by
      intro sameGate
      have outside := boundaryGate_unselected candidate records gate
        (by rw [← found]; exact List.get_mem _ _)
      rw [sameGate, interfaceGet_selected candidate records owner] at outside
      cases outside
    have valuesDistinct : gate.val ≠
        ((terminalInterfacePorts candidate records).get owner).val :=
      fun equal => distinct (Fin.ext equal)
    have strictlyBefore : gate.val <
        ((terminalInterfacePorts candidate records).get owner).val := by omega
    rw [if_pos strictlyBefore]

/-- The chosen output is preserved for every open boundary assignment, not only
whole-circuit-induced assignments. Complete local open agreement is required. -/
theorem masked_replacement_output
    (equivalent : replacement.semantics =
      (extractTerminalSupport candidate records).extractedCandidate.semantics)
    (owner : Fin (terminalInterfacePorts candidate records).length)
    (valuation : Valuation (terminalBoundaryPorts candidate.program records).length) :
    replacement.semantics (maskedBoundary candidate records owner valuation) owner =
      (extractTerminalSupport candidate records).extractedCandidate.semantics valuation owner := by
  rw [equivalent]
  simp only [extractTerminalSupport_semantics, terminalOpenSupportSemantics]
  exact terminalOpenGateEvaluation_prefix_congr candidate records
    (maskedBoundary candidate records owner valuation) valuation
    (((terminalInterfacePorts candidate records).get owner).val + 1)
    (fun port before => maskedBoundary_agreement candidate records owner valuation port before)
    ((terminalInterfacePorts candidate records).get owner) (Nat.lt_succ_self _)

/-- A complete simultaneous valuation derived from the two actual executions. -/
def values (input : Valuation inputs) :
    Valuation (nodeCount candidate records replacementGates) :=
  splitFin
    (fun outside => candidate.program.eval input
      ((ArbitrarySupportSplice.exterior records).get outside))
    (fun copied => replacement.program.eval
      (maskedBoundary candidate records (copyOwner (width := replacementGates) copied)
        (terminalInducedBoundaryValuation candidate records input))
      (copyGate copied))

private theorem boundarySource_eval
    (owner : Fin (terminalInterfacePorts candidate records).length)
    (port : Fin (terminalBoundaryPorts candidate.program records).length)
    (input : Valuation inputs) :
    (boundarySource candidate records owner port).eval input
      (values candidate records replacement input) =
      maskedBoundary candidate records owner
        (terminalInducedBoundaryValuation candidate records input) port := by
  unfold boundarySource
  split
  · rename_i index found
    change input index = _
    unfold maskedBoundary terminalInducedBoundaryValuation
    rw [found]
    rfl
  · rename_i gate found
    split
    · rename_i before
      dsimp only [Source.eval, values]
      rw [splitFin_left, get_memberIndex]
      unfold maskedBoundary terminalInducedBoundaryValuation
      rw [found]
      dsimp only
      rw [if_pos before]
      rfl
    · rename_i notBefore
      change false = _
      unfold maskedBoundary
      rw [found]
      dsimp only
      rw [if_neg notBefore]

theorem replacementSource_eval
    (owner : Fin (terminalInterfacePorts candidate records).length)
    (source : Source (terminalBoundaryPorts candidate.program records).length replacementGates)
    (input : Valuation inputs) :
    (replacementSource candidate records owner source).eval input
      (values candidate records replacement input) =
      source.eval (maskedBoundary candidate records owner
        (terminalInducedBoundaryValuation candidate records input))
        (replacement.program.eval (maskedBoundary candidate records owner
          (terminalInducedBoundaryValuation candidate records input))) := by
  cases source with
  | input port => exact boundarySource_eval candidate records replacement owner port input
  | constant value => rfl
  | gate index =>
      change values candidate records replacement input
        (Fin.natAdd (ArbitrarySupportSplice.exterior records).length (copyNode owner index)) =
        replacement.program.eval (maskedBoundary candidate records owner
          (terminalInducedBoundaryValuation candidate records input)) index
      unfold values
      rw [splitFin_right, copyOwner_copyNode, copyGate_copyNode]

theorem originalSource_eval
    (equivalent : replacement.semantics =
      (extractTerminalSupport candidate records).extractedCandidate.semantics)
    (source : Source inputs gates)
    (visible : ArbitrarySupportSplice.Visible candidate records source)
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
        let owner := memberIndex (visible gate rfl selected)
        change replacement.semantics
          (maskedBoundary candidate records owner
            (terminalInducedBoundaryValuation candidate records input)) owner =
          candidate.program.eval input gate
        rw [masked_replacement_output candidate records replacement equivalent,
          extractTerminalSupport_induced, get_memberIndex]
      · dsimp only [Source.eval, values]
        rw [splitFin_left, get_memberIndex]

/-- Every actual NAND equation holds for the derived valuation. -/
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
    change candidate.program.eval input ((ArbitrarySupportSplice.exterior records).get outside) =
      (exteriorGate candidate records replacement outside).eval input
        (values candidate records replacement input)
    unfold exteriorGate Gate.eval
    dsimp only
    rw [originalSource_eval candidate records replacement equivalent,
      originalSource_eval candidate records replacement equivalent]
    exact (ArbitrarySupportSplice.sources_eval candidate.program input
      ((ArbitrarySupportSplice.exterior records).get outside)).symm
  · dsimp only [values, graph]
    rw [splitFin_right, splitFin_right]
    let owner := copyOwner
      (owners := (terminalInterfacePorts candidate records).length)
      (width := replacementGates) inside
    let localGate := copyGate
      (owners := (terminalInterfacePorts candidate records).length)
      (width := replacementGates) inside
    change replacement.program.eval (maskedBoundary candidate records owner
      (terminalInducedBoundaryValuation candidate records input)) localGate =
      (replacementGate candidate records replacement owner localGate).eval input
        (values candidate records replacement input)
    unfold replacementGate Gate.eval
    dsimp only
    rw [replacementSource_eval, replacementSource_eval]
    exact (ArbitrarySupportSplice.sources_eval replacement.program
      (maskedBoundary candidate records owner
        (terminalInducedBoundaryValuation candidate records input)) localGate).symm

/-- Complete ordered output preservation follows from local agreement and actual
graph equations, with no supplied final semantic or compiler-success witness. -/
theorem expanded_semantics
    (equivalent : replacement.semantics =
      (extractTerminalSupport candidate records).extractedCandidate.semantics)
    (input : Valuation inputs) (output : Fin outputs) :
    (expanded candidate records replacement).candidate.semantics input output =
      candidate.semantics input output := by
  change ((compiled candidate records replacement).candidate
    (word candidate records replacement)).semantics input output = _
  rw [(compiled candidate records replacement).candidate_semantics _ input
    (values candidate records replacement input)
    (values_solution candidate records replacement equivalent input)]
  exact originalSource_eval candidate records replacement equivalent
    (candidate.directWireWord.source output)
    (ArbitrarySupportSplice.output_visible candidate records output) input

/-- The exact original-size comparison includes every physical replacement copy. -/
theorem expanded_smaller_iff :
    (expanded candidate records replacement).gateCount < gates ↔
      (terminalInterfacePorts candidate records).length * replacementGates <
        (extractTerminalSupport candidate records).gateCount := by
  rw [expanded_gateCount, nodeCount]
  have partition := ArbitrarySupportSplice.exterior_accounting candidate records
  constructor
  · intro smaller
    omega
  · intro smaller
    omega

/-- A single retained producer needs one copy, at arbitrary incoming boundary width. -/
theorem single_interface_smaller
    (single : (terminalInterfacePorts candidate records).length = 1)
    (smaller : replacementGates < (extractTerminalSupport candidate records).gateCount) :
    (expanded candidate records replacement).gateCount < gates := by
  apply (expanded_smaller_iff candidate records replacement).2
  simpa only [single, Nat.one_mul] using smaller



private theorem allFin_nodup (width : Nat) : (allFin width).Nodup := by
  induction width with
  | zero => exact List.nodup_nil
  | succ width ih =>
      rw [allFin, List.nodup_cons]
      constructor
      · intro member
        obtain ⟨index, _present, same⟩ := List.mem_map.mp member
        have impossible := congrArg Fin.val same
        change index.val + 1 = 0 at impossible
        omega
      · exact List.Pairwise.map Fin.succ
          (fun left right different same =>
            different (Fin.ext (Nat.succ.inj (congrArg Fin.val same)))) ih

/-- The computed interface enumerates physical producers once, not observations
or semantic equivalence classes of wires. -/
theorem interface_nodup : (terminalInterfacePorts candidate records).Nodup :=
  List.Pairwise.filter _ (allFin_nodup gates)

/-- Distinct interface indices name distinct original physical gate producers. -/
theorem interface_owner_injective
    (left right : Fin (terminalInterfacePorts candidate records).length)
    (same : (terminalInterfacePorts candidate records).get left =
      (terminalInterfacePorts candidate records).get right) : left = right :=
  Fin.ext ((List.getElem_inj (interface_nodup candidate records)).1 same)

/-- The actual compiled position of one retained exterior gate. -/
def exteriorPosition (outside : Fin (ArbitrarySupportSplice.exterior records).length) :
    Fin (expanded candidate records replacement).gateCount :=
  (compiled candidate records replacement).position
    (Fin.castAdd ((terminalInterfacePorts candidate records).length * replacementGates) outside)

/-- The actual compiled position of a retained-producer/local-gate pair. -/
def copyPosition (owner : Fin (terminalInterfacePorts candidate records).length)
    (gate : Fin replacementGates) :
    Fin (expanded candidate records replacement).gateCount :=
  (compiled candidate records replacement).position
    (Fin.natAdd (ArbitrarySupportSplice.exterior records).length (copyNode owner gate))

/-- Distinct exterior nodes remain distinct physical gates after compilation. -/
theorem exteriorPosition_injective
    (left right : Fin (ArbitrarySupportSplice.exterior records).length)
    (same : exteriorPosition candidate records replacement left =
      exteriorPosition candidate records replacement right) : left = right := by
  have raw := (compiled candidate records replacement).position_injective _ _ same
  have valuesEqual := congrArg Fin.val raw
  exact Fin.ext valuesEqual

/-- No physical copied gate is charged to two different owner/local-gate pairs. -/
theorem copyPosition_injective
    (leftOwner rightOwner : Fin (terminalInterfacePorts candidate records).length)
    (leftGate rightGate : Fin replacementGates)
    (same : copyPosition candidate records replacement leftOwner leftGate =
      copyPosition candidate records replacement rightOwner rightGate) :
    leftOwner = rightOwner ∧ leftGate = rightGate := by
  have raw := (compiled candidate records replacement).position_injective _ _ same
  have nodesEqual : copyNode leftOwner leftGate = copyNode rightOwner rightGate := by
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val raw)
  exact copyNode_injective leftOwner rightOwner leftGate rightGate nodesEqual

/-- Exterior ownership and copied-gate ownership never overlap. -/
theorem exteriorPosition_ne_copyPosition
    (outside : Fin (ArbitrarySupportSplice.exterior records).length)
    (owner : Fin (terminalInterfacePorts candidate records).length)
    (gate : Fin replacementGates) :
    exteriorPosition candidate records replacement outside ≠
      copyPosition candidate records replacement owner gate := by
  intro same
  have raw := (compiled candidate records replacement).position_injective _ _ same
  have valuesEqual := congrArg Fin.val raw
  change outside.val = (ArbitrarySupportSplice.exterior records).length +
    (copyNode owner gate).val at valuesEqual
  have outsideBound := outside.isLt
  omega

/-- Every raw node is one exterior or one owner/local-gate pair, including all
empty-dimension cases. Compilation preserves these distinct positions. -/
theorem raw_node_ownership
    (node : Fin (nodeCount candidate records replacementGates)) :
    (∃ outside, node =
      Fin.castAdd ((terminalInterfacePorts candidate records).length * replacementGates) outside) ∨
    (∃ owner gate, node =
      Fin.natAdd (ArbitrarySupportSplice.exterior records).length (copyNode owner gate)) := by
  rcases finSum_decompose node with ⟨outside, atOutside⟩ | ⟨copied, atCopy⟩
  · exact Or.inl ⟨outside, atOutside⟩
  · exact Or.inr ⟨copyOwner copied, copyGate copied,
      atCopy.trans (congrArg (Fin.natAdd (ArbitrarySupportSplice.exterior records).length)
        (copyNode_decompose copied).symm)⟩


private theorem finitePosition_surjective {nodes count : Nat}
    (position : Fin nodes → Fin count) (countExact : count = nodes)
    (positionInjective : Function.Injective position) (target : Fin count) :
    ∃ node, position node = target := by
  by_cases found : ∃ node, position node = target
  · exact found
  · let augmented : Fin (nodes + 1) → Fin count :=
      splitFin position (fun _ : Fin 1 => target)
    have injective : Function.Injective augmented := by
      intro left right same
      rcases finSum_decompose left with ⟨leftNode, rfl⟩ | ⟨leftExtra, rfl⟩
      · rcases finSum_decompose right with ⟨rightNode, rfl⟩ | ⟨rightExtra, rfl⟩
        · simp only [augmented, splitFin_left] at same
          exact congrArg (Fin.castAdd 1) (positionInjective same)
        · simp only [augmented, splitFin_left, splitFin_right] at same
          exact False.elim (found ⟨leftNode, same⟩)
      · rcases finSum_decompose right with ⟨rightNode, rfl⟩ | ⟨rightExtra, rfl⟩
        · simp only [augmented, splitFin_left, splitFin_right] at same
          exact False.elim (found ⟨rightNode, same.symm⟩)
        · have extraEqual : leftExtra = rightExtra := by
            apply Fin.ext
            have leftBound := leftExtra.isLt
            have rightBound := rightExtra.isLt
            omega
          exact congrArg (Fin.natAdd nodes) extraEqual
    have impossible := finCard_le_of_injective augmented injective
    omega

/-- Every actual emitted gate belongs to an exterior node or a concrete copy.
Together with disjointness and injectivity, this excludes omitted or free charges. -/
theorem expanded_gate_ownership
    (gate : Fin (expanded candidate records replacement).gateCount) :
    (∃ outside, gate = exteriorPosition candidate records replacement outside) ∨
    (∃ owner localGate, gate = copyPosition candidate records replacement owner localGate) := by
  obtain ⟨node, atNode⟩ := finitePosition_surjective
    (compiled candidate records replacement).position
    (compiled candidate records replacement).count_eq
    (compiled candidate records replacement).position_injective gate
  rcases raw_node_ownership candidate records node with
    ⟨outside, atOutside⟩ | ⟨owner, localGate, atCopy⟩
  · exact Or.inl ⟨outside, atNode.symm.trans
      (congrArg (compiled candidate records replacement).position atOutside)⟩
  · exact Or.inr ⟨owner, localGate, atNode.symm.trans
      (congrArg (compiled candidate records replacement).position atCopy)⟩

/-- The compiled output uses the exact source translation, not a value-only label. -/
theorem expanded_source (output : Fin outputs) :
    (expanded candidate records replacement).candidate.directWireWord.source output =
      (compiled candidate records replacement).translateSource
        ((word candidate records replacement).source output) := by
  unfold expanded CompiledRawNandGraph.candidate
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_pointwise]

/-- Repeated observations of the same physical source remain the same actual
compiled source. No extra copy is allocated for another reference. -/
theorem expanded_source_equal (left right : Fin outputs)
    (same : candidate.directWireWord.source left = candidate.directWireWord.source right) :
    (expanded candidate records replacement).candidate.directWireWord.source left =
      (expanded candidate records replacement).candidate.directWireWord.source right := by
  rw [expanded_source, expanded_source]
  apply congrArg (compiled candidate records replacement).translateSource
  change originalSource candidate records replacement _ _ =
    originalSource candidate records replacement _ _
  simp only [same]

section Carrier

variable {fields : Nat}
variable (carrier : WireCarrier inputs outputs fields)
variable (carrierRecords : List (TerminalPrimitiveRecord inputs
  carrier.exposed.gateCount (outputs + fields) profileWidth))
variable (carrierReplacement : Candidate
  (terminalBoundaryPorts carrier.exposed.candidate.program carrierRecords).length
  replacementGates
  (terminalInterfacePorts carrier.exposed.candidate carrierRecords).length)

/-- Expose every computational field before expansion, then recover the complete
ordered field word from the same actual compiled implementation. -/
def expandedCarrier : WireCarrier inputs outputs fields :=
  WireCarrier.unpack
    (expanded carrier.exposed.candidate carrierRecords carrierReplacement)

/-- Ordinary outputs follow from the complete exposed-word agreement. -/
theorem expandedCarrier_output
    (equivalent : carrierReplacement.semantics =
      (extractTerminalSupport carrier.exposed.candidate carrierRecords).extractedCandidate.semantics)
    (input : Valuation inputs) (output : Fin outputs) :
    (expandedCarrier carrier carrierRecords carrierReplacement).implementation.candidate.semantics
        input output =
      carrier.implementation.candidate.semantics input output :=
  (WireCarrier.unpack_output
    (expanded carrier.exposed.candidate carrierRecords carrierReplacement) input output).trans
      ((expanded_semantics carrier.exposed.candidate carrierRecords carrierReplacement equivalent
        input (Fin.castAdd fields output)).trans (carrier.exposed_output input output))

/-- All computational fields retain their full values, including fields hidden by
a later quotient. This requires full local agreement, never quotient-only equality. -/
theorem expandedCarrier_field
    (equivalent : carrierReplacement.semantics =
      (extractTerminalSupport carrier.exposed.candidate carrierRecords).extractedCandidate.semantics)
    (input : Valuation inputs) (field : Fin fields) :
    (expandedCarrier carrier carrierRecords carrierReplacement).fieldValue input field =
      carrier.fieldValue input field :=
  (WireCarrier.unpack_field
    (expanded carrier.exposed.candidate carrierRecords carrierReplacement) input field).trans
      ((expanded_semantics carrier.exposed.candidate carrierRecords carrierReplacement equivalent
        input (Fin.natAdd outputs field)).trans (carrier.exposed_field input field))

/-- Unpacking does not conceal physical copies: every copy is in the actual count. -/
theorem expandedCarrier_gateCount :
    (expandedCarrier carrier carrierRecords carrierReplacement).implementation.gateCount =
      (ArbitrarySupportSplice.exterior carrierRecords).length +
        (terminalInterfacePorts carrier.exposed.candidate carrierRecords).length *
          replacementGates :=
  expanded_gateCount carrier.exposed.candidate carrierRecords carrierReplacement

/-- Exact strict saving after charging one whole copy per retained producer. -/
theorem expandedCarrier_smaller_iff :
    (expandedCarrier carrier carrierRecords carrierReplacement).implementation.gateCount <
        carrier.implementation.gateCount ↔
      (terminalInterfacePorts carrier.exposed.candidate carrierRecords).length *
          replacementGates <
        (extractTerminalSupport carrier.exposed.candidate carrierRecords).gateCount :=
  expanded_smaller_iff carrier.exposed.candidate carrierRecords carrierReplacement

/-- Properness and paid saving are separate hypotheses. Neither is inferred from
the other's name or from a locally smaller replacement. -/
theorem expandedCarrier_proper_and_smaller
    (proper : (extractTerminalSupport carrier.exposed.candidate carrierRecords).gateCount <
      carrier.implementation.gateCount)
    (paidSaving : (terminalInterfacePorts carrier.exposed.candidate carrierRecords).length *
      replacementGates <
        (extractTerminalSupport carrier.exposed.candidate carrierRecords).gateCount) :
    (extractTerminalSupport carrier.exposed.candidate carrierRecords).gateCount <
        carrier.implementation.gateCount ∧
      (expandedCarrier carrier carrierRecords carrierReplacement).implementation.gateCount <
        carrier.implementation.gateCount :=
  ⟨proper, (expandedCarrier_smaller_iff carrier carrierRecords carrierReplacement).2 paidSaving⟩


/-- Field order and multiplicity are retained, while identical literal field
sources share their exact compiled wire rather than allocating per-field copies. -/
theorem expandedCarrier_source_equal (left right : Fin fields)
    (same : carrier.source left = carrier.source right) :
    (expandedCarrier carrier carrierRecords carrierReplacement).source left =
      (expandedCarrier carrier carrierRecords carrierReplacement).source right := by
  change (expanded carrier.exposed.candidate carrierRecords carrierReplacement).candidate.directWireWord.source
      (Fin.natAdd outputs left) =
    (expanded carrier.exposed.candidate carrierRecords carrierReplacement).candidate.directWireWord.source
      (Fin.natAdd outputs right)
  exact expanded_source_equal carrier.exposed.candidate carrierRecords carrierReplacement
    (Fin.natAdd outputs left) (Fin.natAdd outputs right)
    ((carrier.exposed_field_source left).trans
      (same.trans (carrier.exposed_field_source right).symm))


/-- Rebind an existing lost-field creation to the same actual expanded coordinate.
This transports a literal R5 binding; it is not a new global obligation calculus. -/
def expandedR5Creation (keep : Fin fields → Bool)
    (creation : WireObligationRestoration.R5Creation carrier keep) :
    WireObligationRestoration.R5Creation
      (expandedCarrier carrier carrierRecords carrierReplacement) keep :=
  WireObligationRestoration.createR5
    (expandedCarrier carrier carrierRecords carrierReplacement) keep
    creation.coordinate creation.forgotten

theorem expandedR5Creation_coordinate (keep : Fin fields → Bool)
    (creation : WireObligationRestoration.R5Creation carrier keep) :
    (expandedR5Creation carrier carrierRecords carrierReplacement keep creation).coordinate =
      creation.coordinate := rfl

/-- The rebound R5 field has its original full value on every input. No supplied
full-value witness, quotient equality, or completion of other R5-R8 events is used. -/
theorem expandedR5Creation_fullWitness
    (equivalent : carrierReplacement.semantics =
      (extractTerminalSupport carrier.exposed.candidate carrierRecords).extractedCandidate.semantics)
    (keep : Fin fields → Bool)
    (creation : WireObligationRestoration.R5Creation carrier keep)
    (input : Valuation inputs) :
    (expandedR5Creation carrier carrierRecords carrierReplacement keep creation).originalSource.eval
        input ((expandedCarrier carrier carrierRecords carrierReplacement).implementation.candidate.program.eval input) =
      creation.originalSource.eval input (carrier.implementation.candidate.program.eval input) := by
  change (expandedCarrier carrier carrierRecords carrierReplacement).fieldValue
      input creation.coordinate =
    creation.originalSource.eval input (carrier.implementation.candidate.program.eval input)
  rw [creation.sourceExact]
  exact expandedCarrier_field carrier carrierRecords carrierReplacement equivalent
    input creation.coordinate

end Carrier

end WireCausalExpansion
end DirectWire
end PNP
