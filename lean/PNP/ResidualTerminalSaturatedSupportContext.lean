/-
Copyright (c) 2026 PNP Labs.

Computed physical replacement contexts for production saturated supports.
The supplied profile observer and exhaustive reference minima are unchanged.
These physical laws do not assert full-profile compatibility or a global route.
-/

import PNP.ResidualTerminalPhysicalChargeLedger
import PNP.NANDSlack

namespace PNP
namespace DirectWire

private theorem candidateGateSourceRequires_eq_usesWire
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (consumer producer : Fin gates) :
    (terminalCandidateSaturationSystem candidate model).requires
        .gateSource (.gate consumer) (.gate producer) =
      candidate.program.terminalGateUsesWire consumer (.gate producer) := by
  let recordSource : Source inputs gates →
      Option (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
    fun source => match source with
      | .input index => some (.boundary index)
      | .constant _value => none
      | .gate index => some (.gate index)
  have sourceMatches (source : Source inputs gates) :
      decide (recordSource source = some (.gate producer)) =
        decide (source.terminalSupportWire? = some (.gate producer)) := by
    cases source <;>
      simp only [recordSource, Source.terminalSupportWire?, Option.some.injEq,
        TerminalPrimitiveRecord.gate.injEq, TerminalSupportWire.gate.injEq,
        reduceCtorEq]
  change
    ((decide (recordSource (candidate.program.terminalGateSources consumer).1 =
        some (.gate producer)) ||
      decide (recordSource (candidate.program.terminalGateSources consumer).2 =
        some (.gate producer))) || false) =
    (decide ((candidate.program.terminalGateSources consumer).1.terminalSupportWire? =
        some (.gate producer)) ||
      decide ((candidate.program.terminalGateSources consumer).2.terminalSupportWire? =
        some (.gate producer)))
  rw [Bool.or_false, sourceMatches, sourceMatches]

private theorem candidateSaturate_gateSource_closed
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (consumer producer : Fin gates)
    (selected : terminalGateSelected
      (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)
      consumer = true)
    (uses : candidate.program.terminalGateUsesWire consumer (.gate producer) = true) :
    terminalGateSelected
      (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)
      producer = true := by
  apply (terminalGateSelected_eq_true_iff _ _).2
  apply terminalSaturateRecords_closed
    (terminalCandidateSaturationSystem candidate model) seed
    .gateSource (.gate consumer) (.gate producer)
    ((terminalGateSelected_eq_true_iff _ _).1 selected)
  rw [candidateGateSourceRequires_eq_usesWire]
  exact uses

/-- Actual production saturation internalizes every physical predecessor gate.
    Consequently its extracted incoming boundary consists only of primary
    inputs; no fan-in-closure certificate is supplied by the caller. -/
theorem terminalCandidateSaturate_boundary_isInput
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (wire : TerminalSupportWire inputs gates)
    (member : wire ∈ (extractTerminalSupport candidate
      (terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed)).boundary) :
    ∃ input : Fin inputs, wire = TerminalSupportWire.input input := by
  cases wire with
  | input index => exact ⟨index, rfl⟩
  | gate producer =>
      let records := terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed
      change TerminalSupportWire.gate producer ∈
        terminalBoundaryPorts candidate.program records at member
      obtain ⟨external, consumer, _enumerated, selected, uses⟩ :=
        (terminalBoundaryWire_eq_true_iff candidate.program records
          (.gate producer)).1
            ((mem_terminalBoundaryPorts_iff candidate.program records
              (.gate producer)).1 member)
      have unselected : terminalGateSelected records producer = false :=
        (terminalWireExternal_eq_true_iff records (.gate producer)).1 external
      have internal := candidateSaturate_gateSource_closed
        candidate model seed consumer producer selected uses
      rw [unselected] at internal
      exact False.elim (Bool.noConfusion internal)

/-- Enumerate precisely the physical gates outside the selected support.
    No profile records or caller-supplied partition are introduced. -/
def terminalPhysicalComplementRecords
    {inputs gates outputs profileWidth : Nat}
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  (terminalSelectedGateIndices fun gate => !(terminalGateSelected records gate)).map
    TerminalPrimitiveRecord.gate

private theorem bool_eq_of_true_iff (left right : Bool)
    (same : left = true ↔ right = true) : left = right := by
  cases left <;> cases right
  · rfl
  · exact False.elim (Bool.noConfusion (same.2 rfl))
  · exact False.elim (Bool.noConfusion (same.1 rfl))
  · rfl

private theorem physicalComplement_selected
    {inputs gates outputs profileWidth : Nat}
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates) :
    terminalGateSelected (terminalPhysicalComplementRecords records) gate =
      !(terminalGateSelected records gate) := by
  apply bool_eq_of_true_iff
  apply (terminalGateSelected_eq_true_iff _ gate).trans
  constructor
  · intro member
    obtain ⟨found, selected, same⟩ := List.mem_map.mp member
    have equal : found = gate := TerminalPrimitiveRecord.gate.inj same
    subst found
    exact (mem_terminalSelectedGateIndices_iff _ gate).1 selected
  · intro selected
    exact List.mem_map.mpr ⟨gate,
      (mem_terminalSelectedGateIndices_iff _ gate).2 selected, rfl⟩

private theorem selectedGateCount_partition
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

private theorem physicalComplement_gateCount_partition
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (extractTerminalSupport candidate records).gateCount +
      (extractTerminalSupport candidate
        (terminalPhysicalComplementRecords records)).gateCount = gates := by
  rw [extractTerminalSupport_gateCount, extractTerminalSupport_gateCount]
  have selector : terminalGateSelected (terminalPhysicalComplementRecords records) =
      (fun gate => !(terminalGateSelected records gate)) :=
    funext (physicalComplement_selected records)
  unfold terminalSelectedGates
  rw [selector]
  exact selectedGateCount_partition (terminalGateSelected records)

/-- The canonical physical complement selects exactly the unselected gates. -/
theorem terminalPhysicalComplementRecords_selected
    {inputs gates outputs profileWidth : Nat}
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates) :
    terminalGateSelected (terminalPhysicalComplementRecords records) gate =
      !(terminalGateSelected records gate) :=
  physicalComplement_selected records gate

/-- An arbitrary physical support and its canonical complement partition the
    original gates exactly; saturation is not a premise. -/
theorem terminalPhysicalComplementRecords_gateCount_partition
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (extractTerminalSupport candidate records).gateCount +
      (extractTerminalSupport candidate
        (terminalPhysicalComplementRecords records)).gateCount = gates :=
  physicalComplement_gateCount_partition candidate records

private theorem complementBoundary_gate_in_supportInterface
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (producer : Fin gates)
    (member : TerminalSupportWire.gate producer ∈
      (extractTerminalSupport candidate
        (terminalPhysicalComplementRecords records)).boundary) :
    producer ∈ (extractTerminalSupport candidate records).interface := by
  let complement := terminalPhysicalComplementRecords records
  change TerminalSupportWire.gate producer ∈
    terminalBoundaryPorts candidate.program complement at member
  obtain ⟨external, consumer, enumerated, selected, uses⟩ :=
    (terminalBoundaryWire_eq_true_iff candidate.program complement
      (.gate producer)).1
        ((mem_terminalBoundaryPorts_iff candidate.program complement
          (.gate producer)).1 member)
  have complementFalse : terminalGateSelected complement producer = false :=
    (terminalWireExternal_eq_true_iff complement (.gate producer)).1 external
  have producerSelected : terminalGateSelected records producer = true := by
    have flipped := physicalComplement_selected records producer
    change terminalGateSelected complement producer = _ at flipped
    rw [complementFalse] at flipped
    cases original : terminalGateSelected records producer with
    | false => rw [original] at flipped; exact False.elim (Bool.noConfusion flipped)
    | true => rfl
  have consumerOutside : terminalGateSelected records consumer = false := by
    change terminalGateSelected (terminalPhysicalComplementRecords records)
      consumer = true at selected
    rw [physicalComplement_selected] at selected
    cases original : terminalGateSelected records consumer with
    | false => rfl
    | true => rw [original] at selected; exact False.elim (Bool.noConfusion selected)
  apply (mem_terminalInterfacePorts_iff candidate records producer).2
  apply (terminalInterfaceGate_eq_true_iff candidate records producer).2
  refine ⟨producerSelected, Or.inl ?_⟩
  exact (terminalGateHasExternalConsumer_eq_true_iff
    candidate.program records producer).2
      ⟨consumer, enumerated, consumerOutside, uses⟩

private def physicalLocateMember {alpha : Type} [DecidableEq alpha]
    (item : alpha) :
    (items : List alpha) → item ∈ items →
      {index : Fin items.length // items.get index = item}
  | [], member => False.elim (by cases member)
  | head :: tail, member =>
      if equal : item = head then
        ⟨⟨0, Nat.zero_lt_succ _⟩, equal.symm⟩
      else
        let tailMember := (List.mem_cons.mp member).resolve_left equal
        let located := physicalLocateMember item tail tailMember
        ⟨located.1.succ, located.2⟩

private def physicalMemberIndex {alpha : Type} [DecidableEq alpha]
    {item : alpha} {items : List alpha} (member : item ∈ items) :
    Fin items.length :=
  (physicalLocateMember item items member).1

private theorem physicalGet_memberIndex {alpha : Type} [DecidableEq alpha]
    {item : alpha} {items : List alpha} (member : item ∈ items) :
    items.get (physicalMemberIndex member) = item :=
  (physicalLocateMember item items member).2

private def physicalSupportEnvironment
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    Candidate inputs 0 ((extractTerminalSupport candidate records).boundary.length + inputs) :=
  let support := extractTerminalSupport candidate records
  Candidate.ofDirectWireWord .empty ⟨splitFin
    (fun index => match support.boundary.get index with
      | .input input => .input input
      | .gate _producer => .constant false)
    (fun input => .input input)⟩

private def physicalComplementInputBinding
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    Fin (extractTerminalSupport candidate
      (terminalPhysicalComplementRecords records)).boundary.length →
      Fin ((extractTerminalSupport candidate records).interface.length + inputs) :=
  let support := extractTerminalSupport candidate records
  let complement := extractTerminalSupport candidate (terminalPhysicalComplementRecords records)
  fun index => match equal : complement.boundary.get index with
    | .input input => Fin.natAdd support.interface.length input
    | .gate producer =>
        have boundaryMember : TerminalSupportWire.gate producer ∈ complement.boundary :=
          equal ▸ List.get_mem complement.boundary index
        Fin.castAdd inputs (physicalMemberIndex
          (complementBoundary_gate_in_supportInterface candidate records producer boundaryMember))

private def physicalSupportContinuation
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    Candidate ((extractTerminalSupport candidate records).interface.length + inputs)
      (extractTerminalSupport candidate
        (terminalPhysicalComplementRecords records)).gateCount outputs :=
  let support := extractTerminalSupport candidate records
  let complement := extractTerminalSupport candidate (terminalPhysicalComplementRecords records)
  let renamed := complement.extractedCandidate.renameInputs
    (physicalComplementInputBinding candidate records)
  Candidate.ofDirectWireWord renamed.program ⟨fun output =>
    match candidate.directWireWord.source output with
    | .input input => .input (Fin.natAdd support.interface.length input)
    | .constant value => .constant value
    | .gate producer =>
        if inSupport : producer ∈ support.interface then
          .input (Fin.castAdd inputs (physicalMemberIndex inSupport))
        else if inComplement : producer ∈ complement.interface then
          renamed.directWireWord.source (physicalMemberIndex inComplement)
        else
          .constant false⟩

/-- Compute the concrete physical replacement frame from production saturation.
    The unchanged extractor builds both gate halves; no frame, partition or
    reconstruction certificate is an input. -/
def terminalCandidateSaturatePhysicalContext
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    let records := terminalSaturateRecords
      (terminalCandidateSaturationSystem candidate model) seed
    let support := extractTerminalSupport candidate records
    let complement := extractTerminalSupport candidate (terminalPhysicalComplementRecords records)
    FramedContext inputs support.boundary.length support.interface.length
      inputs outputs 0 complement.gateCount :=
  let records := terminalSaturateRecords
    (terminalCandidateSaturationSystem candidate model) seed
  ⟨physicalSupportEnvironment candidate records, physicalSupportContinuation candidate records⟩

/-- Exact physical replacement accounting, without any semantic or
    smaller-replacement premise. Every original gate is counted once. -/
theorem terminalCandidateSaturatePhysicalContext_size
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    {replacementGates : Nat}
    (replacement : Candidate
      (extractTerminalSupport candidate (terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed)).boundary.length
      replacementGates
      (extractTerminalSupport candidate (terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed)).interface.length) :
    ((terminalCandidateSaturatePhysicalContext candidate model seed).plug
        replacement).program.size +
      (terminalSaturatePhysicalCharges
        (terminalCandidateSaturationSystem candidate model) seed).length =
      gates + replacementGates := by
  let records := terminalSaturateRecords
    (terminalCandidateSaturationSystem candidate model) seed
  have partition := physicalComplement_gateCount_partition candidate records
  have charges := terminalCandidateSaturatePhysicalCharges_size candidate model seed
  change (extractTerminalSupport candidate records).gateCount =
    (terminalSaturatePhysicalCharges
      (terminalCandidateSaturationSystem candidate model) seed).length at charges
  rw [Program.size_eq_gateCount]
  change (0 + replacementGates) +
    (extractTerminalSupport candidate (terminalPhysicalComplementRecords records)).gateCount +
    (terminalSaturatePhysicalCharges
      (terminalCandidateSaturationSystem candidate model) seed).length = gates + replacementGates
  omega

private def physicalSupportValue
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (input : Valuation inputs) :
    Valuation ((extractTerminalSupport candidate records).interface.length + inputs) :=
  splitFin
    (fun index => candidate.program.eval input
      ((extractTerminalSupport candidate records).interface.get index))
    input

private theorem physicalSupportEnvironment_bypass
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (input : Valuation inputs) (index : Fin inputs) :
    (physicalSupportEnvironment candidate records).semantics input
      (Fin.natAdd (extractTerminalSupport candidate records).boundary.length index) =
      input index := by
  simp only [physicalSupportEnvironment, Candidate.ofDirectWireWord_semantics,
    DirectWire.semantics, DirectWireWord.eval, splitFin_right, Source.eval]

private theorem physicalSupportEnvironment_induced
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (input : Valuation inputs)
    (index : Fin (extractTerminalSupport candidate (terminalSaturateRecords
      (terminalCandidateSaturationSystem candidate model) seed)).boundary.length) :
    let records := terminalSaturateRecords
      (terminalCandidateSaturationSystem candidate model) seed
    (physicalSupportEnvironment candidate records).semantics input
        (Fin.castAdd inputs index) =
      terminalInducedBoundaryValuation candidate records input index := by
  dsimp only
  let records := terminalSaturateRecords
    (terminalCandidateSaturationSystem candidate model) seed
  let support := extractTerminalSupport candidate records
  obtain ⟨primary, same⟩ := terminalCandidateSaturate_boundary_isInput
    candidate model seed (support.boundary.get index) (List.get_mem _ index)
  simp only [physicalSupportEnvironment, Candidate.ofDirectWireWord_semantics,
    DirectWire.semantics, DirectWireWord.eval, splitFin_left]
  change (match support.boundary.get index with
      | .input source => Source.input source
      | .gate _source => Source.constant false).eval input (Program.empty.eval input) =
    (support.boundary.get index).candidateValue candidate input
  rw [same]
  rfl

private theorem physicalComplementInputBinding_induced
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (input : Valuation inputs)
    (index : Fin (extractTerminalSupport candidate
      (terminalPhysicalComplementRecords records)).boundary.length) :
    physicalSupportValue candidate records input
        (physicalComplementInputBinding candidate records index) =
      terminalInducedBoundaryValuation candidate
        (terminalPhysicalComplementRecords records) input index := by
  let complement := extractTerminalSupport candidate (terminalPhysicalComplementRecords records)
  change _ = (complement.boundary.get index).candidateValue candidate input
  unfold physicalComplementInputBinding
  dsimp only
  split
  · rename_i primary same
    simp only [physicalSupportValue, splitFin_right]
    rw [same]
    rfl
  · rename_i producer same
    simp only [physicalSupportValue, splitFin_left, physicalGet_memberIndex]
    rw [same]
    rfl

private theorem physicalComplementRenamed_induced
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (input : Valuation inputs)
    (output : Fin (extractTerminalSupport candidate
      (terminalPhysicalComplementRecords records)).interface.length) :
    ((extractTerminalSupport candidate (terminalPhysicalComplementRecords records)).extractedCandidate.renameInputs (physicalComplementInputBinding candidate records)).semantics
      (physicalSupportValue candidate records input) output =
      candidate.program.eval input
        ((extractTerminalSupport candidate (terminalPhysicalComplementRecords records)).interface.get
          output) := by
  rw [Candidate.renameInputs_semantics]
  have binding :
      (fun index => physicalSupportValue candidate records input
        (physicalComplementInputBinding candidate records index)) =
      terminalInducedBoundaryValuation candidate
        (terminalPhysicalComplementRecords records) input :=
    funext (physicalComplementInputBinding_induced candidate records input)
  rw [binding]
  exact extractTerminalSupport_induced candidate (terminalPhysicalComplementRecords records)
    input output

private theorem physicalGlobalOutput_gate_exposed
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (output : Fin outputs) (producer : Fin gates)
    (same : candidate.directWireWord.source output = Source.gate producer) :
    producer ∈ (extractTerminalSupport candidate records).interface ∨
      producer ∈ (extractTerminalSupport candidate
        (terminalPhysicalComplementRecords records)).interface := by
  have global := (terminalGateIsGlobalOutput_eq_true_iff
    candidate.directWireWord producer).2 ⟨output, same⟩
  cases selected : terminalGateSelected records producer with
  | false =>
      apply Or.inr
      apply completeTerminalPhysicalSupport_outgoing_complete candidate
        (terminalPhysicalComplementRecords records) producer
      · rw [physicalComplement_selected, selected]
        rfl
      · exact Or.inr global
  | true =>
      exact Or.inl (completeTerminalPhysicalSupport_outgoing_complete
        candidate records producer selected (Or.inr global))

private theorem physicalSupportContinuation_induced
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (input : Valuation inputs) (output : Fin outputs) :
    (physicalSupportContinuation candidate records).semantics
      (physicalSupportValue candidate records input) output =
      candidate.semantics input output := by
  change _ = (candidate.directWireWord.source output).eval input (candidate.program.eval input)
  cases source : candidate.directWireWord.source output with
  | input primary =>
      simp only [physicalSupportContinuation, Candidate.ofDirectWireWord_semantics,
        DirectWire.semantics, DirectWireWord.eval, source,
        Source.eval, physicalSupportValue, splitFin_right]
  | constant value =>
      simp only [physicalSupportContinuation, Candidate.ofDirectWireWord_semantics,
        DirectWire.semantics, DirectWireWord.eval, source, Source.eval]
  | gate producer =>
      simp only [physicalSupportContinuation, Candidate.ofDirectWireWord_semantics,
        DirectWire.semantics, DirectWireWord.eval, source]
      split
      · rename_i inSupport
        simp only [Source.eval, physicalSupportValue, splitFin_left, physicalGet_memberIndex]
      · rename_i notInSupport
        split
        · rename_i inComplement
          change ((extractTerminalSupport candidate
              (terminalPhysicalComplementRecords records)).extractedCandidate.renameInputs
                (physicalComplementInputBinding candidate records)).semantics
              (physicalSupportValue candidate records input)
              (physicalMemberIndex inComplement) =
            candidate.program.eval input producer
          rw [physicalComplementRenamed_induced, physicalGet_memberIndex]
        · rename_i notInComplement
          exact False.elim ((physicalGlobalOutput_gate_exposed
            candidate records output producer source).elim notInSupport notInComplement)

/-- Plugging the unchanged extracted support into its computed frame recovers
    the entire original ordered Boolean output word at every input valuation. -/
theorem terminalCandidateSaturatePhysicalContext_equivalent
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    let support := extractTerminalSupport candidate (terminalSaturateRecords
      (terminalCandidateSaturationSystem candidate model) seed)
    let context := terminalCandidateSaturatePhysicalContext candidate model seed
    Equivalent (context.plug support.extractedCandidate).program
      (context.plug support.extractedCandidate).directWireWord
      candidate.program candidate.directWireWord := by
  dsimp only
  let records := terminalSaturateRecords
    (terminalCandidateSaturationSystem candidate model) seed
  let support := extractTerminalSupport candidate records
  let context := terminalCandidateSaturatePhysicalContext candidate model seed
  intro input output
  change (context.plug support.extractedCandidate).semantics input output =
    candidate.semantics input output
  rw [FramedContext.plug_semantics]
  have boundary :
      (fun index => (physicalSupportEnvironment candidate records).semantics input
        (Fin.castAdd inputs index)) =
      terminalInducedBoundaryValuation candidate records input :=
    funext (physicalSupportEnvironment_induced candidate model seed input)
  have supportValues :
      (fun index => support.extractedCandidate.semantics
        (fun port => (physicalSupportEnvironment candidate records).semantics input
          (Fin.castAdd inputs port)) index) =
      (fun index => candidate.program.eval input (support.interface.get index)) := by
    rw [boundary]
    exact funext (extractTerminalSupport_induced candidate records input)
  have bypassValues :
      (fun index => (physicalSupportEnvironment candidate records).semantics input
        (Fin.natAdd support.boundary.length index)) = input :=
    funext (physicalSupportEnvironment_bypass candidate records input)
  change (physicalSupportContinuation candidate records).semantics
    (fun joined => splitFin
      (fun index => support.extractedCandidate.semantics
        (fun port => (physicalSupportEnvironment candidate records).semantics input
          (Fin.castAdd inputs port)) index)
      (fun index => (physicalSupportEnvironment candidate records).semantics input
        (Fin.natAdd support.boundary.length index)) joined) output =
    candidate.semantics input output
  rw [supportValues, bypassValues]
  exact physicalSupportContinuation_induced candidate records input output

/-- Every equivalent replacement on the exact extracted boundary/interface
    preserves the whole circuit. Whole-circuit correctness is derived rather
    than supplied as a premise. -/
theorem terminalCandidateSaturatePhysicalContext_replace_equivalent
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    {replacementGates : Nat}
    (replacement : Candidate
      (extractTerminalSupport candidate (terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed)).boundary.length
      replacementGates
      (extractTerminalSupport candidate (terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed)).interface.length) :
    let support := extractTerminalSupport candidate (terminalSaturateRecords
      (terminalCandidateSaturationSystem candidate model) seed)
    let context := terminalCandidateSaturatePhysicalContext candidate model seed
    Equivalent replacement.program replacement.directWireWord
      support.extractedCandidate.program support.extractedCandidate.directWireWord →
    Equivalent (context.plug replacement).program
      (context.plug replacement).directWireWord candidate.program candidate.directWireWord := by
  dsimp only
  intro equivalent
  exact Equivalent.trans
    (compatibleReplacement_framed
      (terminalCandidateSaturatePhysicalContext candidate model seed)
      replacement _ equivalent)
    (terminalCandidateSaturatePhysicalContext_equivalent candidate model seed)

/-- The physical Boolean slack of the actual computed saturated support is
    bounded by whole-circuit slack. This uses the unchanged exhaustive reference
    minimum; it is not a polynomial minimization or full-profile theorem. -/
theorem terminalCandidateSaturatePhysicalSupport_slack_le
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    residualSlack (extractTerminalSupport candidate (terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed)).extractedCandidate.toImplementation ≤
      residualSlack candidate.toImplementation := by
  let records := terminalSaturateRecords
    (terminalCandidateSaturationSystem candidate model) seed
  let support := extractTerminalSupport candidate records
  let context := terminalCandidateSaturatePhysicalContext candidate model seed
  have framed := framedGlobalSlackLaw context support.extractedCandidate
  have minima := referenceMinimum_invariant
    (context.plug support.extractedCandidate).toImplementation candidate.toImplementation
    (terminalCandidateSaturatePhysicalContext_equivalent candidate model seed)
  have size : (context.plug support.extractedCandidate).toImplementation.gateCount = gates := by
    have partition := physicalComplement_gateCount_partition candidate records
    change (0 + support.gateCount) +
      (extractTerminalSupport candidate (terminalPhysicalComplementRecords records)).gateCount = gates
    simpa only [Nat.zero_add] using partition
  change residualSlack support.extractedCandidate.toImplementation ≤
    residualSlack (context.plug support.extractedCandidate).toImplementation at framed
  unfold residualSlack at framed ⊢
  rw [size, minima] at framed
  exact framed

end DirectWire
end PNP
