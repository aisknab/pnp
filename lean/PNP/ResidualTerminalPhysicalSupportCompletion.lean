/-
Copyright (c) 2026 PNP Labs.

Physical boundary and interface completion for finite terminal supports.  The
selected gates come from one finite list of terminal primitive records.  The
actual direct-wire program, rather than a caller annotation, determines every
wire entering or leaving the selected gate set.

This reconstructs the physical `(U, partial U, iota U)` part of the completed
support in Sections 2 and 3 of the pinned manuscript.  It does not classify
profile records into the manuscript's frontier, construct a proper positive
support, prove square legitimacy or projection compatibility, preserve
positivity under saturation, or establish any downstream route or runtime
claim.
-/

import PNP.ResidualTerminalExecutableSaturation
import PNP.NANDSourceListOrder

namespace PNP
namespace DirectWire

/-- A physical wire which can cross a gate support boundary.  Constants are
    deliberately absent: a direct-wire NAND gate may use either carrier
    constant locally without exposing a boundary port. -/
inductive TerminalSupportWire (inputs gates : Nat) where
  | input (index : Fin inputs)
  | gate (index : Fin gates)
  deriving Repr, DecidableEq

/-- Canonical physical-wire order: primary inputs, then gate outputs. -/
def allTerminalSupportWires (inputs gates : Nat) :
    List (TerminalSupportWire inputs gates) :=
  (allFin inputs).map TerminalSupportWire.input ++
    (allFin gates).map TerminalSupportWire.gate

/-- Every physical support wire occurs in the canonical enumeration. -/
theorem mem_allTerminalSupportWires {inputs gates : Nat}
    (wire : TerminalSupportWire inputs gates) :
    wire ∈ allTerminalSupportWires inputs gates := by
  cases wire with
  | input index =>
      apply List.mem_append_left
      exact mem_map_of_mem TerminalSupportWire.input (mem_allFin index)
  | gate index =>
      apply List.mem_append_right
      exact mem_map_of_mem TerminalSupportWire.gate (mem_allFin index)

/-- Re-express an available direct-wire source as a physical support wire.
    Constants return `none` because they do not cross the support boundary. -/
def Source.terminalSupportWire? {inputs gates : Nat} :
    Source inputs gates → Option (TerminalSupportWire inputs gates)
  | .input index => some (.input index)
  | .constant _value => none
  | .gate index => some (.gate index)

/-- The two sources of any gate, transported to the width of the complete
    program.  This is total even though each stored gate is indexed only by
    the prefix available when it was appended. -/
def Program.terminalGateSources {inputs : Nat} :
    {gates : Nat} → Program inputs gates → Fin gates →
      Source inputs gates × Source inputs gates
  | 0, .empty, index => Fin.elim0 index
  | gates + 1, .snoc initial gate, index =>
      if earlier : index.val < gates then
        let sourcePair :=
          terminalGateSources initial ⟨index.val, earlier⟩
        (sourcePair.1.weakenGates 1, sourcePair.2.weakenGates 1)
      else
        (gate.left.weakenGates 1, gate.right.weakenGates 1)

private def physicalTerminalAny {alpha : Type} : List alpha → (alpha → Bool) → Bool
  | [], _predicate => false
  | item :: items, predicate => predicate item || physicalTerminalAny items predicate

private theorem physicalTerminalAny_true_iff {alpha : Type}
    (items : List alpha) (predicate : alpha → Bool) :
    physicalTerminalAny items predicate = true ↔
      ∃ item, item ∈ items ∧ predicate item = true := by
  induction items with
  | nil =>
      constructor
      · intro impossible
        exact Bool.noConfusion impossible
      · rintro ⟨item, member, _checked⟩
        cases member
  | cons head tail ih =>
      unfold physicalTerminalAny
      cases headCheck : predicate head with
      | false =>
          change physicalTerminalAny tail predicate = true ↔ _
          constructor
          · intro checked
            obtain ⟨item, member, itemCheck⟩ := ih.mp checked
            exact ⟨item, List.Mem.tail head member, itemCheck⟩
          · rintro ⟨item, member, itemCheck⟩
            cases List.mem_cons.mp member with
            | inl equal =>
                subst item
                rw [headCheck] at itemCheck
                exact Bool.noConfusion itemCheck
            | inr tailMember =>
                exact ih.mpr ⟨item, tailMember, itemCheck⟩
      | true =>
          change true = true ↔ _
          constructor
          · intro _checked
            exact ⟨head, List.Mem.head tail, headCheck⟩
          · intro _witness
            rfl

private def sourceMatchesTerminalWire {inputs gates : Nat}
    (source : Source inputs gates) (wire : TerminalSupportWire inputs gates) : Bool :=
  decide (source.terminalSupportWire? = some wire)

/-- Whether one actual program gate consumes the given physical wire. -/
def Program.terminalGateUsesWire {inputs gates : Nat}
    (program : Program inputs gates) (consumer : Fin gates)
    (wire : TerminalSupportWire inputs gates) : Bool :=
  let sourcePair := program.terminalGateSources consumer
  sourceMatchesTerminalWire sourcePair.1 wire ||
    sourceMatchesTerminalWire sourcePair.2 wire

/-- A primitive-record list selects precisely its listed physical gate
    records.  Boundary, interface, and profile records do not select gates. -/
def terminalGateSelected
    {inputs gates outputs profileWidth : Nat}
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates) : Bool :=
  decide (TerminalPrimitiveRecord.gate gate ∈ records)

/-- A wire is outside a selected gate set exactly when it is a primary input
    or the output of an unselected gate. -/
def terminalWireExternal
    {inputs gates outputs profileWidth : Nat}
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalSupportWire inputs gates → Bool
  | .input _index => true
  | .gate index => !(terminalGateSelected records index)

/-- Exact physical incoming-boundary test. -/
def terminalBoundaryWire
    {inputs gates outputs profileWidth : Nat}
    (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (wire : TerminalSupportWire inputs gates) : Bool :=
  terminalWireExternal records wire &&
    physicalTerminalAny (allFin gates) fun consumer =>
      terminalGateSelected records consumer &&
        program.terminalGateUsesWire consumer wire

/-- A selected producer has an external internal-gate consumer. -/
def terminalGateHasExternalConsumer
    {inputs gates outputs profileWidth : Nat}
    (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (producer : Fin gates) : Bool :=
  physicalTerminalAny (allFin gates) fun consumer =>
    !(terminalGateSelected records consumer) &&
      program.terminalGateUsesWire consumer (.gate producer)

/-- A selected producer is exposed by the implementation's ordered output
    tuple. -/
def terminalGateIsGlobalOutput {inputs gates outputs : Nat}
    (word : DirectWireWord inputs gates outputs) (producer : Fin gates) : Bool :=
  physicalTerminalAny (allFin outputs) fun output =>
    decide (word.source output = Source.gate producer)

/-- A physical gate is a global output exactly when the actual output tuple
    names it at some position. Multiplicity and ordering are preserved. -/
theorem terminalGateIsGlobalOutput_eq_true_iff {inputs gates outputs : Nat}
    (word : DirectWireWord inputs gates outputs) (producer : Fin gates) :
    terminalGateIsGlobalOutput word producer = true ↔
      ∃ output : Fin outputs, word.source output = Source.gate producer := by
  constructor
  · intro checked
    obtain ⟨output, _enumerated, same⟩ :=
      (physicalTerminalAny_true_iff (allFin outputs)
        (fun output => decide (word.source output = Source.gate producer))).1 checked
    exact ⟨output, of_decide_eq_true same⟩
  · rintro ⟨output, same⟩
    exact (physicalTerminalAny_true_iff (allFin outputs)
      (fun output => decide (word.source output = Source.gate producer))).2
        ⟨output, mem_allFin output, decide_eq_true same⟩

/-- Exact physical outgoing-interface test. -/
def terminalInterfaceGate
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (producer : Fin gates) : Bool :=
  terminalGateSelected records producer &&
    (terminalGateHasExternalConsumer candidate.program records producer ||
      terminalGateIsGlobalOutput candidate.directWireWord producer)

/-- A gate is selected exactly when its primitive gate record occurs in the
    supplied terminal record list. -/
theorem terminalGateSelected_eq_true_iff
    {inputs gates outputs profileWidth : Nat}
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates) :
    terminalGateSelected records gate = true ↔
      TerminalPrimitiveRecord.gate gate ∈ records := by
  unfold terminalGateSelected
  constructor
  · exact of_decide_eq_true
  · exact decide_eq_true

/-- Exact semantic form of the physical external-wire predicate. -/
theorem terminalWireExternal_eq_true_iff
    {inputs gates outputs profileWidth : Nat}
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (wire : TerminalSupportWire inputs gates) :
    terminalWireExternal records wire = true ↔
      match wire with
      | .input _index => True
      | .gate gate => terminalGateSelected records gate = false := by
  cases wire with
  | input index =>
      constructor <;> intro _checked
      · trivial
      · rfl
  | gate gate =>
      change (!terminalGateSelected records gate) = true ↔
        terminalGateSelected records gate = false
      cases selected : terminalGateSelected records gate with
      | false =>
          constructor <;> intro _checked <;> rfl
      | true =>
          constructor
          · intro impossible
            exact Bool.noConfusion impossible
          · intro impossible
            exact Bool.noConfusion impossible

/-- Exact witness form of the incoming-boundary predicate. -/
theorem terminalBoundaryWire_eq_true_iff
    {inputs gates outputs profileWidth : Nat}
    (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (wire : TerminalSupportWire inputs gates) :
    terminalBoundaryWire program records wire = true ↔
      terminalWireExternal records wire = true ∧
        ∃ consumer, consumer ∈ allFin gates ∧
          terminalGateSelected records consumer = true ∧
            program.terminalGateUsesWire consumer wire = true := by
  simp only [terminalBoundaryWire, Bool.and_eq_true,
    physicalTerminalAny_true_iff]

/-- Exact witness form of an external consumer of a selected producer. -/
theorem terminalGateHasExternalConsumer_eq_true_iff
    {inputs gates outputs profileWidth : Nat}
    (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (producer : Fin gates) :
    terminalGateHasExternalConsumer program records producer = true ↔
      ∃ consumer, consumer ∈ allFin gates ∧
        terminalGateSelected records consumer = false ∧
          program.terminalGateUsesWire consumer (.gate producer) = true := by
  constructor
  · intro checked
    obtain ⟨consumer, consumerMember, both⟩ :=
      (physicalTerminalAny_true_iff (allFin gates) (fun consumer =>
        !(terminalGateSelected records consumer) &&
          program.terminalGateUsesWire consumer (.gate producer))).1 checked
    have split :
        (!terminalGateSelected records consumer) = true ∧
          program.terminalGateUsesWire consumer (.gate producer) = true := by
      simpa only [Bool.and_eq_true] using both
    have selectedFalse : terminalGateSelected records consumer = false := by
      cases selected : terminalGateSelected records consumer with
      | false => rfl
      | true =>
          rw [selected] at split
          exact Bool.noConfusion split.1
    exact ⟨consumer, consumerMember, selectedFalse, split.2⟩
  · rintro ⟨consumer, consumerMember, selectedFalse, uses⟩
    apply (physicalTerminalAny_true_iff (allFin gates) (fun consumer =>
      !(terminalGateSelected records consumer) &&
        program.terminalGateUsesWire consumer (.gate producer))).2
    refine ⟨consumer, consumerMember, ?_⟩
    simp only [Bool.and_eq_true]
    constructor
    · rw [selectedFalse]
      rfl
    · exact uses

/-- Exact semantic form of the outgoing-interface predicate. -/
theorem terminalInterfaceGate_eq_true_iff
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (producer : Fin gates) :
    terminalInterfaceGate candidate records producer = true ↔
      terminalGateSelected records producer = true ∧
        (terminalGateHasExternalConsumer candidate.program records producer = true ∨
          terminalGateIsGlobalOutput candidate.directWireWord producer = true) := by
  simp only [terminalInterfaceGate, Bool.and_eq_true, Bool.or_eq_true]

/-- Injective canonical coordinate: primary inputs precede all gate outputs. -/
def TerminalSupportWire.orderCode {inputs gates : Nat} :
    TerminalSupportWire inputs gates → Nat
  | .input index => index.val
  | .gate index => inputs + index.val

theorem TerminalSupportWire.orderCode_injective {inputs gates : Nat} :
    Function.Injective (@TerminalSupportWire.orderCode inputs gates) := by
  intro left right same
  cases left with
  | input left =>
      cases right with
      | input right => exact congrArg TerminalSupportWire.input (Fin.ext same)
      | gate right =>
          change left.val = inputs + right.val at same
          have bounded := left.isLt
          rw [same] at bounded
          exact False.elim ((Nat.not_lt_of_ge
            (Nat.le_add_right inputs right.val)) bounded)
  | gate left =>
      cases right with
      | input right =>
          change inputs + left.val = right.val at same
          have bounded := right.isLt
          rw [← same] at bounded
          exact False.elim ((Nat.not_lt_of_ge
            (Nat.le_add_right inputs left.val)) bounded)
      | gate right =>
          exact congrArg TerminalSupportWire.gate (Fin.ext (Nat.add_left_cancel same))

private theorem allFin_strictOrder (width : Nat) :
    (allFin width).Pairwise (fun left right => left.val < right.val) := by
  induction width with
  | zero => exact List.Pairwise.nil
  | succ width ih =>
      apply List.pairwise_cons.mpr
      constructor
      · intro item member
        obtain ⟨earlier, _member, same⟩ := List.mem_map.mp member
        subst item
        exact Nat.zero_lt_succ earlier.val
      · rw [List.pairwise_map]
        exact ih.imp (fun less => Nat.succ_lt_succ less)

/-- The specification's ambient list has the exact canonical strict order. -/
theorem allTerminalSupportWires_strictOrder (inputs gates : Nat) :
    (allTerminalSupportWires inputs gates).Pairwise
      (fun left right => left.orderCode < right.orderCode) := by
  unfold allTerminalSupportWires
  apply List.pairwise_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_map]
    exact allFin_strictOrder inputs
  · rw [List.pairwise_map]
    exact (allFin_strictOrder gates).imp (fun less => Nat.add_lt_add_left less inputs)
  · intro left leftMember right rightMember
    obtain ⟨input, _inputMember, inputSame⟩ := List.mem_map.mp leftMember
    obtain ⟨gate, _gateMember, gateSame⟩ := List.mem_map.mp rightMember
    subst left
    subst right
    exact Nat.lt_of_lt_of_le input.isLt (Nat.le_add_right inputs gate.val)

/-- One actual nonconstant source contributes one occurrence, not an input scan. -/
def Source.terminalWireOccurrences {inputs gates : Nat} :
    Source inputs gates → List (TerminalSupportWire inputs gates)
  | .constant _ => []
  | .input index => [.input index]
  | .gate index => [.gate index]

theorem Source.mem_terminalWireOccurrences_iff {inputs gates : Nat}
    (source : Source inputs gates) (wire : TerminalSupportWire inputs gates) :
    wire ∈ source.terminalWireOccurrences ↔
      source.terminalSupportWire? = some wire := by
  cases source with
  | constant value =>
      constructor
      · intro impossible
        cases impossible
      · intro impossible
        cases impossible
  | input index =>
      constructor
      · intro member
        have same := List.mem_singleton.mp member
        cases same
        rfl
      · intro same
        have sameWire := Option.some.inj same
        cases sameWire
        exact List.mem_cons_self
  | gate index =>
      constructor
      · intro member
        have same := List.mem_singleton.mp member
        cases same
        rfl
      · intro same
        have sameWire := Option.some.inj same
        cases sameWire
        exact List.mem_cons_self

theorem Source.terminalWireOccurrences_length {inputs gates : Nat}
    (source : Source inputs gates) : source.terminalWireOccurrences.length ≤ 1 := by
  cases source with
  | constant value => exact Nat.zero_le 1
  | input index => exact Nat.le_refl 1
  | gate index => exact Nat.le_refl 1

/-- Actual gate-source occurrences only, with multiplicity retained before sorting. -/
def terminalSourceWireOccurrences {inputs gates : Nat} (program : Program inputs gates) :
    List (TerminalSupportWire inputs gates) :=
  (allFin gates).flatMap fun consumer =>
    (program.terminalGateSources consumer).1.terminalWireOccurrences ++
      (program.terminalGateSources consumer).2.terminalWireOccurrences

private theorem sourceOccurrence_flatMap_length {alpha beta : Type}
    (items : List alpha) (mapping : alpha → List beta) (bound : Nat)
    (each : ∀ item, item ∈ items → (mapping item).length ≤ bound) :
    (items.flatMap mapping).length ≤ items.length * bound := by
  induction items with
  | nil =>
      simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons head tail ih =>
      have first := each head List.mem_cons_self
      have rest := ih (fun item member => each item (List.mem_cons_of_mem head member))
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
      exact Nat.le_trans (Nat.add_le_add first rest) (Nat.le_of_eq (Nat.add_comm _ _))

/-- The occurrence budget depends on physical gates, not unused declared inputs. -/
theorem terminalSourceWireOccurrences_length {inputs gates : Nat}
    (program : Program inputs gates) :
    (terminalSourceWireOccurrences program).length ≤ 2 * gates := by
  have bound := sourceOccurrence_flatMap_length (allFin gates)
    (fun consumer =>
      (program.terminalGateSources consumer).1.terminalWireOccurrences ++
        (program.terminalGateSources consumer).2.terminalWireOccurrences) 2
    (fun consumer _member => by
      rw [List.length_append]
      exact Nat.add_le_add (Source.terminalWireOccurrences_length _)
        (Source.terminalWireOccurrences_length _))
  simpa only [terminalSourceWireOccurrences, allFin_length, Nat.mul_comm] using bound

/-- Every incoming crossing is witnessed by an actual selected gate's source. -/
theorem terminalBoundaryWire_mem_sourceOccurrences
    {inputs gates outputs profileWidth : Nat} (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (wire : TerminalSupportWire inputs gates)
    (crossing : terminalBoundaryWire program records wire = true) :
    wire ∈ terminalSourceWireOccurrences program := by
  obtain ⟨_external, consumer, enumerated, _selected, used⟩ :=
    (terminalBoundaryWire_eq_true_iff program records wire).mp crossing
  apply List.mem_flatMap.mpr
  refine ⟨consumer, enumerated, ?_⟩
  change (decide ((program.terminalGateSources consumer).1.terminalSupportWire? = some wire) ||
    decide ((program.terminalGateSources consumer).2.terminalSupportWire? = some wire)) = true
    at used
  simp only [Bool.or_eq_true] at used
  rcases used with left | right
  · exact List.mem_append_left _
      ((Source.mem_terminalWireOccurrences_iff _ wire).mpr (of_decide_eq_true left))
  · exact List.mem_append_right _
      ((Source.mem_terminalWireOccurrences_iff _ wire).mpr (of_decide_eq_true right))

/-- Canonical physical boundary computed solely from actual gate-source occurrences. -/
def terminalBoundaryPortsSourceDriven
    {inputs gates outputs profileWidth : Nat} (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (TerminalSupportWire inputs gates) :=
  SourceListOrder.canonical TerminalSupportWire.orderCode
    ((terminalSourceWireOccurrences program).filter (terminalBoundaryWire program records))

/-- Exact ordered equality with the independent ambient-enumeration specification. -/
theorem terminalBoundaryPortsSourceDriven_eq_reference
    {inputs gates outputs profileWidth : Nat} (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalBoundaryPortsSourceDriven program records =
      (allTerminalSupportWires inputs gates).filter (terminalBoundaryWire program records) := by
  apply SourceListOrder.canonical_eq_reference TerminalSupportWire.orderCode
    TerminalSupportWire.orderCode_injective
  · have distinct : (allTerminalSupportWires inputs gates).Nodup :=
      (allTerminalSupportWires_strictOrder inputs gates).imp (fun less same => by
        subst same
        exact Nat.lt_irrefl _ less)
    exact distinct.sublist List.filter_sublist
  · exact ((allTerminalSupportWires_strictOrder inputs gates).imp
      (fun less => Nat.le_of_lt less)).filter _
  · intro wire
    rw [List.mem_filter, List.mem_filter]
    constructor
    · intro checked
      exact ⟨mem_allTerminalSupportWires wire, checked.2⟩
    · intro checked
      exact ⟨terminalBoundaryWire_mem_sourceOccurrences program records wire checked.2,
        checked.2⟩

theorem terminalBoundaryPortsSourceDriven_length
    {inputs gates outputs profileWidth : Nat} (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalBoundaryPortsSourceDriven program records).length ≤ 2 * gates :=
  Nat.le_trans (SourceListOrder.canonical_length_le _ _)
    (Nat.le_trans (List.length_filter_le _ _) (terminalSourceWireOccurrences_length program))

theorem terminalBoundaryPortsSourceDriven_nodup
    {inputs gates outputs profileWidth : Nat} (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalBoundaryPortsSourceDriven program records).Nodup :=
  SourceListOrder.canonical_nodup _ _

theorem terminalBoundaryPortsSourceDriven_ordered
    {inputs gates outputs profileWidth : Nat} (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalBoundaryPortsSourceDriven program records).Pairwise
      (fun left right => left.orderCode ≤ right.orderCode) :=
  SourceListOrder.canonical_ordered _ _

/-- Canonically ordered incoming physical ports from actual gate sources. -/
def terminalBoundaryPorts
    {inputs gates outputs profileWidth : Nat}
    (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (TerminalSupportWire inputs gates) :=
  terminalBoundaryPortsSourceDriven program records


/-- Exact reference semantics; the active extractor does not execute this enumeration. -/
theorem terminalBoundaryPorts_reference
    {inputs gates outputs profileWidth : Nat} (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalBoundaryPorts program records =
      (allTerminalSupportWires inputs gates).filter (terminalBoundaryWire program records) :=
  terminalBoundaryPortsSourceDriven_eq_reference program records

/-- Active physical extraction has at most two incoming ports per physical gate. -/
theorem terminalBoundaryPorts_length
    {inputs gates outputs profileWidth : Nat} (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalBoundaryPorts program records).length ≤ 2 * gates :=
  terminalBoundaryPortsSourceDriven_length program records

/-- Active extraction never repeats a coordinate. -/
theorem terminalBoundaryPorts_nodup
    {inputs gates outputs profileWidth : Nat} (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalBoundaryPorts program records).Nodup :=
  terminalBoundaryPortsSourceDriven_nodup program records

/-- Active extraction preserves the canonical coordinate order. -/
theorem terminalBoundaryPorts_ordered
    {inputs gates outputs profileWidth : Nat} (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalBoundaryPorts program records).Pairwise
      (fun left right => left.orderCode ≤ right.orderCode) :=
  terminalBoundaryPortsSourceDriven_ordered program records

/-- Canonically ordered outgoing physical ports. -/
def terminalInterfacePorts
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (Fin gates) :=
  (allFin gates).filter (terminalInterfaceGate candidate records)

/-- The boundary list contains exactly the actual incoming crossing wires. -/
theorem mem_terminalBoundaryPorts_iff
    {inputs gates outputs profileWidth : Nat}
    (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (wire : TerminalSupportWire inputs gates) :
    wire ∈ terminalBoundaryPorts program records ↔
      terminalBoundaryWire program records wire = true := by
  rw [terminalBoundaryPorts_reference]
  constructor
  · intro member
    exact (List.mem_filter.mp member).2
  · intro checked
    exact List.mem_filter.mpr ⟨mem_allTerminalSupportWires wire, checked⟩

/-- The interface list contains exactly the actual outgoing crossing wires. -/
theorem mem_terminalInterfacePorts_iff
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (producer : Fin gates) :
    producer ∈ terminalInterfacePorts candidate records ↔
      terminalInterfaceGate candidate records producer = true := by
  constructor
  · intro member
    exact (List.mem_filter.mp member).2
  · intro checked
    exact List.mem_filter.mpr ⟨mem_allFin producer, checked⟩

/-- Physical completion of a finite terminal record list.  The profile record
    list is retained but deliberately not classified as a manuscript frontier. -/
structure TerminalPhysicalCompletedSupport
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs) where
  records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  boundary : List (TerminalSupportWire inputs gates)
  interface : List (Fin gates)

/-- Compute physical ports directly from the actual direct-wire candidate. -/
def completeTerminalPhysicalSupport
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalPhysicalCompletedSupport (profileWidth := profileWidth) candidate :=
  { records := records
    boundary := terminalBoundaryPorts candidate.program records
    interface := terminalInterfacePorts candidate records }

/-- One source of a selected gate is physically accounted for when it is a
    local constant, an internal selected gate, or a listed incoming port. -/
def TerminalPhysicalCompletedSupport.SourceAccounted
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    (support : TerminalPhysicalCompletedSupport
      (profileWidth := profileWidth) candidate)
    (source : Source inputs gates) : Prop :=
  match source with
  | .input index => .input index ∈ support.boundary
  | .constant _value => True
  | .gate index =>
      terminalGateSelected support.records index = true ∨
        .gate index ∈ support.boundary

/-- Physical compatibility is the exact incoming/outgoing crossing condition
    needed before later open-support extraction and replacement. -/
def TerminalPhysicalCompletedSupport.Compatible
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    (support : TerminalPhysicalCompletedSupport
      (profileWidth := profileWidth) candidate) : Prop :=
  (∀ consumer,
      terminalGateSelected support.records consumer = true →
        let sourcePair := candidate.program.terminalGateSources consumer
        support.SourceAccounted sourcePair.1 ∧
          support.SourceAccounted sourcePair.2) ∧
    (∀ producer,
      terminalGateSelected support.records producer = true →
      (terminalGateHasExternalConsumer candidate.program support.records producer = true ∨
        terminalGateIsGlobalOutput candidate.directWireWord producer = true) →
      producer ∈ support.interface)

private theorem sourceMatchesTerminalWire_self
    {inputs gates : Nat} (source : Source inputs gates)
    (wire : TerminalSupportWire inputs gates)
    (equal : source.terminalSupportWire? = some wire) :
    sourceMatchesTerminalWire source wire = true := by
  unfold sourceMatchesTerminalWire
  exact decide_eq_true equal

private theorem gateUsesWire_of_left
    {inputs gates : Nat} (program : Program inputs gates)
    (consumer : Fin gates) (wire : TerminalSupportWire inputs gates)
    (equal : (program.terminalGateSources consumer).1.terminalSupportWire? =
      some wire) :
    program.terminalGateUsesWire consumer wire = true := by
  unfold Program.terminalGateUsesWire
  dsimp only
  rw [sourceMatchesTerminalWire_self _ _ equal]
  rfl

private theorem gateUsesWire_of_right
    {inputs gates : Nat} (program : Program inputs gates)
    (consumer : Fin gates) (wire : TerminalSupportWire inputs gates)
    (equal : (program.terminalGateSources consumer).2.terminalSupportWire? =
      some wire) :
    program.terminalGateUsesWire consumer wire = true := by
  unfold Program.terminalGateUsesWire
  dsimp only
  rw [sourceMatchesTerminalWire_self _ _ equal]
  cases sourceMatchesTerminalWire
      (program.terminalGateSources consumer).1 wire <;> rfl

private theorem boundaryWire_of_selected_source
    {inputs gates outputs profileWidth : Nat}
    (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (consumer : Fin gates)
    (selected : terminalGateSelected records consumer = true)
    (wire : TerminalSupportWire inputs gates)
    (external : terminalWireExternal records wire = true)
    (used : program.terminalGateUsesWire consumer wire = true) :
    wire ∈ terminalBoundaryPorts program records := by
  apply (mem_terminalBoundaryPorts_iff program records wire).2
  unfold terminalBoundaryWire
  rw [external]
  apply (physicalTerminalAny_true_iff _ _).2
  exact ⟨consumer, mem_allFin consumer, by rw [selected, used]; rfl⟩

private theorem sourceAccounted
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (consumer : Fin gates)
    (selected : terminalGateSelected records consumer = true)
    (source : Source inputs gates)
    (used :
      (candidate.program.terminalGateSources consumer).1 = source ∨
        (candidate.program.terminalGateSources consumer).2 = source) :
    (completeTerminalPhysicalSupport candidate records).SourceAccounted source := by
  cases source with
  | constant value =>
      trivial
  | input index =>
      apply boundaryWire_of_selected_source candidate.program records consumer
        selected (.input index) rfl
      cases used with
      | inl leftEqual =>
          apply gateUsesWire_of_left
          rw [leftEqual]
          rfl
      | inr rightEqual =>
          apply gateUsesWire_of_right
          rw [rightEqual]
          rfl
  | gate producer =>
      cases producerSelected : terminalGateSelected records producer with
      | true => exact Or.inl producerSelected
      | false =>
          apply Or.inr
          apply boundaryWire_of_selected_source candidate.program records consumer
            selected (.gate producer) (by
              simp only [terminalWireExternal, producerSelected,
                Bool.not_false])
          cases used with
          | inl leftEqual =>
              apply gateUsesWire_of_left
              rw [leftEqual]
              rfl
          | inr rightEqual =>
              apply gateUsesWire_of_right
              rw [rightEqual]
              rfl

/-- Every source of every selected gate is accounted for by the computed
    physical boundary. -/
theorem completeTerminalPhysicalSupport_incoming_complete
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (consumer : Fin gates)
    (selected : terminalGateSelected records consumer = true) :
    let sourcePair := candidate.program.terminalGateSources consumer
    (completeTerminalPhysicalSupport candidate records).SourceAccounted sourcePair.1 ∧
      (completeTerminalPhysicalSupport candidate records).SourceAccounted sourcePair.2 := by
  dsimp only
  constructor
  · exact sourceAccounted candidate records consumer selected _ (Or.inl rfl)
  · exact sourceAccounted candidate records consumer selected _ (Or.inr rfl)

/-- Every selected gate used outside the support or by a global output occurs
    in the computed interface. -/
theorem completeTerminalPhysicalSupport_outgoing_complete
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (producer : Fin gates)
    (selected : terminalGateSelected records producer = true)
    (leaves :
      terminalGateHasExternalConsumer candidate.program records producer = true ∨
        terminalGateIsGlobalOutput candidate.directWireWord producer = true) :
    producer ∈ (completeTerminalPhysicalSupport candidate records).interface := by
  apply (mem_terminalInterfacePorts_iff candidate records producer).2
  unfold terminalInterfaceGate
  rw [selected]
  cases leaves with
  | inl external =>
      rw [external]
      rfl
  | inr output =>
      cases terminalGateHasExternalConsumer candidate.program records producer <;>
        rw [output] <;> rfl

/-- Universal physical completion theorem: the computed boundary and interface
    are compatible for every finite direct-wire candidate and every finite
    selected terminal record list. -/
theorem completeTerminalPhysicalSupport_compatible
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (completeTerminalPhysicalSupport candidate records).Compatible := by
  constructor
  · intro consumer selected
    exact completeTerminalPhysicalSupport_incoming_complete
      candidate records consumer selected
  · intro producer selected leaves
    exact completeTerminalPhysicalSupport_outgoing_complete
      candidate records producer selected leaves

/-- Saturate an arbitrary finite seed with the executable work list, then
    compute its physical boundary and interface from the candidate itself. -/
def completeSaturatedTerminalPhysicalSupport
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalPhysicalCompletedSupport (profileWidth := profileWidth) candidate :=
  completeTerminalPhysicalSupport candidate
    (terminalSaturateRecords system seed)

/-- The combined construction retains exactly the executable saturated record
    list; it does not accept a caller-provided replacement. -/
theorem completeSaturatedTerminalPhysicalSupport_records
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (completeSaturatedTerminalPhysicalSupport candidate system seed).records =
      terminalSaturateRecords system seed := rfl

/-- Universal composed milestone theorem: executable saturation followed by
    computed physical completion is compatible for every finite candidate,
    dependency system, and seed list. -/
theorem completeSaturatedTerminalPhysicalSupport_compatible
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (completeSaturatedTerminalPhysicalSupport candidate system seed).Compatible :=
  completeTerminalPhysicalSupport_compatible candidate
    (terminalSaturateRecords system seed)

end DirectWire
end PNP
