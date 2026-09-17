/-
Copyright (c) 2026 PNP Labs.

Derive arbitrary physical support correspondence from the actual circuit
reindexer. Gate, wire and primitive-record maps are computed from the compiler's
placement. Boundary and interface membership follow from literal source wiring,
not from a supplied support certificate or whole-circuit semantic equality.

This module does not yet transport independent open valuations or replacement
programs. Preserved profile labels do not establish manuscript profile semantics.
-/

import PNP.NANDStructuralReindexing

namespace PNP.DirectWire.StructuralReindexing

variable {inputs gates outputs profileWidth : Nat}

def forwardWire (program : Program inputs gates) (relabeling : GateRenaming gates) :
    TerminalSupportWire inputs gates →
      TerminalSupportWire inputs (compiled program relabeling).count
  | .input index => .input index
  | .gate node => .gate (forwardGate program relabeling node)

def backwardWire (program : Program inputs gates) (relabeling : GateRenaming gates) :
    TerminalSupportWire inputs (compiled program relabeling).count →
      TerminalSupportWire inputs gates
  | .input index => .input index
  | .gate position => .gate (backwardGate program relabeling position)

theorem backward_forward_wire (program : Program inputs gates)
    (relabeling : GateRenaming gates) (wire : TerminalSupportWire inputs gates) :
    backwardWire program relabeling (forwardWire program relabeling wire) = wire := by
  cases wire <;> simp only [forwardWire, backwardWire, backward_forward]

theorem forward_backward_wire (program : Program inputs gates)
    (relabeling : GateRenaming gates)
    (wire : TerminalSupportWire inputs (compiled program relabeling).count) :
    forwardWire program relabeling (backwardWire program relabeling wire) = wire := by
  cases wire <;> simp only [forwardWire, backwardWire, forward_backward]

def forwardRecord (program : Program inputs gates) (relabeling : GateRenaming gates) :
    TerminalPrimitiveRecord inputs gates outputs profileWidth →
      TerminalPrimitiveRecord inputs (compiled program relabeling).count outputs profileWidth
  | .gate node => .gate (forwardGate program relabeling node)
  | .boundary index => .boundary index
  | .interface index => .interface index
  | .profile index => .profile index

def backwardRecord (program : Program inputs gates) (relabeling : GateRenaming gates) :
    TerminalPrimitiveRecord inputs (compiled program relabeling).count outputs profileWidth →
      TerminalPrimitiveRecord inputs gates outputs profileWidth
  | .gate position => .gate (backwardGate program relabeling position)
  | .boundary index => .boundary index
  | .interface index => .interface index
  | .profile index => .profile index

theorem backward_forward_record (program : Program inputs gates)
    (relabeling : GateRenaming gates)
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    backwardRecord program relabeling (forwardRecord program relabeling record) = record := by
  cases record <;> simp only [forwardRecord, backwardRecord, backward_forward]

theorem forward_backward_record (program : Program inputs gates)
    (relabeling : GateRenaming gates)
    (record : TerminalPrimitiveRecord inputs (compiled program relabeling).count outputs profileWidth) :
    forwardRecord program relabeling (backwardRecord program relabeling record) = record := by
  cases record <;> simp only [forwardRecord, backwardRecord, forward_backward]

theorem forwardRecord_injective (program : Program inputs gates)
    (relabeling : GateRenaming gates) :
    Function.Injective
      (forwardRecord (outputs := outputs) (profileWidth := profileWidth) program relabeling) := by
  intro left right same
  have recovered := congrArg (backwardRecord program relabeling) same
  rw [backward_forward_record, backward_forward_record] at recovered
  exact recovered

def forwardRecords (program : Program inputs gates) (relabeling : GateRenaming gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (TerminalPrimitiveRecord inputs (compiled program relabeling).count outputs profileWidth) :=
  records.map (forwardRecord program relabeling)

def backwardRecords (program : Program inputs gates) (relabeling : GateRenaming gates)
    (records :
      List (TerminalPrimitiveRecord inputs (compiled program relabeling).count outputs profileWidth)) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  records.map (backwardRecord program relabeling)

/-- List order and duplicate occurrences survive the round trip. -/
theorem backward_forward_records (program : Program inputs gates)
    (relabeling : GateRenaming gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    backwardRecords program relabeling (forwardRecords program relabeling records) = records := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      change backwardRecord program relabeling (forwardRecord program relabeling record) ::
        backwardRecords program relabeling (forwardRecords program relabeling rest) = record :: rest
      rw [backward_forward_record, ih]

/-- Every descendant record list is covered, not only a chosen forward family. -/
theorem forward_backward_records (program : Program inputs gates)
    (relabeling : GateRenaming gates)
    (records :
      List (TerminalPrimitiveRecord inputs (compiled program relabeling).count outputs profileWidth)) :
    forwardRecords program relabeling (backwardRecords program relabeling records) = records := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      change forwardRecord program relabeling (backwardRecord program relabeling record) ::
        forwardRecords program relabeling (backwardRecords program relabeling rest) = record :: rest
      rw [forward_backward_record, ih]

theorem forwardRecord_mem (program : Program inputs gates) (relabeling : GateRenaming gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    forwardRecord program relabeling record ∈ forwardRecords program relabeling records ↔
      record ∈ records := by
  constructor
  · intro member
    obtain ⟨prior, present, same⟩ := List.mem_map.mp member
    have equal := forwardRecord_injective program relabeling same
    exact equal ▸ present
  · intro member
    exact List.mem_map.mpr ⟨record, member, rfl⟩

private theorem bool_eq_of_true_iff (left right : Bool)
    (same : left = true ↔ right = true) : left = right := by
  cases left <;> cases right
  · rfl
  · exact Bool.noConfusion (same.mpr rfl)
  · exact Bool.noConfusion (same.mp rfl)
  · rfl

theorem selected_forward (program : Program inputs gates) (relabeling : GateRenaming gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (node : Fin gates) :
    terminalGateSelected (forwardRecords program relabeling records)
        (forwardGate program relabeling node) =
      terminalGateSelected records node := by
  apply bool_eq_of_true_iff
  rw [terminalGateSelected_eq_true_iff, terminalGateSelected_eq_true_iff]
  exact forwardRecord_mem program relabeling records (.gate node)

theorem external_forward (program : Program inputs gates) (relabeling : GateRenaming gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (wire : TerminalSupportWire inputs gates) :
    terminalWireExternal (forwardRecords program relabeling records)
        (forwardWire program relabeling wire) = terminalWireExternal records wire := by
  cases wire with
  | input index => rfl
  | gate node =>
      change (!terminalGateSelected (forwardRecords program relabeling records)
        (forwardGate program relabeling node)) = !terminalGateSelected records node
      rw [selected_forward]

theorem backward_forward_source (program : Program inputs gates)
    (relabeling : GateRenaming gates) (source : Source inputs gates) :
    sourceMap (backwardGate program relabeling)
        (sourceMap (forwardGate program relabeling) source) = source := by
  cases source <;> simp only [sourceMap, backward_forward]

theorem sourceMap_forward_injective (program : Program inputs gates)
    (relabeling : GateRenaming gates) :
    Function.Injective
      (@sourceMap inputs gates (compiled program relabeling).count
        (forwardGate program relabeling)) := by
  intro left right same
  have recovered := congrArg (sourceMap (backwardGate program relabeling)) same
  rw [backward_forward_source, backward_forward_source] at recovered
  exact recovered

theorem source_wire_map (program : Program inputs gates) (relabeling : GateRenaming gates)
    (source : Source inputs gates) :
    (sourceMap (forwardGate program relabeling) source).terminalSupportWire? =
      source.terminalSupportWire?.map (forwardWire program relabeling) := by
  cases source <;> rfl

theorem source_wire_iff (program : Program inputs gates) (relabeling : GateRenaming gates)
    (source : Source inputs gates) (wire : TerminalSupportWire inputs gates) :
    (sourceMap (forwardGate program relabeling) source).terminalSupportWire? =
        some (forwardWire program relabeling wire) ↔
      source.terminalSupportWire? = some wire := by
  rw [source_wire_map]
  have inverse (value : Option (TerminalSupportWire inputs gates)) :
      (value.map (forwardWire program relabeling)).map (backwardWire program relabeling) =
        value := by
    cases value with
    | none => rfl
    | some prior =>
        change some (backwardWire program relabeling (forwardWire program relabeling prior)) =
          some prior
        rw [backward_forward_wire]
  constructor
  · intro same
    have recovered := congrArg (Option.map (backwardWire program relabeling)) same
    rw [inverse, Option.map_some, backward_forward_wire] at recovered
    exact recovered
  · intro same
    rw [same]
    rfl

/-- Exact wire incidence follows from actual emitted literal source pairs. -/
theorem uses_forward (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates) (consumer : Fin gates)
    (wire : TerminalSupportWire inputs gates) :
    (result original relabeling).program.terminalGateUsesWire
        (forwardGate original.program relabeling consumer)
        (forwardWire original.program relabeling wire) =
      original.program.terminalGateUsesWire consumer wire := by
  unfold Program.terminalGateUsesWire
  rw [result_sources]
  change
    (decide ((sourceMap (forwardGate original.program relabeling)
        (original.program.terminalGateSources consumer).1).terminalSupportWire? =
          some (forwardWire original.program relabeling wire)) ||
      decide ((sourceMap (forwardGate original.program relabeling)
        (original.program.terminalGateSources consumer).2).terminalSupportWire? =
          some (forwardWire original.program relabeling wire))) =
    (decide ((original.program.terminalGateSources consumer).1.terminalSupportWire? = some wire) ||
      decide ((original.program.terminalGateSources consumer).2.terminalSupportWire? = some wire))
  simp only [source_wire_iff]

theorem boundary_forward (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (wire : TerminalSupportWire inputs gates) :
    terminalBoundaryWire (result original relabeling).program
        (forwardRecords original.program relabeling records)
        (forwardWire original.program relabeling wire) =
      terminalBoundaryWire original.program records wire := by
  apply bool_eq_of_true_iff
  rw [terminalBoundaryWire_eq_true_iff, terminalBoundaryWire_eq_true_iff, external_forward]
  constructor
  · rintro ⟨external, consumer, _enumerated, selected, uses⟩
    refine ⟨external, backwardGate original.program relabeling consumer, mem_allFin _, ?_, ?_⟩
    · have selectedSame := selected_forward original.program relabeling records
        (backwardGate original.program relabeling consumer)
      rw [forward_backward] at selectedSame
      exact selectedSame.symm.trans selected
    · have incidence := uses_forward original relabeling
        (backwardGate original.program relabeling consumer) wire
      rw [forward_backward] at incidence
      exact incidence.symm.trans uses
  · rintro ⟨external, consumer, _enumerated, selected, uses⟩
    exact ⟨external, forwardGate original.program relabeling consumer, mem_allFin _,
      (selected_forward original.program relabeling records consumer).trans selected,
      (uses_forward original relabeling consumer wire).trans uses⟩

theorem externalConsumer_forward (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (producer : Fin gates) :
    terminalGateHasExternalConsumer (result original relabeling).program
        (forwardRecords original.program relabeling records)
        (forwardGate original.program relabeling producer) =
      terminalGateHasExternalConsumer original.program records producer := by
  apply bool_eq_of_true_iff
  rw [terminalGateHasExternalConsumer_eq_true_iff, terminalGateHasExternalConsumer_eq_true_iff]
  constructor
  · rintro ⟨consumer, _enumerated, selected, uses⟩
    refine ⟨backwardGate original.program relabeling consumer, mem_allFin _, ?_, ?_⟩
    · have selectedSame := selected_forward original.program relabeling records
        (backwardGate original.program relabeling consumer)
      rw [forward_backward] at selectedSame
      exact selectedSame.symm.trans selected
    · have incidence := uses_forward original relabeling
        (backwardGate original.program relabeling consumer) (.gate producer)
      rw [forward_backward] at incidence
      exact incidence.symm.trans uses
  · rintro ⟨consumer, _enumerated, selected, uses⟩
    exact ⟨forwardGate original.program relabeling consumer, mem_allFin _,
      (selected_forward original.program relabeling records consumer).trans selected,
      (uses_forward original relabeling consumer (.gate producer)).trans uses⟩

theorem globalOutput_forward (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates) (producer : Fin gates) :
    terminalGateIsGlobalOutput (result original relabeling).directWireWord
        (forwardGate original.program relabeling producer) =
      terminalGateIsGlobalOutput original.directWireWord producer := by
  apply bool_eq_of_true_iff
  rw [terminalGateIsGlobalOutput_eq_true_iff, terminalGateIsGlobalOutput_eq_true_iff]
  constructor
  · rintro ⟨output, same⟩
    refine ⟨output, ?_⟩
    rw [result_output_source] at same
    change sourceMap (forwardGate original.program relabeling) (original.directWireWord.source output) =
      sourceMap (forwardGate original.program relabeling) (.gate producer) at same
    exact sourceMap_forward_injective original.program relabeling same
  · rintro ⟨output, same⟩
    refine ⟨output, ?_⟩
    rw [result_output_source, same]
    rfl

theorem interface_forward (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (producer : Fin gates) :
    terminalInterfaceGate (result original relabeling)
        (forwardRecords original.program relabeling records)
        (forwardGate original.program relabeling producer) =
      terminalInterfaceGate original records producer := by
  unfold terminalInterfaceGate
  rw [selected_forward, externalConsumer_forward, globalOutput_forward]

theorem boundary_ports_forward (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (wire : TerminalSupportWire inputs gates) :
    forwardWire original.program relabeling wire ∈
        terminalBoundaryPorts (result original relabeling).program
          (forwardRecords original.program relabeling records) ↔
      wire ∈ terminalBoundaryPorts original.program records := by
  rw [mem_terminalBoundaryPorts_iff, mem_terminalBoundaryPorts_iff, boundary_forward]

theorem interface_ports_forward (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (producer : Fin gates) :
    forwardGate original.program relabeling producer ∈
        terminalInterfacePorts (result original relabeling)
          (forwardRecords original.program relabeling records) ↔
      producer ∈ terminalInterfacePorts original records := by
  rw [mem_terminalInterfacePorts_iff, mem_terminalInterfacePorts_iff, interface_forward]

/-- Pull back every actual descendant boundary, with no supplied coverage data. -/
theorem descendant_boundary (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates)
    (records : List
      (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))
    (wire : TerminalSupportWire inputs (compiled original.program relabeling).count) :
    wire ∈ terminalBoundaryPorts (result original relabeling).program records ↔
      backwardWire original.program relabeling wire ∈
        terminalBoundaryPorts original.program (backwardRecords original.program relabeling records) := by
  have same := boundary_ports_forward original relabeling
    (backwardRecords original.program relabeling records)
    (backwardWire original.program relabeling wire)
  rw [forward_backward_records, forward_backward_wire] at same
  exact same

/-- Pull back every actual descendant interface, including actual global outputs. -/
theorem descendant_interface (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates)
    (records : List
      (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))
    (producer : Fin (compiled original.program relabeling).count) :
    producer ∈ terminalInterfacePorts (result original relabeling) records ↔
      backwardGate original.program relabeling producer ∈
        terminalInterfacePorts original (backwardRecords original.program relabeling records) := by
  have same := interface_ports_forward original relabeling
    (backwardRecords original.program relabeling records)
    (backwardGate original.program relabeling producer)
  rw [forward_backward_records, forward_backward] at same
  exact same

end PNP.DirectWire.StructuralReindexing
