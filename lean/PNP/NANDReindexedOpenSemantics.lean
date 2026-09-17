/-
Copyright (c) 2026 PNP Labs.

Preserve the independent open function of every arbitrary descendant support
through the actual structural reindexer. Boundary and interface positions are
the computed bijections, including nonidentity permutations. The proof follows
literal gate sources in the original causal order for all boundary valuations.

This establishes physical open semantics, not full manuscript profiles,
literal replacement transport, matched surcharge or global normalization.
-/

import PNP.NANDReindexedPorts

namespace PNP.DirectWire.StructuralReindexing

variable {inputs gates outputs profileWidth : Nat}
variable (original : Candidate inputs gates outputs) (relabeling : GateRenaming gates)
variable (records : List
  (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))
variable (valuation : Valuation
  (terminalBoundaryPorts original.program (backwardRecords original.program relabeling records)).length)

/-- Every external wire reads the same independently chosen bit after reindexing. -/
theorem external_wire_value_preserved (wire : TerminalSupportWire inputs gates)
    (external : terminalWireExternal (backwardRecords original.program relabeling records) wire = true) :
    terminalOpenWireValue (result original relabeling) records
        (pushBoundaryValuation original relabeling records valuation)
        (forwardWire original.program relabeling wire) =
      terminalOpenWireValue original (backwardRecords original.program relabeling records)
        valuation wire := by
  have externalNew :
      terminalWireExternal records (forwardWire original.program relabeling wire) = true := by
    have same := external_forward original.program relabeling
      (backwardRecords original.program relabeling records) wire
    rw [forward_backward_records] at same
    exact same.trans external
  by_cases member : wire ∈ terminalBoundaryPorts original.program
      (backwardRecords original.program relabeling records)
  · obtain ⟨index, bound, atIndex⟩ := List.mem_iff_getElem.mp member
    let position : Fin (terminalBoundaryPorts original.program
        (backwardRecords original.program relabeling records)).length := ⟨index, bound⟩
    have oldAt : (terminalBoundaryPorts original.program
        (backwardRecords original.program relabeling records)).get position = wire := atIndex
    have newAt := (boundaryPorts original relabeling records).forward_get position
    rw [oldAt] at newAt
    rw [← newAt, terminalOpenWireValue_boundary_get]
    change valuation ((boundaryPorts original relabeling records).backward
      ((boundaryPorts original relabeling records).forward position)) = _
    rw [(boundaryPorts original relabeling records).backward_forward,
      ← oldAt, terminalOpenWireValue_boundary_get]
  · have absentNew : forwardWire original.program relabeling wire ∉
        terminalBoundaryPorts (result original relabeling).program records := by
      intro present
      have oldMember := (descendant_boundary original relabeling records
        (forwardWire original.program relabeling wire)).mp present
      rw [backward_forward_wire] at oldMember
      exact member oldMember
    rw [terminalOpenWireValue_external_absent (result original relabeling) records
      (pushBoundaryValuation original relabeling records valuation)
      (forwardWire original.program relabeling wire) externalNew absentNew,
      terminalOpenWireValue_external_absent original
        (backwardRecords original.program relabeling records) valuation wire external member]

/-- All gate coordinates agree for all independent predecessor-boundary inputs. -/
theorem open_gate_preserved (node : Fin gates) :
    terminalOpenGateEvaluation (result original relabeling) records
        (pushBoundaryValuation original relabeling records valuation)
        (forwardGate original.program relabeling node) =
      terminalOpenGateEvaluation original
        (backwardRecords original.program relabeling records) valuation node := by
  have selectedSame (producer : Fin gates) :
      terminalGateSelected records (forwardGate original.program relabeling producer) =
        terminalGateSelected (backwardRecords original.program relabeling records) producer := by
    have same := selected_backward original relabeling records
      (forwardGate original.program relabeling producer)
    rw [backward_forward] at same
    exact same.symm
  have sourceSame (source : Source inputs gates)
      (ordered : ∀ producer, source = .gate producer → producer.val < node.val) :
      terminalOpenSourceValue (result original relabeling) records
          (pushBoundaryValuation original relabeling records valuation)
          (sourceMap (forwardGate original.program relabeling) source) =
        terminalOpenSourceValue original
          (backwardRecords original.program relabeling records) valuation source := by
    cases source with
    | input index =>
        exact external_wire_value_preserved original relabeling records valuation (.input index) rfl
    | constant value => rfl
    | gate producer =>
        cases selected : terminalGateSelected
            (backwardRecords original.program relabeling records) producer with
        | false =>
            have external :
                terminalWireExternal (backwardRecords original.program relabeling records)
                  (.gate producer) = true := by
              change (!terminalGateSelected
                (backwardRecords original.program relabeling records) producer) = true
              rw [selected]
              rfl
            exact external_wire_value_preserved original relabeling records valuation
              (.gate producer) external
        | true =>
            have selectedNew := (selectedSame producer).trans selected
            simp only [sourceMap, terminalOpenSourceValue, terminalOpenWireValue,
              selectedNew, selected, if_true]
            exact open_gate_preserved producer
  rw [terminalOpenGateEvaluation_sourceEquation, terminalOpenGateEvaluation_sourceEquation,
    result_sources, selectedSame]
  have leftSame := sourceSame (original.program.terminalGateSources node).1
    (fun producer same => ArbitrarySupportSplice.sources_ordered original.program node producer
      (Or.inl same))
  have rightSame := sourceSame (original.program.terminalGateSources node).2
    (fun producer same => ArbitrarySupportSplice.sources_ordered original.program node producer
      (Or.inr same))
  rw [leftSame, rightSame]
termination_by node.val
decreasing_by exact ordered producer rfl

/-- The full ordered open support function is preserved with both port maps explicit. -/
theorem open_support_preserved
    (output : Fin (terminalInterfacePorts original
      (backwardRecords original.program relabeling records)).length) :
    terminalOpenSupportSemantics (result original relabeling) records
        (pushBoundaryValuation original relabeling records valuation)
        ((interfacePorts original relabeling records).forward output) =
      terminalOpenSupportSemantics original
        (backwardRecords original.program relabeling records) valuation output := by
  unfold terminalOpenSupportSemantics
  rw [(interfacePorts original relabeling records).forward_get]
  exact open_gate_preserved original relabeling records valuation _

/-- Equivalent descendant-facing form covers every descendant-boundary valuation. -/
theorem open_support_pullback
    (descendantValuation :
      Valuation (terminalBoundaryPorts (result original relabeling).program records).length)
    (output : Fin (terminalInterfacePorts (result original relabeling) records).length) :
    terminalOpenSupportSemantics original (backwardRecords original.program relabeling records)
        (pullBoundaryValuation original relabeling records descendantValuation)
        ((interfacePorts original relabeling records).backward output) =
      terminalOpenSupportSemantics (result original relabeling) records descendantValuation output := by
  have same := open_support_preserved original relabeling records
    (pullBoundaryValuation original relabeling records descendantValuation)
    ((interfacePorts original relabeling records).backward output)
  rw [push_pull_boundary_valuation, (interfacePorts original relabeling records).forward_backward] at same
  exact same.symm

/-- The actual extracted direct-wire candidates realize this same open correspondence. -/
theorem extracted_support_preserved
    (output : Fin (terminalInterfacePorts original
      (backwardRecords original.program relabeling records)).length) :
    (extractTerminalSupport (result original relabeling) records).extractedCandidate.semantics
        (pushBoundaryValuation original relabeling records valuation)
        ((interfacePorts original relabeling records).forward output) =
      (extractTerminalSupport original
        (backwardRecords original.program relabeling records)).extractedCandidate.semantics
          valuation output :=
  (extractTerminalSupport_semantics (result original relabeling) records
    (pushBoundaryValuation original relabeling records valuation)
    ((interfacePorts original relabeling records).forward output)).trans
      ((open_support_preserved original relabeling records valuation output).trans
        (extractTerminalSupport_semantics original
          (backwardRecords original.program relabeling records) valuation output).symm)

end PNP.DirectWire.StructuralReindexing
