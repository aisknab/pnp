/-
Copyright (c) 2026 PNP Labs.

Record-width transport for the actual physical extractor and splice compiler.
Gate requests retain their original order and duplicates. The gate-only view
does not replace the original record ledger: restoring that ledger recovers
the entire computed extraction, including its literal program and outputs.

Equal physical selection is not full profile-observer congruence. This module
does not prove properness, full-span validity, global routing or a lower bound.
-/

import PNP.NANDArbitrarySupportSplice

set_option autoImplicit false

namespace PNP.DirectWire.SupportRecordTransport

variable {inputs gates outputs fromWidth toWidth replacementGates : Nat}

def gateRequest : TerminalPrimitiveRecord inputs gates outputs fromWidth → Option (Fin gates)
  | .gate node => some node
  | .boundary _ => none
  | .interface _ => none
  | .profile _ => none

/-- Preserve repeated requests and their order; do not turn the ledger into a set. -/
def gateRequests (records : List (TerminalPrimitiveRecord inputs gates outputs fromWidth)) :
    List (Fin gates) := records.filterMap gateRequest

def gateOnly (records : List (TerminalPrimitiveRecord inputs gates outputs fromWidth)) :
    List (TerminalPrimitiveRecord inputs gates outputs 0) :=
  (gateRequests records).map TerminalPrimitiveRecord.gate

theorem gateRequests_mem
    (records : List (TerminalPrimitiveRecord inputs gates outputs fromWidth)) (node : Fin gates) :
    node ∈ gateRequests records ↔ TerminalPrimitiveRecord.gate node ∈ records := by
  constructor
  · intro member
    obtain ⟨record, present, found⟩ := List.mem_filterMap.mp member
    cases record with
    | gate index =>
        have equal := Option.some.inj found
        subst index
        exact present
    | boundary index => cases found
    | interface index => cases found
    | profile index => cases found
  · intro present
    exact List.mem_filterMap.mpr ⟨.gate node, present, rfl⟩

theorem gateOnly_selected
    (records : List (TerminalPrimitiveRecord inputs gates outputs fromWidth)) :
    terminalGateSelected (gateOnly records) = terminalGateSelected records := by
  funext node
  have matching : terminalGateSelected (gateOnly records) node = true ↔
      terminalGateSelected records node = true := by
    rw [terminalGateSelected_eq_true_iff, terminalGateSelected_eq_true_iff]
    constructor
    · intro member
      obtain ⟨prior, present, same⟩ := List.mem_map.mp member
      have equal := TerminalPrimitiveRecord.gate.inj same
      subst prior
      exact (gateRequests_mem records node).mp present
    · intro member
      exact List.mem_map.mpr ⟨node, (gateRequests_mem records node).mpr member, rfl⟩
  cases leftAt : terminalGateSelected (gateOnly records) node with
  | false =>
      cases rightAt : terminalGateSelected records node with
      | false => rfl
      | true =>
          have impossible := matching.mpr rightAt
          rw [leftAt] at impossible
          cases impossible
  | true => exact (matching.mp leftAt).symm

theorem gateOnly_recovery (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs fromWidth)) :
    (extractTerminalSupport candidate (gateOnly records)).withRecords records =
      extractTerminalSupport candidate records :=
  extractTerminalSupport_withRecords_of_gateSelected_eq candidate _ _ (gateOnly_selected records)

variable (candidate : Candidate inputs gates outputs)
variable (left : List (TerminalPrimitiveRecord inputs gates outputs fromWidth))
variable (right : List (TerminalPrimitiveRecord inputs gates outputs toWidth))
variable (same : terminalGateSelected left = terminalGateSelected right)

include same in
theorem boundary_eq :
    terminalBoundaryPorts candidate.program left = terminalBoundaryPorts candidate.program right := by
  rw [terminalBoundaryPorts_reference, terminalBoundaryPorts_reference]
  apply congrArg (fun predicate => (allTerminalSupportWires inputs gates).filter predicate)
  funext wire
  unfold terminalBoundaryWire
  cases wire <;> simp only [terminalWireExternal, same]

include same in
theorem interface_eq :
    terminalInterfacePorts candidate left = terminalInterfacePorts candidate right := by
  unfold terminalInterfacePorts
  apply congrArg (fun predicate => (allFin gates).filter predicate)
  funext producer
  simp only [terminalInterfaceGate, terminalGateHasExternalConsumer, same]

include same in
theorem exterior_eq : ArbitrarySupportSplice.exterior left = ArbitrarySupportSplice.exterior right := by
  simp only [ArbitrarySupportSplice.exterior, same]

private theorem candidateTypeEq {beforeInputs afterInputs beforeOutputs afterOutputs : Nat}
    (incoming : beforeInputs = afterInputs) (outgoing : beforeOutputs = afterOutputs) :
    Candidate beforeInputs replacementGates beforeOutputs =
      Candidate afterInputs replacementGates afterOutputs := by
  cases incoming
  cases outgoing
  rfl

def offerTypeEq :
    Candidate (terminalBoundaryPorts candidate.program left).length replacementGates
        (terminalInterfacePorts candidate left).length =
      Candidate (terminalBoundaryPorts candidate.program right).length replacementGates
        (terminalInterfacePorts candidate right).length :=
  candidateTypeEq
    (congrArg List.length (boundary_eq candidate left right same))
    (congrArg List.length (interface_eq candidate left right same))

def transportOffer
    (offered : Candidate (terminalBoundaryPorts candidate.program left).length replacementGates
      (terminalInterfacePorts candidate left).length) :
    Candidate (terminalBoundaryPorts candidate.program right).length replacementGates
      (terminalInterfacePorts candidate right).length :=
  Eq.mp (offerTypeEq candidate left right same) offered

private theorem compatibility_cast
    {width : Nat} (first last : TerminalExtractedSupport (profileWidth := width) candidate)
    (equal : first = last)
    (offered : Candidate first.boundary.length replacementGates first.interface.length)
    (compatible : offered.semantics = first.extractedCandidate.semantics) :
    (Eq.mp (candidateTypeEq (replacementGates := replacementGates)
      (congrArg (fun support => support.boundary.length) equal)
      (congrArg (fun support => support.interface.length) equal)) offered).semantics =
        last.extractedCandidate.semantics := by
  cases equal
  exact compatible

theorem transport_compatible
    (offered : Candidate (terminalBoundaryPorts candidate.program left).length replacementGates
      (terminalInterfacePorts candidate left).length)
    (compatible : offered.semantics = (extractTerminalSupport candidate left).extractedCandidate.semantics) :
    (transportOffer candidate left right same offered).semantics =
      (extractTerminalSupport candidate right).extractedCandidate.semantics :=
  compatibility_cast candidate
    ((extractTerminalSupport candidate left).withRecords right) (extractTerminalSupport candidate right)
    (extractTerminalSupport_withRecords_of_gateSelected_eq candidate left right same) offered compatible

variable (offered : Candidate (terminalBoundaryPorts candidate.program left).length replacementGates
  (terminalInterfacePorts candidate left).length)

private theorem transported_heq {alpha beta : Type} (equal : alpha = beta) (value : alpha) :
    HEq value (Eq.mp equal value) := by
  cases equal
  rfl

/-- Literal raw graph identity, not merely equality of Boolean behavior. -/
theorem graph_heq :
    HEq (ArbitrarySupportSplice.graph candidate left offered)
      (ArbitrarySupportSplice.graph candidate right (transportOffer candidate left right same offered)) :=
  (ArbitrarySupportSplice.graph_word_heq_of_physical_data candidate left offered right same
    (boundary_eq candidate left right same) (interface_eq candidate left right same)
    (exterior_eq left right same) _ (transported_heq _ offered)).1

theorem word_heq :
    HEq (ArbitrarySupportSplice.word candidate left offered)
      (ArbitrarySupportSplice.word candidate right (transportOffer candidate left right same offered)) :=
  (ArbitrarySupportSplice.graph_word_heq_of_physical_data candidate left offered right same
    (boundary_eq candidate left right same) (interface_eq candidate left right same)
    (exterior_eq left right same) _ (transported_heq _ offered)).2

private theorem compiler_congr {before after : Nat} (countEq : before = after)
    (first : RawNandGraph inputs before) (last : RawNandGraph inputs after) (sameGraph : HEq first last) :
    HEq (compileRawNandGraph first) (compileRawNandGraph last) ∧
      (compileRawNandGraph first).isSome = (compileRawNandGraph last).isSome := by
  cases countEq
  have equal := eq_of_heq sameGraph
  cases equal
  exact ⟨HEq.rfl, rfl⟩

theorem compile_heq :
    HEq (ArbitrarySupportSplice.compile candidate left offered)
      (ArbitrarySupportSplice.compile candidate right (transportOffer candidate left right same offered)) :=
  (compiler_congr
    (congrArg (fun nodes : List (Fin gates) => nodes.length + replacementGates)
      (exterior_eq left right same)) _ _ (graph_heq candidate left right same offered)).1

theorem compile_isSome :
    (ArbitrarySupportSplice.compile candidate left offered).isSome =
      (ArbitrarySupportSplice.compile candidate right
        (transportOffer candidate left right same offered)).isSome :=
  (compiler_congr
    (congrArg (fun nodes : List (Fin gates) => nodes.length + replacementGates)
      (exterior_eq left right same)) _ _ (graph_heq candidate left right same offered)).2

end PNP.DirectWire.SupportRecordTransport
