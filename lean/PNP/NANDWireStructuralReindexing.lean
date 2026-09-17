/-
Copyright (c) 2026 PNP Labs.

Reindex the actual exposed circuit, then recover every ordinary output and
literal computational field. Physical gate maps and causal labels come from
the real structural compiler. No observation function or transport map is
supplied as a substitute for the construction.

This is computational wire-carrier transport, not full manuscript profiles,
global certificate discovery, unconditional ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDReindexingCausalBounds
import PNP.NANDWireCausalBounds

namespace PNP.DirectWire.WireCarrier

open StructuralReindexing

variable {inputs outputs fields : Nat}

def reindex (carrier : WireCarrier inputs outputs fields)
    (relabeling : GateRenaming carrier.implementation.gateCount) :
    WireCarrier inputs outputs fields :=
  unpack (result carrier.exposed.candidate relabeling).toImplementation

theorem reindex_exposed (carrier : WireCarrier inputs outputs fields)
    (relabeling : GateRenaming carrier.implementation.gateCount) :
    (carrier.reindex relabeling).exposed =
      (result carrier.exposed.candidate relabeling).toImplementation :=
  exposed_unpack _

theorem reindex_gateCount (carrier : WireCarrier inputs outputs fields)
    (relabeling : GateRenaming carrier.implementation.gateCount) :
    (carrier.reindex relabeling).implementation.gateCount =
      carrier.implementation.gateCount :=
  result_gateCount carrier.exposed.candidate relabeling

def reindexForwardGate (carrier : WireCarrier inputs outputs fields)
    (relabeling : GateRenaming carrier.implementation.gateCount) :
    Fin carrier.implementation.gateCount →
      Fin (carrier.reindex relabeling).implementation.gateCount :=
  forwardGate carrier.exposed.candidate.program relabeling

def reindexBackwardGate (carrier : WireCarrier inputs outputs fields)
    (relabeling : GateRenaming carrier.implementation.gateCount) :
    Fin (carrier.reindex relabeling).implementation.gateCount →
      Fin carrier.implementation.gateCount :=
  backwardGate carrier.exposed.candidate.program relabeling

theorem reindex_backward_forward (carrier : WireCarrier inputs outputs fields)
    (relabeling : GateRenaming carrier.implementation.gateCount)
    (gate : Fin carrier.implementation.gateCount) :
    carrier.reindexBackwardGate relabeling (carrier.reindexForwardGate relabeling gate) =
      gate :=
  backward_forward carrier.exposed.candidate.program relabeling gate

theorem reindex_forward_backward (carrier : WireCarrier inputs outputs fields)
    (relabeling : GateRenaming carrier.implementation.gateCount)
    (gate : Fin (carrier.reindex relabeling).implementation.gateCount) :
    carrier.reindexForwardGate relabeling (carrier.reindexBackwardGate relabeling gate) =
      gate :=
  forward_backward carrier.exposed.candidate.program relabeling gate

theorem reindex_output (carrier : WireCarrier inputs outputs fields)
    (relabeling : GateRenaming carrier.implementation.gateCount)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (carrier.reindex relabeling).implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output :=
  (unpack_output _ valuation output).trans
    ((result_semantics carrier.exposed.candidate relabeling valuation
      (Fin.castAdd fields output)).trans (carrier.exposed_output valuation output))

theorem reindex_field (carrier : WireCarrier inputs outputs fields)
    (relabeling : GateRenaming carrier.implementation.gateCount)
    (valuation : Valuation inputs) (field : Fin fields) :
    (carrier.reindex relabeling).fieldValue valuation field =
      carrier.fieldValue valuation field :=
  (unpack_field _ valuation field).trans
    ((result_semantics carrier.exposed.candidate relabeling valuation
      (Fin.natAdd outputs field)).trans (carrier.exposed_field valuation field))

/-- The field is an actual rebound wire, not just an equal Boolean observer. -/
theorem reindex_field_source (carrier : WireCarrier inputs outputs fields)
    (relabeling : GateRenaming carrier.implementation.gateCount) (field : Fin fields) :
    (carrier.reindex relabeling).source field =
      sourceMap (carrier.reindexForwardGate relabeling) (carrier.source field) := by
  change (result carrier.exposed.candidate relabeling).directWireWord.source
      (Fin.natAdd outputs field) = _
  rw [result_output_source, exposed_field_source]
  rfl

theorem reindex_exposed_level (carrier : WireCarrier inputs outputs fields)
    (relabeling : GateRenaming carrier.implementation.gateCount)
    (labels : Fin inputs → Nat) (observation : Fin (outputs + fields)) :
    CausalBound.outputLevel (carrier.reindex relabeling).exposed.candidate labels observation =
      CausalBound.outputLevel carrier.exposed.candidate labels observation := by
  rw [reindex_exposed]
  exact result_output_level carrier.exposed.candidate relabeling labels observation

theorem reindex_output_level (carrier : WireCarrier inputs outputs fields)
    (relabeling : GateRenaming carrier.implementation.gateCount)
    (labels : Fin inputs → Nat) (output : Fin outputs) :
    CausalBound.outputLevel (carrier.reindex relabeling).implementation.candidate labels output =
      CausalBound.outputLevel carrier.implementation.candidate labels output := by
  simpa only [exposed_output_level] using
    reindex_exposed_level carrier relabeling labels (Fin.castAdd fields output)

theorem reindex_field_level (carrier : WireCarrier inputs outputs fields)
    (relabeling : GateRenaming carrier.implementation.gateCount)
    (labels : Fin inputs → Nat) (field : Fin fields) :
    (carrier.reindex relabeling).fieldLevel labels field = carrier.fieldLevel labels field := by
  simpa only [exposed_field_level] using
    reindex_exposed_level carrier relabeling labels (Fin.natAdd outputs field)

theorem reindex_causalBounds (carrier : WireCarrier inputs outputs fields)
    (relabeling : GateRenaming carrier.implementation.gateCount)
    (labels : Fin inputs → Nat) (outputCaps : Fin outputs → Nat)
    (fieldCaps : Fin fields → Nat)
    (bounded : carrier.CausalBounds labels outputCaps fieldCaps) :
    (carrier.reindex relabeling).CausalBounds labels outputCaps fieldCaps := by
  constructor
  · intro output
    rw [reindex_output_level]
    exact bounded.1 output
  · intro field
    rw [reindex_field_level]
    exact bounded.2 field

end PNP.DirectWire.WireCarrier
