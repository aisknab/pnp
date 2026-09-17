import PNP.NANDReindexingCausalBounds

open PNP.DirectWire
open PNP.DirectWire.StructuralReindexing
open PNP.DirectWire.CausalBound

-- Arbitrary dimensions, raw-derived reindexing and independent causal labels.
example {inputs gates outputs : Nat} (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates) (labels : Fin inputs → Nat) (gate : Fin gates) :
    levels (result original relabeling).program labels
        (forwardGate original.program relabeling gate) =
      levels original.program labels gate :=
  result_gate_level original relabeling labels gate

example {inputs gates outputs : Nat} (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates) (labels : Fin inputs → Nat)
    (wire : Source inputs gates) :
    source (sourceMap (forwardGate original.program relabeling) wire)
        labels (levels (result original relabeling).program labels) =
      source wire labels (levels original.program labels) :=
  result_source_level original relabeling labels wire

example {inputs gates outputs : Nat} (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates) (labels : Fin inputs → Nat) (output : Fin outputs) :
    source ((result original relabeling).directWireWord.source output)
        labels (levels (result original relabeling).program labels) =
      source (original.directWireWord.source output)
        labels (levels original.program labels) :=
  result_output_level original relabeling labels output

#print axioms PNP.DirectWire.StructuralReindexing.result_gate_level
#print axioms PNP.DirectWire.StructuralReindexing.result_source_level
#print axioms PNP.DirectWire.StructuralReindexing.result_output_level
