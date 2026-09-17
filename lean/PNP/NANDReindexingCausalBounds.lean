/-
Copyright (c) 2026 PNP Labs.

Exact syntactic causal-label preservation under the computed structural
reindexer. Labels are arbitrary natural numbers on original input coordinates;
the theorem follows from actual source wiring, not Boolean equivalence.

This is an integration prerequisite for structural actions in complete
replacement programs. It does not establish full manuscript profiles,
global certificate discovery, unconditional ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDStructuralReindexing
import PNP.NANDNormalizationCausalBounds

namespace PNP.DirectWire.StructuralReindexing

open GateRenaming
open CausalBound

variable {inputs gates outputs : Nat}

/-- Every actual reordered gate has exactly its original causal label. -/
theorem result_gate_level (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates) (labels : Fin inputs → Nat) (node : Fin gates) :
    levels (result original relabeling).program labels
        (forwardGate original.program relabeling node) =
      levels original.program labels node := by
  have allLevels : ∀ n, ∀ index : Fin gates, index.val < n →
      levels (result original relabeling).program labels
          (forwardGate original.program relabeling index) =
        levels original.program labels index := by
    intro n
    induction n with
    | zero =>
        intro index within
        exact False.elim (Nat.not_lt_zero _ within)
    | succ n ih =>
        intro index within
        have sameSource (wire : Source inputs gates)
            (occurs : (original.program.terminalGateSources index).1 = wire ∨
              (original.program.terminalGateSources index).2 = wire) :
            source (sourceMap (forwardGate original.program relabeling) wire)
                labels (levels (result original relabeling).program labels) =
              source wire labels (levels original.program labels) := by
          cases wire with
          | input input => rfl
          | constant value => rfl
          | gate earlier =>
              have before := ArbitrarySupportSplice.sources_ordered
                original.program index earlier occurs
              exact ih earlier (by omega)
        calc
          levels (result original relabeling).program labels
              (forwardGate original.program relabeling index) =
              max (source ((result original relabeling).program.terminalGateSources
                    (forwardGate original.program relabeling index)).1
                  labels (levels (result original relabeling).program labels))
                (source ((result original relabeling).program.terminalGateSources
                    (forwardGate original.program relabeling index)).2
                  labels (levels (result original relabeling).program labels)) :=
            (terminal_sources_level (result original relabeling).program labels
              (forwardGate original.program relabeling index)).symm
          _ = max
              (source (sourceMap (forwardGate original.program relabeling)
                  (original.program.terminalGateSources index).1)
                labels (levels (result original relabeling).program labels))
              (source (sourceMap (forwardGate original.program relabeling)
                  (original.program.terminalGateSources index).2)
                labels (levels (result original relabeling).program labels)) := by
            rw [result_sources]
          _ = max (source (original.program.terminalGateSources index).1
                  labels (levels original.program labels))
                (source (original.program.terminalGateSources index).2
                  labels (levels original.program labels)) := by
            rw [sameSource _ (Or.inl rfl), sameSource _ (Or.inr rfl)]
          _ = levels original.program labels index :=
            terminal_sources_level original.program labels index
  exact allLevels gates node node.isLt

/-- Actual renamed inputs, constants and gate wires retain their causal labels. -/
theorem result_source_level (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates) (labels : Fin inputs → Nat)
    (wire : Source inputs gates) :
    source (sourceMap (forwardGate original.program relabeling) wire)
        labels (levels (result original relabeling).program labels) =
      source wire labels (levels original.program labels) := by
  cases wire with
  | input index => rfl
  | constant value => rfl
  | gate index => exact result_gate_level original relabeling labels index

/-- Each actual ordered output retains its syntactic input-dependency bound. -/
theorem result_output_level (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates) (labels : Fin inputs → Nat)
    (output : Fin outputs) :
    source ((result original relabeling).directWireWord.source output)
        labels (levels (result original relabeling).program labels) =
      source (original.directWireWord.source output)
        labels (levels original.program labels) := by
  rw [result_output_source]
  exact result_source_level original relabeling labels _

end PNP.DirectWire.StructuralReindexing
