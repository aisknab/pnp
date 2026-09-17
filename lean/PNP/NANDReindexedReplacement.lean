/-
Copyright (c) 2026 PNP Labs.

Construct an actual predecessor replacement from every descendant replacement,
using only the computed boundary and interface index bijections. The literal
program retains every offered gate at its original coordinate; only primary
inputs and ordered output references are rewired. No padding is introduced.

All independent open semantics and exact physical savings transport. These
results do not assert that every compatible literal splice is acyclic, and do
not establish the remaining manuscript profile or materializer obligations.
-/

import PNP.NANDReindexedOpenSemantics

namespace PNP.DirectWire.StructuralReindexing

private theorem renameInputs_weaken {fromInputs toInputs gates : Nat}
    (source : Source fromInputs gates) (rename : Fin fromInputs → Fin toInputs) :
    (source.renameInputs rename).weakenGates 1 =
      (source.weakenGates 1).renameInputs rename := by
  cases source <;> rfl

/-- Renaming inputs changes exactly the input references of each literal gate. -/
theorem renameInputs_gateSources {fromInputs toInputs gates : Nat}
    (program : Program fromInputs gates) (rename : Fin fromInputs → Fin toInputs)
    (node : Fin gates) :
    (program.renameInputs rename).terminalGateSources node =
      ((program.terminalGateSources node).1.renameInputs rename,
        (program.terminalGateSources node).2.renameInputs rename) := by
  induction program with
  | empty => exact Fin.elim0 node
  | @snoc gates initial gate ih =>
      by_cases earlier : node.val < gates
      · simp only [Program.renameInputs, Program.terminalGateSources, dif_pos earlier]
        rw [ih]
        exact Prod.ext (renameInputs_weaken _ _) (renameInputs_weaken _ _)
      · simp only [Program.renameInputs, Program.terminalGateSources, dif_neg earlier,
          Gate.renameInputs]
        exact Prod.ext (renameInputs_weaken _ _) (renameInputs_weaken _ _)

variable {inputs gates outputs profileWidth replacementGates : Nat}
variable (original : Candidate inputs gates outputs) (relabeling : GateRenaming gates)
variable (records : List
  (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))
variable (offered : Candidate
  (terminalBoundaryPorts (result original relabeling).program records).length replacementGates
  (terminalInterfacePorts (result original relabeling) records).length)

/-- Actual replacement expansion: computed input and output rewiring, no new gate. -/
def pullReplacement : Candidate
    (terminalBoundaryPorts original.program
      (backwardRecords original.program relabeling records)).length replacementGates
    (terminalInterfacePorts original (backwardRecords original.program relabeling records)).length :=
  Candidate.ofDirectWireWord
    (offered.program.renameInputs (boundaryPorts original relabeling records).backward)
    ⟨fun output =>
      (offered.directWireWord.source ((interfacePorts original relabeling records).forward output)).renameInputs
        (boundaryPorts original relabeling records).backward⟩

theorem pullReplacement_program :
    (pullReplacement original relabeling records offered).program =
      offered.program.renameInputs (boundaryPorts original relabeling records).backward := rfl

/-- Every replacement gate keeps its coordinate and its exact translated sources. -/
theorem pullReplacement_gate_sources (node : Fin replacementGates) :
    (pullReplacement original relabeling records offered).program.terminalGateSources node =
      ((offered.program.terminalGateSources node).1.renameInputs
          (boundaryPorts original relabeling records).backward,
        (offered.program.terminalGateSources node).2.renameInputs
          (boundaryPorts original relabeling records).backward) :=
  renameInputs_gateSources offered.program _ node

/-- Output positions are reindexed as well as their primary-input references. -/
theorem pullReplacement_output_source
    (output : Fin (terminalInterfacePorts original
      (backwardRecords original.program relabeling records)).length) :
    (pullReplacement original relabeling records offered).directWireWord.source output =
      (offered.directWireWord.source ((interfacePorts original relabeling records).forward output)).renameInputs
        (boundaryPorts original relabeling records).backward := by
  unfold pullReplacement
  exact Candidate.ofDirectWireWord_pointwise _ _ _

theorem pullReplacement_gate_count :
    (pullReplacement original relabeling records offered).toImplementation.gateCount =
      offered.toImplementation.gateCount := rfl

/-- Every independent input valuation and every ordered output is covered. -/
theorem pullReplacement_semantics
    (valuation : Valuation (terminalBoundaryPorts original.program
      (backwardRecords original.program relabeling records)).length)
    (output : Fin (terminalInterfacePorts original
      (backwardRecords original.program relabeling records)).length) :
    (pullReplacement original relabeling records offered).semantics valuation output =
      offered.semantics (pushBoundaryValuation original relabeling records valuation)
        ((interfacePorts original relabeling records).forward output) := by
  unfold pullReplacement
  rw [Candidate.ofDirectWireWord_semantics]
  have values :
      (offered.program.renameInputs (boundaryPorts original relabeling records).backward).eval
          valuation =
        offered.program.eval (pushBoundaryValuation original relabeling records valuation) := by
    funext node
    exact Program.eval_renameInputs offered.program _ valuation node
  change ((offered.directWireWord.source
      ((interfacePorts original relabeling records).forward output)).renameInputs
        (boundaryPorts original relabeling records).backward).eval valuation
          ((offered.program.renameInputs
            (boundaryPorts original relabeling records).backward).eval valuation) = _
  rw [values, Source.eval_renameInputs]
  rfl

/-- A compatible offered replacement produces a compatible predecessor replacement. -/
theorem pullReplacement_compatible
    (equivalent : offered.semantics =
      (extractTerminalSupport (result original relabeling) records).extractedCandidate.semantics) :
    (pullReplacement original relabeling records offered).semantics =
      (extractTerminalSupport original
        (backwardRecords original.program relabeling records)).extractedCandidate.semantics := by
  funext valuation output
  rw [pullReplacement_semantics, equivalent]
  exact extracted_support_preserved original relabeling records valuation output

/-- The actual extracted supports, not a containing circuit, have equal size. -/
theorem support_gate_count :
    (extractTerminalSupport original
        (backwardRecords original.program relabeling records)).gateCount =
      (extractTerminalSupport (result original relabeling) records).gateCount := by
  rw [extractTerminalSupport_gateCount, extractTerminalSupport_gateCount]
  exact selected_gate_count original relabeling records

theorem support_surcharge_zero :
    ((extractTerminalSupport original
        (backwardRecords original.program relabeling records)).gateCount : Int) -
      (extractTerminalSupport (result original relabeling) records).gateCount = 0 := by
  rw [support_gate_count]
  exact Int.sub_self _

theorem replacement_surcharge_zero :
    ((pullReplacement original relabeling records offered).toImplementation.gateCount : Int) -
      offered.toImplementation.gateCount = 0 := by
  rw [pullReplacement_gate_count]
  exact Int.sub_self _

/-- Both actual signed surcharge differences are zero, hence exactly matched. -/
theorem matched_surcharge :
    ((extractTerminalSupport original
        (backwardRecords original.program relabeling records)).gateCount : Int) -
        (extractTerminalSupport (result original relabeling) records).gateCount =
      ((pullReplacement original relabeling records offered).toImplementation.gateCount : Int) -
        offered.toImplementation.gateCount := by
  rw [support_surcharge_zero, replacement_surcharge_zero]

/-- The complete signed saving agrees, even for equal or larger replacements. -/
theorem replacement_saving_preserved :
    ((extractTerminalSupport original
        (backwardRecords original.program relabeling records)).gateCount : Int) -
        (pullReplacement original relabeling records offered).toImplementation.gateCount =
      ((extractTerminalSupport (result original relabeling) records).gateCount : Int) -
        offered.toImplementation.gateCount := by
  rw [support_gate_count, pullReplacement_gate_count]

theorem strict_gain_pullback
    (smaller : offered.toImplementation.gateCount <
      (extractTerminalSupport (result original relabeling) records).gateCount) :
    (pullReplacement original relabeling records offered).toImplementation.gateCount <
      (extractTerminalSupport original
        (backwardRecords original.program relabeling records)).gateCount := by
  rw [pullReplacement_gate_count, support_gate_count]
  exact smaller

end PNP.DirectWire.StructuralReindexing
