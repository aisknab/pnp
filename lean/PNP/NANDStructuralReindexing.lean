/-
Copyright (c) 2026 PNP Labs.

Reindex an actual finite NAND circuit from checked raw swap instructions.
The dependency graph, complete topological order, inverse physical placement,
literal source pairs and ordered output wiring are all derived from the input.

This constructs the physical reordering operation. Arbitrary-support Pull/Expand,
full manuscript profile transport and the remaining normalization rules are
separate obligations; no global or polynomial-time claim is made here.
-/

import PNP.NANDGateRenaming
import PNP.NANDArbitrarySupportSplice

namespace PNP.DirectWire.StructuralReindexing

variable {inputs gates outputs : Nat}

def graph (program : Program inputs gates) (relabeling : GateRenaming gates) :
    RawNandGraph inputs gates :=
  { gate := fun node =>
      let pair := program.terminalGateSources (relabeling.backward node)
      ⟨sourceMap relabeling.forward pair.1, sourceMap relabeling.forward pair.2⟩ }

theorem graph_edge_ordered (program : Program inputs gates) (relabeling : GateRenaming gates)
    (producer consumer : Fin gates) (edge : (graph program relabeling).Depends producer consumer) :
    (relabeling.backward producer).val < (relabeling.backward consumer).val := by
  change sourceMap relabeling.forward
      (program.terminalGateSources (relabeling.backward consumer)).1 = .gate producer ∨
    sourceMap relabeling.forward
      (program.terminalGateSources (relabeling.backward consumer)).2 = .gate producer at edge
  apply ArbitrarySupportSplice.sources_ordered program
    (relabeling.backward consumer) (relabeling.backward producer)
  rcases edge with left | right
  · exact Or.inl ((sourceMap_eq_gate_iff relabeling _ producer).mp left)
  · exact Or.inr ((sourceMap_eq_gate_iff relabeling _ producer).mp right)

private theorem graph_accessible (program : Program inputs gates)
    (relabeling : GateRenaming gates) (node : Fin gates) :
    Acc (graph program relabeling).Depends node :=
  Acc.intro node (fun producer _edge => graph_accessible program relabeling producer)
termination_by (relabeling.backward node).val
decreasing_by exact graph_edge_ordered program relabeling producer node _edge

theorem graph_wellFounded (program : Program inputs gates) (relabeling : GateRenaming gates) :
    WellFounded (graph program relabeling).Depends :=
  ⟨graph_accessible program relabeling⟩

theorem compile_isSome (program : Program inputs gates) (relabeling : GateRenaming gates) :
    (compileRawNandGraph (graph program relabeling)).isSome = true := by
  obtain ⟨compiled, accepted⟩ :=
    (compileRawNandGraph_success_iff (graph program relabeling)).mpr
      (graph_wellFounded program relabeling)
  rw [accepted]
  rfl

def compiled (program : Program inputs gates) (relabeling : GateRenaming gates) :
    CompiledRawNandGraph (graph program relabeling) :=
  (compileRawNandGraph (graph program relabeling)).get (compile_isSome program relabeling)

theorem compiled_accepted (program : Program inputs gates) (relabeling : GateRenaming gates) :
    compileRawNandGraph (graph program relabeling) = some (compiled program relabeling) :=
  (Option.some_get (compile_isSome program relabeling)).symm

def renamedWord (word : DirectWireWord inputs gates outputs) (relabeling : GateRenaming gates) :
    DirectWireWord inputs gates outputs :=
  ⟨fun output => sourceMap relabeling.forward (word.source output)⟩

def result (original : Candidate inputs gates outputs) (relabeling : GateRenaming gates) :
    Candidate inputs (compiled original.program relabeling).count outputs :=
  (compiled original.program relabeling).candidate (renamedWord original.directWireWord relabeling)

def forwardGate (program : Program inputs gates) (relabeling : GateRenaming gates)
    (node : Fin gates) : Fin (compiled program relabeling).count :=
  (compiled program relabeling).position (relabeling.forward node)

def backwardGate (program : Program inputs gates) (relabeling : GateRenaming gates)
    (position : Fin (compiled program relabeling).count) : Fin gates :=
  relabeling.backward ((compiled program relabeling).physicalOrigin position)

theorem backward_forward (program : Program inputs gates) (relabeling : GateRenaming gates)
    (node : Fin gates) :
    backwardGate program relabeling (forwardGate program relabeling node) = node := by
  unfold backwardGate forwardGate
  rw [CompiledRawNandGraph.physicalOrigin_position, relabeling.backward_forward]

theorem forward_backward (program : Program inputs gates) (relabeling : GateRenaming gates)
    (position : Fin (compiled program relabeling).count) :
    forwardGate program relabeling (backwardGate program relabeling position) = position := by
  unfold forwardGate backwardGate
  rw [relabeling.forward_backward, CompiledRawNandGraph.position_physicalOrigin]

theorem forwardGate_injective (program : Program inputs gates) (relabeling : GateRenaming gates) :
    Function.Injective (forwardGate program relabeling) := by
  intro left right same
  have original := congrArg (backwardGate program relabeling) same
  rw [backward_forward, backward_forward] at original
  exact original

theorem backwardGate_injective (program : Program inputs gates) (relabeling : GateRenaming gates) :
    Function.Injective (backwardGate program relabeling) := by
  intro left right same
  have positions := congrArg (forwardGate program relabeling) same
  rw [forward_backward, forward_backward] at positions
  exact positions

theorem translated_source (program : Program inputs gates) (relabeling : GateRenaming gates)
    (source : Source inputs gates) :
    (compiled program relabeling).translateSource (sourceMap relabeling.forward source) =
      sourceMap (forwardGate program relabeling) source := by
  cases source <;> rfl

/-- Actual physical gates, not a numerical substitute for ownership, correspond. -/
theorem result_sources (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates) (node : Fin gates) :
    (result original relabeling).program.terminalGateSources
        (forwardGate original.program relabeling node) =
      (sourceMap (forwardGate original.program relabeling)
          (original.program.terminalGateSources node).1,
        sourceMap (forwardGate original.program relabeling)
          (original.program.terminalGateSources node).2) := by
  change (compiled original.program relabeling).program.terminalGateSources
      ((compiled original.program relabeling).position (relabeling.forward node)) = _
  rw [RawNandWireStructure.compile_sources (graph original.program relabeling)
    (compiled original.program relabeling) (compiled_accepted original.program relabeling)]
  change ((compiled original.program relabeling).translateSource
      (sourceMap relabeling.forward
        (original.program.terminalGateSources (relabeling.backward (relabeling.forward node))).1),
    (compiled original.program relabeling).translateSource
      (sourceMap relabeling.forward
        (original.program.terminalGateSources (relabeling.backward (relabeling.forward node))).2)) = _
  rw [relabeling.backward_forward, translated_source, translated_source]

theorem result_output_source (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates) (output : Fin outputs) :
    (result original relabeling).directWireWord.source output =
      sourceMap (forwardGate original.program relabeling) (original.directWireWord.source output) := by
  unfold result CompiledRawNandGraph.candidate
  rw [Candidate.ofDirectWireWord_pointwise]
  exact translated_source original.program relabeling (original.directWireWord.source output)

theorem result_gateCount (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates) :
    (result original relabeling).toImplementation.gateCount = gates :=
  (compiled original.program relabeling).count_eq

theorem graph_solution (program : Program inputs gates) (relabeling : GateRenaming gates)
    (input : Valuation inputs) :
    (graph program relabeling).Solution input
      (fun node => program.eval input (relabeling.backward node)) := by
  intro node
  change program.eval input (relabeling.backward node) =
    boolNand
      ((sourceMap relabeling.forward
        (program.terminalGateSources (relabeling.backward node)).1).eval input
          (fun index => program.eval input (relabeling.backward index)))
      ((sourceMap relabeling.forward
        (program.terminalGateSources (relabeling.backward node)).2).eval input
          (fun index => program.eval input (relabeling.backward index)))
  rw [sourceMap_eval, sourceMap_eval]
  exact (ArbitrarySupportSplice.sources_eval program input (relabeling.backward node)).symm

/-- Every ordered output is preserved for every input valuation. -/
theorem result_semantics (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates) (input : Valuation inputs) (output : Fin outputs) :
    (result original relabeling).semantics input output = original.semantics input output := by
  have actual := (compiled original.program relabeling).candidate_semantics
    (renamedWord original.directWireWord relabeling) input
    (fun node => original.program.eval input (relabeling.backward node))
    (graph_solution original.program relabeling input) output
  exact actual.trans
    (sourceMap_eval relabeling (original.directWireWord.source output) input
      (original.program.eval input))

/-- Raw instructions supply no map, order, successful compiler result or equality proof. -/
def attempt (original : Candidate inputs gates outputs) (code : List (Nat × Nat)) :
    Option (Implementation inputs outputs) :=
  (GateRenaming.decode gates code).map (fun relabeling => (result original relabeling).toImplementation)

theorem attempt_isSome (original : Candidate inputs gates outputs) (code : List (Nat × Nat)) :
    (attempt original code).isSome = GateRenaming.validCode gates code := by
  have same : (attempt original code).isSome = (GateRenaming.decode gates code).isSome := by
    unfold attempt
    cases GateRenaming.decode gates code <;> rfl
  exact same.trans (GateRenaming.decode_isSome gates code)

theorem attempt_semantics (original : Candidate inputs gates outputs) (code : List (Nat × Nat))
    (output : Implementation inputs outputs) (accepted : attempt original code = some output)
    (input : Valuation inputs) (coordinate : Fin outputs) :
    output.candidate.semantics input coordinate = original.semantics input coordinate := by
  unfold attempt at accepted
  cases decoded : GateRenaming.decode gates code with
  | none =>
      simp only [decoded, Option.map_none] at accepted
      cases accepted
  | some relabeling =>
      simp only [decoded, Option.map_some, Option.some.injEq] at accepted
      subst output
      exact result_semantics original relabeling input coordinate

theorem attempt_gateCount (original : Candidate inputs gates outputs) (code : List (Nat × Nat))
    (output : Implementation inputs outputs) (accepted : attempt original code = some output) :
    output.gateCount = gates := by
  unfold attempt at accepted
  cases decoded : GateRenaming.decode gates code with
  | none =>
      simp only [decoded, Option.map_none] at accepted
      cases accepted
  | some relabeling =>
      simp only [decoded, Option.map_some, Option.some.injEq] at accepted
      subst output
      exact result_gateCount original relabeling

end PNP.DirectWire.StructuralReindexing
