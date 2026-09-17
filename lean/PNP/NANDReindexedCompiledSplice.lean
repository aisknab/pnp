/-
Copyright (c) 2026 PNP Labs.

Literal physical-position transport between the actual compiled splices.
The correspondence composes the old compiler's inverse placement, the computed
raw-splice bijection and the new compiler's placement. No gate is padded,
invented or identified only by numerical size or Boolean equivalence.

An accepted descendant splice computes an accepted predecessor splice. Whole
semantics and exact savings follow under the actual open-support compatibility
premise. This does not make every compatible splice acyclic or discharge the
remaining manuscript profile, materializer, global or polynomial obligations.
-/

import PNP.NANDReindexedSplice

namespace PNP.DirectWire.StructuralReindexing

variable {inputs gates outputs profileWidth replacementGates : Nat}
variable (original : Candidate inputs gates outputs) (relabeling : GateRenaming gates)
variable (records : List
  (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))
variable (offered : Candidate
  (terminalBoundaryPorts (result original relabeling).program records).length replacementGates
  (terminalInterfacePorts (result original relabeling) records).length)

section CompiledPair

variable (before : CompiledRawNandGraph
  (ArbitrarySupportSplice.graph original
    (backwardRecords original.program relabeling records)
    (pullReplacement original relabeling records offered)))
variable (after : CompiledRawNandGraph
  (ArbitrarySupportSplice.graph (result original relabeling) records offered))

/-- Follow actual inverse placement, raw ownership, then actual new placement. -/
def splicePhysicalForward (position : Fin before.count) : Fin after.count :=
  after.position (spliceForward original relabeling records (before.physicalOrigin position))

def splicePhysicalBackward (position : Fin after.count) : Fin before.count :=
  before.position (spliceBackward original relabeling records (after.physicalOrigin position))

theorem splice_physical_backward_forward (position : Fin before.count) :
    splicePhysicalBackward original relabeling records offered before after
      (splicePhysicalForward original relabeling records offered before after position) = position := by
  unfold splicePhysicalBackward splicePhysicalForward
  rw [CompiledRawNandGraph.physicalOrigin_position, splice_backward_forward,
    CompiledRawNandGraph.position_physicalOrigin]

theorem splice_physical_forward_backward (position : Fin after.count) :
    splicePhysicalForward original relabeling records offered before after
      (splicePhysicalBackward original relabeling records offered before after position) = position := by
  unfold splicePhysicalForward splicePhysicalBackward
  rw [CompiledRawNandGraph.physicalOrigin_position, splice_forward_backward,
    CompiledRawNandGraph.position_physicalOrigin]

theorem splice_physical_position
    (node : Fin ((ArbitrarySupportSplice.exterior
      (backwardRecords original.program relabeling records)).length + replacementGates)) :
    splicePhysicalForward original relabeling records offered before after (before.position node) =
      after.position (spliceForward original relabeling records node) := by
  unfold splicePhysicalForward
  rw [CompiledRawNandGraph.physicalOrigin_position]

theorem splice_physical_exterior
    (outside : Fin (ArbitrarySupportSplice.exterior
      (backwardRecords original.program relabeling records)).length) :
    splicePhysicalForward original relabeling records offered before after
        (before.position (Fin.castAdd replacementGates outside)) =
      after.position (Fin.castAdd replacementGates
        ((exteriorPorts original relabeling records).forward outside)) := by
  rw [splice_physical_position, spliceForward_exterior]

theorem splice_physical_replacement (inside : Fin replacementGates) :
    splicePhysicalForward original relabeling records offered before after
        (before.position (Fin.natAdd (ArbitrarySupportSplice.exterior
          (backwardRecords original.program relabeling records)).length inside)) =
      after.position (Fin.natAdd (ArbitrarySupportSplice.exterior records).length inside) := by
  rw [splice_physical_position, spliceForward_replacement]

private theorem splice_physical_source
    (source : Source inputs ((ArbitrarySupportSplice.exterior
      (backwardRecords original.program relabeling records)).length + replacementGates)) :
    sourceMap (splicePhysicalForward original relabeling records offered before after)
        (before.translateSource source) =
      after.translateSource (sourceMap (spliceForward original relabeling records) source) := by
  cases source with
  | input index => rfl
  | constant value => rfl
  | gate node =>
      exact congrArg Source.gate
        (splice_physical_position original relabeling records offered before after node)

/-- Both literal input wires at every actual emitted gate correspond. The success
equations exclude arbitrary semantically equivalent compiler-result records. -/
theorem splice_compiled_sources
    (beforeAccepted : ArbitrarySupportSplice.compile original
      (backwardRecords original.program relabeling records)
      (pullReplacement original relabeling records offered) = some before)
    (afterAccepted : ArbitrarySupportSplice.compile (result original relabeling) records offered =
      some after)
    (position : Fin before.count) :
    after.program.terminalGateSources
        (splicePhysicalForward original relabeling records offered before after position) =
      (sourceMap (splicePhysicalForward original relabeling records offered before after)
          (before.program.terminalGateSources position).1,
        sourceMap (splicePhysicalForward original relabeling records offered before after)
          (before.program.terminalGateSources position).2) := by
  rw [RawNandWireStructure.physicalOrigin_sources _ before beforeAccepted position]
  unfold splicePhysicalForward
  rw [RawNandWireStructure.compile_sources _ after afterAccepted]
  have pairs := splice_sources original relabeling records offered (before.physicalOrigin position)
  have leftSame := congrArg Prod.fst pairs
  have rightSame := congrArg Prod.snd pairs
  dsimp only at leftSame rightSame
  rw [leftSame, rightSame]
  exact Prod.ext
    (splice_physical_source original relabeling records offered before after _).symm
    (splice_physical_source original relabeling records offered before after _).symm

/-- Every ordered compiled output retains its literal source, including constants
and aliases. This follows from the actual raw word and compiler placement. -/
theorem splice_compiled_output_source (output : Fin outputs) :
    (ArbitrarySupportSplice.result (result original relabeling) records offered after).directWireWord.source
        output =
      sourceMap (splicePhysicalForward original relabeling records offered before after)
        ((ArbitrarySupportSplice.result original
          (backwardRecords original.program relabeling records)
          (pullReplacement original relabeling records offered) before).directWireWord.source output) := by
  unfold ArbitrarySupportSplice.result CompiledRawNandGraph.candidate
  rw [Candidate.ofDirectWireWord_pointwise, Candidate.ofDirectWireWord_pointwise]
  dsimp only
  rw [splice_output_source]
  exact (splice_physical_source original relabeling records offered before after _).symm

theorem splice_compiled_gate_count : before.count = after.count := by
  rw [before.count_eq, after.count_eq, exterior_gate_count original relabeling records]

theorem splice_compiled_semantics
    (equivalent : offered.semantics =
      (extractTerminalSupport (result original relabeling) records).extractedCandidate.semantics)
    (input : Valuation inputs) (output : Fin outputs) :
    (ArbitrarySupportSplice.result original
      (backwardRecords original.program relabeling records)
      (pullReplacement original relabeling records offered) before).semantics input output =
    (ArbitrarySupportSplice.result (result original relabeling) records offered after).semantics
      input output := by
  rw [ArbitrarySupportSplice.result_semantics original
    (backwardRecords original.program relabeling records)
    (pullReplacement original relabeling records offered)
    (pullReplacement_compatible original relabeling records offered equivalent) before,
    ArbitrarySupportSplice.result_semantics (result original relabeling) records offered
      equivalent after, result_semantics]

end CompiledPair

variable (descendant : CompiledRawNandGraph
  (ArbitrarySupportSplice.graph (result original relabeling) records offered))
variable (accepted : ArbitrarySupportSplice.compile (result original relabeling) records offered =
  some descendant)

include descendant accepted in
theorem pull_splice_isSome :
    (ArbitrarySupportSplice.compile original
      (backwardRecords original.program relabeling records)
      (pullReplacement original relabeling records offered)).isSome = true := by
  obtain ⟨before, success⟩ :=
    (splice_compile_success_iff original relabeling records offered).mpr ⟨descendant, accepted⟩
  rw [success]
  rfl

/-- Compute the actual predecessor result; no predecessor order or witness is supplied. -/
def pullCompiledSplice : CompiledRawNandGraph
    (ArbitrarySupportSplice.graph original
      (backwardRecords original.program relabeling records)
      (pullReplacement original relabeling records offered)) :=
  (ArbitrarySupportSplice.compile original
    (backwardRecords original.program relabeling records)
    (pullReplacement original relabeling records offered)).get
      (pull_splice_isSome original relabeling records offered descendant accepted)

theorem pullCompiledSplice_accepted :
    ArbitrarySupportSplice.compile original
      (backwardRecords original.program relabeling records)
      (pullReplacement original relabeling records offered) =
        some (pullCompiledSplice original relabeling records offered descendant accepted) :=
  (Option.some_get
    (pull_splice_isSome original relabeling records offered descendant accepted)).symm

/-- The complete bounded replacement result: actual compilation, independent open
compatibility, whole semantics, exact physical counts, signed saving and strict gain.
Literal physical source and ownership equations above apply to this computed result. -/
theorem literal_replacement_transport
    (equivalent : offered.semantics =
      (extractTerminalSupport (result original relabeling) records).extractedCandidate.semantics) :
    let before := pullCompiledSplice original relabeling records offered descendant accepted
    ArbitrarySupportSplice.compile original
        (backwardRecords original.program relabeling records)
        (pullReplacement original relabeling records offered) = some before ∧
      (pullReplacement original relabeling records offered).semantics =
        (extractTerminalSupport original
          (backwardRecords original.program relabeling records)).extractedCandidate.semantics ∧
      (∀ input output, (ArbitrarySupportSplice.result original
        (backwardRecords original.program relabeling records)
        (pullReplacement original relabeling records offered) before).semantics input output =
          original.semantics input output) ∧
      before.count = descendant.count ∧
      ((extractTerminalSupport original
          (backwardRecords original.program relabeling records)).gateCount : Int) -
          (pullReplacement original relabeling records offered).toImplementation.gateCount =
        ((extractTerminalSupport (result original relabeling) records).gateCount : Int) -
          offered.toImplementation.gateCount ∧
      ((gates : Int) - before.count =
        ((compiled original.program relabeling).count : Int) - descendant.count) ∧
      (replacementGates <
        (extractTerminalSupport (result original relabeling) records).gateCount →
          before.count < gates) := by
  dsimp only
  let before := pullCompiledSplice original relabeling records offered descendant accepted
  have compatibility := pullReplacement_compatible original relabeling records offered equivalent
  have sameCount := splice_compiled_gate_count original relabeling records offered before descendant
  refine ⟨pullCompiledSplice_accepted original relabeling records offered descendant accepted,
    compatibility, ?_, sameCount,
    replacement_saving_preserved original relabeling records offered, ?_, ?_⟩
  · exact ArbitrarySupportSplice.result_semantics original
      (backwardRecords original.program relabeling records)
      (pullReplacement original relabeling records offered) compatibility before
  · rw [sameCount]
    exact congrArg (fun size : Nat => (size : Int) - descendant.count)
      (compiled original.program relabeling).count_eq.symm
  · intro smaller
    have oldSmaller : replacementGates < (extractTerminalSupport original
        (backwardRecords original.program relabeling records)).gateCount := by
      rw [support_gate_count original relabeling records]
      exact smaller
    exact ArbitrarySupportSplice.result_strict_gain original
      (backwardRecords original.program relabeling records)
      (pullReplacement original relabeling records offered) oldSmaller before

end PNP.DirectWire.StructuralReindexing
