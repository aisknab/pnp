/-
Copyright (c) 2026 PNP Labs.

Compute the physical unused-gate support and its replacement context from the
actual output cone. Proper physical support is kept separate from complete
manuscript profile admissibility, and no global or polynomial claim is made.
-/

import PNP.PCCMinOutputConePruning
import PNP.ResidualTerminalSaturatedSupportContext

namespace PNP
namespace DirectWire

/-- Actual physical complement of the computed live output cone. -/
def deadSupportRecords {inputs outputs : Nat}
    (current : Implementation inputs outputs) :=
  terminalPhysicalComplementRecords (outputConeRecords current.candidate)

/-- Ordered incoming wires of the actual extracted dead support. -/
def deadSupportBoundary {inputs outputs : Nat}
    (current : Implementation inputs outputs) :=
  terminalBoundaryPorts current.candidate.program (deadSupportRecords current)

/-- Actual extracted NAND count, not an assigned numerical weight. -/
def deadSupportGateCount {inputs outputs : Nat}
    (current : Implementation inputs outputs) : Nat :=
  (extractTerminalSupport current.candidate (deadSupportRecords current)).gateCount

private theorem deadBool_eq_of_true_iff (left right : Bool)
    (same : left = true ↔ right = true) : left = right := by
  cases left <;> cases right
  · rfl
  · exact False.elim (Bool.noConfusion (same.mpr rfl))
  · exact False.elim (Bool.noConfusion (same.mp rfl))
  · rfl

private theorem deadSupport_selected {inputs outputs : Nat}
    (current : Implementation inputs outputs) (gate : Fin current.gateCount) :
    terminalGateSelected (deadSupportRecords current) gate =
      !(terminalGateSelected (outputConeRecords current.candidate) gate) := by
  apply deadBool_eq_of_true_iff
  apply (terminalGateSelected_eq_true_iff _ gate).trans
  constructor
  · intro member
    obtain ⟨found, selected, equal⟩ := List.mem_map.mp member
    have same : found = gate := TerminalPrimitiveRecord.gate.inj equal
    subst found
    exact (mem_terminalSelectedGateIndices_iff _ gate).mp selected
  · intro selected
    exact List.mem_map.mpr ⟨gate,
      (mem_terminalSelectedGateIndices_iff _ gate).mpr selected, rfl⟩

private theorem deadSupport_selected_iff {inputs outputs : Nat}
    (current : Implementation inputs outputs) (gate : Fin current.gateCount) :
    terminalGateSelected (deadSupportRecords current) gate = true ↔
      terminalGateSelected (outputConeRecords current.candidate) gate = false := by
  rw [deadSupport_selected]
  cases terminalGateSelected (outputConeRecords current.candidate) gate <;> decide

private theorem deadSupport_unselected_iff {inputs outputs : Nat}
    (current : Implementation inputs outputs) (gate : Fin current.gateCount) :
    terminalGateSelected (deadSupportRecords current) gate = false ↔
      terminalGateSelected (outputConeRecords current.candidate) gate = true := by
  rw [deadSupport_selected]
  cases terminalGateSelected (outputConeRecords current.candidate) gate <;> decide

/-- No dead gate feeds an original output or a retained live gate. -/
theorem deadSupport_interface_empty {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    terminalInterfacePorts current.candidate (deadSupportRecords current) = [] := by
  have absent (producer : Fin current.gateCount) :
      producer ∉ terminalInterfacePorts current.candidate (deadSupportRecords current) := by
    intro member
    obtain ⟨dead, consumerOrOutput⟩ := (terminalInterfaceGate_eq_true_iff _ _ _).mp
      ((mem_terminalInterfacePorts_iff _ _ _).mp member)
    have notLive := (deadSupport_selected_iff current producer).mp dead
    have live : terminalGateSelected (outputConeRecords current.candidate) producer = true := by
      apply (terminalGateSelected_eq_true_iff _ _).mpr
      cases consumerOrOutput with
      | inl externalConsumer =>
          obtain ⟨consumer, _, notDead, uses⟩ :=
            (terminalGateHasExternalConsumer_eq_true_iff _ _ _).mp externalConsumer
          exact outputConeRecords_closed current.candidate consumer producer
            ((terminalGateSelected_eq_true_iff _ _).mp
              ((deadSupport_unselected_iff current consumer).mp notDead)) uses
      | inr isOutput =>
          exact outputConeRecords_output current.candidate producer isOutput
    rw [live] at notLive
    exact Bool.noConfusion notLive
  cases portsEq : terminalInterfacePorts current.candidate (deadSupportRecords current) with
  | nil => rfl
  | cons producer tail =>
      exact False.elim (absent producer (by rw [portsEq]; exact List.Mem.head _))

private theorem deadSelectedGateCount_partition {gates : Nat}
    (selected : Fin gates → Bool) :
    (terminalSelectedGateIndices selected).length +
      (terminalSelectedGateIndices fun gate => !(selected gate)).length = gates := by
  induction gates with
  | zero => rfl
  | succ gates ih =>
      have earlier := ih (fun gate => selected gate.castSucc)
      cases lastValue : selected (Fin.last gates) <;>
        simp only [terminalSelectedGateIndices, lastValue, Bool.not_false,
          Bool.not_true, Bool.false_eq_true, if_false, if_true, List.length_append,
          List.length_map, List.length_cons, List.length_nil] <;> omega

/-- The live environment and actual extracted dead support partition all gates. -/
theorem deadSupportGateCount_partition {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    (outputConeImplementation current).gateCount + deadSupportGateCount current =
      current.gateCount := by
  change (extractTerminalSupport current.candidate
      (outputConeRecords current.candidate)).gateCount +
    (extractTerminalSupport current.candidate (deadSupportRecords current)).gateCount = _
  rw [extractTerminalSupport_gateCount, extractTerminalSupport_gateCount]
  have complement :
      terminalSelectedGates (deadSupportRecords current) =
        terminalSelectedGateIndices fun gate =>
          !(terminalGateSelected (outputConeRecords current.candidate) gate) := by
    unfold terminalSelectedGates
    congr 1
    funext gate
    exact deadSupport_selected current gate
  rw [complement]
  exact deadSelectedGateCount_partition _

/-- The computed deletion count is the physical extracted support size. -/
theorem deadSupportGateCount_eq_deleted {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    deadSupportGateCount current = outputConeDeletedGateCount current := by
  have partition := deadSupportGateCount_partition current
  unfold outputConeDeletedGateCount
  omega

private theorem deadBoundaryGate_liveInterface {inputs outputs : Nat}
    (current : Implementation inputs outputs) (producer : Fin current.gateCount)
    (member : TerminalSupportWire.gate producer ∈ deadSupportBoundary current) :
    producer ∈ terminalInterfacePorts current.candidate
      (outputConeRecords current.candidate) := by
  obtain ⟨external, consumer, enumerated, dead, uses⟩ :=
    (terminalBoundaryWire_eq_true_iff _ _ _).mp
      ((mem_terminalBoundaryPorts_iff _ _ _).mp member)
  have notDead : terminalGateSelected (deadSupportRecords current) producer = false :=
    (terminalWireExternal_eq_true_iff _ _).mp external
  have live := (deadSupport_unselected_iff current producer).mp notDead
  apply (mem_terminalInterfacePorts_iff _ _ _).mpr
  apply (terminalInterfaceGate_eq_true_iff _ _ _).mpr
  refine ⟨live, Or.inl ?_⟩
  exact (terminalGateHasExternalConsumer_eq_true_iff _ _ _).mpr
    ⟨consumer, enumerated, (deadSupport_selected_iff current consumer).mp dead, uses⟩

private def deadLocateMember {alpha : Type} [DecidableEq alpha] (item : alpha) :
    (items : List alpha) → item ∈ items →
      {index : Fin items.length // items.get index = item}
  | [], member => False.elim (by cases member)
  | head :: tail, member =>
      if equal : item = head then
        ⟨⟨0, by simp only [List.length_cons]; exact Nat.zero_lt_succ _⟩,
          by change head = item; exact equal.symm⟩
      else
        let tailMember := (List.mem_cons.mp member).resolve_left equal
        let located := deadLocateMember item tail tailMember
        ⟨located.1.succ, by
          change tail.get located.1 = item
          exact located.2⟩

/-- Wire every computed dead-support input to its actual primary input or live
frontier producer. No valuation or boundary certificate is supplied. -/
def deadSupportInputSource {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (index : Fin (deadSupportBoundary current).length) :
    Source inputs (outputConeImplementation current).gateCount :=
  match wireEq : (deadSupportBoundary current).get index with
  | .input original => .input original
  | .gate producer =>
      let located := deadLocateMember producer
        (terminalInterfacePorts current.candidate (outputConeRecords current.candidate))
        (deadBoundaryGate_liveInterface current producer
          (wireEq ▸ List.get_mem _ index))
      (outputConeFrontierCandidate current.candidate).directWireWord.source located.1

private theorem deadSupportInputSource_value {inputs outputs : Nat}
    (current : Implementation inputs outputs) (input : Valuation inputs)
    (index : Fin (deadSupportBoundary current).length) :
    (deadSupportInputSource current index).eval input
        ((outputConeFrontierCandidate current.candidate).program.eval input) =
      terminalInducedBoundaryValuation current.candidate (deadSupportRecords current)
        input index := by
  unfold deadSupportInputSource
  split
  · rename_i original wireEq
    change input original =
      ((deadSupportBoundary current).get index).candidateValue current.candidate input
    rw [wireEq]
    rfl
  · rename_i producer wireEq
    let located := deadLocateMember producer
      (terminalInterfacePorts current.candidate (outputConeRecords current.candidate))
      (deadBoundaryGate_liveInterface current producer (wireEq ▸ List.get_mem _ index))
    change (outputConeFrontierCandidate current.candidate).semantics input located.1 = _
    rw [outputConeFrontierCandidate_semantics, located.2]
    change current.candidate.program.eval input producer =
      ((deadSupportBoundary current).get index).candidateValue current.candidate input
    rw [wireEq]
    rfl

/-- The live cone computes the exact dead-support boundary and all original
ordered outputs as bypass wires, using one copy of its physical program. -/
def deadSupportEnvironment {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    Candidate inputs (outputConeImplementation current).gateCount
      ((deadSupportBoundary current).length + outputs) :=
  Candidate.ofDirectWireWord (outputConeFrontierCandidate current.candidate).program
    ⟨splitFin (deadSupportInputSource current)
      (outputConeImplementation current).candidate.directWireWord.source⟩

/-- Every support input in the computed environment has its actual original value. -/
theorem deadSupportEnvironment_boundary {inputs outputs : Nat}
    (current : Implementation inputs outputs) (input : Valuation inputs)
    (index : Fin (deadSupportBoundary current).length) :
    (deadSupportEnvironment current).semantics input (Fin.castAdd outputs index) =
      terminalInducedBoundaryValuation current.candidate (deadSupportRecords current)
        input index := by
  rw [deadSupportEnvironment, Candidate.ofDirectWireWord_semantics]
  change (splitFin (deadSupportInputSource current)
      (outputConeImplementation current).candidate.directWireWord.source
      (Fin.castAdd outputs index)).eval input
        ((outputConeFrontierCandidate current.candidate).program.eval input) = _
  rw [splitFin_left]
  exact deadSupportInputSource_value current input index

/-- Bypass ports preserve original order, including constants, inputs and repeats. -/
theorem deadSupportEnvironment_bypass {inputs outputs : Nat}
    (current : Implementation inputs outputs) (input : Valuation inputs)
    (output : Fin outputs) :
    (deadSupportEnvironment current).semantics input
        (Fin.natAdd (deadSupportBoundary current).length output) =
      current.candidate.semantics input output := by
  rw [deadSupportEnvironment, Candidate.ofDirectWireWord_semantics]
  change (splitFin (deadSupportInputSource current)
      (outputConeImplementation current).candidate.directWireWord.source
      (Fin.natAdd (deadSupportBoundary current).length output)).eval input
        ((outputConeFrontierCandidate current.candidate).program.eval input) = _
  rw [splitFin_right]
  exact outputConeImplementation_equivalent current input output

private theorem deadSupport_outputWidth_zero {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    (extractTerminalSupport current.candidate (deadSupportRecords current)).interface.length =
      0 := by
  change (terminalInterfacePorts current.candidate (deadSupportRecords current)).length = 0
  rw [deadSupport_interface_empty]
  rfl

private theorem deadCast_program {inputs gates before after : Nat}
    (equal : before = after) (candidate : Candidate inputs gates before) :
    (equal ▸ candidate).program = candidate.program := by
  cases equal
  rfl

private theorem deadCast_heq {inputs gates before after : Nat}
    (equal : before = after) (candidate : Candidate inputs gates before) :
    HEq (equal ▸ candidate) candidate := by
  cases equal
  rfl

/-- The actual extracted dead support, reindexed only by its proved empty
outgoing interface. Its program and incoming boundary are unchanged. -/
def deadSupportCandidate {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    Candidate (deadSupportBoundary current).length (deadSupportGateCount current) 0 :=
  deadSupport_outputWidth_zero current ▸
    (extractTerminalSupport current.candidate (deadSupportRecords current)).extractedCandidate

/-- This is the computed extracted support, not a substitute with discarded outputs. -/
theorem deadSupportCandidate_extracted {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    HEq (deadSupportCandidate current)
      (extractTerminalSupport current.candidate (deadSupportRecords current)).extractedCandidate :=
  deadCast_heq (deadSupport_outputWidth_zero current) _

/-- Reindexing the proved empty interface preserves every extracted physical gate. -/
theorem deadSupportCandidate_program {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    (deadSupportCandidate current).program =
      (extractTerminalSupport current.candidate (deadSupportRecords current)).extractedCandidate.program :=
  deadCast_program (deadSupport_outputWidth_zero current) _

/-- The zero-gate replacement has the same incoming boundary and empty interface. -/
def deadSupportEmptyReplacement {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    Candidate (deadSupportBoundary current).length 0 0 :=
  Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩

/-- Open equivalence holds at the actual, proved zero-output support interface. -/
theorem deadSupportEmptyReplacement_equivalent {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    Equivalent (deadSupportEmptyReplacement current).program
      (deadSupportEmptyReplacement current).directWireWord
      (deadSupportCandidate current).program (deadSupportCandidate current).directWireWord := by
  intro _ output
  exact Fin.elim0 output

private def deadBypassContinuation (outputs : Nat) : Candidate (0 + outputs) 0 outputs :=
  Candidate.ofDirectWireWord .empty ⟨fun output => .input (Fin.natAdd 0 output)⟩

private theorem deadBypassContinuation_semantics (outputs : Nat)
    (input : Valuation (0 + outputs)) (output : Fin outputs) :
    (deadBypassContinuation outputs).semantics input output =
      input (Fin.natAdd 0 output) := by
  rw [deadBypassContinuation, Candidate.ofDirectWireWord_semantics]
  rfl

/-- A fully computed physical replacement frame: one live-cone environment,
the actual dead-support boundary, no support outputs, and zero-gate bypass. -/
def deadSupportContext {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    FramedContext inputs (deadSupportBoundary current).length 0 outputs outputs
      (outputConeImplementation current).gateCount 0 where
  environment := deadSupportEnvironment current
  continuation := deadBypassContinuation outputs

/-- Any replacement with this actual empty outgoing interface leaves all original
outputs unchanged. The context, boundary and bypass are computed from the input. -/
theorem deadSupportContext_plug_equivalent {inputs outputs replacementGates : Nat}
    (current : Implementation inputs outputs)
    (replacement : Candidate (deadSupportBoundary current).length replacementGates 0) :
    Equivalent ((deadSupportContext current).plug replacement).program
      ((deadSupportContext current).plug replacement).directWireWord
      current.candidate.program current.candidate.directWireWord := by
  intro input output
  change ((deadSupportContext current).plug replacement).semantics input output = _
  rw [FramedContext.plug_semantics]
  rw [show (deadSupportContext current).continuation = deadBypassContinuation outputs from rfl]
  rw [deadBypassContinuation_semantics, splitFin_right]
  exact deadSupportEnvironment_bypass current input output

/-- Putting back the actual extracted support reconstructs the original physical
gate count, without claiming syntactic identity of the reordered serialization. -/
theorem deadSupportContext_original_size {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    ((deadSupportContext current).plug (deadSupportCandidate current)).program.size =
      current.gateCount := by
  rw [Program.size_eq_gateCount]
  exact deadSupportGateCount_partition current

/-- Execute the actual framed replacement with the zero-gate support. -/
def deadSupportReplacementImplementation {inputs outputs : Nat}
    (current : Implementation inputs outputs) : Implementation inputs outputs :=
  ((deadSupportContext current).plug (deadSupportEmptyReplacement current)).toImplementation

/-- The replaced program has exactly the computed live-cone gate count. -/
theorem deadSupportReplacement_gateCount {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    (deadSupportReplacementImplementation current).gateCount =
      (outputConeImplementation current).gateCount := rfl

/-- The result is the concrete frame's replacement, with complete output semantics. -/
theorem deadSupportReplacement_equivalent {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    Equivalent (deadSupportReplacementImplementation current).candidate.program
      (deadSupportReplacementImplementation current).candidate.directWireWord
      current.candidate.program current.candidate.directWireWord :=
  deadSupportContext_plug_equivalent current (deadSupportEmptyReplacement current)

/-- The exact removed support, rather than a supplied weight, accounts for cost. -/
theorem deadSupportReplacement_accounting {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    (deadSupportReplacementImplementation current).gateCount + deadSupportGateCount current =
      current.gateCount := by
  rw [deadSupportReplacement_gateCount]
  exact deadSupportGateCount_partition current

/-- Physical replacement retires exactly the actual dead support's semantic slack.
The reference minimum is used only in the theorem, never in the construction. -/
theorem deadSupportReplacement_residualSlack {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    residualSlack current = residualSlack (deadSupportReplacementImplementation current) +
      deadSupportGateCount current := by
  have accounting := deadSupportReplacement_accounting current
  have bounded := referenceMinimum_le_target (deadSupportReplacementImplementation current)
  have sameMinimum := referenceMinimum_invariant (deadSupportReplacementImplementation current)
    current (deadSupportReplacement_equivalent current)
  unfold residualSlack
  rw [sameMinimum] at bounded ⊢
  omega

/-- Exact acceptance boundary for strict physical gain, without a properness claim. -/
theorem deadSupportReplacement_strictGain_iff {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    StrictEquivalentGain current (deadSupportReplacementImplementation current) ↔
      0 < deadSupportGateCount current := by
  have accounting := deadSupportReplacement_accounting current
  constructor
  · intro gain
    have smaller := gain.smaller
    omega
  · intro positive
    exact ⟨by omega, deadSupportReplacement_equivalent current⟩

/-- A witness for this computed proper physical support and concrete replacement.
This is not the manuscript's complete profile/obligation admissibility certificate. -/
structure DeadSupportPhysicalGain {inputs outputs : Nat}
    (current : Implementation inputs outputs) : Type where
  supportNonempty : 0 < deadSupportGateCount current
  supportProper : deadSupportGateCount current < current.gateCount
  gain : StrictEquivalentGain current (deadSupportReplacementImplementation current)

/-- Return a witness only when the computed dead support and retained circuit
both contain a gate. No correctness, coverage or context data is supplied. -/
def deadSupportProperGain {inputs outputs : Nat}
    (current : Implementation inputs outputs) : Option (DeadSupportPhysicalGain current) :=
  if positive : 0 < deadSupportGateCount current ∧
      0 < (outputConeImplementation current).gateCount then
    some
      { supportNonempty := positive.1
        supportProper := by
          have partition := deadSupportGateCount_partition current
          omega
        gain := (deadSupportReplacement_strictGain_iff current).mpr positive.1 }
  else none

/-- The computed recognizer accepts exactly a nonempty proper physical deletion. -/
theorem deadSupportProperGain_isSome_iff {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    (deadSupportProperGain current).isSome = true ↔
      0 < deadSupportGateCount current ∧
        0 < (outputConeImplementation current).gateCount := by
  unfold deadSupportProperGain
  split
  · rename_i positive
    exact ⟨fun _ => positive, fun _ => rfl⟩
  · rename_i notPositive
    constructor
    · intro impossible
      exact Bool.noConfusion impossible
    · intro positive
      exact False.elim (notPositive positive)

/-- Every returned proper-support witness has strict semantic-slack descent. -/
theorem deadSupportProperGain_sound {inputs outputs : Nat}
    (current : Implementation inputs outputs) (witness : DeadSupportPhysicalGain current)
    (_found : deadSupportProperGain current = some witness) :
    0 < deadSupportGateCount current ∧
      deadSupportGateCount current < current.gateCount ∧
      StrictEquivalentGain current (deadSupportReplacementImplementation current) ∧
      residualSlack (deadSupportReplacementImplementation current) < residualSlack current :=
  ⟨witness.supportNonempty, witness.supportProper, witness.gain, witness.gain.strictResidualDescent⟩

/-- Removing the whole gate set is not accepted as a proper-support witness. -/
theorem deadSupportProperGain_none_of_all_dead {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (allDead : (outputConeImplementation current).gateCount = 0) :
    deadSupportProperGain current = none := by
  unfold deadSupportProperGain
  apply dif_neg
  intro positive
  have retained := positive.2
  omega

/-- An empty dead support cannot produce a strict-gain witness. -/
theorem deadSupportProperGain_none_of_no_dead {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (noDead : deadSupportGateCount current = 0) :
    deadSupportProperGain current = none := by
  unfold deadSupportProperGain
  apply dif_neg
  intro positive
  have deleted := positive.1
  omega

end DirectWire
end PNP
