/-
Copyright (c) 2026 PNP Labs.

Compute the physical output-dependency cone of an arbitrary finite direct-wire
NAND candidate and reuse checked terminal extraction to delete unused gates.
Only physical gate-source edges are closed here. The empty profile index is
not a full-profile model and does not discharge manuscript metadata obligations.

No supplied support, correctness certificate, semantic minimization or runtime
oracle is used. This is a physical normalization component, not complete Package
E normalization, a proper full-profile gain, ZeroSlack or polynomial PCCMin.
-/

import PNP.PCCMinNormalizeOracleComposition
import PNP.ResidualTerminalSupportExtraction

namespace PNP
namespace DirectWire

/-- The physical-only closure system reads actual program predecessors. -/
def outputConeSystem {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) :
    TerminalSaturationSystem inputs gates outputs 0 where
  profileSystem :=
    { role := Fin.elim0
      observe := fun _ => Fin.elim0 }
  requires := fun kind dependent required =>
    match kind, dependent, required with
    | .gateSource, .gate consumer, .gate producer =>
        candidate.program.terminalGateUsesWire consumer (.gate producer)
    | _, _, _ => false

/-- Seeds are precisely the actual gate-valued output wires. -/
def outputConeSeed {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) :
    List (TerminalPrimitiveRecord inputs gates outputs 0) :=
  ((allFin gates).filter
    (terminalGateIsGlobalOutput candidate.directWireWord)).map
      TerminalPrimitiveRecord.gate

/-- Compute the complete physical predecessor closure using the existing
bounded work-list, rather than enumerating subsets or semantic minima. -/
def outputConeRecords {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) :
    List (TerminalPrimitiveRecord inputs gates outputs 0) :=
  terminalSaturateRecords (outputConeSystem candidate) (outputConeSeed candidate)

/-- Every gate named by an original output is retained. -/
theorem outputConeRecords_output {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (producer : Fin gates)
    (isOutput : terminalGateIsGlobalOutput candidate.directWireWord producer = true) :
    TerminalPrimitiveRecord.gate producer ∈ outputConeRecords candidate := by
  apply terminalSaturateRecords_extensive
  exact List.mem_map.mpr ⟨producer,
    List.mem_filter.mpr ⟨mem_allFin producer, isOutput⟩, rfl⟩

/-- Every actual gate predecessor of a retained gate is retained. -/
theorem outputConeRecords_closed {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (consumer producer : Fin gates)
    (selected : TerminalPrimitiveRecord.gate consumer ∈ outputConeRecords candidate)
    (uses : candidate.program.terminalGateUsesWire consumer (.gate producer) = true) :
    TerminalPrimitiveRecord.gate producer ∈ outputConeRecords candidate :=
  terminalSaturateRecords_closed (outputConeSystem candidate)
    (outputConeSeed candidate) .gateSource (.gate consumer) (.gate producer)
    selected uses

/-- The computed cone is the least gate set containing every output gate and
closed under physical predecessors. No supplied coverage proof controls it. -/
theorem outputConeRecords_least {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (support : Fin gates → Prop)
    (containsOutputs : ∀ producer,
      terminalGateIsGlobalOutput candidate.directWireWord producer = true →
        support producer)
    (closed : ∀ consumer producer, support consumer →
      candidate.program.terminalGateUsesWire consumer (.gate producer) = true →
        support producer)
    (producer : Fin gates)
    (selected : TerminalPrimitiveRecord.gate producer ∈ outputConeRecords candidate) :
    support producer := by
  let recordSupport : TerminalRawSupport inputs gates outputs 0 := fun record =>
    match record with
    | .gate gate => support gate
    | _ => False
  have containsSeed : TerminalRawSupport.Subset
      (fun record => record ∈ outputConeSeed candidate) recordSupport := by
    intro record member
    obtain ⟨gate, gateMember, rfl⟩ := List.mem_map.mp member
    exact containsOutputs gate (List.mem_filter.mp gateMember).2
  have supportClosed : TerminalRawSupport.Closed recordSupport
      (outputConeSystem candidate) := by
    intro kind dependent required dependentMember edge
    cases kind <;> cases dependent <;> cases required <;>
      simp only [outputConeSystem, Bool.false_eq_true] at edge
    exact closed _ _ dependentMember edge
  exact terminalSaturate_least (outputConeSystem candidate)
    (fun record => record ∈ outputConeSeed candidate) recordSupport
    containsSeed supportClosed (.gate producer)
    (terminalSaturateRecords_sound _ _ _ selected)

/-- A predecessor-closed physical cone has no external gate-valued input.
Its only incoming wires are original primary inputs. -/
theorem outputConeRecords_noExternalGate {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (producer : Fin gates) :
    TerminalSupportWire.gate producer ∉ terminalBoundaryPorts candidate.program
      (outputConeRecords candidate) := by
  intro member
  have boundary := (mem_terminalBoundaryPorts_iff _ _ _).mp member
  obtain ⟨external, consumer, _, selected, uses⟩ :=
    (terminalBoundaryWire_eq_true_iff _ _ _).mp boundary
  have consumerMember := (terminalGateSelected_eq_true_iff _ _).mp selected
  have producerMember := outputConeRecords_closed candidate consumer producer
    consumerMember uses
  have producerSelected := (terminalGateSelected_eq_true_iff _ _).mpr producerMember
  have producerUnselected := (terminalWireExternal_eq_true_iff _ _).mp external
  change terminalGateSelected (outputConeRecords candidate) producer = false at producerUnselected
  rw [producerSelected] at producerUnselected
  exact Bool.noConfusion producerUnselected

private def coneLocateMember {alpha : Type} [DecidableEq alpha] (item : alpha) :
    (items : List alpha) → item ∈ items →
      {index : Fin items.length // items.get index = item}
  | [], member => False.elim (by cases member)
  | head :: tail, member =>
      if equal : item = head then
        ⟨⟨0, by simp only [List.length_cons]; exact Nat.zero_lt_succ _⟩,
          by change head = item; exact equal.symm⟩
      else
        let tailMember := (List.mem_cons.mp member).resolve_left equal
        let located := coneLocateMember item tail tailMember
        ⟨located.1.succ, by
          change tail.get located.1 = item
          exact located.2⟩

/-- Rename the computed incoming boundary back to actual primary inputs.
The impossible gate case is discharged by predecessor closure. -/
private def outputConeBoundaryInput {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (index : Fin (terminalBoundaryPorts candidate.program
      (outputConeRecords candidate)).length) : Fin inputs :=
  match wireEq : (terminalBoundaryPorts candidate.program
      (outputConeRecords candidate)).get index with
  | .input original => original
  | .gate producer => False.elim
      (outputConeRecords_noExternalGate candidate producer
        (wireEq ▸ List.get_mem _ index))

private theorem outputConeBoundaryInput_value {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (input : Valuation inputs)
    (index : Fin (terminalBoundaryPorts candidate.program
      (outputConeRecords candidate)).length) :
    input (outputConeBoundaryInput candidate index) =
      terminalInducedBoundaryValuation candidate (outputConeRecords candidate)
        input index := by
  unfold outputConeBoundaryInput
  split
  · rename_i original wireEq
    simp only [terminalInducedBoundaryValuation, wireEq,
      TerminalSupportWire.candidateValue]
  · rename_i producer wireEq
    exact False.elim (outputConeRecords_noExternalGate candidate producer
      (wireEq ▸ List.get_mem _ index))

private def outputConeRenamedCandidate {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) :=
  (extractTerminalSupport candidate (outputConeRecords candidate)).extractedCandidate.renameInputs
    (outputConeBoundaryInput candidate)


/-- The retained cone with its complete physical outgoing frontier, including
live wires consumed only by removed gates. This exposes the existing computed
frontier without changing the pruning algorithm. -/
def outputConeFrontierCandidate {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) :
    Candidate inputs
      (extractTerminalSupport candidate (outputConeRecords candidate)).gateCount
      (terminalInterfacePorts candidate (outputConeRecords candidate)).length :=
  outputConeRenamedCandidate candidate

/-- Every retained frontier port has its original whole-circuit value. -/
theorem outputConeFrontierCandidate_semantics {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (input : Valuation inputs)
    (output : Fin (terminalInterfacePorts candidate (outputConeRecords candidate)).length) :
    (outputConeFrontierCandidate candidate).semantics input output =
      candidate.program.eval input
        ((terminalInterfacePorts candidate (outputConeRecords candidate)).get output) := by
  have renamed := Candidate.renameInputs_semantics (outputConeBoundaryInput candidate)
    (extractTerminalSupport candidate (outputConeRecords candidate)).extractedCandidate
    input output
  have boundaryValues : (fun index => input (outputConeBoundaryInput candidate index)) =
      terminalInducedBoundaryValuation candidate (outputConeRecords candidate) input := by
    funext index
    exact outputConeBoundaryInput_value candidate input index
  have boundaryMatch := congrArg
    (fun valuation =>
      (extractTerminalSupport candidate (outputConeRecords candidate)).extractedCandidate.semantics
        valuation output) boundaryValues
  exact renamed.trans (boundaryMatch.trans
    (extractTerminalSupport_induced candidate (outputConeRecords candidate) input output))

private theorem outputConeOutput_interface {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (output : Fin outputs)
    (producer : Fin gates)
    (wireEq : candidate.directWireWord.source output = .gate producer) :
    producer ∈ terminalInterfacePorts candidate (outputConeRecords candidate) := by
  have isOutput := (terminalGateIsGlobalOutput_eq_true_iff
    candidate.directWireWord producer).mpr ⟨output, wireEq⟩
  apply (mem_terminalInterfacePorts_iff _ _ _).mpr
  apply (terminalInterfaceGate_eq_true_iff _ _ _).mpr
  exact ⟨(terminalGateSelected_eq_true_iff _ _).mpr
    (outputConeRecords_output candidate producer isOutput), Or.inr isOutput⟩

/-- Reconnect each original output position, including constants, primary
inputs and repeated gate wires. -/
private def outputConeOutputSource {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (output : Fin outputs) :
    Source inputs (extractTerminalSupport candidate (outputConeRecords candidate)).gateCount :=
  match wireEq : candidate.directWireWord.source output with
  | .input original => .input original
  | .constant value => .constant value
  | .gate producer =>
      let located := coneLocateMember producer
        (terminalInterfacePorts candidate (outputConeRecords candidate))
        (outputConeOutput_interface candidate output producer wireEq)
      (outputConeRenamedCandidate candidate).directWireWord.source located.1

private theorem outputConeOutputSource_eval {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (input : Valuation inputs) (output : Fin outputs) :
    (outputConeOutputSource candidate output).eval input
        ((outputConeRenamedCandidate candidate).program.eval input) =
      candidate.semantics input output := by
  unfold outputConeOutputSource
  split
  · rename_i original wireEq
    simp only [Candidate.semantics, semantics, DirectWireWord.eval, wireEq, Source.eval]
  · rename_i value wireEq
    simp only [Candidate.semantics, semantics, DirectWireWord.eval, wireEq, Source.eval]
  · rename_i producer wireEq
    let located := coneLocateMember producer
      (terminalInterfacePorts candidate (outputConeRecords candidate))
      (outputConeOutput_interface candidate output producer wireEq)
    change (outputConeRenamedCandidate candidate).semantics input located.1 = _
    rw [outputConeRenamedCandidate, Candidate.renameInputs_semantics]
    have boundaryValues : (fun index => input (outputConeBoundaryInput candidate index)) =
        terminalInducedBoundaryValuation candidate (outputConeRecords candidate) input := by
      funext index
      exact outputConeBoundaryInput_value candidate input index
    rw [boundaryValues]
    exact (extractTerminalSupport_induced candidate (outputConeRecords candidate)
      input located.1).trans (by
        rw [located.2]
        simp only [Candidate.semantics, semantics, DirectWireWord.eval, wireEq, Source.eval])

/-- Extract the computed output cone and return the original input/output shape. -/
def outputConeImplementation {inputs outputs : Nat}
    (current : Implementation inputs outputs) : Implementation inputs outputs :=
  { gateCount := (extractTerminalSupport current.candidate
      (outputConeRecords current.candidate)).gateCount
    candidate := Candidate.ofDirectWireWord
      (outputConeRenamedCandidate current.candidate).program
      ⟨outputConeOutputSource current.candidate⟩ }

/-- The complete ordered output semantics is unchanged for every valuation. -/
theorem outputConeImplementation_equivalent {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    Equivalent (outputConeImplementation current).candidate.program
      (outputConeImplementation current).candidate.directWireWord
      current.candidate.program current.candidate.directWireWord := by
  intro input output
  change (outputConeImplementation current).candidate.semantics input output = _
  rw [outputConeImplementation, Candidate.ofDirectWireWord_semantics]
  exact outputConeOutputSource_eval current.candidate input output

private theorem coneSelectedGateCount_le {gates : Nat} (selected : Fin gates → Bool) :
    (terminalSelectedGateIndices selected).length ≤ gates := by
  induction gates with
  | zero => exact Nat.le_refl 0
  | succ gates ih =>
      have earlier := ih (fun gate => selected gate.castSucc)
      cases lastValue : selected (Fin.last gates) <;>
        simp only [terminalSelectedGateIndices, lastValue, Bool.false_eq_true,
          if_false, if_true, List.length_append, List.length_map,
          List.length_cons, List.length_nil] <;> omega

/-- One physical gate is emitted for each selected original gate; none is added. -/
theorem outputConeImplementation_gateCount_le {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    (outputConeImplementation current).gateCount ≤ current.gateCount := by
  change (extractTerminalSupport current.candidate
    (outputConeRecords current.candidate)).gateCount ≤ current.gateCount
  rw [extractTerminalSupport_gateCount]
  exact coneSelectedGateCount_le _

/-- Number of original physical gates deleted by the computed pass. -/
def outputConeDeletedGateCount {inputs outputs : Nat}
    (current : Implementation inputs outputs) : Nat :=
  current.gateCount - (outputConeImplementation current).gateCount

/-- Retained and deleted gates account for the exact original physical cost. -/
theorem outputConeImplementation_exact_accounting {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    (outputConeImplementation current).gateCount + outputConeDeletedGateCount current =
      current.gateCount := by
  have bounded := outputConeImplementation_gateCount_le current
  unfold outputConeDeletedGateCount
  omega

/-- Semantic reference minimum is invariant; the pass never executes its search. -/
theorem outputConeImplementation_referenceMinimum {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    referenceMinimum (outputConeImplementation current) = referenceMinimum current :=
  referenceMinimum_invariant (outputConeImplementation current) current
    (outputConeImplementation_equivalent current)

/-- Deleting unused physical gates retires exactly that many units of slack. -/
theorem outputConeImplementation_residualSlack {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    residualSlack current = residualSlack (outputConeImplementation current) +
      outputConeDeletedGateCount current := by
  have accounting := outputConeImplementation_exact_accounting current
  have bounded := referenceMinimum_le_target (outputConeImplementation current)
  have sameMinimum := outputConeImplementation_referenceMinimum current
  unfold residualSlack
  rw [sameMinimum] at bounded ⊢
  omega

/-- A strict physical gain is produced exactly when a gate was deleted.
This does not assert preservation of arbitrary supplied full-profile observers. -/
theorem outputConeImplementation_strictGain_iff {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    StrictEquivalentGain current (outputConeImplementation current) ↔
      0 < outputConeDeletedGateCount current := by
  have accounting := outputConeImplementation_exact_accounting current
  constructor
  · intro gain
    have smaller := gain.smaller
    omega
  · intro positive
    exact ⟨by omega, outputConeImplementation_equivalent current⟩

/-- Concrete physical pruning stage for the existing normalizer interface. -/
def outputConeNormalizer : PCCMinTotalNormalizer where
  normalize := fun current =>
    if positive : 0 < outputConeDeletedGateCount current then
      .gain (outputConeImplementation current)
        ((outputConeImplementation_strictGain_iff current).mpr positive)
    else
      .normal
        { result := outputConeImplementation current
          equivalent := outputConeImplementation_equivalent current
          gateCount_le := outputConeImplementation_gateCount_le current }

/-- Both branches expose the computed implementation; the no-deletion branch
does not assert semantic minimality, full normal form or global completion. -/
theorem outputConeNormalizer_checked {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    match outputConeNormalizer.normalize current with
    | .gain next _ =>
        next = outputConeImplementation current ∧
          0 < outputConeDeletedGateCount current
    | .normal normalized =>
        normalized.result = outputConeImplementation current ∧
          outputConeDeletedGateCount current = 0 ∧
          normalized.result.gateCount = current.gateCount := by
  by_cases positive : 0 < outputConeDeletedGateCount current
  · simp only [outputConeNormalizer, positive, dite_true]
    constructor <;> trivial
  · simp only [outputConeNormalizer, positive, dite_false]
    have accounting := outputConeImplementation_exact_accounting current
    exact ⟨trivial, by omega, by omega⟩

end DirectWire
end PNP
