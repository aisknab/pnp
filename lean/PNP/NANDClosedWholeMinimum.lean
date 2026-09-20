import PNP.NANDClosedWholeMinimumPrefix

/-!
Size-preserving comparison from arbitrary full-equivalent whole carriers to
the actual computed whole-support interface. These proofs compare finite
reference minima; they are not a polynomial construction or a local rule trace.
-/

namespace PNP.DirectWire.ClosedWholeMinimum

variable {inputs outputs fields : Nat}

def forwardSource (target offered : WireCarrier inputs outputs fields)
    (producer : Fin target.implementation.gateCount) :
    Source (inputs + target.implementation.gateCount) offered.implementation.gateCount :=
  match outputIndex target producer with
  | some output => (offered.implementation.candidate.directWireWord.source output).renameInputs
      (Fin.castAdd target.implementation.gateCount)
  | none => .constant false

def forward (target offered : WireCarrier inputs outputs fields) :
    Implementation (inputs + target.implementation.gateCount) target.implementation.gateCount :=
  (Candidate.ofDirectWireWord
    (WireProfileAmbient.padImplementation offered.implementation
      target.implementation.gateCount).candidate.program
    ⟨forwardSource target offered⟩).toImplementation

theorem forward_gateCount (target offered : WireCarrier inputs outputs fields) :
    (forward target offered).gateCount = offered.implementation.gateCount := rfl

theorem forward_output_some (target offered : WireCarrier inputs outputs fields)
    (producer : Fin target.implementation.gateCount) (output : Fin outputs)
    (found : outputIndex target producer = some output)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (forward target offered).candidate.semantics valuation producer =
      offered.implementation.candidate.semantics
        (fun index => valuation (Fin.castAdd target.implementation.gateCount index)) output := by
  change (Candidate.ofDirectWireWord
    (WireProfileAmbient.padImplementation offered.implementation
      target.implementation.gateCount).candidate.program
    ⟨forwardSource target offered⟩).semantics valuation producer = _
  rw [Candidate.ofDirectWireWord_semantics]
  change (forwardSource target offered producer).eval valuation
    ((WireProfileAmbient.padImplementation offered.implementation
      target.implementation.gateCount).candidate.program.eval valuation) = _
  unfold forwardSource
  rw [found]
  exact WireProfileAmbient.eval_paddedSource offered.implementation
    target.implementation.gateCount
    (offered.implementation.candidate.directWireWord.source output) valuation

theorem forward_output_none (target offered : WireCarrier inputs outputs fields)
    (producer : Fin target.implementation.gateCount)
    (missing : outputIndex target producer = none)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (forward target offered).candidate.semantics valuation producer = false := by
  change (Candidate.ofDirectWireWord
    (WireProfileAmbient.padImplementation offered.implementation
      target.implementation.gateCount).candidate.program
    ⟨forwardSource target offered⟩).semantics valuation producer = false
  rw [Candidate.ofDirectWireWord_semantics]
  change (forwardSource target offered producer).eval valuation _ = false
  unfold forwardSource
  rw [missing]
  rfl

theorem forward_equivalent (target offered : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (same : WireProfile.FullEquivalent target offered) :
    Equivalent (forward target offered).candidate.program
      (forward target offered).candidate.directWireWord
      (ClosedSupportObservation.implementation target keep (seed target)).candidate.program
      (ClosedSupportObservation.implementation target keep (seed target)).candidate.directWireWord := by
  intro valuation producer
  change (forward target offered).candidate.semantics valuation producer =
    (ClosedSupportObservation.implementation target keep (seed target)).candidate.semantics
      valuation producer
  cases found : outputIndex target producer with
  | none =>
      exact (forward_output_none target offered producer found valuation).trans
        (ambient_output_absent target keep producer found valuation).symm
  | some output =>
      have sourceAt := outputIndex_sound target producer output found
      have member := (interface_iff_output target keep producer).mpr ⟨output, sourceAt⟩
      rw [forward_output_some target offered producer output found]
      have original :
          target.implementation.candidate.semantics
              (fun index => valuation (Fin.castAdd target.implementation.gateCount index)) output =
            target.implementation.candidate.program.eval
              (fun index => valuation (Fin.castAdd target.implementation.gateCount index)) producer := by
        change (target.implementation.candidate.directWireWord.source output).eval _ _ = _
        rw [sourceAt]
        rfl
      exact (((WireProfile.full_iff target offered).mp same).1 _ output).trans
        (original.trans (ClosedSupportFullGain.ambient_output target keep (seed target)
          producer member valuation).symm)

theorem forward_available (target offered : WireCarrier inputs outputs fields)
    (same : WireProfile.FullEquivalent target offered) (field : Fin fields) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (forward target offered) field = true := by
  apply WireProfileAvailability.available_of_source
    (WireProfileAmbient.ambientTarget target) (forward target offered) field
    ((offered.source field).renameInputs (Fin.castAdd target.implementation.gateCount))
  intro valuation
  have evaluated := WireProfileAmbient.eval_paddedSource offered.implementation
    target.implementation.gateCount (offered.source field) valuation
  exact evaluated.trans
    ((((WireProfile.full_iff target offered).mp same).2 _ field).trans
      (WireProfileFieldClosed.ambient_fieldValue target valuation field).symm)

def fullComparison (target offered : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (same : WireProfile.FullEquivalent target offered) :
    TerminalFullCarrierRealization (WireProfileAmbient.model target keep).ambientProfileSystem
      (ClosedSupportObservation.implementation target keep (seed target)) :=
  { realization :=
      { implementation := forward target offered
        equivalent := forward_equivalent target offered keep same }
    profileEqual := fun field =>
      (forward_available target offered same field).trans
        (available_all target keep field).symm }

theorem support_minimum_le (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (snapshot target keep).fullMinimum ≤ WireProfile.fullMinimum target := by
  have lower := terminalFullProfileMinimum_le
    (fullComparison target (WireProfile.fullWitness target) keep
      (WireProfile.fullWitness_matches target))
  change (snapshot target keep).fullMinimum ≤
    (forward target (WireProfile.fullWitness target)).gateCount at lower
  rw [forward_gateCount, WireProfile.fullWitness_gateCount] at lower
  exact lower

/-- Equality is established by explicit size-preserving comparisons in both directions. -/
theorem full_minimum (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (snapshot target keep).fullMinimum = WireProfile.fullMinimum target :=
  Nat.le_antisymm (support_minimum_le target keep) (global_minimum_le target keep)

/-- The actual computed replacement attains the independent whole-carrier full minimum. -/
theorem result_optimal (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (ClosedSupportFullGain.result target keep (seed target)).implementation.gateCount =
      WireProfile.fullMinimum target :=
  (result_gateCount target keep).trans (full_minimum target keep)

theorem fullSlack_eq (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (snapshot target keep).fullSlack = WireProfile.fullSlack target := by
  change (extractTerminalSupport target.implementation.candidate (records target keep)).gateCount -
    (snapshot target keep).fullMinimum =
      target.implementation.gateCount - WireProfile.fullMinimum target
  rw [support_gateCount, full_minimum]

theorem result_zero_fullSlack (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    WireProfile.fullSlack (ClosedSupportFullGain.result target keep (seed target)) = 0 := by
  unfold WireProfile.fullSlack
  rw [ClosedSupportFullGain.result_fullMinimum, result_optimal, Nat.sub_self]

/-- This is a whole-span reference branch, not proper-local VerifyDW. -/
theorem improvement_none_iff (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    ClosedSupportFullGain.improvement? target keep (seed target) = none ↔
      WireProfile.fullSlack target = 0 := by
  rw [ClosedSupportFullGain.improvement?_none_iff]
  change (snapshot target keep).fullSlack = 0 ↔ WireProfile.fullSlack target = 0
  rw [fullSlack_eq]

end PNP.DirectWire.ClosedWholeMinimum
