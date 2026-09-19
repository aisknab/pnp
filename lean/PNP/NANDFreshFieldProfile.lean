import PNP.NANDFreshFieldExtension
import PNP.NANDWireProfileRestoration

/-!
Bind the verified independent-field family to the repository's actual full and
quotient profile minima. Added inputs are unused by the old computation; the
fields are actual independent NAND gate outputs. The resulting positive defect
is forced semantically. Arbitrary internal fields, arbitrary materializer
charges, global routing, and polynomial minimization remain outside this result.
-/

namespace PNP.DirectWire.FreshNandCost

variable {inputs outputs : Nat}

def padInputs (target : Implementation inputs outputs) (extra : Nat) :
    Implementation (inputs + extra) outputs :=
  ⟨target.gateCount, target.candidate.renameInputs (Fin.castAdd extra)⟩

theorem padInputs_semantics (target : Implementation inputs outputs) (extra : Nat)
    (valuation : Valuation (inputs + extra)) (output : Fin outputs) :
    (padInputs target extra).candidate.semantics valuation output =
      target.candidate.semantics (fun index => valuation (Fin.castAdd extra index)) output :=
  Candidate.renameInputs_semantics (Fin.castAdd extra) target.candidate valuation output

private def restrictionPrefix (inputs extra : Nat) : Candidate inputs 0 (inputs + extra) :=
  Candidate.ofDirectWireWord .empty
    ⟨splitFin (fun index => .input index) (fun _ => .constant false)⟩

private theorem restrictionPrefix_input (extra : Nat) (valuation : Valuation inputs)
    (index : Fin inputs) :
    (restrictionPrefix inputs extra).semantics valuation (Fin.castAdd extra index) =
      valuation index := by
  unfold restrictionPrefix
  rw [Candidate.ofDirectWireWord_semantics]
  unfold DirectWire.semantics DirectWireWord.eval
  dsimp only
  rw [splitFin_left]
  rfl

/-- Unused primary inputs do not change the minimum over arbitrary realizations. -/
theorem referenceMinimum_padInputs (target : Implementation inputs outputs) (extra : Nat) :
    referenceMinimum (padInputs target extra) = referenceMinimum target := by
  apply Nat.le_antisymm
  · apply referenceMinimum_le_of_equivalent (padInputs target extra)
      ((referenceMinimumWitness target).renameInputs (Fin.castAdd extra))
    intro valuation output
    change ((referenceMinimumWitness target).renameInputs (Fin.castAdd extra)).semantics
      valuation output = (padInputs target extra).candidate.semantics valuation output
    rw [Candidate.renameInputs_semantics, padInputs_semantics]
    exact equivalentBool_sound (referenceMinimumWitness_equivalent target) _ output
  · let witness := referenceMinimumWitness (padInputs target extra)
    let restricted := (restrictionPrefix inputs extra).sequential witness
    have equivalent : Equivalent restricted.program restricted.directWireWord
        target.candidate.program target.candidate.directWireWord := by
      intro valuation output
      change restricted.semantics valuation output = target.candidate.semantics valuation output
      dsimp only [restricted]
      rw [Candidate.sequential_semantics]
      have same := equivalentBool_sound (referenceMinimumWitness_equivalent (padInputs target extra))
      have result := same ((restrictionPrefix inputs extra).semantics valuation) output
      change witness.semantics ((restrictionPrefix inputs extra).semantics valuation) output =
        (padInputs target extra).candidate.semantics
          ((restrictionPrefix inputs extra).semantics valuation) output at result
      rw [padInputs_semantics] at result
      have inputEqual : (fun index =>
          (restrictionPrefix inputs extra).semantics valuation (Fin.castAdd extra index)) = valuation := by
        funext index
        exact restrictionPrefix_input extra valuation index
      rw [inputEqual] at result
      exact result
    have lower := referenceMinimum_le_of_equivalent target restricted equivalent
    simpa only [Nat.zero_add] using lower

def profile (target : Implementation inputs outputs) (width : Nat) :
    WireCarrier (inputs + (width + width)) outputs width :=
  WireCarrier.unpack (extend target width)

theorem profile_gateCount (target : Implementation inputs outputs) (width : Nat) :
    (profile target width).implementation.gateCount = target.gateCount + width := rfl

theorem profile_output (target : Implementation inputs outputs) (width : Nat)
    (valuation : Valuation (inputs + (width + width))) (output : Fin outputs) :
    (profile target width).implementation.candidate.semantics valuation output =
      target.candidate.semantics
        (fun index => valuation (Fin.castAdd (width + width) index)) output := by
  unfold profile
  rw [WireCarrier.unpack_output]
  exact extended_old target.candidate width valuation output

theorem profile_field (target : Implementation inputs outputs) (width : Nat)
    (valuation : Valuation (inputs + (width + width))) (field : Fin width) :
    (profile target width).fieldValue valuation field = freshValue valuation field := by
  unfold profile
  rw [WireCarrier.unpack_field]
  exact extended_fresh target.candidate width valuation field

theorem profile_fullMinimum (target : Implementation inputs outputs) (width : Nat) :
    WireProfile.fullMinimum (profile target width) = referenceMinimum target + width := by
  unfold WireProfile.fullMinimum profile
  rw [WireCarrier.exposed_unpack, referenceMinimum_extend]

private def forgotten (target : Implementation inputs outputs) (width : Nat) :
    Implementation (inputs + (width + width)) (outputs + width) :=
  ZeroCostExposure.extend (padInputs target (width + width))
    (fun _ : Fin width => .constant false)

private theorem forgotten_equivalent (target : Implementation inputs outputs) (width : Nat) :
    Equivalent (WireProfile.mask (profile target width) (fun _ => false)).exposed.candidate.program
      (WireProfile.mask (profile target width) (fun _ => false)).exposed.candidate.directWireWord
      (forgotten target width).candidate.program (forgotten target width).candidate.directWireWord := by
  intro valuation coordinate
  change (WireProfile.mask (profile target width) (fun _ => false)).exposed.candidate.semantics
    valuation coordinate = (forgotten target width).candidate.semantics valuation coordinate
  unfold forgotten
  rcases finSum_decompose coordinate with ⟨output, equal⟩ | ⟨field, equal⟩
  · rw [equal, WireCarrier.exposed_output, ZeroCostExposure.extend_original]
    change (profile target width).implementation.candidate.semantics valuation output =
      (padInputs target (width + width)).candidate.semantics valuation output
    rw [profile_output, padInputs_semantics]
  · rw [equal, WireCarrier.exposed_field, ZeroCostExposure.extend_field,
      WireProfile.mask_fieldValue]
    rfl

theorem profile_quotientMinimum (target : Implementation inputs outputs) (width : Nat) :
    WireProfile.quotientMinimum (profile target width) (fun _ => false) = referenceMinimum target := by
  have same := referenceMinimum_invariant
    (WireProfile.mask (profile target width) (fun _ => false)).exposed
    (forgotten target width) (forgotten_equivalent target width)
  have free := ZeroCostExposure.referenceMinimum_extend (padInputs target (width + width))
    (fun _ : Fin width => .constant false)
  exact same.trans (free.trans (referenceMinimum_padInputs target (width + width)))

theorem profile_projectionDefect (target : Implementation inputs outputs) (width : Nat) :
    WireProfile.projectionDefect (profile target width) (fun _ => false) = width := by
  unfold WireProfile.projectionDefect
  rw [profile_fullMinimum, profile_quotientMinimum]
  rw [Nat.add_comm (referenceMinimum target) width, Nat.add_sub_cancel]

theorem profile_fullSlack (target : Implementation inputs outputs) (width : Nat) :
    WireProfile.fullSlack (profile target width) = residualSlack target := by
  unfold WireProfile.fullSlack residualSlack
  rw [profile_gateCount, profile_fullMinimum]
  omega

/-- The existing materializer cannot pay less than the independently proved defect.
No equality with its charge, or optimality of its output, is inferred. -/
theorem profile_materializer_charge_lower_bound
    (target : Implementation inputs outputs) (width : Nat) :
    width ≤ WireQuotientLift.charge (profile target width) (fun _ => false) := by
  have lower := WireProfileRestoration.projectionDefect_le_charge
    (profile target width) (fun _ => false)
  rw [profile_projectionDefect] at lower
  exact lower

end PNP.DirectWire.FreshNandCost
