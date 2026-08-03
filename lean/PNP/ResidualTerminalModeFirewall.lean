/-
Copyright (c) 2026 PNP Labs.

The terminal full/quotient mode firewall for finite direct-wire profile data.
Projection keeps the complete Boolean implementation and semantics but may
forget finite profile coordinates.  Consequently projected profile equality is
comparison-only: constructive full-carrier use requires equality at every
forgotten coordinate as a checked full lift.

This is the direct-wire terminal specialization of the pinned manuscript's
mode firewall and its `quotientEqualityNotConstructive` MuBridge obligation.
It does not define support carriers, projection-defect minima, saturation,
Package E, BCELReady, ZeroSlack, or a polynomial residual route.
-/

import PNP.ResidualTerminalFullBridge

namespace PNP
namespace DirectWire

/-- The ten finite profile roles named by the manuscript's full carrier. -/
inductive TerminalProfileRole where
  | carrier
  | origin
  | kernel
  | obligation
  | prefix
  | direction
  | saturation
  | budget
  | charge
  | frontier
  deriving Repr, DecidableEq

/-- A finite Boolean encoding of terminal carrier profile data. -/
abbrev TerminalProfile (width : Nat) := Fin width → Bool

/-- A profile system computes every finite profile coordinate from the actual
    implementation.  It contains no caller assertion that projection or
    lifting is sound. -/
structure TerminalProfileSystem (inputs outputs profileWidth : Nat) where
  role : Fin profileWidth → TerminalProfileRole
  observe : Implementation inputs outputs → TerminalProfile profileWidth

/-- A forgetful quotient projection.  A `true` coordinate remains visible;
    a `false` coordinate is deliberately absent from quotient comparison. -/
structure TerminalProfileProjection (profileWidth : Nat) where
  keep : Fin profileWidth → Bool

/-- One profile coordinate is retained by the quotient projection. -/
def TerminalProfileProjection.Keeps {profileWidth : Nat}
    (projection : TerminalProfileProjection profileWidth)
    (coordinate : Fin profileWidth) : Prop :=
  projection.keep coordinate = true

/-- One profile coordinate is forgotten by the quotient projection. -/
def TerminalProfileProjection.Forgets {profileWidth : Nat}
    (projection : TerminalProfileProjection profileWidth)
    (coordinate : Fin profileWidth) : Prop :=
  projection.keep coordinate = false

/-- The projection retains every finite profile coordinate. -/
def TerminalProfileProjection.KeepsAll {profileWidth : Nat}
    (projection : TerminalProfileProjection profileWidth) : Prop :=
  ∀ coordinate, projection.Keeps coordinate

/-- All obligation-role coordinates computed for an implementation are closed.
    `true` represents an open obligation and `false` a discharged one. -/
def TerminalProfileSystem.ObligationsDischarged
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (implementation : Implementation inputs outputs) : Prop :=
  ∀ coordinate,
    system.role coordinate = .obligation →
      system.observe implementation coordinate = false

/-- A full-carrier realization retains complete Boolean semantics and agrees
    with the current implementation at every finite profile coordinate. -/
structure TerminalFullCarrierRealization
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) where
  realization : TerminalFullRealization current
  profileEqual : ∀ coordinate,
    system.observe realization.implementation coordinate =
      system.observe current coordinate

/-- A quotient comparison retains complete Boolean semantics but checks only
    the profile coordinates selected by the projection. -/
structure TerminalQuotientComparison
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current : Implementation inputs outputs) where
  realization : TerminalFullRealization current
  keptProfileEqual : ∀ coordinate,
    projection.Keeps coordinate →
      system.observe realization.implementation coordinate =
        system.observe current coordinate

/-- Project a full-carrier realization to comparison-only quotient evidence.
    The represented implementation is definitionally unchanged. -/
def TerminalFullCarrierRealization.project
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    (full : TerminalFullCarrierRealization system current) :
    TerminalQuotientComparison system projection current :=
  { realization := full.realization
    keptProfileEqual := fun coordinate _kept => full.profileEqual coordinate }

@[simp] theorem TerminalFullCarrierRealization.project_realization
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    (full : TerminalFullCarrierRealization system current) :
    (full.project (projection := projection)).realization = full.realization := rfl

/-- Projection keeps the exact represented direct-wire implementation. -/
theorem TerminalFullCarrierRealization.project_implementation
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    (full : TerminalFullCarrierRealization system current) :
    (full.project (projection := projection)).realization.implementation =
      full.realization.implementation := rfl

/-- Projection neither inserts nor removes a NAND gate. -/
theorem TerminalFullCarrierRealization.project_gateCount
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    (full : TerminalFullCarrierRealization system current) :
    (full.project (projection := projection)).realization.implementation.gateCount =
      full.realization.implementation.gateCount := rfl

/-- Projection preserves the complete multi-output Boolean equivalence. -/
theorem TerminalFullCarrierRealization.project_equivalent
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    (full : TerminalFullCarrierRealization system current) :
    Equivalent
      (full.project (projection := projection)).realization.implementation.candidate.program
      (full.project (projection := projection)).realization.implementation.candidate.directWireWord
      current.candidate.program current.candidate.directWireWord :=
  full.realization.equivalent

/-- Pointwise form of exact Boolean-semantic preservation by projection. -/
theorem TerminalFullCarrierRealization.project_semantics
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    (full : TerminalFullCarrierRealization system current)
    (input : Valuation inputs) (output : Fin outputs) :
    (full.project (projection := projection)).realization.implementation.candidate.semantics
        input output = current.candidate.semantics input output :=
  full.realization.equivalent input output

/-- Exact agreement on every coordinate omitted by a quotient comparison. -/
def TerminalQuotientComparison.LostProfileAgreement
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    (comparison : TerminalQuotientComparison system projection current) : Prop :=
  ∀ coordinate,
    projection.Forgets coordinate →
      system.observe comparison.realization.implementation coordinate =
        system.observe current coordinate

/-- A checked full lift consists precisely of quotient evidence plus equality
    at every finite coordinate that the quotient forgot. -/
structure TerminalCheckedFullLift
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    (comparison : TerminalQuotientComparison system projection current) : Prop where
  lostProfileAgreement : comparison.LostProfileAgreement

/-- A checked full lift reconstructs the full-carrier realization. -/
def TerminalCheckedFullLift.fullRealization
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    {comparison : TerminalQuotientComparison system projection current}
    (lift : TerminalCheckedFullLift comparison) :
    TerminalFullCarrierRealization system current :=
  { realization := comparison.realization
    profileEqual := by
      intro coordinate
      cases kept : projection.keep coordinate with
      | false => exact lift.lostProfileAgreement coordinate kept
      | true => exact comparison.keptProfileEqual coordinate kept }

@[simp] theorem TerminalCheckedFullLift.fullRealization_realization
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    {comparison : TerminalQuotientComparison system projection current}
    (lift : TerminalCheckedFullLift comparison) :
    lift.fullRealization.realization = comparison.realization := rfl

/-- Every full-profile coordinate reconstructed by a checked lift agrees with
    the target terminal carrier. -/
theorem TerminalCheckedFullLift.fullRealization_profileEqual
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    {comparison : TerminalQuotientComparison system projection current}
    (lift : TerminalCheckedFullLift comparison)
    (coordinate : Fin profileWidth) :
    system.observe lift.fullRealization.realization.implementation coordinate =
      system.observe current coordinate :=
  lift.fullRealization.profileEqual coordinate

/-- Full-carrier evidence supplies a checked lift of its own projection. -/
def TerminalFullCarrierRealization.checkedFullLift
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    (full : TerminalFullCarrierRealization system current) :
    TerminalCheckedFullLift (full.project (projection := projection)) :=
  { lostProfileAgreement := fun coordinate _forgotten =>
      full.profileEqual coordinate }

/-- Full profile agreement for the implementation represented by a quotient
    comparison. -/
def TerminalQuotientComparison.FullProfileEqual
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    (comparison : TerminalQuotientComparison system projection current) : Prop :=
  ∀ coordinate,
    system.observe comparison.realization.implementation coordinate =
      system.observe current coordinate

/-- The mode firewall's exact positive direction: a quotient comparison has a
    checked full lift exactly when its complete full profile agrees. -/
theorem terminalCheckedFullLift_iff_fullProfileEqual
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    (comparison : TerminalQuotientComparison system projection current) :
    TerminalCheckedFullLift comparison ↔ comparison.FullProfileEqual := by
  constructor
  · intro lift
    exact lift.fullRealization.profileEqual
  · intro fullEqual
    constructor
    intro coordinate _forgotten
    exact fullEqual coordinate

/-- A lossless projection needs no additional coordinate evidence. -/
theorem TerminalQuotientComparison.checkedFullLift_of_keepsAll
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    (comparison : TerminalQuotientComparison system projection current)
    (keepsAll : projection.KeepsAll) :
    TerminalCheckedFullLift comparison :=
  { lostProfileAgreement := by
      intro coordinate forgotten
      have kept := keepsAll coordinate
      change projection.keep coordinate = true at kept
      change projection.keep coordinate = false at forgotten
      rw [kept] at forgotten
      exact False.elim (Bool.noConfusion forgotten) }

/-- A full-carrier realization transports closure of all obligation-role
    coordinates from the current carrier to the represented implementation. -/
theorem TerminalFullCarrierRealization.obligationsDischarged
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {current : Implementation inputs outputs}
    (full : TerminalFullCarrierRealization system current)
    (currentDischarged : system.ObligationsDischarged current) :
    system.ObligationsDischarged full.realization.implementation := by
  intro coordinate roleEqual
  rw [full.profileEqual coordinate]
  exact currentDischarged coordinate roleEqual

/-- Checked lifting cannot silently reopen a forgotten obligation. -/
theorem TerminalCheckedFullLift.obligationsDischarged
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    {comparison : TerminalQuotientComparison system projection current}
    (lift : TerminalCheckedFullLift comparison)
    (currentDischarged : system.ObligationsDischarged current) :
    system.ObligationsDischarged comparison.realization.implementation :=
  lift.fullRealization.obligationsDischarged currentDischarged

/-- A quotient comparison contains a concrete lost-coordinate mismatch. -/
def TerminalQuotientComparison.ForgottenMismatch
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    (comparison : TerminalQuotientComparison system projection current) : Prop :=
  ∃ coordinate,
    projection.Forgets coordinate ∧
      system.observe comparison.realization.implementation coordinate ≠
        system.observe current coordinate

/-- The terminal MuBridge firewall obligation.  Quotient equality cannot be
    used constructively when any forgotten full-profile coordinate differs. -/
theorem terminalQuotientEqualityNotConstructive
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    (comparison : TerminalQuotientComparison system projection current)
    (mismatch : comparison.ForgottenMismatch) :
    ¬TerminalCheckedFullLift comparison := by
  intro lift
  obtain ⟨coordinate, forgotten, different⟩ := mismatch
  exact different (lift.lostProfileAgreement coordinate forgotten)

end DirectWire
end PNP
