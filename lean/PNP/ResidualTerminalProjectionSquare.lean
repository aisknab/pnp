/-
Copyright (c) 2026 PNP Labs.

Forgetful projection of governed terminal support squares.  Projection keeps
the physical boundary and interface of every completed support, and retains
exactly the selected profile coordinates in each of the ten terminal roles.
The projected meet remains the exact shared profile overlap, while the
projected join equals a side-only projected frontier pushout that never reads
the join corner.

This reconstructs the projection-commutation edge in Section 3 of the pinned
manuscript for every finite computed saturated terminal support square and
every explicit forgetful terminal projection.  The terminal dependency system
remains explicit data.  No transported four-corner minimum, BN2 square
legitimacy, side-tight basis, obstruction route, SaturatePositive, BCELReady,
ZeroSlack, PCCMin, polynomial-runtime, or P = NP claim is made.
-/

import PNP.ResidualTerminalFrontierPushout

namespace PNP
namespace DirectWire

/-- Forget selected finite profile coordinates while retaining the complete
    physical frontier. -/
def TerminalGovernedFrontier.project
    {inputs gates profileWidth : Nat}
    (frontier : TerminalGovernedFrontier inputs gates profileWidth)
    (projection : TerminalProfileProjection profileWidth) :
    TerminalGovernedFrontier inputs gates profileWidth :=
  { boundary := frontier.boundary
    interface := frontier.interface
    profiles := fun role =>
      (frontier.profiles role).filter projection.keep }

/-- Projection never changes the incoming physical boundary. -/
theorem TerminalGovernedFrontier.project_boundary
    {inputs gates profileWidth : Nat}
    (frontier : TerminalGovernedFrontier inputs gates profileWidth)
    (projection : TerminalProfileProjection profileWidth) :
    (frontier.project projection).boundary = frontier.boundary :=
  rfl

/-- Projection never changes the outgoing physical interface. -/
theorem TerminalGovernedFrontier.project_interface
    {inputs gates profileWidth : Nat}
    (frontier : TerminalGovernedFrontier inputs gates profileWidth)
    (projection : TerminalProfileProjection profileWidth) :
    (frontier.project projection).interface = frontier.interface :=
  rfl

/-- Exact profile membership after forgetful projection. -/
theorem TerminalGovernedFrontier.mem_project_profiles_iff
    {inputs gates profileWidth : Nat}
    (frontier : TerminalGovernedFrontier inputs gates profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth) :
    coordinate ∈ (frontier.project projection).profiles role ↔
      coordinate ∈ frontier.profiles role ∧ projection.Keeps coordinate := by
  unfold TerminalGovernedFrontier.project TerminalProfileProjection.Keeps
  constructor
  · intro member
    exact List.mem_filter.mp member
  · intro retained
    exact List.mem_filter.mpr retained

/-- Projection preserves duplicate freedom in every profile role. -/
theorem TerminalGovernedFrontier.project_profiles_nodup
    {inputs gates profileWidth : Nat}
    (frontier : TerminalGovernedFrontier inputs gates profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (role : TerminalProfileRole)
    (distinct : (frontier.profiles role).Nodup) :
    ((frontier.project projection).profiles role).Nodup := by
  exact distinct.sublist List.filter_sublist

/-- Applying the same forgetful projection twice changes nothing. -/
theorem TerminalGovernedFrontier.project_idempotent
    {inputs gates profileWidth : Nat}
    (frontier : TerminalGovernedFrontier inputs gates profileWidth)
    (projection : TerminalProfileProjection profileWidth) :
    (frontier.project projection).project projection =
      frontier.project projection := by
  apply TerminalGovernedFrontier.extensionality
  · rfl
  · rfl
  · funext role
    simp only [TerminalGovernedFrontier.project, List.filter_filter,
      Bool.and_self]

/-- The projected side-only pushout.  Its physical fields are the existing
    computed gluing, and its profile fields retain exactly the coordinates
    selected by the quotient projection.  No join data is an input. -/
def terminalProjectedGovernedFrontierPushout
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalGovernedCompletedSupport candidate system)
    (projection : TerminalProfileProjection profileWidth) :
    TerminalGovernedFrontier inputs gates profileWidth :=
  { boundary := terminalBoundaryFrontierPushout left right
    interface := terminalInterfaceFrontierPushout left right
    profiles := fun role =>
      (terminalProfileFrontierPushout left right role).filter projection.keep }

/-- Exact role-preserving membership in the projected side-only pushout. -/
theorem mem_terminalProjectedGovernedFrontierPushout_profiles_iff
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalGovernedCompletedSupport candidate system)
    (projection : TerminalProfileProjection profileWidth)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth) :
    coordinate ∈
        (terminalProjectedGovernedFrontierPushout left right projection).profiles role ↔
      (coordinate ∈ left.profileCoordinates role ∨
        coordinate ∈ right.profileCoordinates role) ∧
        projection.Keeps coordinate := by
  unfold terminalProjectedGovernedFrontierPushout
    TerminalProfileProjection.Keeps
  rw [List.mem_filter, mem_terminalProfileFrontierPushout_iff]

/-- Projection commutes exactly with the side-only governed frontier pushout. -/
theorem TerminalGovernedFrontier.project_pushout
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalGovernedCompletedSupport candidate system)
    (projection : TerminalProfileProjection profileWidth) :
    (terminalGovernedFrontierPushout left right).project projection =
      terminalProjectedGovernedFrontierPushout left right projection :=
  rfl

/-- The computed projected frontier of one saturated support-square corner. -/
def TerminalSaturatedSupportSquare.projectedFrontier
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (projection : TerminalProfileProjection profileWidth)
    (corner : TerminalSupportSquareCorner) :
    TerminalGovernedFrontier inputs gates profileWidth :=
  (square.governedCompleted candidate corner).frontier.project projection

/-- Projection retains the exact computed physical boundary at every corner. -/
theorem TerminalSaturatedSupportSquare.projectedFrontier_boundary
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (projection : TerminalProfileProjection profileWidth)
    (corner : TerminalSupportSquareCorner) :
    (square.projectedFrontier candidate projection corner).boundary =
      (square.governedCompleted candidate corner).frontier.boundary :=
  rfl

/-- Projection retains the exact computed physical interface at every corner. -/
theorem TerminalSaturatedSupportSquare.projectedFrontier_interface
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (projection : TerminalProfileProjection profileWidth)
    (corner : TerminalSupportSquareCorner) :
    (square.projectedFrontier candidate projection corner).interface =
      (square.governedCompleted candidate corner).frontier.interface :=
  rfl

/-- Exact record, role, and projection membership at every projected corner. -/
theorem TerminalSaturatedSupportSquare.mem_projectedFrontier_profiles_iff
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (projection : TerminalProfileProjection profileWidth)
    (corner : TerminalSupportSquareCorner)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth) :
    coordinate ∈
        (square.projectedFrontier candidate projection corner).profiles role ↔
      (TerminalPrimitiveRecord.profile coordinate ∈ square.records corner ∧
        system.profileSystem.role coordinate = role) ∧
        projection.Keeps coordinate := by
  unfold TerminalSaturatedSupportSquare.projectedFrontier
  rw [TerminalGovernedFrontier.mem_project_profiles_iff]
  change (coordinate ∈
      (square.governedCompleted candidate corner).profileCoordinates role ∧
        projection.Keeps coordinate) ↔ _
  rw [square.governedCompleted_profile_iff]

/-- No projected square corner duplicates a retained profile coordinate. -/
theorem TerminalSaturatedSupportSquare.projectedFrontier_profiles_nodup
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (projection : TerminalProfileProjection profileWidth)
    (corner : TerminalSupportSquareCorner)
    (role : TerminalProfileRole) :
    ((square.projectedFrontier candidate projection corner).profiles role).Nodup := by
  apply TerminalGovernedFrontier.project_profiles_nodup
  exact (square.governedCompleted candidate corner).profileCoordinates_nodup role

/-- A coordinate explicitly forgotten by the projection occurs in no projected
    profile role at any corner. -/
theorem TerminalSaturatedSupportSquare.forgotten_not_mem_projectedFrontier
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (projection : TerminalProfileProjection profileWidth)
    (corner : TerminalSupportSquareCorner)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth)
    (forgotten : projection.Forgets coordinate) :
    coordinate ∉
      (square.projectedFrontier candidate projection corner).profiles role := by
  intro member
  have kept :=
    (TerminalGovernedFrontier.mem_project_profiles_iff
      (square.governedCompleted candidate corner).frontier projection role coordinate).1
      member |>.2
  change projection.keep coordinate = true at kept
  change projection.keep coordinate = false at forgotten
  rw [forgotten] at kept
  exact Bool.noConfusion kept

/-- The projected meet profile is exactly the shared projected side profile. -/
theorem TerminalSaturatedSupportSquare.projected_meet_profile_iff
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (projection : TerminalProfileProjection profileWidth)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth) :
    coordinate ∈
        (square.projectedFrontier candidate projection .meet).profiles role ↔
      coordinate ∈
          (square.projectedFrontier candidate projection .left).profiles role ∧
        coordinate ∈
          (square.projectedFrontier candidate projection .right).profiles role := by
  unfold TerminalSaturatedSupportSquare.projectedFrontier
  rw [TerminalGovernedFrontier.mem_project_profiles_iff,
    TerminalGovernedFrontier.mem_project_profiles_iff,
    TerminalGovernedFrontier.mem_project_profiles_iff]
  change (coordinate ∈
        (square.governedCompleted candidate .meet).profileCoordinates role ∧
      projection.Keeps coordinate) ↔
    (coordinate ∈
          (square.governedCompleted candidate .left).profileCoordinates role ∧
        projection.Keeps coordinate) ∧
      coordinate ∈
          (square.governedCompleted candidate .right).profileCoordinates role ∧
        projection.Keeps coordinate
  rw [square.governedCompleted_meet_profile_iff]
  constructor
  · rintro ⟨⟨leftMember, rightMember⟩, kept⟩
    exact ⟨⟨leftMember, kept⟩, rightMember, kept⟩
  · rintro ⟨⟨leftMember, kept⟩, rightMember, _rightKept⟩
    exact ⟨⟨leftMember, rightMember⟩, kept⟩

/-- The projected join profile is exactly the union of the projected sides. -/
theorem TerminalSaturatedSupportSquare.projected_join_profile_iff
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (projection : TerminalProfileProjection profileWidth)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth) :
    coordinate ∈
        (square.projectedFrontier candidate projection .join).profiles role ↔
      coordinate ∈
          (square.projectedFrontier candidate projection .left).profiles role ∨
        coordinate ∈
          (square.projectedFrontier candidate projection .right).profiles role := by
  unfold TerminalSaturatedSupportSquare.projectedFrontier
  rw [TerminalGovernedFrontier.mem_project_profiles_iff,
    TerminalGovernedFrontier.mem_project_profiles_iff,
    TerminalGovernedFrontier.mem_project_profiles_iff]
  change (coordinate ∈
        (square.governedCompleted candidate .join).profileCoordinates role ∧
      projection.Keeps coordinate) ↔
    (coordinate ∈
          (square.governedCompleted candidate .left).profileCoordinates role ∧
        projection.Keeps coordinate) ∨
      coordinate ∈
          (square.governedCompleted candidate .right).profileCoordinates role ∧
        projection.Keeps coordinate
  rw [square.governedCompleted_join_profile_iff]
  constructor
  · rintro ⟨sideMember, kept⟩
    cases sideMember with
    | inl leftMember => exact Or.inl ⟨leftMember, kept⟩
    | inr rightMember => exact Or.inr ⟨rightMember, kept⟩
  · intro sideMember
    cases sideMember with
    | inl leftMember => exact ⟨Or.inl leftMember.1, leftMember.2⟩
    | inr rightMember => exact ⟨Or.inr rightMember.1, rightMember.2⟩

/-- The independently completed projected join equals the side-only projected
    pushout. -/
theorem TerminalSaturatedSupportSquare.projected_join_eq_pushout
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (projection : TerminalProfileProjection profileWidth) :
    square.projectedFrontier candidate projection .join =
      terminalProjectedGovernedFrontierPushout
        (square.governedCompleted candidate .left)
        (square.governedCompleted candidate .right) projection := by
  calc
    square.projectedFrontier candidate projection .join =
        ((terminalGovernedFrontierPushout
          (square.governedCompleted candidate .left)
          (square.governedCompleted candidate .right)).project projection) := by
      unfold TerminalSaturatedSupportSquare.projectedFrontier
      exact congrArg (fun frontier => frontier.project projection)
        (square.governed_frontier_pushout candidate).1
    _ = terminalProjectedGovernedFrontierPushout
          (square.governedCompleted candidate .left)
          (square.governedCompleted candidate .right) projection :=
      TerminalGovernedFrontier.project_pushout _ _ projection

/-- Structural projection compatibility for a computed saturated support
    square: the projected join is the side-only projected pushout and the
    projected meet is the exact shared side profile. -/
def TerminalSaturatedSupportSquare.ProjectionCompatible
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (projection : TerminalProfileProjection profileWidth) : Prop :=
  square.projectedFrontier candidate projection .join =
      terminalProjectedGovernedFrontierPushout
        (square.governedCompleted candidate .left)
        (square.governedCompleted candidate .right) projection ∧
    ∀ role coordinate,
      coordinate ∈
          (square.projectedFrontier candidate projection .meet).profiles role ↔
        coordinate ∈
            (square.projectedFrontier candidate projection .left).profiles role ∧
          coordinate ∈
            (square.projectedFrontier candidate projection .right).profiles role

/-- Legacy Section 3 projection-commutation law for every finite computed
    terminal support square and every forgetful terminal projection. -/
theorem TerminalSaturatedSupportSquare.governed_projection_compatible
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (projection : TerminalProfileProjection profileWidth) :
    square.ProjectionCompatible candidate projection := by
  constructor
  · exact square.projected_join_eq_pushout candidate projection
  · intro role coordinate
    exact square.projected_meet_profile_iff candidate projection role coordinate

end DirectWire
end PNP
