/-
Copyright (c) 2026 PNP Labs.

Canonical carrier transport for the four corners of every finite computed
terminal support square.  Each corner retains its exact extracted open
candidate and governed frontier, while physical and profile coordinates remain
in the common ambient wire, gate, and profile universes.  Side physical
coordinates are classified constructively as retained in the join or
internalized; profile coordinates transport exactly through meet and join.

This reconstructs the carrier-transport edge used by the
`fourCornerOptimaCarrierCompatible` obligation in Section 11.1 of the pinned
manuscript, building on the Section 3 support-square and projection laws.  It
does not transport minimum realizers, construct a coherent four-corner basis,
prove side-tight completion or BN2 square legitimacy, or establish
SaturatePositive, BCELReady, ZeroSlack, polynomial runtime, or P = NP.
-/

import PNP.ResidualTerminalSideTightMinimum

namespace PNP
namespace DirectWire

/-- The two side positions of a terminal support square. -/
inductive TerminalSupportSquareSide where
  | left
  | right
  deriving Repr, DecidableEq

/-- Embed a side position into the four-corner enumeration. -/
def TerminalSupportSquareSide.corner :
    TerminalSupportSquareSide -> TerminalSupportSquareCorner
  | .left => .left
  | .right => .right

/-- The opposite side, used to identify an internalizing support. -/
def TerminalSupportSquareSide.oppositeCorner :
    TerminalSupportSquareSide -> TerminalSupportSquareCorner
  | .left => .right
  | .right => .left

/-- Source data for one computed four-corner carrier.  Every endpoint and
    transport below is derived from these fields; no caller supplies a corner
    frontier, extracted candidate, or transport certificate. -/
structure TerminalFourCornerCarrier
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) where
  square : TerminalSaturatedSupportSquare system
  candidate : Candidate inputs gates outputs
  projection : TerminalProfileProjection profileWidth

/-- Canonical carrier associated with a computed support square. -/
def TerminalSaturatedSupportSquare.fourCornerCarrier
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (projection : TerminalProfileProjection profileWidth) :
    TerminalFourCornerCarrier system :=
  { square := square
    candidate := candidate
    projection := projection }

/-- The exact governed completion at one carrier corner. -/
def TerminalFourCornerCarrier.support
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner) :
    TerminalGovernedCompletedSupport carrier.candidate system :=
  carrier.square.governedCompleted carrier.candidate corner

/-- The exact open candidate extracted at one carrier corner. -/
def TerminalFourCornerCarrier.extracted
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner) :
    TerminalExtractedSupport (profileWidth := profileWidth) carrier.candidate :=
  carrier.square.extracted carrier.candidate corner

/-- The exact projected governed frontier at one carrier corner. -/
def TerminalFourCornerCarrier.projectedFrontier
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner) :
    TerminalGovernedFrontier inputs gates profileWidth :=
  carrier.square.projectedFrontier carrier.candidate carrier.projection corner

/-- Computed boundary disposition for a coordinate on either side.  Absence
    from the selected side returns `none`; a present coordinate is classified
    by the existing join construction. -/
def TerminalFourCornerCarrier.boundaryDisposition?
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (side : TerminalSupportSquareSide)
    (wire : TerminalSupportWire inputs gates) :
    Option TerminalFrontierDisposition :=
  if wire ∈ (carrier.support side.corner).frontier.boundary then
    some (terminalBoundaryFrontierDisposition
      (carrier.support .left) (carrier.support .right) wire)
  else
    none

/-- Computed interface disposition for a coordinate on either side. -/
def TerminalFourCornerCarrier.interfaceDisposition?
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (side : TerminalSupportSquareSide)
    (producer : Fin gates) : Option TerminalFrontierDisposition :=
  if producer ∈ (carrier.support side.corner).frontier.interface then
    some (terminalInterfaceFrontierDisposition
      (carrier.support .left) (carrier.support .right) producer)
  else
    none

/-- Exact success condition for fail-closed boundary classification. -/
theorem TerminalFourCornerCarrier.boundaryDisposition?_eq_some_iff
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (side : TerminalSupportSquareSide)
    (wire : TerminalSupportWire inputs gates)
    (disposition : TerminalFrontierDisposition) :
    carrier.boundaryDisposition? side wire = some disposition ↔
      wire ∈ (carrier.support side.corner).frontier.boundary ∧
        terminalBoundaryFrontierDisposition
          (carrier.support .left) (carrier.support .right) wire = disposition := by
  unfold TerminalFourCornerCarrier.boundaryDisposition?
  by_cases member : wire ∈ (carrier.support side.corner).frontier.boundary
  · rw [if_pos member]
    constructor
    · intro equal
      exact ⟨member, Option.some.inj equal⟩
    · intro result
      exact congrArg some result.2
  · rw [if_neg member]
    constructor
    · intro impossible
      cases impossible
    · intro result
      exact False.elim (member result.1)

/-- Exact success condition for fail-closed interface classification. -/
theorem TerminalFourCornerCarrier.interfaceDisposition?_eq_some_iff
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (side : TerminalSupportSquareSide)
    (producer : Fin gates)
    (disposition : TerminalFrontierDisposition) :
    carrier.interfaceDisposition? side producer = some disposition ↔
      producer ∈ (carrier.support side.corner).frontier.interface ∧
        terminalInterfaceFrontierDisposition
          (carrier.support .left) (carrier.support .right) producer =
            disposition := by
  unfold TerminalFourCornerCarrier.interfaceDisposition?
  by_cases member : producer ∈ (carrier.support side.corner).frontier.interface
  · rw [if_pos member]
    constructor
    · intro equal
      exact ⟨member, Option.some.inj equal⟩
    · intro result
      exact congrArg some result.2
  · rw [if_neg member]
    constructor
    · intro impossible
      cases impossible
    · intro result
      exact False.elim (member result.1)

private theorem nodup_of_listNoDuplicates {alpha : Type}
    {items : List alpha} (distinct : ListNoDuplicates items) : items.Nodup := by
  induction distinct with
  | nil => exact List.nodup_nil
  | cons headAbsent _tailDistinct ih =>
      exact List.nodup_cons.mpr ⟨headAbsent, ih⟩

/-- Every corner boundary is in canonical ambient order and duplicate-free. -/
theorem TerminalFourCornerCarrier.boundary_nodup
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner) :
    (carrier.support corner).frontier.boundary.Nodup := by
  rw [(carrier.support corner).frontier_boundary]
  exact (allTerminalSupportWires_nodup inputs gates).sublist List.filter_sublist

/-- Every corner interface is in canonical ambient order and duplicate-free. -/
theorem TerminalFourCornerCarrier.interface_nodup
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner) :
    (carrier.support corner).frontier.interface.Nodup := by
  rw [(carrier.support corner).frontier_interface]
  exact (nodup_of_listNoDuplicates (allFin_noDuplicates gates)).sublist
    List.filter_sublist

/-- Every role-indexed profile list is in canonical ambient order and
    duplicate-free. -/
theorem TerminalFourCornerCarrier.profile_nodup
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner) (role : TerminalProfileRole) :
    ((carrier.support corner).frontier.profiles role).Nodup :=
  (carrier.support corner).profileCoordinates_nodup role

/-- The extracted input order is exactly the governed boundary order. -/
theorem TerminalFourCornerCarrier.extracted_boundary
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner) :
    (carrier.extracted corner).boundary =
      (carrier.support corner).frontier.boundary :=
  rfl

/-- The extracted output order is exactly the governed interface order. -/
theorem TerminalFourCornerCarrier.extracted_interface
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner) :
    (carrier.extracted corner).interface =
      (carrier.support corner).frontier.interface :=
  rfl

/-- Every carrier corner is governed and physically compatible. -/
theorem TerminalFourCornerCarrier.corner_compatible
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (corner : TerminalSupportSquareCorner) :
    (carrier.support corner).Compatible :=
  carrier.square.governedCompleted_compatible carrier.candidate corner

/-- A meet profile coordinate is transported to exactly both sides. -/
theorem TerminalFourCornerCarrier.meet_profile_transport
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth) :
    coordinate ∈ (carrier.support .meet).frontier.profiles role ↔
      coordinate ∈ (carrier.support .left).frontier.profiles role ∧
        coordinate ∈ (carrier.support .right).frontier.profiles role :=
  carrier.square.governedCompleted_meet_profile_iff
    carrier.candidate role coordinate

/-- Every profile coordinate on either side transports unchanged to the join. -/
theorem TerminalFourCornerCarrier.side_profile_transport
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (side : TerminalSupportSquareSide)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth)
    (member : coordinate ∈
      (carrier.support side.corner).frontier.profiles role) :
    coordinate ∈ (carrier.support .join).frontier.profiles role := by
  cases side with
  | left =>
      exact carrier.square.side_profile_mem_join carrier.candidate role coordinate
        (Or.inl member)
  | right =>
      exact carrier.square.side_profile_mem_join carrier.candidate role coordinate
        (Or.inr member)

/-- The join profile consists of exactly the transported side profiles. -/
theorem TerminalFourCornerCarrier.join_profile_transport
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth) :
    coordinate ∈ (carrier.support .join).frontier.profiles role ↔
      coordinate ∈ (carrier.support .left).frontier.profiles role ∨
        coordinate ∈ (carrier.support .right).frontier.profiles role :=
  carrier.square.governedCompleted_join_profile_iff
    carrier.candidate role coordinate

/-- Retained side boundaries occur at the identical ambient coordinate in the
    computed join boundary. -/
theorem TerminalFourCornerCarrier.boundary_retained
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (side : TerminalSupportSquareSide)
    (wire : TerminalSupportWire inputs gates)
    (classified : carrier.boundaryDisposition? side wire = some .retained) :
    wire ∈ (carrier.support .join).frontier.boundary := by
  have data :=
    (carrier.boundaryDisposition?_eq_some_iff side wire .retained).1 classified
  cases side with
  | left =>
      simp only [TerminalSupportSquareSide.corner,
        TerminalFourCornerCarrier.support] at data ⊢
      have split := carrier.square.left_boundary_disposition carrier.candidate wire
        data.1
      cases split with
      | inl retained =>
          rw [carrier.square.governedCompleted_join_boundary_eq_pushout
            carrier.candidate]
          exact retained.2
      | inr internalized =>
          rw [data.2] at internalized
          cases internalized.1
  | right =>
      simp only [TerminalSupportSquareSide.corner,
        TerminalFourCornerCarrier.support] at data ⊢
      have split := carrier.square.right_boundary_disposition carrier.candidate wire
        data.1
      cases split with
      | inl retained =>
          rw [carrier.square.governedCompleted_join_boundary_eq_pushout
            carrier.candidate]
          exact retained.2
      | inr internalized =>
          rw [data.2] at internalized
          cases internalized.1

/-- An internalized side boundary is exactly an ambient gate selected by the
    opposite side. -/
theorem TerminalFourCornerCarrier.boundary_internalized
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (side : TerminalSupportSquareSide)
    (wire : TerminalSupportWire inputs gates)
    (classified : carrier.boundaryDisposition? side wire = some .internalized) :
    ∃ gate, wire = .gate gate ∧
      terminalGateSelected (carrier.square.records side.oppositeCorner) gate = true := by
  have data :=
    (carrier.boundaryDisposition?_eq_some_iff side wire .internalized).1 classified
  cases side with
  | left =>
      simp only [TerminalSupportSquareSide.corner,
        TerminalSupportSquareSide.oppositeCorner,
        TerminalFourCornerCarrier.support] at data ⊢
      have split := carrier.square.left_boundary_disposition carrier.candidate wire
        data.1
      cases split with
      | inl retained =>
          rw [data.2] at retained
          cases retained.1
      | inr internalized => exact internalized.2
  | right =>
      simp only [TerminalSupportSquareSide.corner,
        TerminalSupportSquareSide.oppositeCorner,
        TerminalFourCornerCarrier.support] at data ⊢
      have split := carrier.square.right_boundary_disposition carrier.candidate wire
        data.1
      cases split with
      | inl retained =>
          rw [data.2] at retained
          cases retained.1
      | inr internalized => exact internalized.2

/-- Retained side interfaces occur at the identical ambient gate coordinate
    in the computed join interface. -/
theorem TerminalFourCornerCarrier.interface_retained
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (side : TerminalSupportSquareSide)
    (producer : Fin gates)
    (classified : carrier.interfaceDisposition? side producer = some .retained) :
    producer ∈ (carrier.support .join).frontier.interface := by
  have data :=
    (carrier.interfaceDisposition?_eq_some_iff side producer .retained).1 classified
  have sideMember : producer ∈ (carrier.support .left).frontier.interface ∨
      producer ∈ (carrier.support .right).frontier.interface := by
    cases side with
    | left => exact Or.inl data.1
    | right => exact Or.inr data.1
  have split := carrier.square.side_interface_disposition carrier.candidate
    producer sideMember
  have disposition :
      terminalInterfaceFrontierDisposition
          (carrier.square.governedCompleted carrier.candidate .left)
          (carrier.square.governedCompleted carrier.candidate .right) producer =
        .retained := by
    simpa only [TerminalFourCornerCarrier.support] using data.2
  cases split with
  | inl retained =>
      change producer ∈
        (carrier.square.governedCompleted carrier.candidate .join).frontier.interface
      rw [carrier.square.governedCompleted_join_interface_eq_pushout carrier.candidate]
      exact retained.2
  | inr internalized =>
      rw [disposition] at internalized
      cases internalized.1

/-- An internalized side interface has neither an external consumer nor a
    global-output use in the combined support. -/
theorem TerminalFourCornerCarrier.interface_internalized
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (side : TerminalSupportSquareSide)
    (producer : Fin gates)
    (classified :
      carrier.interfaceDisposition? side producer = some .internalized) :
    terminalGateHasExternalConsumer carrier.candidate.program
        (carrier.square.leftRecords ++ carrier.square.rightRecords) producer = false ∧
      terminalGateIsGlobalOutput carrier.candidate.directWireWord producer = false := by
  have data :=
    (carrier.interfaceDisposition?_eq_some_iff side producer .internalized).1
      classified
  have sideMember : producer ∈ (carrier.support .left).frontier.interface ∨
      producer ∈ (carrier.support .right).frontier.interface := by
    cases side with
    | left => exact Or.inl data.1
    | right => exact Or.inr data.1
  have split := carrier.square.side_interface_disposition carrier.candidate
    producer sideMember
  have disposition :
      terminalInterfaceFrontierDisposition
          (carrier.square.governedCompleted carrier.candidate .left)
          (carrier.square.governedCompleted carrier.candidate .right) producer =
        .internalized := by
    simpa only [TerminalFourCornerCarrier.support] using data.2
  cases split with
  | inl retained =>
      rw [disposition] at retained
      cases retained.1
  | inr internalized => exact ⟨internalized.2.1, internalized.2.2⟩

/-- The common projection commutes with the exact meet and join carrier
    transports. -/
theorem TerminalFourCornerCarrier.projection_compatible
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system) :
    carrier.square.ProjectionCompatible carrier.candidate carrier.projection :=
  carrier.square.governed_projection_compatible
    carrier.candidate carrier.projection

/-- Complete checked carrier boundary for all four computed corners. -/
structure TerminalFourCornerCarrier.Compatible
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system) : Prop where
  cornerCompatible : ∀ corner, (carrier.support corner).Compatible
  extractedBoundary : ∀ corner,
    (carrier.extracted corner).boundary =
      (carrier.support corner).frontier.boundary
  extractedInterface : ∀ corner,
    (carrier.extracted corner).interface =
      (carrier.support corner).frontier.interface
  boundaryDistinct : ∀ corner,
    (carrier.support corner).frontier.boundary.Nodup
  interfaceDistinct : ∀ corner,
    (carrier.support corner).frontier.interface.Nodup
  profileDistinct : ∀ corner role,
    ((carrier.support corner).frontier.profiles role).Nodup
  meetProfile : ∀ role coordinate,
    coordinate ∈ (carrier.support .meet).frontier.profiles role ↔
      coordinate ∈ (carrier.support .left).frontier.profiles role ∧
        coordinate ∈ (carrier.support .right).frontier.profiles role
  joinProfile : ∀ role coordinate,
    coordinate ∈ (carrier.support .join).frontier.profiles role ↔
      coordinate ∈ (carrier.support .left).frontier.profiles role ∨
        coordinate ∈ (carrier.support .right).frontier.profiles role
  boundaryClassified : ∀ side wire,
    wire ∈ (carrier.support side.corner).frontier.boundary →
      ∃ disposition, carrier.boundaryDisposition? side wire = some disposition
  interfaceClassified : ∀ side producer,
    producer ∈ (carrier.support side.corner).frontier.interface →
      ∃ disposition, carrier.interfaceDisposition? side producer = some disposition
  projectedSquare :
    carrier.square.ProjectionCompatible carrier.candidate carrier.projection

/-- Every finite computed saturated support square has one complete,
    duplicate-free, fail-closed four-corner carrier transport. -/
theorem TerminalFourCornerCarrier.complete_transport
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system) : carrier.Compatible := by
  refine
    { cornerCompatible := carrier.corner_compatible
      extractedBoundary := carrier.extracted_boundary
      extractedInterface := carrier.extracted_interface
      boundaryDistinct := carrier.boundary_nodup
      interfaceDistinct := carrier.interface_nodup
      profileDistinct := carrier.profile_nodup
      meetProfile := carrier.meet_profile_transport
      joinProfile := carrier.join_profile_transport
      boundaryClassified := ?_
      interfaceClassified := ?_
      projectedSquare := carrier.projection_compatible }
  · intro side wire member
    refine ⟨terminalBoundaryFrontierDisposition
      (carrier.support .left) (carrier.support .right) wire, ?_⟩
    exact (carrier.boundaryDisposition?_eq_some_iff side wire _).2
      ⟨member, rfl⟩
  · intro side producer member
    refine ⟨terminalInterfaceFrontierDisposition
      (carrier.support .left) (carrier.support .right) producer, ?_⟩
    exact (carrier.interfaceDisposition?_eq_some_iff side producer _).2
      ⟨member, rfl⟩

end DirectWire
end PNP
