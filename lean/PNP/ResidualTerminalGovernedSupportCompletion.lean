/-
Copyright (c) 2026 PNP Labs.

Canonical governed completion of finite terminal supports.  The physical
boundary and interface are computed from the direct-wire candidate, while
every selected profile coordinate is classified by the ten carrier roles of
the terminal mode firewall.  Saturated record sets therefore produce one
closed, physically compatible, role-partitioned completed support without a
caller-supplied frontier or completion certificate.

This reconstructs the governed completion layer required by Sections 2 and 3
of the pinned manuscript before frontier pushout and projection-compatible
support squares can be proved.  The terminal dependency system remains
explicit data.  No dependency extraction, obstruction routing, frontier
pushout, projection commutation, square-legitimacy, SaturatePositive,
BCELReady, ZeroSlack, PCCMin, polynomial-runtime, or P = NP claim is made.
-/

import PNP.ResidualTerminalSupportSquareClosure

namespace PNP
namespace DirectWire

/-- The ten terminal profile roles in one deterministic manuscript order. -/
def allTerminalProfileRoles : List TerminalProfileRole :=
  [.carrier, .origin, .kernel, .obligation, .prefix, .direction,
    .saturation, .budget, .charge, .frontier]

/-- Every terminal profile role occurs in the deterministic role list. -/
theorem mem_allTerminalProfileRoles (role : TerminalProfileRole) :
    role ∈ allTerminalProfileRoles := by
  cases role <;> simp only [allTerminalProfileRoles, List.mem_cons,
    true_or, or_true]

/-- Selected profile coordinates having one exact terminal carrier role. -/
def terminalProfileCoordinatesForRole
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (records : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (role : TerminalProfileRole) : List (Fin profileWidth) :=
  (allFin profileWidth).filter fun coordinate => decide
    (TerminalPrimitiveRecord.profile coordinate ∈ records ∧
      system.profileSystem.role coordinate = role)

/-- Exact membership in one computed role frontier. -/
theorem mem_terminalProfileCoordinatesForRole_iff
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (records : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (role : TerminalProfileRole) (coordinate : Fin profileWidth) :
    coordinate ∈ terminalProfileCoordinatesForRole system records role ↔
      TerminalPrimitiveRecord.profile coordinate ∈ records ∧
        system.profileSystem.role coordinate = role := by
  unfold terminalProfileCoordinatesForRole
  constructor
  · intro member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · intro selected
    exact List.mem_filter.mpr
      ⟨mem_allFin coordinate, decide_eq_true selected⟩

private theorem nodup_of_listNoDuplicates {alpha : Type}
    {items : List alpha} (distinct : ListNoDuplicates items) :
    items.Nodup := by
  induction distinct with
  | nil => exact List.nodup_nil
  | cons headAbsent _tailDistinct ih =>
      exact List.nodup_cons.mpr ⟨headAbsent, ih⟩

/-- A role frontier never duplicates a profile coordinate. -/
theorem terminalProfileCoordinatesForRole_nodup
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (records : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (role : TerminalProfileRole) :
    (terminalProfileCoordinatesForRole system records role).Nodup := by
  exact (nodup_of_listNoDuplicates (allFin_noDuplicates profileWidth)).sublist
    List.filter_sublist

/-- The canonical governed frontier of a terminal support. -/
structure TerminalGovernedFrontier
    (inputs gates profileWidth : Nat) where
  boundary : List (TerminalSupportWire inputs gates)
  interface : List (Fin gates)
  profiles : TerminalProfileRole → List (Fin profileWidth)

/-- A completed support stores only its selected records.  Every frontier
    field below is computed, so the type contains no caller certificate. -/
structure TerminalGovernedCompletedSupport
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) where
  records : List
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)

/-- Package an arbitrary record list for canonical governed completion. -/
def completeTerminalGovernedSupport
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (records : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalGovernedCompletedSupport candidate system :=
  { records := records }

/-- The exact computed physical completion underlying a governed support. -/
def TerminalGovernedCompletedSupport.physical
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalGovernedCompletedSupport candidate system) :
    TerminalPhysicalCompletedSupport (profileWidth := profileWidth) candidate :=
  completeTerminalPhysicalSupport candidate support.records

/-- The exact selected coordinates of one profile role. -/
def TerminalGovernedCompletedSupport.profileCoordinates
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalGovernedCompletedSupport candidate system)
    (role : TerminalProfileRole) : List (Fin profileWidth) :=
  terminalProfileCoordinatesForRole system support.records role

/-- Compute the complete physical and role-indexed frontier. -/
def TerminalGovernedCompletedSupport.frontier
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalGovernedCompletedSupport candidate system) :
    TerminalGovernedFrontier inputs gates profileWidth :=
  { boundary := support.physical.boundary
    interface := support.physical.interface
    profiles := support.profileCoordinates }

/-- Governance means that the retained record set is closed under every
    labelled dependency in the explicit terminal system. -/
def TerminalGovernedCompletedSupport.Governed
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalGovernedCompletedSupport candidate system) : Prop :=
  TerminalRawSupport.Closed (fun record => record ∈ support.records) system

/-- Completed compatibility combines dependency closure with the exact
    physical incoming and outgoing crossing conditions. -/
def TerminalGovernedCompletedSupport.Compatible
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalGovernedCompletedSupport candidate system) : Prop :=
  support.Governed ∧ support.physical.Compatible

/-- Governed completion retains exactly the supplied record list. -/
theorem completeTerminalGovernedSupport_records
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (records : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (completeTerminalGovernedSupport candidate system records).records = records :=
  rfl

/-- The governed boundary is exactly the independently computed physical
    incoming boundary. -/
theorem TerminalGovernedCompletedSupport.frontier_boundary
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalGovernedCompletedSupport candidate system) :
    support.frontier.boundary =
      terminalBoundaryPorts candidate.program support.records :=
  rfl

/-- The governed interface is exactly the independently computed physical
    outgoing interface. -/
theorem TerminalGovernedCompletedSupport.frontier_interface
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalGovernedCompletedSupport candidate system) :
    support.frontier.interface =
      terminalInterfacePorts candidate support.records :=
  rfl

/-- Exact role-frontier membership for every completed support. -/
theorem TerminalGovernedCompletedSupport.mem_profileCoordinates_iff
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalGovernedCompletedSupport candidate system)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth) :
    coordinate ∈ support.profileCoordinates role ↔
      TerminalPrimitiveRecord.profile coordinate ∈ support.records ∧
        system.profileSystem.role coordinate = role :=
  mem_terminalProfileCoordinatesForRole_iff system support.records role coordinate

/-- Every role frontier is duplicate-free. -/
theorem TerminalGovernedCompletedSupport.profileCoordinates_nodup
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalGovernedCompletedSupport candidate system)
    (role : TerminalProfileRole) :
    (support.profileCoordinates role).Nodup :=
  terminalProfileCoordinatesForRole_nodup system support.records role

/-- A selected profile coordinate occurs in its computed role frontier. -/
theorem TerminalGovernedCompletedSupport.mem_own_profile_role_iff
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalGovernedCompletedSupport candidate system)
    (coordinate : Fin profileWidth) :
    coordinate ∈ support.profileCoordinates
        (system.profileSystem.role coordinate) ↔
      TerminalPrimitiveRecord.profile coordinate ∈ support.records := by
  rw [support.mem_profileCoordinates_iff]
  constructor
  · exact fun selected => selected.1
  · exact fun selected => ⟨selected, rfl⟩

/-- One coordinate cannot occur in two distinct role frontiers. -/
theorem TerminalGovernedCompletedSupport.profile_role_unique
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalGovernedCompletedSupport candidate system)
    (coordinate : Fin profileWidth) (left right : TerminalProfileRole)
    (leftMember : coordinate ∈ support.profileCoordinates left)
    (rightMember : coordinate ∈ support.profileCoordinates right) :
    left = right := by
  have leftRole :=
    ((support.mem_profileCoordinates_iff left coordinate).1 leftMember).2
  have rightRole :=
    ((support.mem_profileCoordinates_iff right coordinate).1 rightMember).2
  exact leftRole.symm.trans rightRole

/-- Distinct role frontiers are disjoint. -/
theorem TerminalGovernedCompletedSupport.profileCoordinates_disjoint
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalGovernedCompletedSupport candidate system)
    (left right : TerminalProfileRole) (different : left ≠ right)
    (coordinate : Fin profileWidth)
    (leftMember : coordinate ∈ support.profileCoordinates left) :
    coordinate ∉ support.profileCoordinates right := by
  intro rightMember
  exact different
    (support.profile_role_unique coordinate left right leftMember rightMember)

/-- The ten role frontiers cover exactly the selected profile records. -/
theorem TerminalGovernedCompletedSupport.profile_record_covered_iff
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalGovernedCompletedSupport candidate system)
    (coordinate : Fin profileWidth) :
    TerminalPrimitiveRecord.profile coordinate ∈ support.records ↔
      ∃ role, role ∈ allTerminalProfileRoles ∧
        coordinate ∈ support.profileCoordinates role := by
  constructor
  · intro selected
    let role := system.profileSystem.role coordinate
    exact ⟨role, mem_allTerminalProfileRoles role,
      (support.mem_own_profile_role_iff coordinate).2 selected⟩
  · rintro ⟨role, _listed, member⟩
    exact ((support.mem_profileCoordinates_iff role coordinate).1 member).1

/-- Closure of a governed completion exposes every directly required record. -/
theorem TerminalGovernedCompletedSupport.required_mem
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalGovernedCompletedSupport candidate system)
    (governed : support.Governed)
    (kind : TerminalSaturationRuleKind)
    (dependent required :
      TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (dependentMember : dependent ∈ support.records)
    (edge : system.requires kind dependent required = true) :
    required ∈ support.records :=
  governed kind dependent required dependentMember edge

/-- If a required record is a profile coordinate, closure places it in the
    unique frontier role computed by the profile system. -/
theorem TerminalGovernedCompletedSupport.required_profile_mem
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalGovernedCompletedSupport candidate system)
    (governed : support.Governed)
    (kind : TerminalSaturationRuleKind)
    (dependent : TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (coordinate : Fin profileWidth)
    (dependentMember : dependent ∈ support.records)
    (edge : system.requires kind dependent (.profile coordinate) = true) :
    coordinate ∈ support.profileCoordinates
      (system.profileSystem.role coordinate) :=
  (support.mem_own_profile_role_iff coordinate).2
    (support.required_mem governed kind dependent (.profile coordinate)
      dependentMember edge)

/-- Saturate a seed, then compute its governed physical and profile frontier. -/
def completeSaturatedTerminalGovernedSupport
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalGovernedCompletedSupport candidate system :=
  completeTerminalGovernedSupport candidate system
    (terminalSaturateRecords system seed)

/-- Saturated governed completion retains exactly the executable closure. -/
theorem completeSaturatedTerminalGovernedSupport_records
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (completeSaturatedTerminalGovernedSupport candidate system seed).records =
      terminalSaturateRecords system seed :=
  rfl

/-- Every saturated governed completion is closed and physically compatible. -/
theorem completeSaturatedTerminalGovernedSupport_compatible
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (completeSaturatedTerminalGovernedSupport candidate system seed).Compatible :=
  ⟨terminalSaturateRecords_closed system seed,
    completeTerminalPhysicalSupport_compatible candidate
      (terminalSaturateRecords system seed)⟩

/-- Compute canonical governed completion for one of the four square corners. -/
def TerminalSaturatedSupportSquare.governedCompleted
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (corner : TerminalSupportSquareCorner) :
    TerminalGovernedCompletedSupport candidate system :=
  completeTerminalGovernedSupport candidate system (square.records corner)

/-- A square-corner completion retains exactly that computed corner. -/
theorem TerminalSaturatedSupportSquare.governedCompleted_records
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (corner : TerminalSupportSquareCorner) :
    (square.governedCompleted candidate corner).records = square.records corner :=
  rfl

/-- Every computed square corner is governed and physically compatible. -/
theorem TerminalSaturatedSupportSquare.governedCompleted_compatible
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (corner : TerminalSupportSquareCorner) :
    (square.governedCompleted candidate corner).Compatible :=
  ⟨square.records_closed corner, square.physically_compatible candidate corner⟩

/-- Exact profile-role membership for every corner of every computed square. -/
theorem TerminalSaturatedSupportSquare.governedCompleted_profile_iff
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (corner : TerminalSupportSquareCorner)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth) :
    coordinate ∈
        (square.governedCompleted candidate corner).profileCoordinates role ↔
      TerminalPrimitiveRecord.profile coordinate ∈ square.records corner ∧
        system.profileSystem.role coordinate = role :=
  (square.governedCompleted candidate corner).mem_profileCoordinates_iff
    role coordinate

/-- Every dependency required at a square corner remains in that exact corner. -/
theorem TerminalSaturatedSupportSquare.governedCompleted_required_mem
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (corner : TerminalSupportSquareCorner)
    (kind : TerminalSaturationRuleKind)
    (dependent required :
      TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (dependentMember : dependent ∈ square.records corner)
    (edge : system.requires kind dependent required = true) :
    required ∈ (square.governedCompleted candidate corner).records := by
  exact square.records_closed corner kind dependent required dependentMember edge

/-- Every required profile coordinate at every square corner is placed in its
    unique computed terminal role frontier. -/
theorem TerminalSaturatedSupportSquare.governedCompleted_required_profile_mem
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (corner : TerminalSupportSquareCorner)
    (kind : TerminalSaturationRuleKind)
    (dependent : TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (coordinate : Fin profileWidth)
    (dependentMember : dependent ∈ square.records corner)
    (edge : system.requires kind dependent (.profile coordinate) = true) :
    coordinate ∈ (square.governedCompleted candidate corner).profileCoordinates
      (system.profileSystem.role coordinate) := by
  exact (square.governedCompleted candidate corner).required_profile_mem
    (square.governedCompleted_compatible candidate corner).1 kind dependent
      coordinate dependentMember edge

end DirectWire
end PNP
