import PNP.ResidualTerminalGovernedSupportCompletion

namespace PNP
namespace DirectWire

abbrev governedRecord := TerminalPrimitiveRecord 1 1 1 10

def governedInput0 : Fin 1 := ⟨0, by decide⟩
def governedGate0 : Fin 1 := ⟨0, by decide⟩
def governedProfile0 : Fin 10 := ⟨0, by decide⟩
def governedProfile1 : Fin 10 := ⟨1, by decide⟩
def governedProfile2 : Fin 10 := ⟨2, by decide⟩
def governedProfile3 : Fin 10 := ⟨3, by decide⟩
def governedProfile4 : Fin 10 := ⟨4, by decide⟩
def governedProfile5 : Fin 10 := ⟨5, by decide⟩
def governedProfile6 : Fin 10 := ⟨6, by decide⟩
def governedProfile7 : Fin 10 := ⟨7, by decide⟩
def governedProfile8 : Fin 10 := ⟨8, by decide⟩
def governedProfile9 : Fin 10 := ⟨9, by decide⟩

def governedProgram : Program 1 1 :=
  .snoc .empty
    { left := .input governedInput0
      right := .input governedInput0 }

def governedWord : DirectWireWord 1 1 1 :=
  ⟨fun _output => .gate governedGate0⟩

def governedCandidate : Candidate 1 1 1 :=
  Candidate.ofDirectWireWord governedProgram governedWord

def governedGateRecord : governedRecord := .gate governedGate0
def governedProfile0Record : governedRecord := .profile governedProfile0
def governedProfile1Record : governedRecord := .profile governedProfile1
def governedProfile2Record : governedRecord := .profile governedProfile2
def governedProfile3Record : governedRecord := .profile governedProfile3
def governedProfile4Record : governedRecord := .profile governedProfile4
def governedProfile5Record : governedRecord := .profile governedProfile5
def governedProfile6Record : governedRecord := .profile governedProfile6
def governedProfile7Record : governedRecord := .profile governedProfile7
def governedProfile8Record : governedRecord := .profile governedProfile8
def governedProfile9Record : governedRecord := .profile governedProfile9

def governedProfileRole (coordinate : Fin 10) : TerminalProfileRole :=
  if coordinate.val = 0 then .carrier
  else if coordinate.val = 1 then .origin
  else if coordinate.val = 2 then .kernel
  else if coordinate.val = 3 then .obligation
  else if coordinate.val = 4 then .prefix
  else if coordinate.val = 5 then .direction
  else if coordinate.val = 6 then .saturation
  else if coordinate.val = 7 then .budget
  else if coordinate.val = 8 then .charge
  else .frontier

def governedProfileSystem : TerminalProfileSystem 1 1 10 :=
  { role := governedProfileRole
    observe := fun _implementation _coordinate => false }

/-- One finite dependency chain exercises every saturation rule kind and
    reaches one coordinate in every terminal profile role. -/
def governedSaturationSystem : TerminalSaturationSystem 1 1 1 10 :=
  { profileSystem := governedProfileSystem
    requires := fun kind dependent required => decide (
      (kind = .gateSource ∧ dependent = governedGateRecord ∧
        required = governedProfile0Record) ∨
      (kind = .origin ∧ dependent = governedProfile0Record ∧
        required = governedProfile1Record) ∨
      (kind = .kernel ∧ dependent = governedProfile1Record ∧
        required = governedProfile2Record) ∨
      (kind = .obligation ∧ dependent = governedProfile2Record ∧
        required = governedProfile3Record) ∨
      (kind = .prefixTail ∧ dependent = governedProfile3Record ∧
        required = governedProfile4Record) ∨
      (kind = .direction ∧ dependent = governedProfile4Record ∧
        required = governedProfile5Record) ∨
      (kind = .saturation ∧ dependent = governedProfile5Record ∧
        required = governedProfile6Record) ∨
      (kind = .budget ∧ dependent = governedProfile6Record ∧
        required = governedProfile7Record) ∨
      (kind = .charge ∧ dependent = governedProfile7Record ∧
        required = governedProfile8Record) ∨
      (kind = .interfaceConsumer ∧
        dependent = governedProfile8Record ∧
        required = governedProfile9Record)) }

def governedSquare : TerminalSaturatedSupportSquare governedSaturationSystem :=
  terminalSaturatedSupportSquare governedSaturationSystem
    [governedGateRecord] [governedProfile5Record]

/-! The left and join corners traverse all ten roles.  The right and meet
    corners traverse the five-role suffix beginning at direction. -/

example : governedProfile0 ∈
    (governedSquare.governedCompleted governedCandidate .left).profileCoordinates
      .carrier := by decide
example : governedProfile1 ∈
    (governedSquare.governedCompleted governedCandidate .left).profileCoordinates
      .origin := by decide
example : governedProfile2 ∈
    (governedSquare.governedCompleted governedCandidate .left).profileCoordinates
      .kernel := by decide
example : governedProfile3 ∈
    (governedSquare.governedCompleted governedCandidate .left).profileCoordinates
      .obligation := by decide
example : governedProfile4 ∈
    (governedSquare.governedCompleted governedCandidate .left).profileCoordinates
      .prefix := by decide
example : governedProfile5 ∈
    (governedSquare.governedCompleted governedCandidate .left).profileCoordinates
      .direction := by decide
example : governedProfile6 ∈
    (governedSquare.governedCompleted governedCandidate .left).profileCoordinates
      .saturation := by decide
example : governedProfile7 ∈
    (governedSquare.governedCompleted governedCandidate .left).profileCoordinates
      .budget := by decide
example : governedProfile8 ∈
    (governedSquare.governedCompleted governedCandidate .left).profileCoordinates
      .charge := by decide
example : governedProfile9 ∈
    (governedSquare.governedCompleted governedCandidate .left).profileCoordinates
      .frontier := by decide

example : governedProfile4 ∉
    (governedSquare.governedCompleted governedCandidate .right).profileCoordinates
      .prefix := by decide
example : governedProfile5 ∈
    (governedSquare.governedCompleted governedCandidate .right).profileCoordinates
      .direction := by decide
example : governedProfile9 ∈
    (governedSquare.governedCompleted governedCandidate .meet).profileCoordinates
      .frontier := by decide
example : governedProfile0 ∈
    (governedSquare.governedCompleted governedCandidate .join).profileCoordinates
      .carrier := by decide

/-- Every corner uses the same exact computed role-partition theorem. -/
example (corner : TerminalSupportSquareCorner)
    (role : TerminalProfileRole) (coordinate : Fin 10) :
    coordinate ∈
        (governedSquare.governedCompleted governedCandidate corner).profileCoordinates
          role ↔
      TerminalPrimitiveRecord.profile coordinate ∈
          governedSquare.records corner ∧
        governedSaturationSystem.profileSystem.role coordinate = role :=
  governedSquare.governedCompleted_profile_iff
    governedCandidate corner role coordinate

example (corner : TerminalSupportSquareCorner) (coordinate : Fin 10) :
    TerminalPrimitiveRecord.profile coordinate ∈
        (governedSquare.governedCompleted governedCandidate corner).records ↔
      ∃ role, role ∈ allTerminalProfileRoles ∧
        coordinate ∈
          (governedSquare.governedCompleted governedCandidate corner).profileCoordinates
            role :=
  (governedSquare.governedCompleted governedCandidate corner)
    |>.profile_record_covered_iff coordinate

example (corner : TerminalSupportSquareCorner)
    (left right : TerminalProfileRole) (different : left ≠ right)
    (coordinate : Fin 10)
    (member : coordinate ∈
      (governedSquare.governedCompleted governedCandidate corner).profileCoordinates
        left) :
    coordinate ∉
      (governedSquare.governedCompleted governedCandidate corner).profileCoordinates
        right :=
  (governedSquare.governedCompleted governedCandidate corner)
    |>.profileCoordinates_disjoint left right different coordinate member

/-! Physical completion is retained while profile-only corners expose no
    physical boundary or interface. -/

example :
    (governedSquare.governedCompleted governedCandidate .left).frontier.boundary =
        [TerminalSupportWire.input governedInput0] := by decide
example :
    (governedSquare.governedCompleted governedCandidate .left).frontier.interface =
      [governedGate0] := by decide
example :
    (governedSquare.governedCompleted governedCandidate .meet).frontier.boundary =
      [] := by decide
example :
    (governedSquare.governedCompleted governedCandidate .meet).frontier.interface =
      [] := by decide
example :
    (governedSquare.governedCompleted governedCandidate .right).frontier.boundary =
      [] := by decide
example :
    (governedSquare.governedCompleted governedCandidate .right).frontier.interface =
      [] := by decide
example :
    (governedSquare.governedCompleted governedCandidate .join).frontier.boundary =
        [TerminalSupportWire.input governedInput0] := by decide
example :
    (governedSquare.governedCompleted governedCandidate .join).frontier.interface =
      [governedGate0] := by decide

example (corner : TerminalSupportSquareCorner) :
    (governedSquare.governedCompleted governedCandidate corner).Compatible :=
  governedSquare.governedCompleted_compatible governedCandidate corner

/-- The final chain edge is exposed through the governed frontier theorem,
    rather than a caller-provided completion certificate. -/
example : governedProfile9 ∈
    (governedSquare.governedCompleted governedCandidate .left).profileCoordinates
      .frontier := by
  exact governedSquare.governedCompleted_required_profile_mem
    governedCandidate .left .interfaceConsumer governedProfile8Record
      governedProfile9 (by decide) (by decide)

example :
    (completeSaturatedTerminalGovernedSupport governedCandidate
      governedSaturationSystem [governedGateRecord]).Compatible :=
  completeSaturatedTerminalGovernedSupport_compatible governedCandidate
    governedSaturationSystem [governedGateRecord]

end DirectWire
end PNP
