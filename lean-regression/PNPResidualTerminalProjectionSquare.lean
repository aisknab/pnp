import PNP.ResidualTerminalProjectionSquare

namespace PNP
namespace DirectWire

abbrev projectionRecord := TerminalPrimitiveRecord 1 3 1 10

def projectionInput0 : Fin 1 := ⟨0, by decide⟩
def projectionGate0 : Fin 3 := ⟨0, by decide⟩
def projectionGate1 : Fin 3 := ⟨1, by decide⟩
def projectionGate2 : Fin 3 := ⟨2, by decide⟩

def projectionProgram0 : Program 1 1 :=
  .snoc .empty
    { left := .input projectionInput0
      right := .input projectionInput0 }

def projectionProgram1 : Program 1 2 :=
  .snoc projectionProgram0
    { left := .gate ⟨0, by decide⟩
      right := .input projectionInput0 }

def projectionProgram : Program 1 3 :=
  .snoc projectionProgram1
    { left := .gate ⟨1, by decide⟩
      right := .input projectionInput0 }

def projectionRegressionWord : DirectWireWord 1 3 1 :=
  ⟨fun _output => .gate projectionGate2⟩

def projectionCandidate : Candidate 1 3 1 :=
  Candidate.ofDirectWireWord projectionProgram projectionRegressionWord

def projectionRole (index : Nat) : TerminalProfileRole :=
  match index with
  | 0 => .carrier
  | 1 => .origin
  | 2 => .kernel
  | 3 => .obligation
  | 4 => .prefix
  | 5 => .direction
  | 6 => .saturation
  | 7 => .budget
  | 8 => .charge
  | _ => .frontier

def projectionProfileSystem : TerminalProfileSystem 1 1 10 :=
  { role := fun coordinate => projectionRole coordinate.val
    observe := fun _implementation coordinate => coordinate.val % 2 = 0 }

def projectionSaturationSystem : TerminalSaturationSystem 1 3 1 10 :=
  { profileSystem := projectionProfileSystem
    requires := fun _kind _dependent _required => false }

def projectionProfileRecord (index : Fin 10) : projectionRecord := .profile index
def projectionGateRecord (index : Fin 3) : projectionRecord := .gate index

def projectionProfile0 : Fin 10 := ⟨0, by decide⟩
def projectionProfile1 : Fin 10 := ⟨1, by decide⟩
def projectionProfile2 : Fin 10 := ⟨2, by decide⟩
def projectionProfile3 : Fin 10 := ⟨3, by decide⟩
def projectionProfile4 : Fin 10 := ⟨4, by decide⟩
def projectionProfile5 : Fin 10 := ⟨5, by decide⟩
def projectionProfile6 : Fin 10 := ⟨6, by decide⟩
def projectionProfile7 : Fin 10 := ⟨7, by decide⟩
def projectionProfile8 : Fin 10 := ⟨8, by decide⟩
def projectionProfile9 : Fin 10 := ⟨9, by decide⟩

def projectionSquare : TerminalSaturatedSupportSquare projectionSaturationSystem :=
  terminalSaturatedSupportSquare projectionSaturationSystem
    [projectionGateRecord projectionGate0,
      projectionProfileRecord projectionProfile0,
      projectionProfileRecord projectionProfile1,
      projectionProfileRecord projectionProfile2,
      projectionProfileRecord projectionProfile4,
      projectionProfileRecord projectionProfile6,
      projectionProfileRecord projectionProfile8]
    [projectionGateRecord projectionGate1,
      projectionProfileRecord projectionProfile0,
      projectionProfileRecord projectionProfile2,
      projectionProfileRecord projectionProfile3,
      projectionProfileRecord projectionProfile5,
      projectionProfileRecord projectionProfile7,
      projectionProfileRecord projectionProfile9]

def projectionKeepAll : TerminalProfileProjection 10 :=
  { keep := fun _coordinate => true }

def projectionForgetAll : TerminalProfileProjection 10 :=
  { keep := fun _coordinate => false }

def projectionAlternating : TerminalProfileProjection 10 :=
  { keep := fun coordinate => coordinate.val % 2 = 0 }

example :
    (projectionSquare.projectedFrontier projectionCandidate
      projectionAlternating .left).boundary =
      (projectionSquare.governedCompleted projectionCandidate .left).frontier.boundary :=
  projectionSquare.projectedFrontier_boundary projectionCandidate
    projectionAlternating .left

example :
    (projectionSquare.projectedFrontier projectionCandidate
      projectionAlternating .right).interface =
      (projectionSquare.governedCompleted projectionCandidate .right).frontier.interface :=
  projectionSquare.projectedFrontier_interface projectionCandidate
    projectionAlternating .right

example : projectionProfile0 ∈
    (projectionSquare.projectedFrontier projectionCandidate
      projectionAlternating .join).profiles .carrier := by decide

example : projectionProfile1 ∉
    (projectionSquare.projectedFrontier projectionCandidate
      projectionAlternating .join).profiles .origin := by decide

example : projectionProfile2 ∈
    (projectionSquare.projectedFrontier projectionCandidate
      projectionAlternating .meet).profiles .kernel := by decide

example : projectionProfile3 ∉
    (projectionSquare.projectedFrontier projectionCandidate
      projectionAlternating .join).profiles .obligation := by decide

example : projectionProfile4 ∈
    (projectionSquare.projectedFrontier projectionCandidate
      projectionAlternating .join).profiles .prefix := by decide

example : projectionProfile5 ∉
    (projectionSquare.projectedFrontier projectionCandidate
      projectionAlternating .join).profiles .direction := by decide

example : projectionProfile6 ∈
    (projectionSquare.projectedFrontier projectionCandidate
      projectionAlternating .join).profiles .saturation := by decide

example : projectionProfile7 ∉
    (projectionSquare.projectedFrontier projectionCandidate
      projectionAlternating .join).profiles .budget := by decide

example : projectionProfile8 ∈
    (projectionSquare.projectedFrontier projectionCandidate
      projectionAlternating .join).profiles .charge := by decide

example : projectionProfile9 ∉
    (projectionSquare.projectedFrontier projectionCandidate
      projectionAlternating .join).profiles .frontier := by decide

example (role : TerminalProfileRole) :
    (projectionSquare.projectedFrontier projectionCandidate
      projectionForgetAll .join).profiles role = [] := by
  cases role <;> decide

example :
    projectionSquare.projectedFrontier projectionCandidate
        projectionKeepAll .join =
      (projectionSquare.governedCompleted projectionCandidate .join).frontier := by
  apply TerminalGovernedFrontier.extensionality
  · rfl
  · rfl
  · funext role
    simp [TerminalSaturatedSupportSquare.projectedFrontier,
      TerminalGovernedFrontier.project, projectionKeepAll]

example :
    projectionSquare.projectedFrontier projectionCandidate
        projectionAlternating .join =
      terminalProjectedGovernedFrontierPushout
        (projectionSquare.governedCompleted projectionCandidate .left)
        (projectionSquare.governedCompleted projectionCandidate .right)
        projectionAlternating :=
  projectionSquare.projected_join_eq_pushout projectionCandidate
    projectionAlternating

example (role : TerminalProfileRole) (coordinate : Fin 10) :
    coordinate ∈
        (projectionSquare.projectedFrontier projectionCandidate
          projectionAlternating .meet).profiles role ↔
      coordinate ∈
          (projectionSquare.projectedFrontier projectionCandidate
            projectionAlternating .left).profiles role ∧
        coordinate ∈
          (projectionSquare.projectedFrontier projectionCandidate
            projectionAlternating .right).profiles role :=
  projectionSquare.projected_meet_profile_iff projectionCandidate
    projectionAlternating role coordinate

example :
    projectionSquare.ProjectionCompatible projectionCandidate
      projectionAlternating :=
  projectionSquare.governed_projection_compatible projectionCandidate
    projectionAlternating

example :
    ((projectionSquare.governedCompleted projectionCandidate .join).frontier.project
      projectionAlternating).project projectionAlternating =
      (projectionSquare.governedCompleted projectionCandidate .join).frontier.project
        projectionAlternating :=
  TerminalGovernedFrontier.project_idempotent _ projectionAlternating

def projectionEmptySquare :
    TerminalSaturatedSupportSquare projectionSaturationSystem :=
  terminalSaturatedSupportSquare projectionSaturationSystem [] []

def projectionIdenticalSquare :
    TerminalSaturatedSupportSquare projectionSaturationSystem :=
  terminalSaturatedSupportSquare projectionSaturationSystem
    [projectionProfileRecord projectionProfile0]
    [projectionProfileRecord projectionProfile0]

def projectionDisjointSquare :
    TerminalSaturatedSupportSquare projectionSaturationSystem :=
  terminalSaturatedSupportSquare projectionSaturationSystem
    [projectionProfileRecord projectionProfile4]
    [projectionProfileRecord projectionProfile6]

example : projectionEmptySquare.ProjectionCompatible projectionCandidate
    projectionAlternating :=
  projectionEmptySquare.governed_projection_compatible projectionCandidate
    projectionAlternating

example : projectionIdenticalSquare.ProjectionCompatible projectionCandidate
    projectionAlternating :=
  projectionIdenticalSquare.governed_projection_compatible projectionCandidate
    projectionAlternating

example : projectionDisjointSquare.ProjectionCompatible projectionCandidate
    projectionAlternating :=
  projectionDisjointSquare.governed_projection_compatible projectionCandidate
    projectionAlternating

end DirectWire
end PNP
