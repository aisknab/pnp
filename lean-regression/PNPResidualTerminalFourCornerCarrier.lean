import PNP.ResidualTerminalFourCornerCarrier

namespace PNP
namespace DirectWire

abbrev carrierRecord := TerminalPrimitiveRecord 1 3 1 2

def carrierInput0 : Fin 1 := ⟨0, by decide⟩
def carrierGate0 : Fin 3 := ⟨0, by decide⟩
def carrierGate1 : Fin 3 := ⟨1, by decide⟩
def carrierGate2 : Fin 3 := ⟨2, by decide⟩
def carrierProfile0 : Fin 2 := ⟨0, by decide⟩
def carrierProfile1 : Fin 2 := ⟨1, by decide⟩

def carrierProgram0 : Program 1 1 :=
  .snoc .empty
    { left := .input carrierInput0
      right := .input carrierInput0 }

def carrierProgram1 : Program 1 2 :=
  .snoc carrierProgram0
    { left := .gate ⟨0, by decide⟩
      right := .input carrierInput0 }

def carrierProgram : Program 1 3 :=
  .snoc carrierProgram1
    { left := .gate ⟨1, by decide⟩
      right := .input carrierInput0 }

def carrierWord : DirectWireWord 1 3 1 :=
  ⟨fun _output => .gate carrierGate2⟩

def carrierCandidate : Candidate 1 3 1 :=
  Candidate.ofDirectWireWord carrierProgram carrierWord

def carrierProfileSystem : TerminalProfileSystem 1 1 2 :=
  { role := fun coordinate =>
      if coordinate.val = 0 then .origin else .charge
    observe := fun _implementation _coordinate => false }

def carrierSaturationSystem : TerminalSaturationSystem 1 3 1 2 :=
  { profileSystem := carrierProfileSystem
    requires := fun _kind _dependent _required => false }

def carrierGate0Record : carrierRecord := .gate carrierGate0
def carrierGate1Record : carrierRecord := .gate carrierGate1
def carrierProfile0Record : carrierRecord := .profile carrierProfile0
def carrierProfile1Record : carrierRecord := .profile carrierProfile1

/-- Gate zero is selected on the left and consumed by gate one on the right.
    Thus the shared input survives, while the gate-zero boundary and interface
    coordinates become internal to the join. -/
def carrierSquare : TerminalSaturatedSupportSquare carrierSaturationSystem :=
  terminalSaturatedSupportSquare carrierSaturationSystem
    [carrierGate0Record, carrierProfile0Record]
    [carrierGate1Record, carrierProfile0Record, carrierProfile1Record]

def carrierKeepOrigin : TerminalProfileProjection 2 :=
  { keep := fun coordinate => coordinate.val = 0 }

def carrierExample : TerminalFourCornerCarrier carrierSaturationSystem :=
  carrierSquare.fourCornerCarrier carrierCandidate carrierKeepOrigin

def carrierEmptySquare :
    TerminalSaturatedSupportSquare carrierSaturationSystem :=
  terminalSaturatedSupportSquare carrierSaturationSystem [] []

def carrierEmpty : TerminalFourCornerCarrier carrierSaturationSystem :=
  carrierEmptySquare.fourCornerCarrier carrierCandidate carrierKeepOrigin

example : TerminalSupportSquareSide.left.corner =
    TerminalSupportSquareCorner.left := rfl

example : TerminalSupportSquareSide.left.oppositeCorner =
    TerminalSupportSquareCorner.right := rfl

example : TerminalSupportSquareSide.right.oppositeCorner =
    TerminalSupportSquareCorner.left := rfl

example :
    (carrierExample.support .left).frontier.boundary =
      [.input carrierInput0] := by decide

example :
    (carrierExample.support .right).frontier.boundary =
      [.input carrierInput0, .gate carrierGate0] := by decide

example :
    (carrierExample.support .join).frontier.boundary =
      [.input carrierInput0] := by decide

example :
    (carrierExample.support .left).frontier.interface = [carrierGate0] := by
  decide

example :
    (carrierExample.support .right).frontier.interface = [carrierGate1] := by
  decide

example :
    (carrierExample.support .join).frontier.interface = [carrierGate1] := by
  decide

example (corner : TerminalSupportSquareCorner) :
    (carrierExample.extracted corner).boundary =
      (carrierExample.support corner).frontier.boundary :=
  carrierExample.extracted_boundary corner

example (corner : TerminalSupportSquareCorner) :
    (carrierExample.extracted corner).interface =
      (carrierExample.support corner).frontier.interface :=
  carrierExample.extracted_interface corner

example (corner : TerminalSupportSquareCorner) :
    (carrierExample.support corner).frontier.boundary.Nodup :=
  carrierExample.boundary_nodup corner

example (corner : TerminalSupportSquareCorner) :
    (carrierExample.support corner).frontier.interface.Nodup :=
  carrierExample.interface_nodup corner

example (corner : TerminalSupportSquareCorner) (role : TerminalProfileRole) :
    ((carrierExample.support corner).frontier.profiles role).Nodup :=
  carrierExample.profile_nodup corner role

example (corner : TerminalSupportSquareCorner) :
    (carrierExample.support corner).Compatible :=
  carrierExample.corner_compatible corner

example : carrierProfile0 ∈
    (carrierExample.support .meet).frontier.profiles .origin := by decide

example : carrierProfile1 ∉
    (carrierExample.support .meet).frontier.profiles .charge := by decide

example : carrierProfile1 ∈
    (carrierExample.support .join).frontier.profiles .charge :=
  carrierExample.side_profile_transport .right .charge carrierProfile1
    (by decide)

example (role : TerminalProfileRole) (coordinate : Fin 2) :
    coordinate ∈ (carrierExample.support .meet).frontier.profiles role ↔
      coordinate ∈ (carrierExample.support .left).frontier.profiles role ∧
        coordinate ∈ (carrierExample.support .right).frontier.profiles role :=
  carrierExample.meet_profile_transport role coordinate

example (role : TerminalProfileRole) (coordinate : Fin 2) :
    coordinate ∈ (carrierExample.support .join).frontier.profiles role ↔
      coordinate ∈ (carrierExample.support .left).frontier.profiles role ∨
        coordinate ∈ (carrierExample.support .right).frontier.profiles role :=
  carrierExample.join_profile_transport role coordinate

example : carrierExample.boundaryDisposition? .left
    (.input carrierInput0) = some .retained := by decide

example : carrierExample.boundaryDisposition? .right
    (.gate carrierGate0) = some .internalized := by decide

example : carrierExample.boundaryDisposition? .left
    (.gate carrierGate2) = none := by decide

example : carrierExample.interfaceDisposition? .left carrierGate0 =
    some .internalized := by decide

example : carrierExample.interfaceDisposition? .right carrierGate1 =
    some .retained := by decide

example : carrierExample.interfaceDisposition? .left carrierGate1 = none := by
  decide

example : TerminalSupportWire.input carrierInput0 ∈
    (carrierExample.support .join).frontier.boundary :=
  carrierExample.boundary_retained .left (.input carrierInput0) (by decide)

example : ∃ gate,
    (TerminalSupportWire.gate carrierGate0 : TerminalSupportWire 1 3) =
        .gate gate ∧
      terminalGateSelected
        (carrierSquare.records TerminalSupportSquareCorner.left) gate = true :=
  carrierExample.boundary_internalized .right (.gate carrierGate0) (by decide)

example : carrierGate1 ∈
    (carrierExample.support .join).frontier.interface :=
  carrierExample.interface_retained .right carrierGate1 (by decide)

example :
    terminalGateHasExternalConsumer carrierCandidate.program
        (carrierSquare.leftRecords ++ carrierSquare.rightRecords)
        carrierGate0 = false ∧
      terminalGateIsGlobalOutput carrierCandidate.directWireWord carrierGate0 =
        false :=
  carrierExample.interface_internalized .left carrierGate0 (by decide)

example :
    carrierExample.boundaryDisposition? .right (.gate carrierGate0) =
        some .internalized ↔
      (TerminalSupportWire.gate carrierGate0 : TerminalSupportWire 1 3) ∈
          (carrierExample.support .right).frontier.boundary ∧
        terminalBoundaryFrontierDisposition
            (carrierExample.support .left) (carrierExample.support .right)
            (.gate carrierGate0) = .internalized :=
  carrierExample.boundaryDisposition?_eq_some_iff .right
    (.gate carrierGate0) .internalized

example : carrierSquare.ProjectionCompatible carrierCandidate carrierKeepOrigin :=
  carrierExample.projection_compatible

example : carrierExample.Compatible := carrierExample.complete_transport

example : carrierEmpty.Compatible := carrierEmpty.complete_transport

example : carrierEmpty.boundaryDisposition? .left
    (.input carrierInput0) = none := by decide

example : carrierEmpty.boundaryDisposition? .right
    (.gate carrierGate0) = none := by decide

example : carrierEmpty.interfaceDisposition? .left carrierGate0 = none := by
  decide

example : carrierEmpty.interfaceDisposition? .right carrierGate1 = none := by
  decide

end DirectWire
end PNP
