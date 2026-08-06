import PNP.ResidualTerminalFrontierPushout

namespace PNP
namespace DirectWire

abbrev pushoutRecord := TerminalPrimitiveRecord 1 3 1 2

def pushoutInput0 : Fin 1 := ⟨0, by decide⟩
def pushoutGate0 : Fin 3 := ⟨0, by decide⟩
def pushoutGate1 : Fin 3 := ⟨1, by decide⟩
def pushoutGate2 : Fin 3 := ⟨2, by decide⟩
def pushoutProfile0 : Fin 2 := ⟨0, by decide⟩
def pushoutProfile1 : Fin 2 := ⟨1, by decide⟩

def pushoutProgram0 : Program 1 1 :=
  .snoc .empty
    { left := .input pushoutInput0
      right := .input pushoutInput0 }

def pushoutProgram1 : Program 1 2 :=
  .snoc pushoutProgram0
    { left := .gate ⟨0, by decide⟩
      right := .input pushoutInput0 }

def pushoutProgram : Program 1 3 :=
  .snoc pushoutProgram1
    { left := .gate ⟨1, by decide⟩
      right := .input pushoutInput0 }

def pushoutWord : DirectWireWord 1 3 1 :=
  ⟨fun _output => .gate pushoutGate2⟩

def pushoutCandidate : Candidate 1 3 1 :=
  Candidate.ofDirectWireWord pushoutProgram pushoutWord

def pushoutProfileSystem : TerminalProfileSystem 1 1 2 :=
  { role := fun coordinate =>
      if coordinate.val = 0 then .origin else .charge
    observe := fun _implementation _coordinate => false }

def pushoutSaturationSystem : TerminalSaturationSystem 1 3 1 2 :=
  { profileSystem := pushoutProfileSystem
    requires := fun _kind _dependent _required => false }

def pushoutGate0Record : pushoutRecord := .gate pushoutGate0
def pushoutGate1Record : pushoutRecord := .gate pushoutGate1
def pushoutGate2Record : pushoutRecord := .gate pushoutGate2
def pushoutProfile0Record : pushoutRecord := .profile pushoutProfile0
def pushoutProfile1Record : pushoutRecord := .profile pushoutProfile1

/-- The left producer feeds the right gate.  Their union therefore turns the
    left outgoing interface and the right incoming gate wire into internal
    coordinates.  The profile coordinate zero is their exact overlap. -/
def pushoutSquare : TerminalSaturatedSupportSquare pushoutSaturationSystem :=
  terminalSaturatedSupportSquare pushoutSaturationSystem
    [pushoutGate0Record, pushoutProfile0Record]
    [pushoutGate1Record, pushoutProfile0Record, pushoutProfile1Record]

example :
    (pushoutSquare.governedCompleted pushoutCandidate .left).frontier.boundary =
      [.input pushoutInput0] := by decide

example :
    (pushoutSquare.governedCompleted pushoutCandidate .left).frontier.interface =
      [pushoutGate0] := by decide

example :
    (pushoutSquare.governedCompleted pushoutCandidate .right).frontier.boundary =
      [.input pushoutInput0, .gate pushoutGate0] := by decide

example :
    (pushoutSquare.governedCompleted pushoutCandidate .right).frontier.interface =
      [pushoutGate1] := by decide

example :
    (pushoutSquare.governedCompleted pushoutCandidate .join).frontier.boundary =
      [.input pushoutInput0] := by decide

example :
    (pushoutSquare.governedCompleted pushoutCandidate .join).frontier.interface =
      [pushoutGate1] := by decide

example :
    pushoutProfile0 ∈
      (pushoutSquare.governedCompleted pushoutCandidate .meet).profileCoordinates
        .origin := by decide

example :
    pushoutProfile1 ∉
      (pushoutSquare.governedCompleted pushoutCandidate .meet).profileCoordinates
        .charge := by decide

example :
    pushoutProfile1 ∈
      (pushoutSquare.governedCompleted pushoutCandidate .join).profileCoordinates
        .charge := by decide

example :
    terminalBoundaryFrontierDisposition
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right)
        (.gate pushoutGate0) = .internalized := by decide

example :
    terminalInterfaceFrontierDisposition
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right)
        pushoutGate0 = .internalized := by decide

example :
    terminalBoundaryFrontierDisposition
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right)
        (.input pushoutInput0) = .retained := by decide

example :
    terminalInterfaceFrontierDisposition
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right)
        pushoutGate1 = .retained := by decide

example :
    terminalBoundaryFrontierPushout
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right) =
      [.input pushoutInput0] := by decide

example :
    terminalInterfaceFrontierPushout
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right) =
      [pushoutGate1] := by decide

example :
    terminalProfileFrontierPushout
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right) .origin =
      [pushoutProfile0] := by decide

example :
    terminalProfileFrontierPushout
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right) .charge =
      [pushoutProfile1] := by decide

example :
    (pushoutSquare.governedCompleted pushoutCandidate .join).frontier =
      terminalGovernedFrontierPushout
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right) :=
  (pushoutSquare.governed_frontier_pushout pushoutCandidate).1

example (role : TerminalProfileRole) (coordinate : Fin 2) :
    coordinate ∈
        (pushoutSquare.governedCompleted pushoutCandidate .meet).profileCoordinates role ↔
      coordinate ∈
          (pushoutSquare.governedCompleted pushoutCandidate .left).profileCoordinates role ∧
        coordinate ∈
          (pushoutSquare.governedCompleted pushoutCandidate .right).profileCoordinates role :=
  (pushoutSquare.governed_frontier_pushout pushoutCandidate).2 role coordinate

example :
    terminalBoundaryFrontierPushout
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right) |>.Nodup :=
  terminalBoundaryFrontierPushout_nodup _ _

example :
    terminalInterfaceFrontierPushout
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right) |>.Nodup :=
  terminalInterfaceFrontierPushout_nodup _ _

example :
    terminalProfileFrontierPushout
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right) .origin |>.Nodup :=
  terminalProfileFrontierPushout_nodup _ _ _

example :
    (terminalBoundaryFrontierPushout
      (pushoutSquare.governedCompleted pushoutCandidate .left)
      (pushoutSquare.governedCompleted pushoutCandidate .right)).length = 1 := by
  decide

example :
    (terminalBoundaryFrontierDisposition
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right)
        (.input pushoutInput0) = .retained ∧
      (.input pushoutInput0) ∈ terminalBoundaryFrontierPushout
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right)) ∨
    (terminalBoundaryFrontierDisposition
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right)
        (.input pushoutInput0) = .internalized ∧
      ∃ gate, TerminalSupportWire.input pushoutInput0 = .gate gate ∧
        terminalGateSelected pushoutSquare.rightRecords gate = true) :=
  pushoutSquare.left_boundary_disposition pushoutCandidate
    (.input pushoutInput0) (by decide)

example :
    (terminalBoundaryFrontierDisposition
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right)
        (.gate pushoutGate0) = .retained ∧
      (.gate pushoutGate0) ∈ terminalBoundaryFrontierPushout
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right)) ∨
    (terminalBoundaryFrontierDisposition
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right)
        (.gate pushoutGate0) = .internalized ∧
      ∃ gate,
        (TerminalSupportWire.gate pushoutGate0 : TerminalSupportWire 1 3) =
            .gate gate ∧
        terminalGateSelected pushoutSquare.leftRecords gate = true) :=
  pushoutSquare.right_boundary_disposition pushoutCandidate
    (.gate pushoutGate0) (by decide)

example :
    (terminalInterfaceFrontierDisposition
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right)
        pushoutGate0 = .retained ∧
      pushoutGate0 ∈ terminalInterfaceFrontierPushout
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right)) ∨
    (terminalInterfaceFrontierDisposition
        (pushoutSquare.governedCompleted pushoutCandidate .left)
        (pushoutSquare.governedCompleted pushoutCandidate .right)
        pushoutGate0 = .internalized ∧
      terminalGateHasExternalConsumer pushoutCandidate.program
          (pushoutSquare.leftRecords ++ pushoutSquare.rightRecords)
          pushoutGate0 = false ∧
        terminalGateIsGlobalOutput pushoutCandidate.directWireWord
          pushoutGate0 = false) :=
  pushoutSquare.side_interface_disposition pushoutCandidate pushoutGate0
    (Or.inl (by decide))

/-! Empty sides and global-output retention cover the two boundary cases not
    present in the internalization square. -/

def pushoutEmptySquare : TerminalSaturatedSupportSquare pushoutSaturationSystem :=
  terminalSaturatedSupportSquare pushoutSaturationSystem [] []

example :
    terminalGovernedFrontierPushout
        (pushoutEmptySquare.governedCompleted pushoutCandidate .left)
        (pushoutEmptySquare.governedCompleted pushoutCandidate .right) =
      (pushoutEmptySquare.governedCompleted pushoutCandidate .join).frontier := by
  symm
  exact (pushoutEmptySquare.governed_frontier_pushout pushoutCandidate).1

def pushoutGlobalSquare : TerminalSaturatedSupportSquare pushoutSaturationSystem :=
  terminalSaturatedSupportSquare pushoutSaturationSystem
    [pushoutGate2Record] []

example :
    terminalInterfaceFrontierDisposition
        (pushoutGlobalSquare.governedCompleted pushoutCandidate .left)
        (pushoutGlobalSquare.governedCompleted pushoutCandidate .right)
        pushoutGate2 = .retained := by decide

example :
    (terminalInterfaceFrontierDisposition
        (pushoutGlobalSquare.governedCompleted pushoutCandidate .left)
        (pushoutGlobalSquare.governedCompleted pushoutCandidate .right)
        pushoutGate2 = .retained ∧
      pushoutGate2 ∈ terminalInterfaceFrontierPushout
        (pushoutGlobalSquare.governedCompleted pushoutCandidate .left)
        (pushoutGlobalSquare.governedCompleted pushoutCandidate .right)) ∨
    (terminalInterfaceFrontierDisposition
        (pushoutGlobalSquare.governedCompleted pushoutCandidate .left)
        (pushoutGlobalSquare.governedCompleted pushoutCandidate .right)
        pushoutGate2 = .internalized ∧
      terminalGateHasExternalConsumer pushoutCandidate.program
          (pushoutGlobalSquare.leftRecords ++ pushoutGlobalSquare.rightRecords)
          pushoutGate2 = false ∧
        terminalGateIsGlobalOutput pushoutCandidate.directWireWord
          pushoutGate2 = false) :=
  pushoutGlobalSquare.side_interface_disposition pushoutCandidate pushoutGate2
    (Or.inl (by decide))

end DirectWire
end PNP
