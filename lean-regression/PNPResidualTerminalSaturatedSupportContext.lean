import PNP.ResidualTerminalSaturatedSupportContext

namespace PNP.DirectWire

-- This applies at arbitrary dimensions and supplies no closure or context proof.
example {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (wire : TerminalSupportWire inputs gates)
    (member : wire ∈ (extractTerminalSupport candidate
      (terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed)).boundary) :
    ∃ input : Fin inputs, wire = TerminalSupportWire.input input :=
  terminalCandidateSaturate_boundary_isInput candidate model seed wire member

-- Every replacement size is admitted; semantic equivalence is not needed
-- for the exact physical charge equation.
example {inputs gates outputs profileWidth replacementGates : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (replacement : Candidate
      (extractTerminalSupport candidate (terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed)).boundary.length
      replacementGates
      (extractTerminalSupport candidate (terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed)).interface.length) :
    ((terminalCandidateSaturatePhysicalContext candidate model seed).plug
        replacement).program.size +
      (terminalSaturatePhysicalCharges
        (terminalCandidateSaturationSystem candidate model) seed).length =
      gates + replacementGates :=
  terminalCandidateSaturatePhysicalContext_size candidate model seed replacement

#print axioms terminalCandidateSaturatePhysicalContext_size
#print axioms terminalCandidateSaturate_boundary_isInput

-- All three reconstruction/replacement/slack contracts apply to arbitrary
-- dimensions. No caller supplies a frame or whole-circuit correctness proof.
example {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    let support := extractTerminalSupport candidate (terminalSaturateRecords
      (terminalCandidateSaturationSystem candidate model) seed)
    let context := terminalCandidateSaturatePhysicalContext candidate model seed
    Equivalent (context.plug support.extractedCandidate).program
      (context.plug support.extractedCandidate).directWireWord
      candidate.program candidate.directWireWord :=
  terminalCandidateSaturatePhysicalContext_equivalent candidate model seed

example {inputs gates outputs profileWidth replacementGates : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (replacement : Candidate
      (extractTerminalSupport candidate (terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed)).boundary.length
      replacementGates
      (extractTerminalSupport candidate (terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed)).interface.length) :
    let support := extractTerminalSupport candidate (terminalSaturateRecords
      (terminalCandidateSaturationSystem candidate model) seed)
    let context := terminalCandidateSaturatePhysicalContext candidate model seed
    Equivalent replacement.program replacement.directWireWord
      support.extractedCandidate.program support.extractedCandidate.directWireWord →
    Equivalent (context.plug replacement).program
      (context.plug replacement).directWireWord
      candidate.program candidate.directWireWord :=
  terminalCandidateSaturatePhysicalContext_replace_equivalent candidate model seed replacement

example {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    residualSlack (extractTerminalSupport candidate (terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed)).extractedCandidate.toImplementation ≤
      residualSlack candidate.toImplementation :=
  terminalCandidateSaturatePhysicalSupport_slack_le candidate model seed

#print axioms terminalCandidateSaturatePhysicalContext_equivalent
#print axioms terminalCandidateSaturatePhysicalContext_replace_equivalent
#print axioms terminalCandidateSaturatePhysicalSupport_slack_le

namespace SaturatedSupportContextRegression

def zeroProfileModel {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) :
    TerminalCandidateSaturationModel (profileWidth := 0) candidate :=
  { profileSystem := { role := Fin.elim0, observe := fun _ => Fin.elim0 }
    projection := { keep := Fin.elim0 }
    observe := fun _ => Fin.elim0 }

-- Gates 0 and 2 form a noncontiguous fan-in-closed support. Gate 2 is
-- consumed by two outside gates. Its extracted word is the constant true.
def program : Program 2 5 :=
  .snoc
    (.snoc
      (.snoc
        (.snoc
          (.snoc .empty { left := .input 0, right := .input 0 })
          { left := .input 1, right := .input 1 })
        { left := .gate 0, right := .input 0 })
      { left := .gate 1, right := .gate 2 })
    { left := .gate 2, right := .input 1 }

def candidate : Candidate 2 5 5 :=
  Candidate.ofDirectWireWord program ⟨fun output =>
    if output.val = 0 then .gate 3
    else if output.val = 1 then .gate 4
    else if output.val = 2 then .gate 3
    else if output.val = 3 then .input 0
    else .constant true⟩

def model := zeroProfileModel candidate
abbrev Record := TerminalPrimitiveRecord 2 5 5 0
def seed : List Record := [.gate 2]
def records := terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed
def support := extractTerminalSupport candidate records
def complement := extractTerminalSupport candidate (terminalPhysicalComplementRecords records)
def context := terminalCandidateSaturatePhysicalContext candidate model seed

example : support.selectedGates = [0, 2] := by decide
example : support.boundary = [.input 0] := by decide
example : support.interface = [2] := by decide
example : complement.selectedGates = [1, 3, 4] := by decide
example : complement.boundary = [.input 1, .gate 2] := by decide
example : support.gateCount = 2 := by decide
example : complement.gateCount = 3 := by decide
example : (context.plug support.extractedCandidate).program.size = 5 := by decide

example : equivalentBool (context.plug support.extractedCandidate) candidate = true := by decide

-- This raw support is deliberately not saturated. Its external gate boundary
-- forbids using the public zero-environment theorem without production closure.
example : TerminalSupportWire.gate (0 : Fin 5) ∈
    (extractTerminalSupport candidate ([.gate 2] : List Record)).boundary := by decide

example : (extractTerminalSupport candidate
    (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model)
      ([.gate 2, .gate 2] : List Record))).selectedGates = support.selectedGates := by decide

def smaller : Candidate support.boundary.length 0 support.interface.length :=
  Candidate.ofDirectWireWord .empty ⟨fun _ => .constant true⟩

def larger : Candidate support.boundary.length 3 support.interface.length :=
  Candidate.ofDirectWireWord
    (.snoc
      (.snoc
        (.snoc .empty { left := .constant false, right := .constant true })
        { left := .constant true, right := .constant true })
      { left := .constant false, right := .constant false })
    ⟨fun _ => .constant true⟩

example : Equivalent smaller.program smaller.directWireWord
    support.extractedCandidate.program support.extractedCandidate.directWireWord :=
  equivalentBool_sound (by decide)

example : Equivalent larger.program larger.directWireWord
    support.extractedCandidate.program support.extractedCandidate.directWireWord :=
  equivalentBool_sound (by decide)

example : Equivalent (context.plug smaller).program (context.plug smaller).directWireWord
    candidate.program candidate.directWireWord :=
  terminalCandidateSaturatePhysicalContext_replace_equivalent candidate model seed smaller
    (equivalentBool_sound (by decide))

example : Equivalent (context.plug larger).program (context.plug larger).directWireWord
    candidate.program candidate.directWireWord :=
  terminalCandidateSaturatePhysicalContext_replace_equivalent candidate model seed larger
    (equivalentBool_sound (by decide))

example : (context.plug smaller).program.size = 3 := by decide
example : (context.plug larger).program.size = 6 := by decide

def emptySupport := extractTerminalSupport candidate
  (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) [])
def emptyContext := terminalCandidateSaturatePhysicalContext candidate model []

example : emptySupport.gateCount = 0 := by decide
example : emptySupport.boundary = [] := by decide
example : emptySupport.interface = [] := by decide
example : equivalentBool (emptyContext.plug emptySupport.extractedCandidate) candidate = true := by decide

def fullSeed : List Record := [.gate 0, .gate 1, .gate 2, .gate 3, .gate 4]
def fullSupport := extractTerminalSupport candidate
  (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) fullSeed)
def fullContext := terminalCandidateSaturatePhysicalContext candidate model fullSeed

example : fullSupport.gateCount = 5 := by decide
example : fullContext.continuation.program.size = 0 := by decide
example : equivalentBool (fullContext.plug fullSupport.extractedCandidate) candidate = true := by decide

-- Zero input/gate/output widths exercise all empty finite carriers.
def zeroCandidate : Candidate 0 0 0 := Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩
def zeroModel := zeroProfileModel zeroCandidate
def zeroSupport := extractTerminalSupport zeroCandidate
  (terminalSaturateRecords (terminalCandidateSaturationSystem zeroCandidate zeroModel) [])
def zeroContext := terminalCandidateSaturatePhysicalContext zeroCandidate zeroModel []

example : (zeroContext.plug zeroSupport.extractedCandidate).program.size = 0 := by decide
example : equivalentBool (zeroContext.plug zeroSupport.extractedCandidate) zeroCandidate = true := by decide

-- Local constants need no input port, even for a nonempty selected support.
def constantCandidate : Candidate 0 1 1 :=
  Candidate.ofDirectWireWord
    (.snoc .empty { left := .constant false, right := .constant false })
    ⟨fun _ => .gate 0⟩
def constantModel := zeroProfileModel constantCandidate
def constantSeed : List (TerminalPrimitiveRecord 0 1 1 0) := [.gate 0]
def constantSupport := extractTerminalSupport constantCandidate
  (terminalSaturateRecords
    (terminalCandidateSaturationSystem constantCandidate constantModel) constantSeed)
def constantContext := terminalCandidateSaturatePhysicalContext
  constantCandidate constantModel constantSeed

example : constantSupport.boundary = [] := by decide
example : equivalentBool (constantContext.plug constantSupport.extractedCandidate) constantCandidate = true := by decide

end SaturatedSupportContextRegression

end PNP.DirectWire
