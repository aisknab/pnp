import PNP.ResidualTerminalSupportExtraction

namespace PNP
namespace DirectWire

abbrev extractionRecord := TerminalPrimitiveRecord 2 4 2 0

def extractionInput0 : Fin 2 := ⟨0, by decide⟩
def extractionInput1 : Fin 2 := ⟨1, by decide⟩
def extractionGate0 : Fin 4 := ⟨0, by decide⟩
def extractionGate1 : Fin 4 := ⟨1, by decide⟩
def extractionGate2 : Fin 4 := ⟨2, by decide⟩
def extractionGate3 : Fin 4 := ⟨3, by decide⟩

def extractionProgram0 : Program 2 1 :=
  .snoc .empty
    { left := .input extractionInput0
      right := .constant true }

def extractionProgram1 : Program 2 2 :=
  .snoc extractionProgram0
    { left := .input extractionInput1
      right := .constant false }

def extractionProgram2 : Program 2 3 :=
  .snoc extractionProgram1
    { left := .gate ⟨0, by decide⟩
      right := .gate ⟨1, by decide⟩ }

def extractionProgram : Program 2 4 :=
  .snoc extractionProgram2
    { left := .gate ⟨2, by decide⟩
      right := .input extractionInput0 }

def extractionWord : DirectWireWord 2 4 2 :=
  ⟨fun output =>
    if output.val = 0 then .gate extractionGate2 else .gate extractionGate0⟩

def extractionCandidate : Candidate 2 4 2 :=
  Candidate.ofDirectWireWord extractionProgram extractionWord

def extractionGate0Record : extractionRecord := .gate extractionGate0
def extractionGate1Record : extractionRecord := .gate extractionGate1
def extractionGate2Record : extractionRecord := .gate extractionGate2
def extractionGate3Record : extractionRecord := .gate extractionGate3

def extractionNoncontiguous : List extractionRecord :=
  [extractionGate2Record, extractionGate0Record, extractionGate2Record]

def extractionAll : List extractionRecord :=
  [extractionGate0Record, extractionGate1Record,
    extractionGate2Record, extractionGate3Record]

example : terminalSelectedGates ([] : List extractionRecord) = [] := by decide

example : terminalSelectedGates [extractionGate2Record] = [extractionGate2] := by
  decide

/-- Duplicate, scrambled records normalize to ascending physical gate order. -/
example :
    terminalSelectedGates extractionNoncontiguous =
      [extractionGate0, extractionGate2] := by
  decide

example :
    terminalSelectedGates extractionAll =
      [extractionGate0, extractionGate1, extractionGate2, extractionGate3] := by
  decide

/-- The selected gates are noncontiguous.  Input zero and unselected gate one
    are the exact incoming wires; the constant and gate-zero-to-gate-two edge
    remain internal. -/
example :
    terminalBoundaryPorts extractionProgram extractionNoncontiguous =
      [.input extractionInput0, .gate extractionGate1] := by
  decide

/-- Both selected gates are externally observable, in canonical gate order. -/
example :
    terminalInterfacePorts extractionCandidate extractionNoncontiguous =
      [extractionGate0, extractionGate2] := by
  decide

example :
    (extractTerminalSupport extractionCandidate extractionNoncontiguous).gateCount = 2 := by
  decide

example :
    (extractTerminalSupport extractionCandidate
      ([] : List extractionRecord)).gateCount = 0 := by
  decide

example :
    (extractTerminalSupport extractionCandidate extractionAll).gateCount = 4 := by
  decide

/-- The first extracted NAND retains the local constant. -/
example :
    (extractTerminalSupport extractionCandidate
      extractionNoncontiguous).extractedCandidate.program.terminalGateSources
        ⟨0, by decide⟩ =
      (.input ⟨0, by decide⟩, .constant true) := by
  decide

/-- The second extracted NAND uses the reindexed internal first gate and the
    second boundary coordinate which represents unselected gate one. -/
example :
    (extractTerminalSupport extractionCandidate
      extractionNoncontiguous).extractedCandidate.program.terminalGateSources
        ⟨1, by decide⟩ =
      (.gate ⟨0, by decide⟩, .input ⟨1, by decide⟩) := by
  decide

example :
    (extractTerminalSupport extractionCandidate
      extractionNoncontiguous).extractedCandidate.directWireWord.source
        ⟨0, by decide⟩ = .gate ⟨0, by decide⟩ := by
  decide

example :
    (extractTerminalSupport extractionCandidate
      extractionNoncontiguous).extractedCandidate.directWireWord.source
        ⟨1, by decide⟩ = .gate ⟨1, by decide⟩ := by
  decide

def extractionBoundary00 : Valuation 2 :=
  (BoolTuple.cons false (BoolTuple.cons false .nil)).toValuation
def extractionBoundary01 : Valuation 2 :=
  (BoolTuple.cons false (BoolTuple.cons true .nil)).toValuation
def extractionBoundary10 : Valuation 2 :=
  (BoolTuple.cons true (BoolTuple.cons false .nil)).toValuation
def extractionBoundary11 : Valuation 2 :=
  (BoolTuple.cons true (BoolTuple.cons true .nil)).toValuation

example : terminalOpenSupportSemantics extractionCandidate extractionNoncontiguous
    extractionBoundary00 ⟨0, by decide⟩ = true := by decide
example : terminalOpenSupportSemantics extractionCandidate extractionNoncontiguous
    extractionBoundary00 ⟨1, by decide⟩ = true := by decide
example : terminalOpenSupportSemantics extractionCandidate extractionNoncontiguous
    extractionBoundary01 ⟨0, by decide⟩ = true := by decide
example : terminalOpenSupportSemantics extractionCandidate extractionNoncontiguous
    extractionBoundary01 ⟨1, by decide⟩ = false := by decide
example : terminalOpenSupportSemantics extractionCandidate extractionNoncontiguous
    extractionBoundary10 ⟨0, by decide⟩ = false := by decide
example : terminalOpenSupportSemantics extractionCandidate extractionNoncontiguous
    extractionBoundary10 ⟨1, by decide⟩ = true := by decide
example : terminalOpenSupportSemantics extractionCandidate extractionNoncontiguous
    extractionBoundary11 ⟨0, by decide⟩ = false := by decide
example : terminalOpenSupportSemantics extractionCandidate extractionNoncontiguous
    extractionBoundary11 ⟨1, by decide⟩ = true := by decide

/-- The universal equality is not a truth-table coincidence. -/
example (boundary : Valuation 2) (output : Fin 2) :
    (extractTerminalSupport extractionCandidate
      extractionNoncontiguous).extractedCandidate.semantics boundary output =
      terminalOpenSupportSemantics extractionCandidate extractionNoncontiguous
        boundary output :=
  extractTerminalSupport_semantics extractionCandidate extractionNoncontiguous
    boundary output

def extractionProfileSystem : TerminalProfileSystem 2 2 0 :=
  { role := fun coordinate => Fin.elim0 coordinate
    observe := fun _implementation coordinate => Fin.elim0 coordinate }

def extractionSaturationSystem : TerminalSaturationSystem 2 4 2 0 :=
  { profileSystem := extractionProfileSystem
    requires := fun kind dependent required =>
      match kind with
      | .gateSource => decide (
          dependent = extractionGate0Record ∧ required = extractionGate2Record)
      | _ => false }

example :
    terminalSaturateRecords extractionSaturationSystem
        [extractionGate0Record, extractionGate0Record] =
      [extractionGate2Record, extractionGate0Record] := by
  decide

example :
    (extractSaturatedTerminalSupport extractionCandidate extractionSaturationSystem
      [extractionGate0Record]).gateCount = 2 := by
  decide

def extractionInput00 : Valuation 2 := extractionBoundary00
def extractionInput11 : Valuation 2 := extractionBoundary11

example (output : Fin 2) :
    (extractTerminalSupport extractionCandidate
      extractionNoncontiguous).extractedCandidate.semantics
        (terminalInducedBoundaryValuation extractionCandidate
          extractionNoncontiguous extractionInput00) output =
      extractionCandidate.program.eval extractionInput00
        ((terminalInterfacePorts extractionCandidate
          extractionNoncontiguous).get output) :=
  extractTerminalSupport_induced extractionCandidate extractionNoncontiguous
    extractionInput00 output

example (output : Fin 2) :
    (extractSaturatedTerminalSupport extractionCandidate extractionSaturationSystem
      [extractionGate0Record]).extractedCandidate.semantics
        (terminalInducedBoundaryValuation extractionCandidate
          (terminalSaturateRecords extractionSaturationSystem
            [extractionGate0Record]) extractionInput11) output =
      extractionCandidate.program.eval extractionInput11
        ((terminalInterfacePorts extractionCandidate
          (terminalSaturateRecords extractionSaturationSystem
            [extractionGate0Record])).get output) :=
  extractSaturatedTerminalSupport_induced extractionCandidate
    extractionSaturationSystem [extractionGate0Record] extractionInput11 output

end DirectWire
end PNP
