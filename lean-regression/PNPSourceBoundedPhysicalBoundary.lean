import PNP

namespace PNP.DirectWire.SourceBoundedPhysicalBoundary.Regression

def onePair : Program 4 1 :=
  (.empty : Program 4 0).snoc ⟨.input 3, .input 1⟩

def repeated : Program 4 1 :=
  (.empty : Program 4 0).snoc ⟨.input 2, .input 2⟩

def constants : Program 0 1 :=
  (.empty : Program 0 0).snoc ⟨.constant false, .constant true⟩

def chain : Program 4 3 :=
  (((.empty : Program 4 0).snoc ⟨.input 3, .input 1⟩).snoc
    ⟨.gate ⟨0, by decide⟩, .input 2⟩).snoc
    ⟨.gate ⟨1, by decide⟩, .gate ⟨0, by decide⟩⟩

def checkSmall {inputs gates : Nat} (name : String)
    (program : Program inputs gates) (selected : List (Fin gates))
    (expected : List Nat) : IO Unit := do
  if inputs > 4 || gates > 3 then
    throw (IO.userError "small reference fixture exceeds its guarded dimensions")
  let records : List (TerminalPrimitiveRecord inputs gates 0 0) :=
    selected.map TerminalPrimitiveRecord.gate
  let actual := terminalBoundaryPorts program records
  let reference := (allTerminalSupportWires inputs gates).filter
    (terminalBoundaryWire program records)
  if !(decide (actual = reference)) ||
      actual.map TerminalSupportWire.orderCode != expected then
    throw (IO.userError (name ++ ": exact ordered boundary changed"))
  if (terminalSourceWireOccurrences program).length > 2 * gates ||
      actual.length > 2 * gates then
    throw (IO.userError (name ++ ": physical occurrence bound failed"))
  IO.println ("M260_FIXTURE_GREEN=" ++ name)

def widePair : Program 1000000000 1 :=
  (.empty : Program 1000000000 0).snoc
    ⟨.input ⟨999999999, by decide⟩, .input ⟨7, by decide⟩⟩

def wideChain : Program 1000000000 2 :=
  widePair.snoc ⟨.gate ⟨0, by decide⟩, .input ⟨7, by decide⟩⟩

-- Large-width fixtures never execute the ambient reference or enumerate valuations.
def checkWide {gates : Nat} (name : String)
    (program : Program 1000000000 gates) (selected : List (Fin gates))
    (expected : List Nat) : IO Unit := do
  if gates > 2 then
    throw (IO.userError "large-width fixture exceeds its guarded gate count")
  let records : List (TerminalPrimitiveRecord 1000000000 gates 0 0) :=
    selected.map TerminalPrimitiveRecord.gate
  let actual := terminalBoundaryPorts program records
  if actual.map TerminalSupportWire.orderCode != expected ||
      actual.length > 2 * gates ||
      (terminalSourceWireOccurrences program).length > 2 * gates then
    throw (IO.userError (name ++ ": source-bounded large-width extraction failed"))
  IO.println ("M260_FIXTURE_GREEN=" ++ name)

example {inputs gates outputs profileWidth : Nat} (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalBoundaryPorts program records =
      (allTerminalSupportWires inputs gates).filter (terminalBoundaryWire program records) :=
  terminalBoundaryPorts_reference program records

example {inputs gates outputs profileWidth : Nat} (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalBoundaryPorts program records).length ≤ 2 * gates :=
  terminalBoundaryPorts_length program records

example {inputs gates outputs profileWidth : Nat} (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalBoundaryPorts program records).Nodup :=
  terminalBoundaryPorts_nodup program records

-- kernel-source-order: imported source ordering reduces in the trusted kernel.
example : SourceListOrder.canonical (fun n : Nat => n) [2, 1] = [1, 2] := by decide

-- kernel-duplicate-order: deduplication and ordering compose without an oracle.
example : SourceListOrder.canonical (fun n : Nat => n) [3, 1, 2, 1, 0, 3] =
    [0, 1, 2, 3] := by decide

-- kernel-wide-boundary-order: no ambient-width enumeration is needed by reduction.
example : (terminalBoundaryPorts widePair
    ([.gate ⟨0, by decide⟩] : List (TerminalPrimitiveRecord 1000000000 1 0 0))).map
      TerminalSupportWire.orderCode = [7, 999999999] := by decide

-- kernel-dependent-boundary-width: preserve the original concrete valuation type.
example (boundary : Valuation 2) : Valuation (terminalBoundaryPorts onePair
    ([.gate ⟨0, by decide⟩] : List (TerminalPrimitiveRecord 4 1 0 0))).length := boundary

#eval (show IO Unit from do
  checkSmall "empty-dimensions" (.empty : Program 0 0) [] []
  checkSmall "empty-selected-support" onePair [] []
  checkSmall "primary-source-order" onePair [⟨0, by decide⟩] [1, 3]
  checkSmall "duplicate-source" repeated [⟨0, by decide⟩] [2]
  checkSmall "constant-locality" constants [⟨0, by decide⟩] []
  checkSmall "mixed-input-gate-ports" chain [⟨1, by decide⟩] [2, 4]
  checkSmall "reversed-gate-source-order" chain [⟨2, by decide⟩] [4, 5]
  checkSmall "nonconsecutive-support" chain [⟨0, by decide⟩, ⟨2, by decide⟩] [1, 3, 5]
  checkSmall "duplicate-unordered-records" chain
    [⟨2, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩] [1, 3, 5]
  checkSmall "selected-producer-is-internal" chain
    [⟨1, by decide⟩, ⟨2, by decide⟩] [2, 4]
  checkSmall "whole-support-primary-order" chain
    [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] [1, 2, 3]
  checkWide "billion-unused-inputs-empty-program" (.empty : Program 1000000000 0) [] []
  checkWide "billion-inputs-sparse-primary-ports" widePair [⟨0, by decide⟩] [7, 999999999]
  checkWide "billion-inputs-mixed-ports" wideChain [⟨1, by decide⟩] [7, 1000000000]
  checkWide "billion-inputs-whole-support" wideChain
    [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩] [7, 999999999]
  IO.println "M260_SOURCE_BOUNDED_PHYSICAL_BOUNDARY_RUNTIME_GREEN")

end PNP.DirectWire.SourceBoundedPhysicalBoundary.Regression
