import PNP.NANDWireDescendantInput

open PNP.DirectWire
open PNP.DirectWire.WireDescendantHistory

namespace PNP.WireDescendantInputRegression

example {inputs gates outputs profileWidth : Nat}
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    decodeRecords inputs gates outputs profileWidth (records.map encodeRecord) = some records :=
  decodeRecords_encode records

example (inputs gates outputs profileWidth : Nat)
    (raw : List RawRecord) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (accepted : decodeRecords inputs gates outputs profileWidth raw = some records) :
    records.map encodeRecord = raw :=
  decodeRecords_source inputs gates outputs profileWidth raw records accepted

example {fields : Nat} (events : List (WireObligationHistory.RawEvent fields)) :
    decodeEvents fields (events.map encodeEvent) = some events :=
  decodeEvents_encode events

example (fields : Nat) (raw : List EventInput)
    (events : List (WireObligationHistory.RawEvent fields))
    (accepted : decodeEvents fields raw = some events) :
    events.map encodeEvent = raw :=
  decodeEvents_source fields raw events accepted

example : decodeRecords 2 3 2 4 [.gate 2, .profile 3, .boundary 1, .interface 1] =
    some [.gate 2, .profile 3, .boundary 1, .interface 1] := by decide

example : decodeRecords 2 2 2 2 [.gate 0, .gate 2] = none := by decide
example : decodeRecord 0 1 1 1 (.boundary 0) = none := by decide
example : decodeRecord 1 0 1 1 (.gate 0) = none := by decide
example : decodeRecord 1 1 0 1 (.interface 0) = none := by decide
example : decodeRecord 1 1 1 0 (.profile 0) = none := by decide
example : decodeRecords 0 0 0 0 [] = some [] := rfl

example : decodeAction 2 (.createR5 1) = some (.createR5 1) := by decide
example : decodeAction 2 (.createR5 2) = none := by decide
example : decodeAction 2 (.readFull 2) = none := by decide
example : decodeAction 0 .normalize = some .normalize := rfl

-- Captured R7 support coordinates must remain raw until checked against the
-- actual immutable snapshot; they are not decoded against the current field count.
example : decodeAction 0 (.realizeR7 42 [.gate 999]) =
    some (.realizeR7 42 [.gate 999]) := rfl

example : decodeEvent 2
    { identity := 7, predecessorIDs := [9, 9, 12], action := .createR5 1 } =
    some { identity := 7, predecessorIDs := [9, 9, 12], action := .createR5 1 } := by decide

example : decodeEvents 1
    [{ identity := 1, predecessorIDs := [], action := .normalize },
     { identity := 2, predecessorIDs := [1], action := .readFull 1 }] = none := by decide

example : decodeEvents 0 [] = some [] := rfl

#print axioms decodeRecord_encode
#print axioms decodeRecord_source
#print axioms decodeRecords_encode
#print axioms decodeRecords_source
#print axioms decodeAction_encode
#print axioms decodeAction_source
#print axioms decodeEvent_encode
#print axioms decodeEvent_source
#print axioms decodeEvents_encode
#print axioms decodeEvents_source

end PNP.WireDescendantInputRegression
