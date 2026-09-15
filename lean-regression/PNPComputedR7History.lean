/-
General raw-R7 contracts and executable hostile regressions. Small circuits here
are regression fixtures, not milestone credit or a global strategy theorem.
-/
import PNP.NANDWireHistoryArbitrarySupport

namespace PNP.Regression.ComputedR7History

open DirectWire WireObligationHistory

variable {inputs outputs fields gates observations profileWidth : Nat}

example (record : TerminalPrimitiveRecord inputs gates observations 0) :
    decodeRecord inputs gates observations (encodeRecord record) = some record :=
  decodeRecord_encode record

example (raw : RawSupportRecord) (record : TerminalPrimitiveRecord inputs gates observations 0)
    (accepted : decodeRecord inputs gates observations raw = some record) :
    encodeRecord record = raw := decodeRecord_source raw record accepted

example {source : WireCarrier inputs outputs fields} (state : State source)
    (field : Fin fields) (snapshot : Snapshot source field)
    (found : state.pending field = some snapshot) (raw : List RawSupportRecord)
    (realization : R7Realization snapshot.carrier raw) (labels : Fin inputs → Nat)
    (bounded : state.CausalInvariant labels) :
    (state.restoreR7 field snapshot found raw realization).CausalInvariant labels :=
  state.restoreR7_causalInvariant field snapshot found raw realization labels bounded

example {source : WireCarrier inputs outputs fields} (state : State source)
    (field : Fin fields) (snapshot : Snapshot source field)
    (found : state.pending field = some snapshot) (raw : List RawSupportRecord)
    (realization : R7Realization snapshot.carrier raw) (valuation : Valuation inputs) :
    (state.restoreR7 field snapshot found raw realization).current.fieldValue valuation field =
      snapshot.carrier.fieldValue valuation field :=
  state.restoreR7_full_value field snapshot found raw realization valuation

/-- Raw histories containing R7 still require no extra ambient compilation premise. -/
example (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (raw : List (RawEvent (terminalInterfacePorts candidate records).length)) :
    WireHistoryArbitrarySupport.compile candidate records raw = none ↔
      compileHistory (WireHistoryArbitrarySupport.extractedCarrier candidate records) raw = none :=
  WireHistoryArbitrarySupport.compile_none_iff candidate records

example (records : List (TerminalPrimitiveRecord inputs gates observations 0)) :
    decodeRecords inputs gates observations (records.map encodeRecord) = some records :=
  decodeRecords_encode records

example (raw : List RawSupportRecord)
    (records : List (TerminalPrimitiveRecord inputs gates observations 0))
    (accepted : decodeRecords inputs gates observations raw = some records) :
    records.map encodeRecord = raw := decodeRecords_source raw records accepted

example (original : WireCarrier inputs outputs fields) (raw : List RawSupportRecord) :
    (computeR7 original raw).isSome = true ↔
      ∃ records, decodeRecords inputs original.implementation.gateCount (outputs + fields) raw =
        some records ∧ (WireUnaryArbitrarySupport.pulled original records).boundary.length ≤ 1 :=
  computeR7_isSome_iff original raw

private def doubleNegation : Program 1 2 :=
  ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩).snoc ⟨.gate 0, .gate 0⟩

private def capturedTwo : WireCarrier 1 1 1 :=
  { implementation := (Candidate.ofDirectWireWord doubleNegation
      (⟨fun _ => .constant true⟩ : DirectWireWord 1 2 1)).toImplementation
    source := fun _ => .gate ⟨1, by decide⟩ }

private def capturedOne : WireCarrier 1 0 1 :=
  { implementation := (Candidate.ofDirectWireWord (.snoc .empty ⟨.input 0, .input 0⟩)
      (⟨Fin.elim0⟩ : DirectWireWord 1 1 0)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def binaryCarrier : WireCarrier 2 0 1 :=
  { implementation := (Candidate.ofDirectWireWord (.snoc .empty ⟨.input 0, .input 1⟩)
      (⟨Fin.elim0⟩ : DirectWireWord 2 1 0)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def ambient : Candidate 1 3 2 :=
  Candidate.ofDirectWireWord (doubleNegation.snoc ⟨.input 0, .input 0⟩)
    ⟨fun output => if output.val = 0 then .gate 1 else .gate 2⟩

private def ambientRecords : List (TerminalPrimitiveRecord 1 3 2 0) := [.gate 0, .gate 1]

private def selected : List RawSupportRecord :=
  [.gate 0, .gate 1, .boundary 0, .interface 1]

private def history (records : List RawSupportRecord) : List (RawEvent 1) :=
  [⟨30, [20], .realizeR7 10 records⟩, ⟨20, [10], .normalize⟩,
    ⟨10, [], .createR5 0⟩, ⟨40, [30], .readFull 0⟩]

#eval show IO Unit from do
  let some restored := compileHistory capturedTwo (history selected)
    | throw (IO.userError "R7 rejected valid captured coordinates after physical normalization")
  if restored.execution.records.map (fun record => record.identity) != [10, 20, 30, 40] then
    throw (IO.userError "R7 intrinsic dependency or full read was not ordered")
  if restored.execution.charged != 0 || restored.execution.removed != 2 ||
      restored.state.current.implementation.gateCount != 0 then
    throw (IO.userError "R7 did not use the computed zero-gate double-negation realization")
  for value in [false, true] do
    if restored.state.current.fieldValue (fun _ => value) 0 != value ||
        !restored.state.current.implementation.candidate.semantics (fun _ => value) 0 then
      throw (IO.userError "R7 lost a full field or ordinary output")
  let dischargeIDs := restored.execution.records.filterMap
    (fun record => record.discharge.map (fun discharge => discharge.creation.identity))
  if dischargeIDs != [10] then
    throw (IO.userError "R7 discharge is not bound to its original creation identity")
  let some charged := compileHistory capturedOne (history [.gate 0])
    | throw (IO.userError "R7 rejected the full unary negation materializer")
  if charged.execution.charged != 1 || charged.execution.removed != 1 ||
      charged.state.current.implementation.gateCount != 1 then
    throw (IO.userError "R7 omitted an actual materializer charge")
  for value in [false, true] do
    if charged.state.current.fieldValue (fun _ => value) 0 != !value then
      throw (IO.userError "R7 negation restoration used quotient padding")
  let some swapped := WireHistoryArbitrarySupport.compile ambient ambientRecords
      (history [.gate 0, .gate 1, .boundary 0, .interface 0])
    | throw (IO.userError "R7 history was rejected by the literal ambient splice")
  if swapped.gateCount != 1 then
    throw (IO.userError "R7 ambient replacement duplicated or removed the physical exterior")
  for value in [false, true] do
    if swapped.candidate.semantics (fun _ => value) 0 != value ||
        swapped.candidate.semantics (fun _ => value) 1 != !value then
      throw (IO.userError "R7 ambient replacement lost a protected output")
  for invalid in [[.gate 2], [.boundary 1], [.interface 2], [.gate 0, .gate 99]] do
    if (compileHistory capturedTwo (history invalid)).isSome then
      throw (IO.userError "R7 accepted an out-of-range captured coordinate")
  if (compileHistory binaryCarrier (history [.gate 0])).isSome then
    throw (IO.userError "R7 accepted a completed boundary with two inputs")
  for invalid in [
      [⟨30, [], .realizeR7 999 selected⟩],
      [⟨10, [], .createR5 0⟩, ⟨20, [], .realizeR7 10 selected⟩,
        ⟨30, [20], .realizeR7 10 selected⟩],
      [⟨10, [], .createR5 0⟩, ⟨20, [10], .readFull 0⟩,
        ⟨30, [20], .realizeR7 10 selected⟩],
      [⟨10, [], .createR5 0⟩, ⟨20, [], .realizeR7 10 selected⟩,
        ⟨30, [20], .createR5 0⟩, ⟨40, [30], .realizeR7 10 selected⟩],
      [⟨10, [], .createR5 0⟩]
    ] do
    if (compileHistory capturedTwo invalid).isSome then
      throw (IO.userError "R7 accepted a missing, reused, stale, or unfinished creation")
  IO.println "M265 computed-r7-history-regressions-passed"

end PNP.Regression.ComputedR7History
