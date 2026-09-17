import PNP.NANDWireOpenCertificate

namespace PNP.Regression.WireOpenCertificate

open PNP.DirectWire WireOpenProgram WireOpenProperSupport WireOpenCertificate
open WireDescendantHistory (RawRecord encodeRecord decodeRecords)

example {inputs outputs fields : Nat} {carrier : WireCarrier inputs outputs fields}
    {raw : RawCertificate} (checked : CheckedCertificate carrier raw) :
    StrictEquivalentGain carrier.implementation checked.result.implementation ∧
      residualSlack checked.result.implementation < residualSlack carrier.implementation ∧
      checked.executed.program.execution.CreationsClosed :=
  ⟨checked.strictGain, checked.strictResidualDescent, checked.creation_lifecycle⟩

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (raw : RawCertificate)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (recordsAt : decodeRecords inputs carrier.implementation.gateCount
      (outputs + fields) 0 raw.records = some records)
    (program : CompiledProgram (localSource carrier records) raw.events)
    (programAt : WireOpenProgram.compile (localSource carrier records) raw.events = some program)
    (proper : 0 < (ArbitrarySupportSplice.exterior records).length)
    (smaller : program.result.implementation.gateCount <
      (extractTerminalSupport carrier.exposed.candidate records).gateCount) :
    ∃ checked, verify carrier raw = some checked :=
  verify_complete carrier raw records recordsAt program programAt proper smaller

private def source : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        ((((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩).snoc
          ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .input 0⟩)
        ⟨fun _ => .constant false⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def records : List (TerminalPrimitiveRecord 1 3 2 0) := [.gate 0, .gate 1]

private def removeGate (gate : Nat) : WireDescendantCertificate.RawCertificate :=
  ⟨[.gate gate], [⟨0, [.gate 0], [⟨7, [], .normalize⟩]⟩]⟩

private def raw : List RawEvent :=
  [⟨50, [40], .primitive (.readFull 0)⟩,
   ⟨30, [20], .support (removeGate 0)⟩,
   ⟨40, [30], .primitive (.restoreR8 7)⟩,
   ⟨7, [], .primitive (.createR5 0)⟩,
   ⟨20, [7], .support (removeGate 1)⟩]

private def temporaryGrowth : List RawEvent :=
  [⟨4, [3], .primitive (.readFull 0)⟩,
   ⟨2, [], .primitive (.restoreR8 1)⟩,
   ⟨3, [2], .primitive .normalize⟩,
   ⟨1, [], .primitive (.createR5 0)⟩]


private def historicalRequest : WireDescendantCertificate.RawCertificate :=
  ⟨[.gate 0, .gate 1], [⟨0, [.gate 0, .gate 1],
    [⟨7, [], .createR5 0⟩, ⟨20, [7], .normalize⟩, ⟨30, [20], .restoreR8 7⟩,
     ⟨40, [30], .createR5 0⟩, ⟨50, [40], .normalize⟩, ⟨60, [50], .restoreR8 40⟩]⟩]⟩

/-- Both nested allocated gates are later removed. The outer restoration
reuses the nested event numeral 60 but must have a distinct global identity. -/
private def repeatedNamespaces : List RawEvent :=
  [⟨60, [8], .primitive (.restoreR8 7)⟩,
   ⟨9, [60], .primitive (.readFull 0)⟩,
   ⟨100, [], .support historicalRequest⟩,
   ⟨8, [7], .primitive .normalize⟩,
   ⟨7, [100], .primitive (.createR5 0)⟩]


private def request : RawCertificate := ⟨[.gate 0, .gate 1], raw⟩

private def emptySource : WireCarrier 0 0 0 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 0 0) ⟨Fin.elim0⟩).toImplementation
    source := Fin.elim0 }

#eval show IO Unit from do
  let some checked := verify source request
    | throw (IO.userError "complete improving mixed-program certificate rejected")
  if checked.result.implementation.gateCount != 2 ||
      checked.executed.program.result.implementation.gateCount != 1 ||
      checked.executed.program.execution.charged != 1 ||
      checked.executed.program.execution.removed != 2 ||
      checked.executed.program.state.isClosed != true then
    throw (IO.userError "certificate lost final closure, saving or historical costs")
  if checked.records.map encodeRecord != request.records ||
      checked.ownership.live.length != 2 ||
      checked.ownership.charged != [.allocated 3 0 40 0] ||
      checked.ownership.removed.length != 2 then
    throw (IO.userError "certificate did not retain actual source records and physical ownership")
  for input in [false, true] do
    let valuation : Valuation 1 := fun _ => input
    if checked.result.implementation.candidate.semantics valuation 0 !=
        source.implementation.candidate.semantics valuation 0 ||
        checked.result.fieldValue valuation 0 != source.fieldValue valuation 0 then
      throw (IO.userError "accepted certificate changed an output or full computational field")
  let realizedEvents := raw.map fun event =>
    if event.identity = 40 then
      {event with action := .primitive (.realizeR7 7 [.gate 0, .boundary 0, .interface 0])}
    else event
  let some realized := verify source {request with events := realizedEvents}
    | throw (IO.userError "computed full-mode restoration across support changes was rejected")
  if realized.result.implementation.gateCount != 2 ||
      realized.executed.program.execution.charged != 1 ||
      realized.executed.program.execution.removed != 2 ||
      realized.ownership.charged != [.allocated 3 0 40 0] then
    throw (IO.userError "computed restoration lost its actual allocation or earlier removals")
  for input in [false, true] do
    let valuation : Valuation 1 := fun _ => input
    if realized.result.fieldValue valuation 0 != source.fieldValue valuation 0 then
      throw (IO.userError "computed restoration recovered only a projected field value")
  let some grown := verify source {request with events := temporaryGrowth}
    | throw (IO.userError "temporary growth before final saving was rejected")
  if grown.executed.program.execution.charged != 1 ||
      grown.executed.program.execution.removed != 2 then
    throw (IO.userError "public verifier hid a temporary allocation")
  let some historical := verify source {request with events := repeatedNamespaces}
    | throw (IO.userError "complete nested and ambient history was rejected")
  if historical.ownership.charged !=
      [.allocated 0 0 30 0, .allocated 0 0 60 0, .allocated 3 0 60 0] ||
      historical.ownership.removed.length != 4 ||
      !(historical.ownership.removed.contains (.allocated 0 0 30 0)) ||
      !(historical.ownership.removed.contains (.allocated 0 0 60 0)) then
    throw (IO.userError "public verifier erased removed allocations or merged independent identities")
  for invalid in [RawRecord.gate 3, .boundary 1, .interface 2, .profile 0] do
    if (verify source {request with records := request.records ++ [invalid]}).isSome then
      throw (IO.userError "out-of-range outer coordinate accepted")
  for events in [
      [],
      [⟨1, [], .primitive (.createR5 0)⟩, ⟨2, [], .primitive (.restoreR8 1)⟩],
      [⟨7, [], .primitive (.createR5 0)⟩, ⟨20, [7], .support (removeGate 1)⟩],
      [⟨7, [], .primitive (.createR5 0)⟩, ⟨8, [7], .primitive (.readFull 0)⟩],
      [⟨7, [], .primitive (.createR5 0)⟩, ⟨8, [], .primitive (.cancelR6 7)⟩],
      [⟨7, [], .primitive (.createR5 0)⟩, ⟨8, [7], .primitive (.createR5 0)⟩],
      raw ++ [⟨99, [50], .primitive (.readFull 9)⟩],
      raw ++ [⟨7, [50], .primitive (.readFull 0)⟩],
      raw ++ [⟨99, [777], .primitive (.readFull 0)⟩],
      raw ++ [⟨91, [92], .primitive .normalize⟩, ⟨92, [91], .primitive .normalize⟩],
      raw ++ [⟨99, [50], .support ⟨[.gate 100], []⟩⟩]] do
    if (verify source {request with events := events}).isSome then
      throw (IO.userError "non-improvement, open ledger, malformed graph, false discharge or failed tail accepted")
  let wholeRecords : List (TerminalPrimitiveRecord 1 3 2 0) := [.gate 0, .gate 1, .gate 2]
  let some whole := WireOpenProperSupport.compile source wholeRecords raw
    | throw (IO.userError "whole-support rejection fixture did not actually execute")
  if whole.program.result.implementation.gateCount >= 3 then
    throw (IO.userError "whole-support rejection fixture was not a genuine improvement")
  if (verify source ⟨wholeRecords.map encodeRecord, raw⟩).isSome then
    throw (IO.userError "whole support was mislabeled as a proper local certificate")
  let repeated := {request with records := request.records ++ [.gate 1]}
  let some duplicate := verify source repeated
    | throw (IO.userError "repeated valid record changed support acceptance")
  if duplicate.records.map encodeRecord != repeated.records ||
      duplicate.result.implementation.gateCount != checked.result.implementation.gateCount ||
      duplicate.ownership.charged != checked.ownership.charged then
    throw (IO.userError "repeated record was dropped or counted as another physical gate")
  if (verify emptySource ⟨[], []⟩).isSome || (verify source ⟨[], []⟩).isSome then
    throw (IO.userError "empty support produced a false proper saving")
  IO.println "open-source-only-certificate-regressions-passed"

#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.records_source
#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.proper_support
#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.output
#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.field
#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.gateCount
#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.charge_accounting
#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictGain
#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictResidualDescent
#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.physical_ownership
#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.closed_ledger
#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.creation_lifecycle
#print axioms PNP.DirectWire.WireOpenCertificate.verify_complete
#print axioms PNP.DirectWire.WireOpenCertificate.verify_exists_iff
#print axioms PNP.DirectWire.WireOpenCertificate.verify_sound
#print axioms PNP.DirectWire.WireOpenCertificate.verify_decode_none
#print axioms PNP.DirectWire.WireOpenCertificate.verify_program_none
#print axioms PNP.DirectWire.WireOpenCertificate.verify_not_proper
#print axioms PNP.DirectWire.WireOpenCertificate.verify_no_gain

end PNP.Regression.WireOpenCertificate
