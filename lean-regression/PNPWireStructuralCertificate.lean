import PNP.NANDWireOpenCertificate

namespace PNP.Regression.StructuralCertificate

open PNP.DirectWire WireOpenProgram WireOpenCertificate
open WireDescendantHistory (encodeRecord)

example {inputs outputs fields : Nat} {carrier : WireCarrier inputs outputs fields}
    {raw : RawCertificate} (checked : CheckedCertificate carrier raw) :
    StrictEquivalentGain carrier.implementation checked.result.implementation ∧
      residualSlack checked.result.implementation < residualSlack carrier.implementation ∧
      checked.executed.program.execution.CreationsClosed :=
  ⟨checked.strictGain, checked.strictResidualDescent, checked.creation_lifecycle⟩

example {inputs outputs fields : Nat} {carrier : WireCarrier inputs outputs fields}
    {raw : RawCertificate} (checked : CheckedCertificate carrier raw) :
    checked.ownership.live.length = checked.result.implementation.gateCount ∧
      checked.ownership.charged.length = checked.executed.program.execution.charged ∧
      checked.ownership.removed.length = checked.executed.program.execution.removed ∧
      (checked.ownership.live ++ checked.ownership.removed).Nodup ∧
      (checked.ownership.live ++ checked.ownership.removed).Perm
        (programOriginals carrier.implementation.gateCount ++ checked.ownership.charged) :=
  checked.physical_ownership

#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictGain
#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictResidualDescent
#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.physical_ownership
#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.creation_lifecycle
#print axioms PNP.DirectWire.WireOpenCertificate.verify_program_none
#print axioms PNP.DirectWire.WireOpenCertificate.verify_not_proper
#print axioms PNP.DirectWire.WireOpenCertificate.verify_no_gain

private def fixture : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        ((((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩).snoc
          ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .input 0⟩)
        ⟨fun _ => .constant false⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def records : List (TerminalPrimitiveRecord 1 3 2 0) := [.gate 0, .gate 1]

private def removeGate (gate : Nat) : WireDescendantCertificate.RawCertificate :=
  ⟨[.gate gate], [⟨0, [.gate 0], [⟨7, [], .normalize⟩]⟩]⟩

private def events : List RawEvent :=
  [⟨50, [45], .primitive (.readFull 0)⟩,
   ⟨45, [40], .structural [(0, 0)]⟩,
   ⟨30, [20], .support (removeGate 0)⟩,
   ⟨40, [30], .primitive (.restoreR8 7)⟩,
   ⟨7, [], .primitive (.createR5 0)⟩,
   ⟨20, [10], .support (removeGate 1)⟩,
   ⟨10, [7], .structural [(0, 1)]⟩]

private def request : RawCertificate := ⟨records.map encodeRecord, events⟩

#eval show IO Unit from do
  let some checked := verify fixture request
    | throw (IO.userError "reordering inside a complete improving proper-support program rejected")
  if checked.executed.program.execution.records.map (fun event => event.identity) !=
      [7, 10, 20, 30, 40, 45, 50] then
    throw (IO.userError "public verifier did not execute every structural and primitive action")
  if checked.result.implementation.gateCount != 2 ||
      checked.executed.program.result.implementation.gateCount != 1 ||
      checked.executed.program.execution.charged != 1 ||
      checked.executed.program.execution.removed != 2 ||
      !checked.executed.program.state.isClosed then
    throw (IO.userError "public verifier lost final strict saving, complete costs or final closure")
  if checked.records.map encodeRecord != request.records ||
      checked.ownership.charged != [.allocated 4 0 40 0] ||
      checked.ownership.live.length != 2 || checked.ownership.removed.length != 2 ||
      !checked.ownership.live.contains (.allocated 4 0 40 0) then
    throw (IO.userError "outer literal compiler did not preserve the reordered program ownership")
  for input in [false, true] do
    let valuation : Valuation 1 := fun _ => input
    if checked.result.implementation.candidate.semantics valuation 0 !=
        fixture.implementation.candidate.semantics valuation 0 ||
        checked.result.fieldValue valuation 0 != fixture.fieldValue valuation 0 then
      throw (IO.userError "accepted reordered certificate changed full output or field semantics")
  let realizedEvents := events.map fun event =>
    if event.identity = 40 then
      {event with action := .primitive (.realizeR7 7 [.gate 0, .boundary 0, .interface 0])}
    else event
  let some realized := verify fixture {request with events := realizedEvents}
    | throw (IO.userError "computed full restoration failed after nonidentity reordering")
  if realized.ownership.charged != [.allocated 4 0 40 0] ||
      realized.executed.program.execution.removed != 2 then
    throw (IO.userError "computed restoration changed actual ownership or historical removals")
  let reorderOnly : List RawEvent := [⟨1, [], .structural [(0, 1)]⟩]
  let some noSaving := WireOpenProperSupport.compile fixture records reorderOnly
    | throw (IO.userError "non-saving reordering rejection fixture did not actually execute")
  if noSaving.program.result.implementation.gateCount != 2 ||
      (verify fixture {request with events := reorderOnly}).isSome then
    throw (IO.userError "structural reordering alone was credited as a strict saving")
  let invalidAfterShrink := events.map fun event =>
    if event.identity = 30 then {event with action := .structural [(0, 1)]} else event
  let invalidSecondSwap := events.map fun event =>
    if event.identity = 10 then {event with action := .structural [(0, 1), (0, 2)]} else event
  let unclosed := events.filter fun event => event.identity != 40 &&
    event.identity != 45 && event.identity != 50
  for rejected in [invalidAfterShrink, invalidSecondSwap, unclosed,
      events ++ [⟨99, [50], .structural [(0, 1)]⟩]] do
    if (verify fixture {request with events := rejected}).isSome then
      throw (IO.userError "invalid structural coordinates, open obligations or failed tails accepted")
  let wholeRecords : List (TerminalPrimitiveRecord 1 3 2 0) :=
    [.gate 0, .gate 1, .gate 2]
  let some whole := WireOpenProperSupport.compile fixture wholeRecords events
    | throw (IO.userError "whole-support structural rejection fixture did not actually execute")
  if whole.program.result.implementation.gateCount >= 3 then
    throw (IO.userError "whole-support structural fixture was not a genuine improvement")
  if (verify fixture ⟨wholeRecords.map encodeRecord, events⟩).isSome then
    throw (IO.userError "structural actions turned whole support into a proper local certificate")
  IO.println "wire-structural-certificate-runtime-regressions: passed"

end PNP.Regression.StructuralCertificate
