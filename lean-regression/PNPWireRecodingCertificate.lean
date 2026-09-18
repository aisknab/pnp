import PNP.NANDWireOpenCertificate

namespace PNP.Regression.RecodingCertificate

open PNP.DirectWire WireOpenProgram WireOpenCertificate
open WireDescendantHistory (encodeRecord)
open Concrete.LockedNAND (RawCandidate)

example {inputs outputs fields : Nat} {carrier : WireCarrier inputs outputs fields}
    {raw : RawCertificate} (checked : CheckedCertificate carrier raw) :
    StrictEquivalentGain carrier.implementation checked.result.implementation ∧
      residualSlack checked.result.implementation < residualSlack carrier.implementation ∧
      checked.executed.program.execution.CreationsClosed :=
  ⟨checked.strictGain, checked.strictResidualDescent, checked.creation_lifecycle⟩

example {inputs outputs fields : Nat} {carrier : WireCarrier inputs outputs fields}
    {raw : RawCertificate} (checked : CheckedCertificate carrier raw) :
    checked.result.implementation.gateCount + checked.executed.program.execution.removed =
      carrier.implementation.gateCount + checked.executed.program.execution.charged :=
  checked.charge_accounting

#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictGain
#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictResidualDescent
#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.physical_ownership
#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.creation_lifecycle
#print axioms PNP.DirectWire.WireOpenCertificate.CheckedCertificate.charge_accounting
#print axioms PNP.DirectWire.WireOpenCertificate.verify_program_none
#print axioms PNP.DirectWire.WireOpenCertificate.verify_not_proper
#print axioms PNP.DirectWire.WireOpenCertificate.verify_no_gain

private def identity (width : Nat) : Implementation width width :=
  (Candidate.ofDirectWireWord (.empty : Program width 0)
    ⟨fun field => .input field⟩).toImplementation

private def negation : Implementation 1 1 :=
  (Candidate.ofDirectWireWord
    ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩)
    (⟨fun _ => .gate 0⟩ : DirectWireWord 1 1 1)).toImplementation

private def rawNegation : RawCandidate := RawCandidate.ofCandidate negation.candidate

private def fixture : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        ((((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩).snoc
          ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .input 0⟩)
        ⟨fun _ => .constant false⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def records : List (TerminalPrimitiveRecord 1 3 2 0) := [.gate 0, .gate 1]

private def events : List RawEvent :=
  [⟨40, [35], .primitive (.readFull 0)⟩,
   ⟨20, [10], .recoding rawNegation rawNegation⟩,
   ⟨35, [30], .structural [(0, 0)]⟩,
   ⟨10, [], .primitive (.createR5 0)⟩,
   ⟨30, [20], .primitive (.restoreR8 10)⟩]

private def request : RawCertificate := ⟨records.map encodeRecord, events⟩

#eval show IO Unit from do
  let some checked := verify fixture request
    | throw (IO.userError "recoding within a complete improving proper-support program rejected")
  if checked.executed.program.execution.records.map (fun event => event.identity) !=
      [10, 20, 30, 35, 40] then
    throw (IO.userError "public verifier did not execute the complete mixed conversion program")
  if checked.result.implementation.gateCount != 2 ||
      checked.executed.program.result.implementation.gateCount != 1 ||
      checked.executed.program.execution.charged != 3 ||
      checked.executed.program.execution.removed != 4 ||
      !checked.executed.program.state.isClosed then
    throw (IO.userError "public verifier lost strict saving, literal costs or final closure")
  let expectedCharges := [.allocated 1 0 0 0, .allocated 1 0 1 0, .allocated 2 0 30 0]
  if checked.records.map encodeRecord != request.records ||
      checked.ownership.charged != expectedCharges ||
      checked.ownership.live.length != 2 || checked.ownership.removed.length != 4 ||
      !checked.ownership.live.contains (.allocated 2 0 30 0) ||
      !checked.ownership.removed.contains (.allocated 1 0 0 0) ||
      !checked.ownership.removed.contains (.allocated 1 0 1 0) then
    throw (IO.userError "outer compilation reset conversion phases, removals or restoration identity")
  for input in [false, true] do
    let valuation : Valuation 1 := fun _ => input
    if checked.result.implementation.candidate.semantics valuation 0 !=
        fixture.implementation.candidate.semantics valuation 0 ||
        checked.result.fieldValue valuation 0 != fixture.fieldValue valuation 0 then
      throw (IO.userError "accepted conversion certificate changed full output or field semantics")
  let realizedEvents := events.map fun event =>
    if event.identity = 30 then
      {event with action := .primitive (.realizeR7 10 [.gate 0, .boundary 0, .interface 0])}
    else event
  let some realized := verify fixture {request with events := realizedEvents}
    | throw (IO.userError "computed restoration of the original full value failed after conversion")
  if realized.ownership.charged != expectedCharges ||
      realized.executed.program.execution.removed != 4 then
    throw (IO.userError "computed restoration changed literal conversion charges or removals")
  let minimalRecords : List (TerminalPrimitiveRecord 1 3 2 0) := [.gate 0]
  let conversionOnly : List RawEvent := [⟨1, [], .recoding rawNegation rawNegation⟩]
  let some noSaving := WireOpenProperSupport.compile fixture minimalRecords conversionOnly
    | throw (IO.userError "non-saving conversion fixture did not actually execute")
  -- The literal chain has three distinct live NAND gates. Constant propagation,
  -- sharing and pruning do not promise inverse-cancellation, so both recoder
  -- allocations must remain charged even though the full Boolean value is equal.
  if noSaving.program.result.implementation.gateCount != 3 ||
      noSaving.program.execution.charged != 2 ||
      noSaving.program.execution.removed != 0 ||
      (verify fixture ⟨minimalRecords.map encodeRecord, conversionOnly⟩).isSome then
    throw (IO.userError "conversion without a real final saving was credited as an improvement")
  let wrongWidth := RawCandidate.ofCandidate (identity 2).candidate
  let identityOne := RawCandidate.ofCandidate (identity 1).candidate
  let badLastGate : RawCandidate :=
    ⟨1, [⟨.input 0, .input 0⟩, ⟨.gate 2, .input 0⟩], [.gate 0]⟩
  let unclosed := events.filter fun event => event.identity = 10 || event.identity = 20
  for rejected in [unclosed,
      events ++ [⟨99, [40], .recoding wrongWidth rawNegation⟩],
      events ++ [⟨99, [40], .recoding rawNegation badLastGate⟩],
      events ++ [⟨99, [40], .recoding rawNegation identityOne⟩],
      events ++ [⟨99, [40], .structural [(0, 1)]⟩]] do
    if (verify fixture {request with events := rejected}).isSome then
      throw (IO.userError "open obligation, invalid later conversion or failed mixed tail accepted")
  let wholeRecords : List (TerminalPrimitiveRecord 1 3 2 0) :=
    [.gate 0, .gate 1, .gate 2]
  let some whole := WireOpenProperSupport.compile fixture wholeRecords events
    | throw (IO.userError "whole-support conversion rejection fixture did not actually execute")
  if whole.program.result.implementation.gateCount >= 3 then
    throw (IO.userError "whole-support conversion fixture was not a genuine improvement")
  if (verify fixture ⟨wholeRecords.map encodeRecord, events⟩).isSome then
    throw (IO.userError "conversion turned a whole-support improvement into a proper local certificate")
  IO.println "wire-recoding-certificate-runtime-regressions: passed"

end PNP.Regression.RecodingCertificate
