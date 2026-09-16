import PNP.NANDWireDescendantCertificate

namespace PNP.Regression.WireDescendantCertificate

open PNP.DirectWire WireDescendantHistory WireDescendantProperSupport
open WireDescendantCertificate

example {inputs outputs fields : Nat} {carrier : WireCarrier inputs outputs fields}
    {raw : RawCertificate} (checked : CheckedCertificate carrier raw) :
    StrictEquivalentGain carrier.implementation checked.result.implementation ∧
      residualSlack checked.result.implementation < residualSlack carrier.implementation :=
  ⟨checked.strictGain, checked.strictResidualDescent⟩

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (raw : RawCertificate)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (recordsAt : decodeRecords inputs carrier.implementation.gateCount
      (outputs + fields) 0 raw.records = some records)
    (run : CompiledRun (localSource carrier records) raw.stages)
    (runAt : WireDescendantHistory.compile (localSource carrier records) raw.stages = some run)
    (proper : 0 < (ArbitrarySupportSplice.exterior records).length)
    (smaller : run.result.gateCount <
      (extractTerminalSupport carrier.exposed.candidate records).gateCount) :
    ∃ checked, verify carrier raw = some checked :=
  verify_complete carrier raw records recordsAt run runAt proper smaller

private def usedProgram : Program 2 4 :=
  ((((.empty : Program 2 0).snoc ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .input 1⟩).snoc
    ⟨.gate 0, .input 1⟩).snoc ⟨.gate 1, .gate 2⟩

private def source : WireCarrier 2 2 3 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        ((usedProgram.snoc ⟨.input 0, .input 0⟩).snoc ⟨.gate 3, .input 1⟩)
        ⟨fun output => if output.val = 0 then .gate 3 else .gate 2⟩).toImplementation
    source := fun field =>
      if field.val = 0 then .gate ⟨5, by decide⟩
      else if field.val = 1 then .input 0 else .constant false }

private def growing : RawStage :=
  ⟨0, [.gate 1], [⟨10, [], .createR5 0⟩, ⟨20, [], .restoreR8 10⟩]⟩

private def normalized (gates : Nat) : RawStage :=
  ⟨0, (List.range gates).map RawRecord.gate, [⟨20, [], .normalize⟩]⟩

private def request : RawCertificate :=
  ⟨(List.range 5).map RawRecord.gate, [growing, growing, normalized 7]⟩

private def emptySource : WireCarrier 0 0 0 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 0 0) ⟨Fin.elim0⟩).toImplementation
    source := Fin.elim0 }

#eval show IO Unit from do
  let some checked := verify source request
    | throw (IO.userError "complete improving proper-support certificate rejected")
  if checked.result.implementation.gateCount != 5 ||
      checked.executed.run.result.gateCount != 4 ||
      checked.executed.run.chargedCount != 2 || checked.executed.run.removedCount != 3 then
    throw (IO.userError "certificate lost physical savings or temporary execution costs")
  if checked.records.map encodeRecord != request.records then
    throw (IO.userError "certificate did not preserve the complete offered record list")
  for left in [false, true] do
    for right in [false, true] do
      let valuation : Valuation 2 := fun index => if index.val = 0 then left else right
      for output in List.finRange 2 do
        if checked.result.implementation.candidate.semantics valuation output !=
            source.implementation.candidate.semantics valuation output then
          throw (IO.userError "accepted certificate changed an ordinary output")
      for field in List.finRange 3 do
        if checked.result.fieldValue valuation field != source.fieldValue valuation field then
          throw (IO.userError "accepted certificate changed a computational field")
  for invalid in [RawRecord.gate 6, .boundary 2, .interface 5, .profile 0] do
    if (verify source {request with records := request.records ++ [invalid]}).isSome then
      throw (IO.userError "out-of-range outer coordinate accepted")
  let malformed : RawStage := ⟨0, [.gate 100], []⟩
  if (verify source {request with stages := request.stages ++ [malformed]}).isSome then
    throw (IO.userError "failed final stage returned a successful prefix certificate")
  for stages in [[], [growing], [growing, growing]] do
    if (verify source {request with stages := stages}).isSome then
      throw (IO.userError "non-improving complete program accepted as a strict gain")
  let wholeRecords : List (TerminalPrimitiveRecord 2 6 5 0) :=
    [.gate 0, .gate 1, .gate 2, .gate 3, .gate 4, .gate 5]
  let wholeStages := [growing, growing, normalized 8]
  let some wholeRun := WireDescendantProperSupport.compile source wholeRecords wholeStages
    | throw (IO.userError "whole-support rejection fixture did not execute")
  if wholeRun.run.result.gateCount >= 6 then
    throw (IO.userError "whole-support fixture was not a genuine strict improvement")
  if (verify source ⟨wholeRecords.map encodeRecord, wholeStages⟩).isSome then
    throw (IO.userError "whole support was mislabeled as a proper local certificate")
  let duplicate := {request with records := request.records ++ [.gate 4]}
  let some repeated := verify source duplicate
    | throw (IO.userError "valid repeated record changed support acceptance")
  if repeated.records.map encodeRecord != duplicate.records ||
      repeated.result.implementation.gateCount != checked.result.implementation.gateCount then
    throw (IO.userError "duplicate record was dropped or double-counted as a physical gate")
  if (verify emptySource ⟨[], []⟩).isSome ||
      (verify source ⟨[], []⟩).isSome then
    throw (IO.userError "empty support or zero-dimensional source produced a false gain")
  IO.println "descendant-source-only-certificate-regressions-passed"

#print axioms CheckedCertificate.records_source
#print axioms CheckedCertificate.proper_support
#print axioms CheckedCertificate.output
#print axioms CheckedCertificate.field
#print axioms CheckedCertificate.gateCount
#print axioms CheckedCertificate.charge_accounting
#print axioms CheckedCertificate.strictGain
#print axioms CheckedCertificate.strictResidualDescent
#print axioms verify_complete
#print axioms verify_exists_iff
#print axioms verify_sound
#print axioms verify_decode_none
#print axioms verify_run_none
#print axioms verify_not_proper
#print axioms verify_no_gain

end PNP.Regression.WireDescendantCertificate
