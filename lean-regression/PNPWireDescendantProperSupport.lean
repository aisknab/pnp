import PNP.NANDWireDescendantProperSupport

namespace PNP.Regression.WireDescendantProperSupport

open PNP.DirectWire WireDescendantHistory
open WireDescendantProperSupport

example {inputs outputs fields : Nat} {carrier : WireCarrier inputs outputs fields}
    {records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0)}
    {stages : List RawStage} (executed : SplicedRun carrier records stages)
    (smaller : executed.run.result.gateCount <
      (extractTerminalSupport carrier.exposed.candidate records).gateCount) :
    StrictEquivalentGain carrier.implementation executed.result.implementation ∧
      (∀ valuation field, executed.result.fieldValue valuation field =
        carrier.fieldValue valuation field) ∧
      executed.result.implementation.gateCount + executed.run.removedCount =
        carrier.implementation.gateCount + executed.run.chargedCount :=
  ⟨executed.strictGain smaller, executed.field, executed.charge_accounting⟩

private def usedProgram : Program 2 4 :=
  ((((.empty : Program 2 0).snoc ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .input 1⟩).snoc
    ⟨.gate 0, .input 1⟩).snoc ⟨.gate 1, .gate 2⟩

/-- The exterior field really depends on a selected producer. Input and constant
fields must also survive; neither is a separately supplied observer. -/
private def source : WireCarrier 2 2 3 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        ((usedProgram.snoc ⟨.input 0, .input 0⟩).snoc ⟨.gate 3, .input 1⟩)
        ⟨fun output => if output.val = 0 then .gate 3 else .gate 2⟩).toImplementation
    source := fun field =>
      if field.val = 0 then .gate ⟨5, by decide⟩ else if field.val = 1 then .input 0 else .constant false }

private def records : List (TerminalPrimitiveRecord 2 6 5 0) :=
  [.gate 0, .gate 1, .gate 2, .gate 3, .gate 4]

private def growing : RawStage :=
  ⟨0, [.gate 1], [⟨10, [], .createR5 0⟩, ⟨20, [], .restoreR8 10⟩]⟩

private def normalized : RawStage :=
  ⟨0, (List.range 7).map RawRecord.gate, [⟨20, [], .normalize⟩]⟩

#eval show IO Unit from do
  let some executed := WireDescendantProperSupport.compile source records
      [growing, growing, normalized]
    | throw (IO.userError "accepted local program failed its derived outer splice")
  if executed.run.result.gateCount != 4 || executed.result.implementation.gateCount != 5 ||
      executed.run.chargedCount != 2 || executed.run.removedCount != 3 then
    throw (IO.userError "outer splice lost one-copy exterior or actual historical costs")
  if (ArbitrarySupportSplice.exterior records).length != 1 then
    throw (IO.userError "proper-support fixture has no genuine exterior")
  for left in [false, true] do
    for right in [false, true] do
      let valuation : Valuation 2 := fun index => if index.val = 0 then left else right
      for output in List.finRange 2 do
        if executed.result.implementation.candidate.semantics valuation output !=
            source.implementation.candidate.semantics valuation output then
          throw (IO.userError "ordinary output changed after proper-support embedding")
      for field in List.finRange 3 do
        if executed.result.fieldValue valuation field != source.fieldValue valuation field then
          throw (IO.userError "actual computational field changed after embedding")
  let malformed : RawStage := ⟨0, [.gate 100], []⟩
  if (WireDescendantProperSupport.compile source records [growing, malformed]).isSome then
    throw (IO.userError "failed local tail returned an accepted ambient prefix")
  IO.println "descendant-proper-support-regressions-passed"

#print axioms proper_iff_exterior_positive
#print axioms SplicedRun.open_equivalent
#print axioms SplicedRun.output
#print axioms SplicedRun.field
#print axioms SplicedRun.gateCount
#print axioms SplicedRun.charge_accounting
#print axioms SplicedRun.gain_iff_local_gain
#print axioms SplicedRun.gain_iff_net_charges
#print axioms SplicedRun.strictGain
#print axioms SplicedRun.strictResidualDescent
#print axioms WireDescendantProperSupport.compile_complete
#print axioms WireDescendantProperSupport.compile_exists_iff
#print axioms WireDescendantProperSupport.compile_none_iff

end PNP.Regression.WireDescendantProperSupport
