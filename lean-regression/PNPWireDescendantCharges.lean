import PNP.NANDWireDescendantCharges

namespace PNP.Regression.WireDescendantCharges

open PNP.DirectWire WireDescendantHistory

example {inputs outputs : Nat} {source : Implementation inputs outputs}
    {stages : List RawStage} (run : CompiledRun source stages)
    (left right : Fin (inputEventKeys 0 stages).length) (different : left ≠ right)
    (gate : Fin run.result.gateCount) (inLeft : gate ∈ run.eventRequests left) :
    gate ∉ run.eventRequests right :=
  run.eventRequests_disjoint left right different gate inLeft

example {inputs outputs width : Nat} {source : Implementation inputs outputs}
    {stages : List RawStage} (run : CompiledRun source stages)
    (support : List (TerminalPrimitiveRecord inputs run.result.gateCount outputs width)) :
    ((terminalPhysicalOwners (inputEventKeys 0 stages).length).map (fun owner =>
      (run.materializer support owner).gateCount)).sum =
        (extractTerminalSupport run.result.candidate support).gateCount :=
  run.materializer_chargeIdentity support

private def program : Program 2 4 :=
  ((((.empty : Program 2 0).snoc ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .input 1⟩).snoc
    ⟨.gate 0, .input 1⟩).snoc ⟨.gate 1, .gate 2⟩

private def source : Implementation 2 2 :=
  (Candidate.ofDirectWireWord program
    ⟨fun output => if output.val = 0 then .gate 3 else .gate 2⟩).toImplementation

private def growing : RawStage :=
  ⟨0, [.gate 1], [⟨10, [], .createR5 0⟩, ⟨20, [], .restoreR8 10⟩]⟩

private def normalized : RawStage :=
  ⟨0, (List.range 6).map RawRecord.gate, [⟨20, [], .normalize⟩]⟩

#eval show IO Unit from do
  let some twoStages := compile source [growing, growing]
    | throw (IO.userError "owner-family program rejected")
  let requests := (allFin (inputEventKeys 0 [growing, growing]).length).map fun owner =>
    (twoStages.eventRequests owner).map Fin.val
  if requests != [[], [2], [], [4]] then
    throw (IO.userError "derived raw event requests lost persistent physical allocation positions")
  let assignments := (allFin twoStages.result.gateCount).map fun gate =>
    (terminalPhysicalOwner twoStages.eventRequests gate).map Fin.val
  if assignments != [none, none, some 1, none, some 3, none] then
    throw (IO.userError "surviving original gates and stage-qualified allocations were conflated")
  let some support := decodeRecords 2 twoStages.result.gateCount 2 0
      [.gate 4, .gate 2, .gate 2, .boundary 0, .interface 0]
    | throw (IO.userError "selected ownership support rejected")
  let selectedCharges := (terminalPhysicalOwners (inputEventKeys 0 [growing, growing]).length).map
    fun owner => (twoStages.materializer support owner).gateCount
  if selectedCharges != [0, 0, 1, 0, 1] then
    throw (IO.userError "support metadata or duplicate records created an extra piece charge")
  let wholeSupport := (allFin twoStages.result.gateCount).map
    (TerminalPrimitiveRecord.gate (inputs := 2) (outputs := 2) (profileWidth := 0))
  let wholeCharges := (terminalPhysicalOwners (inputEventKeys 0 [growing, growing]).length).map
    fun owner => (twoStages.materializer wholeSupport owner).gateCount
  if wholeCharges != [4, 0, 1, 0, 1] then
    throw (IO.userError "whole-result extraction did not preserve the fixed remainder")
  let stages := [growing, growing, normalized]
  let some complete := compile source stages
    | throw (IO.userError "removed-allocation owner program rejected")
  if !(allFin (inputEventKeys 0 stages).length).all
      (fun owner => (complete.eventRequests owner).isEmpty) ||
      complete.ledger.charged.length != 2 then
    throw (IO.userError "surviving owner pieces were confused with historical charges")
  IO.println "M267 descendant-owned-piece-regressions-passed"

#print axioms CompiledRun.eventRequests_member
#print axioms CompiledRun.eventRequests_disjoint
#print axioms CompiledRun.eventOwner_some_iff
#print axioms CompiledRun.eventOwner_none_iff
#print axioms CompiledRun.support_membership
#print axioms CompiledRun.support_restrict
#print axioms CompiledRun.materializer_gateCount
#print axioms CompiledRun.materializer_chargeIdentity
#print axioms CompiledRun.materializer_wholeCharge
#print axioms CompiledRun.materializer_semantics
#print axioms CompiledRun.materializer_induced

end PNP.Regression.WireDescendantCharges
