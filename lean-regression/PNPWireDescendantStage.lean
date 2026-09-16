import PNP.NANDWireDescendantStage

namespace PNP.Regression.WireDescendantStage

open PNP.DirectWire WireDescendantHistory WireHistoryAmbientOwnership

example {inputs outputs : Nat} {source : Implementation inputs outputs} {stage : RawStage}
    (compiled : StageCompilation source stage) :
    compiled.records.map encodeRecord = stage.records ∧
      compiled.events.map encodeEvent = stage.events :=
  ⟨compiled.records_source, compiled.events_source⟩

example {inputs outputs : Nat} {source : Implementation inputs outputs} {stage : RawStage}
    (compiled : StageCompilation source stage) :
    compiled.ledger.live.length = compiled.result.gateCount ∧
      compiled.ledger.charged.length = compiled.chargedCount ∧
      compiled.ledger.removed.length = compiled.removedCount ∧
      (compiled.ledger.live ++ compiled.ledger.removed).Nodup ∧
      (compiled.ledger.live ++ compiled.ledger.removed).Perm
        (ambientOriginals source.gateCount ++ compiled.ledger.charged) :=
  compiled.physical_ownership

private def program : Program 2 4 :=
  ((((.empty : Program 2 0).snoc ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .input 1⟩).snoc
    ⟨.gate 0, .input 1⟩).snoc ⟨.gate 1, .gate 2⟩

private def source : Implementation 2 2 :=
  (Candidate.ofDirectWireWord program
    ⟨fun output => if output.val = 0 then .gate 3 else .gate 2⟩).toImplementation

private def restored : RawStage :=
  ⟨0, [.gate 1],
    [⟨10, [], .createR5 0⟩, ⟨20, [10], .normalize⟩, ⟨30, [20], .restoreR8 10⟩]⟩

private def growing : RawStage :=
  ⟨0, [.gate 1], [⟨10, [], .createR5 0⟩, ⟨20, [], .restoreR8 10⟩]⟩

private def emptySource : Implementation 0 0 :=
  (Candidate.ofDirectWireWord (.empty : Program 0 0) ⟨Fin.elim0⟩).toImplementation

#eval show IO Unit from do
  let some compiled := compileStage source restored
    | throw (IO.userError "valid raw stage rejected")
  if compiled.ledger.live !=
      [.original ⟨0, by decide⟩, .original ⟨2, by decide⟩, .allocated 30 0,
       .original ⟨3, by decide⟩] ||
      compiled.ledger.charged != [.allocated 30 0] ||
      compiled.ledger.removed != [.original ⟨1, by decide⟩] then
    throw (IO.userError "raw stage changed the literal compiler provenance")
  if compiled.chargedCount != 1 || compiled.removedCount != 1 then
    throw (IO.userError "stage counts differ from actual execution")
  if compiled.records.map encodeRecord != restored.records ||
      compiled.events.map encodeEvent != restored.events then
    throw (IO.userError "accepted raw stage coordinates or events were changed")
  let some expanded := compileStage source growing
    | throw (IO.userError "temporarily expanding stage was rejected")
  if expanded.result.gateCount != 5 || expanded.chargedCount != 1 ||
      expanded.removedCount != 0 then
    throw (IO.userError "expanding stage was replaced by a decreasing-only route")
  for invalid in
      [RawStage.mk 0 [.gate 4] [], RawStage.mk 0 [.boundary 2] [],
       RawStage.mk 0 [.interface 2] [], RawStage.mk 0 [.profile 0] [],
       RawStage.mk 0 [.gate 1] [⟨1, [], .createR5 1⟩],
       RawStage.mk 0 [.gate 1] [⟨1, [], .createR5 0⟩],
       RawStage.mk 0 [.gate 1] [⟨1, [], .normalize⟩, ⟨1, [], .normalize⟩],
       RawStage.mk 0 [.gate 1] [⟨1, [99], .normalize⟩],
       RawStage.mk 0 [.gate 1] [⟨1, [], .restoreR8 99⟩]] do
    if (compileStage source invalid).isSome then
      throw (IO.userError "malformed or unfinished raw stage accepted")
  let emptyStage : RawStage := ⟨0, [], [⟨1, [], .normalize⟩]⟩
  let some empty := compileStage emptySource emptyStage
    | throw (IO.userError "empty circuit stage rejected")
  if empty.result.gateCount != 0 || !empty.ledger.live.isEmpty ||
      !empty.ledger.charged.isEmpty || !empty.ledger.removed.isEmpty then
    throw (IO.userError "empty stage fabricated a physical gate")
  let repeated : RawStage := ⟨2, [.gate 1, .gate 1, .profile 1], []⟩
  let some repeatedResult := compileStage source repeated
    | throw (IO.userError "valid repeated records or profile coordinate rejected")
  if repeatedResult.records.map encodeRecord != repeated.records then
    throw (IO.userError "raw record order or multiplicity changed")
  IO.println "M267 raw-descendant-stage-regressions-passed"

#print axioms StageCompilation.records_source
#print axioms StageCompilation.events_source
#print axioms StageCompilation.existing_result
#print axioms StageCompilation.semantics
#print axioms StageCompilation.physicalOrigin_position
#print axioms StageCompilation.physical_ownership
#print axioms StageCompilation.gate_balance
#print axioms StageCompilation.charged_origin
#print axioms StageCompilation.event_identity_unique
#print axioms compileStage_records_none
#print axioms compileStage_events_none
#print axioms compileStage_history_none

end PNP.Regression.WireDescendantStage
