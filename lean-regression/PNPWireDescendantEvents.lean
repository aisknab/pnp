import PNP.NANDWireDescendantEvents

namespace PNP.Regression.WireDescendantEvents

open PNP.DirectWire WireDescendantHistory

example {inputs outputs : Nat} {source : Implementation inputs outputs}
    {stages : List RawStage} (run : CompiledRun source stages) :
    (inputEventKeys 0 stages).Nodup :=
  run.inputEventKeys_nodup 0

example {inputs outputs : Nat} {source : Implementation inputs outputs}
    {stages : List RawStage} (run : CompiledRun source stages)
    (origin : DescendantOrigin source.gateCount) (member : origin ∈ run.ledger.charged) :
    ∃ stagePosition identity localGate,
      origin = .allocated stagePosition identity localGate ∧
        (stagePosition, identity) ∈ inputEventKeys 0 stages :=
  run.ledger_charged_origin origin member

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
  let stages := [growing, growing, normalized]
  if inputEventKeys 0 stages != [(0, 10), (0, 20), (1, 10), (1, 20), (2, 20)] then
    throw (IO.userError "raw event family lost input order or reused local IDs")
  if inputEventKeys 7 stages != [(7, 10), (7, 20), (8, 10), (8, 20), (9, 20)] then
    throw (IO.userError "event family failed to advance its internal position")
  let some complete := compile source stages
    | throw (IO.userError "accepted provenance program rejected")
  for origin in complete.ledger.charged do
    match origin with
    | .original _ => throw (IO.userError "initial gate incorrectly entered charged history")
    | .allocated stagePosition identity _ =>
        if !(inputEventKeys 0 stages).contains (stagePosition, identity) then
          throw (IO.userError "historical allocation has no actual raw event")
  let duplicate : RawStage := ⟨0, [], [⟨10, [], .normalize⟩, ⟨10, [], .normalize⟩]⟩
  if inputEventKeys 0 [duplicate] != [(0, 10), (0, 10)] then
    throw (IO.userError "input event family concealed duplicate raw identities")
  if (compile source [duplicate]).isSome then
    throw (IO.userError "duplicate raw event identities gained a successful provenance receipt")
  if !(inputEventKeys 0 []).isEmpty then
    throw (IO.userError "empty raw program invented owner keys")
  IO.println "M267 descendant-event-provenance-regressions-passed"

#print axioms inputEventKeys_nil
#print axioms inputEventKeys_cons
#print axioms inputEventKeys_bounds
#print axioms StageCompilation.rawEventIdentities_nodup
#print axioms CompiledRun.inputEventKeys_nodup
#print axioms CompiledRun.inputEventKeys_unique
#print axioms CompiledRun.carry_charged_origin
#print axioms CompiledRun.ledger_charged_origin
#print axioms CompiledRun.ledger_live_allocated_event

end PNP.Regression.WireDescendantEvents
