import PNP.NANDWireDescendantOwnership

namespace PNP.Regression.WireDescendantOwnership

open PNP.DirectWire WireDescendantHistory

example {inputs outputs : Nat} {source : Implementation inputs outputs}
    {stages : List RawStage} (run : CompiledRun source stages) :
    run.ledger.live.length = run.result.gateCount ∧
      run.ledger.charged.length = run.chargedCount ∧
      run.ledger.removed.length = run.removedCount ∧
      (run.ledger.live ++ run.ledger.removed).Nodup ∧
      (run.ledger.live ++ run.ledger.removed).Perm
        (originalOrigins source.gateCount ++ run.ledger.charged) :=
  run.physical_ownership

example {inputs outputs : Nat} {source : Implementation inputs outputs}
    {stages : List RawStage} (run : CompiledRun source stages) :
    Function.Injective run.ledger.origin :=
  run.ledger_origin_injective

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
  -- Stage two selects physical position one of the first descendant, not
  -- initial-source gate one. Its local permutation [0, 2, 3, 1, new, 4]
  -- composes with the first stage's [0, 2, 1, new, 3] map.
  let some twoStages := compile source [growing, growing]
    | throw (IO.userError "two-stage ownership prefix rejected")
  if twoStages.ledger.live !=
      [.original ⟨0, by decide⟩, .original ⟨1, by decide⟩, .allocated 0 20 0,
       .original ⟨2, by decide⟩, .allocated 1 20 0, .original ⟨3, by decide⟩] then
    throw (IO.userError "whole fold failed to compose the intermediate physical positions")
  let some complete := compile source [growing, growing, normalized]
    | throw (IO.userError "complete raw ownership program rejected")
  let accounting := complete.ledger
  -- Normalization keeps current physical positions [0, 1, 3, 5].
  if accounting.live !=
      [.original ⟨0, by decide⟩, .original ⟨1, by decide⟩,
       .original ⟨2, by decide⟩, .original ⟨3, by decide⟩] then
    throw (IO.userError "complete fold reset the initial-source coordinates or physical order")
  if accounting.charged != [.allocated 0 20 0, .allocated 1 20 0] ||
      accounting.removed.length != 2 || complete.chargedCount != 2 ||
      complete.removedCount != 2 then
    throw (IO.userError "complete ownership fold lost the actual historical execution totals")
  if !(accounting.removed.contains (.allocated 0 20 0)) ||
      !(accounting.removed.contains (.allocated 1 20 0)) then
    throw (IO.userError "complete fold relabelled a removed allocation")
  let some empty := compile source []
    | throw (IO.userError "empty ownership program rejected")
  if empty.ledger.live !=
      [.original ⟨0, by decide⟩, .original ⟨1, by decide⟩,
       .original ⟨2, by decide⟩, .original ⟨3, by decide⟩] ||
      !empty.ledger.charged.isEmpty || !empty.ledger.removed.isEmpty then
    throw (IO.userError "empty fold changed the initial physical ownership")
  IO.println "M267 arbitrary-descendant-ownership-regressions-passed"

#print axioms CompiledRun.carry_nil
#print axioms CompiledRun.carry_cons
#print axioms CompiledRun.carry_wellFormed
#print axioms CompiledRun.carry_charged_length
#print axioms CompiledRun.carry_removed_length
#print axioms CompiledRun.carry_charge_survives
#print axioms CompiledRun.ledger_nil
#print axioms CompiledRun.ledger_wellFormed
#print axioms CompiledRun.physical_ownership
#print axioms CompiledRun.ledger_origin_injective
#print axioms CompiledRun.ledger_charged_before

end PNP.Regression.WireDescendantOwnership
