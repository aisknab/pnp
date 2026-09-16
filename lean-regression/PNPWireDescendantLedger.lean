import PNP.NANDWireDescendantLedger

namespace PNP.Regression.WireDescendantLedger

open PNP.DirectWire WireDescendantHistory

example {initialGates inputs outputs : Nat} {source : Implementation inputs outputs}
    {stage : RawStage} (ledger : PersistentOwnership initialGates source.gateCount)
    (position : Nat) (compiled : StageCompilation source stage)
    (checked : PersistentOwnership.WellFormed ledger position) :
    PersistentOwnership.WellFormed (ledger.advance position compiled) (position + 1) :=
  ledger.advance_wellFormed position compiled checked

private def program : Program 2 4 :=
  ((((.empty : Program 2 0).snoc ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .input 1⟩).snoc
    ⟨.gate 0, .input 1⟩).snoc ⟨.gate 1, .gate 2⟩

private def source : Implementation 2 2 :=
  (Candidate.ofDirectWireWord program
    ⟨fun output => if output.val = 0 then .gate 3 else .gate 2⟩).toImplementation

private def growing : RawStage :=
  ⟨0, [.gate 1], [⟨10, [], .createR5 0⟩, ⟨20, [], .restoreR8 10⟩]⟩

example : (PersistentOwnership.initial 0).live = [] := rfl

#eval show IO Unit from do
  let initial := PersistentOwnership.initial source.gateCount
  let some first := compileStage source growing
    | throw (IO.userError "first stage rejected in persistent-ledger regression")
  let afterFirst := initial.advance 0 first
  if afterFirst.live !=
      [.original ⟨0, by decide⟩, .original ⟨2, by decide⟩, .original ⟨1, by decide⟩,
       .allocated 0 20 0, .original ⟨3, by decide⟩] then
    throw (IO.userError "first global map lost the actual compiler position")
  if afterFirst.charged != [.allocated 0 20 0] || !afterFirst.removed.isEmpty then
    throw (IO.userError "first stage global accounting changed")
  let some second := compileStage first.result growing
    | throw (IO.userError "second expanding stage rejected")
  let afterSecond := afterFirst.advance 1 second
  if afterSecond.charged != [.allocated 0 20 0, .allocated 1 20 0] ||
      !afterSecond.removed.isEmpty || afterSecond.live.length != 6 then
    throw (IO.userError "reused local event ID merged distinct historical allocations")
  if !(afterSecond.live.contains (.allocated 0 20 0)) ||
      !(afterSecond.live.contains (.allocated 1 20 0)) then
    throw (IO.userError "surviving prior allocation was reclassified as an original gate")
  let normalized : RawStage :=
    ⟨0, (List.range second.result.gateCount).map RawRecord.gate, [⟨20, [], .normalize⟩]⟩
  let some third := compileStage second.result normalized
    | throw (IO.userError "whole-descendant normalization rejected")
  let afterThird := afterSecond.advance 2 third
  if afterThird.charged != [.allocated 0 20 0, .allocated 1 20 0] ||
      afterThird.removed.length != 2 || afterThird.live.length != 4 then
    throw (IO.userError "later removal erased historical charges or broke exact accounting")
  if !(afterThird.removed.contains (.allocated 0 20 0)) ||
      !(afterThird.removed.contains (.allocated 1 20 0)) then
    throw (IO.userError "later removal did not preserve the allocation's original stage")
  if afterThird.live.contains (.allocated 0 20 0) ||
      afterThird.live.contains (.allocated 1 20 0) then
    throw (IO.userError "removed allocation remained live")
  IO.println "M267 persistent-descendant-ledger-regressions-passed"

#print axioms createdBefore_mono
#print axioms PersistentOwnership.initial_wellFormed
#print axioms PersistentOwnership.accounted_before
#print axioms PersistentOwnership.origin_before
#print axioms PersistentOwnership.origin_injective
#print axioms PersistentOwnership.liftOrigin_original
#print axioms PersistentOwnership.liftOrigin_allocated
#print axioms PersistentOwnership.liftOrigin_injective
#print axioms PersistentOwnership.lift_originals
#print axioms PersistentOwnership.advance_live
#print axioms PersistentOwnership.advance_charged_length
#print axioms PersistentOwnership.advance_removed_length
#print axioms PersistentOwnership.advance_physicalOrigin_position
#print axioms PersistentOwnership.advance_charge_origin
#print axioms PersistentOwnership.advance_partition
#print axioms PersistentOwnership.advance_wellFormed

end PNP.Regression.WireDescendantLedger
