import PNP.NANDWireOpenPrimitiveOwnership

namespace PNP.Regression.WireOpenPrimitiveOwnership

open PNP.DirectWire WireOpenProgram
open WireObligationHistory (State)

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    {before after : State source} {event : WireObligationHistory.RawEvent fields}
    (step : WireObligationHistory.Transition source before event after) :
    ((PrimitiveOwnership.labelled step).live ++ (PrimitiveOwnership.labelled step).removed).Nodup ∧
      ((PrimitiveOwnership.labelled step).live ++ (PrimitiveOwnership.labelled step).removed).Perm
        (WireDescendantHistory.originalOrigins before.current.implementation.gateCount ++
          (PrimitiveOwnership.labelled step).charged) :=
  ⟨(PrimitiveOwnership.labelled_physical_ownership step).2.2.2.1,
    (PrimitiveOwnership.labelled_physical_ownership step).2.2.2.2⟩

private def source : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .input 0⟩)
        ⟨fun _ => .constant false⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def aliasSource : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .input 0⟩)
        ⟨fun _ => .gate 0⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

#eval show IO Unit from do
  let some created := WireObligationHistory.applyEvent (State.initial source) ⟨7, [], .createR5 0⟩
    | throw (IO.userError "primitive ownership creation fixture rejected")
  let creationLedger := PrimitiveOwnership.labelled created.2
  if creationLedger.live.length != 2 || !creationLedger.charged.isEmpty ||
      !creationLedger.removed.isEmpty then
    throw (IO.userError "R5 creation fabricated a physical allocation or removal")
  let some normalized := WireObligationHistory.applyEvent created.1 ⟨8, [], .normalize⟩
    | throw (IO.userError "primitive ownership normalization fixture rejected")
  let removalLedger := PrimitiveOwnership.labelled normalized.2
  if removalLedger.live.length != 0 || removalLedger.removed.length != 2 ||
      !removalLedger.charged.isEmpty then
    throw (IO.userError "normalization did not retain both actual removed physical positions")
  let originals := removalLedger.removed.map fun origin =>
    match origin with
    | .original gate => some gate.val
    | .allocated _ _ _ => none
  if !originals.contains (some 0) || !originals.contains (some 1) then
    throw (IO.userError "normalization gave an original position a new allocation identity")
  let some restored := WireObligationHistory.applyEvent normalized.1 ⟨9, [], .restoreR8 7⟩
    | throw (IO.userError "primitive ownership restoration fixture rejected")
  let restorationLedger := PrimitiveOwnership.labelled restored.2
  if restorationLedger.live != [.allocated 0 9 0] ||
      restorationLedger.charged != [.allocated 0 9 0] ||
      !restorationLedger.removed.isEmpty then
    throw (IO.userError "restoration must name the executing event and its literal appended gate")
  if normalized.1.current.implementation.gateCount != 0 ||
      source.implementation.gateCount != 2 || restored.1.current.implementation.gateCount != 1 then
    throw (IO.userError "fixture did not distinguish current physical coordinates from the semantic source")
  let some read := WireObligationHistory.applyEvent restored.1 ⟨10, [], .readFull 0⟩
    | throw (IO.userError "closed full-mode read fixture rejected")
  let readLedger := PrimitiveOwnership.labelled read.2
  if readLedger.live.length != 1 || !readLedger.charged.isEmpty || !readLedger.removed.isEmpty then
    throw (IO.userError "full read changed physical component ownership")
  let some aliasCreated := WireObligationHistory.applyEvent (State.initial aliasSource)
      ⟨11, [], .createR5 0⟩
    | throw (IO.userError "representative creation fixture rejected")
  let some cancelled := WireObligationHistory.applyEvent aliasCreated.1 ⟨12, [], .cancelR6 11⟩
    | throw (IO.userError "actual representative cancellation fixture rejected")
  let cancelLedger := PrimitiveOwnership.labelled cancelled.2
  if cancelLedger.live.length != 2 || !cancelLedger.charged.isEmpty || !cancelLedger.removed.isEmpty then
    throw (IO.userError "representative cancellation fabricated materializer cost")
  IO.println "open-primitive-ownership-regressions-passed"

#print axioms PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.allocations_nodup
#print axioms PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.advance_charged
#print axioms PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.advance_removed_length
#print axioms PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.advance_conservation
#print axioms PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.ledger_charged
#print axioms PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.ledger_removed_length
#print axioms PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.ledger_partition
#print axioms PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.physical_ownership
#print axioms PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.lift_injective
#print axioms PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.labelled_live
#print axioms PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.labelled_physical_ownership
#print axioms PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.labelled_charged_origin

end PNP.Regression.WireOpenPrimitiveOwnership
