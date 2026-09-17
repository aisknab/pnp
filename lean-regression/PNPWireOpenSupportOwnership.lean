import PNP.NANDWireOpenSupportOwnership

namespace PNP.Regression.WireOpenSupportOwnership

open PNP.DirectWire WireOpenSupportSplice
open WireDescendantHistory (DescendantOrigin originalOrigins)

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    {before : WireObligationHistory.State source}
    {raw : WireDescendantCertificate.RawCertificate} (receipt : Receipt before raw) :
    (receipt.ownership.live ++ receipt.ownership.removed).Nodup ∧
      (receipt.ownership.live ++ receipt.ownership.removed).Perm
        (originalOrigins before.current.implementation.gateCount ++ receipt.ownership.charged) :=
  ⟨receipt.physical_ownership.2.2.2.1, receipt.physical_ownership.2.2.2.2⟩

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    (before : WireObligationHistory.State source)
    (records : List (TerminalPrimitiveRecord inputs
      before.current.implementation.gateCount (outputs + fields) 0))
    {stages : List WireDescendantHistory.RawStage}
    (executed : WireDescendantProperSupport.SplicedRun before.current records stages)
    (node : Fin ((ArbitrarySupportSplice.exterior records).length + executed.run.result.gateCount)) :
    (ownership before records executed).origin (executed.compiled.position node) =
      ownershipRawNode before records executed node :=
  ownership_compiled_position before records executed node

private def source : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .input 0⟩)
        ⟨fun _ => .constant false⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def emptySource : WireCarrier 0 0 0 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 0 0) ⟨Fin.elim0⟩).toImplementation
    source := Fin.elim0 }

private def normalizeRequest : WireDescendantCertificate.RawCertificate :=
  ⟨[.gate 0, .gate 1], [⟨0, [.gate 0, .gate 1], [⟨7, [], .normalize⟩]⟩]⟩

/-- The first real restoration is subsequently removed; its charge must remain. -/
private def historicalRequest : WireDescendantCertificate.RawCertificate :=
  ⟨[.gate 0, .gate 1], [⟨0, [.gate 0, .gate 1],
    [⟨7, [], .createR5 0⟩, ⟨20, [7], .normalize⟩, ⟨30, [20], .restoreR8 7⟩,
     ⟨40, [30], .createR5 0⟩, ⟨50, [40], .normalize⟩, ⟨60, [50], .restoreR8 40⟩]⟩]⟩

#eval show IO Unit from do
  let some created := WireObligationHistory.applyEvent
      (WireObligationHistory.State.initial source) ⟨7, [], .createR5 0⟩
    | throw (IO.userError "ownership fixture could not create the actual ambient obligation")
  let some openReceipt := execute created.1 normalizeRequest
    | throw (IO.userError "ownership rejected a valid support splice with an open ambient obligation")
  let openLedger := openReceipt.ownership
  if openLedger.live.length != 0 || openLedger.charged.length != 0 || openLedger.removed.length != 2 then
    throw (IO.userError "open-state splice did not conserve the removed original gates")
  let removedOriginals := openLedger.removed.map fun origin =>
    match origin with
    | .original gate => some gate.val
    | .allocated _ _ _ => none
  if !removedOriginals.contains (some 0) || !removedOriginals.contains (some 1) then
    throw (IO.userError "actual extracted original positions were lost or relabeled")
  let some historical := execute (WireObligationHistory.State.initial source) historicalRequest
    | throw (IO.userError "complete nested history with two real restorations rejected")
  let ledger := historical.ownership
  if historical.next.current.implementation.gateCount != 1 ||
      historical.executed.run.chargedCount != 2 || historical.executed.run.removedCount != 3 then
    throw (IO.userError "historical ownership fixture did not perform its two actual allocations")
  if ledger.live != [.allocated 0 60 0] ||
      ledger.charged != [.allocated 0 30 0, .allocated 0 60 0] ||
      ledger.removed.length != 3 || !ledger.removed.contains (.allocated 0 30 0) ||
      ledger.removed.contains (.allocated 0 60 0) then
    throw (IO.userError "a deleted allocation lost its charge or the literal live position has the wrong owner")
  for bit in [false, true] do
    let valuation : Valuation 1 := fun _ => bit
    if historical.next.current.fieldValue valuation 0 != source.fieldValue valuation 0 then
      throw (IO.userError "historical allocation accounting changed the full field value")
  let some empty := execute (WireObligationHistory.State.initial emptySource) ⟨[], []⟩
    | throw (IO.userError "empty ownership splice rejected")
  if !empty.ownership.live.isEmpty || !empty.ownership.charged.isEmpty || !empty.ownership.removed.isEmpty then
    throw (IO.userError "zero-dimensional ownership fabricated a gate")
  IO.println "open-support-ownership-regressions-passed"

#print axioms PNP.DirectWire.WireOpenSupportSplice.ownershipLift_original
#print axioms PNP.DirectWire.WireOpenSupportSplice.ownershipLift_allocated
#print axioms PNP.DirectWire.WireOpenSupportSplice.ownershipLift_injective
#print axioms PNP.DirectWire.WireOpenSupportSplice.ownershipRawNode_exterior
#print axioms PNP.DirectWire.WireOpenSupportSplice.ownershipRawNode_nested
#print axioms PNP.DirectWire.WireOpenSupportSplice.ownership_compiled_position
#print axioms PNP.DirectWire.WireOpenSupportSplice.ownership_partition
#print axioms PNP.DirectWire.WireOpenSupportSplice.ownership_charged_origin
#print axioms PNP.DirectWire.WireOpenSupportSplice.ownership_distinct
#print axioms PNP.DirectWire.WireOpenSupportSplice.physical_ownership
#print axioms PNP.DirectWire.WireOpenSupportSplice.Receipt.physical_ownership

end PNP.Regression.WireOpenSupportOwnership
