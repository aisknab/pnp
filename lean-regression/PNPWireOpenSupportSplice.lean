import PNP.NANDWireOpenSupportSplice

namespace PNP.Regression.WireOpenSupportSplice

open PNP.DirectWire WireObligationHistory WireDescendantHistory WireDescendantProperSupport
open WireOpenSupportSplice

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    (before : State source) (raw : WireDescendantCertificate.RawCertificate)
    (receipt : Receipt before raw) : receipt.next.pending = before.pending := receipt.pending

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    (before : State source)
    (records : List (TerminalPrimitiveRecord inputs
      before.current.implementation.gateCount (outputs + fields) 0))
    {stages : List RawStage} (executed : SplicedRun before.current records stages)
    (labels : Fin inputs → Nat) (bounded : before.CausalInvariant labels) :
    (transfer before records executed).CausalInvariant labels :=
  transfer_causal_invariant before records executed labels bounded

private def source : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .input 0⟩)
        ⟨fun _ => .constant false⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def normalizeAll : RawStage :=
  ⟨0, [.gate 0, .gate 1], [⟨10, [], .normalize⟩]⟩

private def request : WireDescendantCertificate.RawCertificate :=
  ⟨[.gate 0, .gate 1], [normalizeAll]⟩

private def emptySource : WireCarrier 0 0 0 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 0 0) ⟨Fin.elim0⟩).toImplementation
    source := Fin.elim0 }

#eval show IO Unit from do
  let initial := State.initial source
  let some created := applyEvent initial ⟨7, [], .createR5 0⟩
    | throw (IO.userError "fixture failed to create its actual obligation")
  let some entry := findPending created.1 7
    | throw (IO.userError "created snapshot was not retained")
  let some receipt := WireOpenSupportSplice.execute created.1 request
    | throw (IO.userError "open ambient ledger incorrectly prevented a valid local splice")
  let changed := receipt.next
  if changed.current.implementation.gateCount != 0 || changed.charged != 0 || changed.removed != 2 then
    throw (IO.userError "splice did not retain the actual physical normalization accounting")
  let some carried := findPending changed 7
    | throw (IO.userError "support splice silently erased a pending creation")
  if carried.snapshot.identity != entry.snapshot.identity ||
      carried.snapshot.carrier.implementation.gateCount != 2 then
    throw (IO.userError "support splice replaced the original captured carrier")
  if (applyEvent changed ⟨8, [], .readFull 0⟩).isSome then
    throw (IO.userError "an open ambient field was read as a full value")
  if (applyEvent changed ⟨8, [], .cancelR6 7⟩).isSome then
    throw (IO.userError "quotient padding equality was accepted as full-mode cancellation")
  if (applyEvent changed ⟨8, [], .createR5 0⟩).isSome then
    throw (IO.userError "a live creation was overwritten")
  if (applyEvent changed ⟨8, [], .restoreR8 99⟩).isSome then
    throw (IO.userError "an unrelated creation identity was restored")
  let some restored := applyEvent changed ⟨9, [], .restoreR8 7⟩
    | throw (IO.userError "the actual carried creation could not be restored")
  if restored.1.current.implementation.gateCount != 1 ||
      restored.1.charged != 1 || restored.1.removed != 2 then
    throw (IO.userError "restoration failed to charge the real captured materializer")
  if (findPending restored.1 7).isSome ||
      !(applyEvent restored.1 ⟨11, [], .readFull 0⟩).isSome then
    throw (IO.userError "restoration did not close the original obligation")
  for bit in [false, true] do
    let valuation : Valuation 1 := fun _ => bit
    if restored.1.current.implementation.candidate.semantics valuation 0 !=
        source.implementation.candidate.semantics valuation 0 ||
        restored.1.current.fieldValue valuation 0 != source.fieldValue valuation 0 ||
        carried.snapshot.carrier.fieldValue valuation 0 != entry.snapshot.carrier.fieldValue valuation 0 then
      throw (IO.userError "transport changed an ordinary output or the captured full value")
  for invalid in [RawRecord.gate 2, .boundary 1, .interface 2, .profile 0] do
    if (WireOpenSupportSplice.execute created.1
        {request with records := request.records ++ [invalid]}).isSome then
      throw (IO.userError "invalid outer support coordinate accepted")
  let badTail : RawStage := ⟨0, [.gate 99], []⟩
  if (WireOpenSupportSplice.execute created.1
      {request with stages := request.stages ++ [badTail]}).isSome then
    throw (IO.userError "failed local tail returned an accepted prefix")
  if !(WireOpenSupportSplice.execute (State.initial emptySource) ⟨[], []⟩).isSome then
    throw (IO.userError "zero-dimensional identity splice rejected")
  IO.println "open-support-splice-regressions-passed"

#print axioms transfer_pending
#print axioms transfer_keep
#print axioms transfer_snapshot
#print axioms transfer_charge
#print axioms transfer_removal
#print axioms transfer_output
#print axioms transfer_available
#print axioms transfer_balance
#print axioms replacement_dependency_bound
#print axioms result_exposed_dependency_bound
#print axioms result_causal_bounds
#print axioms transfer_causal_invariant
#print axioms Receipt.pending
#print axioms Receipt.records_source
#print axioms execute_of_compiled
#print axioms execute_exists_iff

end PNP.Regression.WireOpenSupportSplice
