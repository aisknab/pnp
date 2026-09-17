import PNP.NANDWireStructuralState

namespace PNP.Regression.StructuralState

open PNP.DirectWire PNP.DirectWire.StructuralReindexing
open WireObligationHistory (State)

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (relabeling : GateRenaming carrier.implementation.gateCount) (field : Fin fields) :
    (carrier.reindex relabeling).source field =
      sourceMap (carrier.reindexForwardGate relabeling) (carrier.source field) :=
  carrier.reindex_field_source relabeling field

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (relabeling : GateRenaming carrier.implementation.gateCount)
    (gate : Fin (carrier.reindex relabeling).implementation.gateCount) :
    carrier.reindexForwardGate relabeling (carrier.reindexBackwardGate relabeling gate) = gate :=
  carrier.reindex_forward_backward relabeling gate

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    (before : State source)
    (relabeling : GateRenaming before.current.implementation.gateCount) :
    (before.reindex relabeling).pending = before.pending :=
  before.reindex_pending relabeling

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    (before : State source)
    (relabeling : GateRenaming before.current.implementation.gateCount)
    (labels : Fin inputs → Nat) (bounded : before.CausalInvariant labels) :
    (before.reindex relabeling).CausalInvariant labels :=
  before.reindex_causalInvariant relabeling labels bounded

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    (before : State source) (code : List (Nat × Nat)) :
    (WireStructuralState.execute before code).isSome =
      GateRenaming.validCode before.current.implementation.gateCount code :=
  WireStructuralState.execute_isSome before code

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    (before : State source) (code : List (Nat × Nat)) :
    WireStructuralState.execute before code = none ↔
      GateRenaming.validCode before.current.implementation.gateCount code = false :=
  WireStructuralState.execute_failure_iff before code

#print axioms PNP.DirectWire.WireCarrier.reindex_field_source
#print axioms PNP.DirectWire.WireCarrier.reindex_output
#print axioms PNP.DirectWire.WireCarrier.reindex_field
#print axioms PNP.DirectWire.WireCarrier.reindex_output_level
#print axioms PNP.DirectWire.WireCarrier.reindex_field_level
#print axioms PNP.DirectWire.WireObligationHistory.State.reindex_pending
#print axioms PNP.DirectWire.WireObligationHistory.State.reindex_causalInvariant
#print axioms PNP.DirectWire.WireStructuralState.execute_isSome
#print axioms PNP.DirectWire.WireStructuralState.execute_failure_iff

private def fixture : WireCarrier 2 1 2 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        ((((.empty : Program 2 0).snoc ⟨.input 0, .input 0⟩).snoc
          ⟨.input 1, .input 1⟩).snoc ⟨.gate 0, .gate 1⟩)
        ⟨fun _ => .gate 2⟩).toImplementation
    source := fun field => if field.val = 0
      then .gate ⟨0, by decide⟩
      else .gate ⟨1, by decide⟩ }

private def emptyFixture : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 0 0) ⟨Fin.elim0⟩).toImplementation
    source := Fin.elim0 }

#eval show IO Unit from do
  let before := (State.initial fixture).create 77 (0 : Fin 2) rfl
  let some receipt := WireStructuralState.execute before [(0, 1)]
    | throw (IO.userError "structural state rejected a valid nonidentity reordering")
  let after := receipt.next
  if after.current.implementation.gateCount != 3 || after.charged != before.charged ||
      after.removed != before.removed then
    throw (IO.userError "reordering changed a physical count or historical cost")
  if (after.pending 0).map (fun snapshot => snapshot.identity) != some 77 ||
      (after.pending 1).isSome then
    throw (IO.userError "reordering changed the pending-obligation identities")
  match after.current.source 1 with
  | .gate index =>
      if index.val != 0 then
        throw (IO.userError "the preserved available field was not physically rebound")
  | _ => throw (IO.userError "the actual gate field became a non-gate source")
  let some snapshot := after.pending 0
    | throw (IO.userError "reordering silently discharged the pending snapshot")
  for left in [false, true] do
    for right in [false, true] do
      let valuation : Valuation 2 := fun index => if index.val = 0 then left else right
      if after.current.implementation.candidate.semantics valuation 0 !=
          before.current.implementation.candidate.semantics valuation 0 ||
          after.current.fieldValue valuation 0 != before.current.fieldValue valuation 0 ||
          after.current.fieldValue valuation 1 != before.current.fieldValue valuation 1 ||
          snapshot.carrier.fieldValue valuation 0 != fixture.fieldValue valuation 0 then
        throw (IO.userError "reordering changed an output, available value or captured full value")
  for invalid in [[(0, 1), (0, 3)], [(3, 0)], [(0, 3)]] do
    if (WireStructuralState.execute before invalid).isSome then
      throw (IO.userError "structural state accepted an invalid complete swap sequence")
  if !(WireStructuralState.execute before [(0, 0), (0, 1), (0, 1)]).isSome ||
      !(WireStructuralState.execute (State.initial emptyFixture) []).isSome ||
      (WireStructuralState.execute (State.initial emptyFixture) [(0, 0)]).isSome then
    throw (IO.userError "self, duplicate or zero-width reordering was misclassified")
  IO.println "wire-structural-state-runtime-regressions: passed"

end PNP.Regression.StructuralState
