import PNP.NANDWireStructuralOwnership

namespace PNP.Regression.StructuralOwnership

open PNP.DirectWire
open WireObligationHistory (State)
open WireDescendantHistory (DescendantOrigin originalOrigins)

variable {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
variable {before : State source} {code : List (Nat × Nat)}

example (receipt : WireStructuralState.Receipt before code)
    (gate : Fin before.current.implementation.gateCount) :
    receipt.ownership.origin (before.current.reindexForwardGate receipt.relabeling gate) =
      .original gate :=
  receipt.ownership_origin_forward gate

example (receipt : WireStructuralState.Receipt before code) :
    Function.Injective receipt.ownership.origin :=
  receipt.ownership_origin_injective

example (receipt : WireStructuralState.Receipt before code) :
    receipt.ownership.WellFormed 0 :=
  receipt.ownership_wellFormed

example (receipt : WireStructuralState.Receipt before code) :
    receipt.ownership.live.length = receipt.next.current.implementation.gateCount ∧
      receipt.ownership.charged.length = 0 ∧
      receipt.ownership.removed.length = 0 ∧
      (receipt.ownership.live ++ receipt.ownership.removed).Nodup ∧
      (receipt.ownership.live ++ receipt.ownership.removed).Perm
        (originalOrigins before.current.implementation.gateCount ++ receipt.ownership.charged) :=
  receipt.physical_ownership

example (receipt : WireStructuralState.Receipt before code)
    (gate : Fin receipt.next.current.implementation.gateCount)
    (stage event localGate : Nat) :
    receipt.ownership.origin gate ≠ .allocated stage event localGate :=
  receipt.ownership_not_allocated gate stage event localGate

#print axioms PNP.DirectWire.WireStructuralState.Receipt.ownership_origin_forward
#print axioms PNP.DirectWire.WireStructuralState.Receipt.ownership_origin_injective
#print axioms PNP.DirectWire.WireStructuralState.Receipt.ownership_live_members
#print axioms PNP.DirectWire.WireStructuralState.Receipt.ownership_wellFormed
#print axioms PNP.DirectWire.WireStructuralState.Receipt.physical_ownership

private def fixture : WireCarrier 2 1 0 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        ((((.empty : Program 2 0).snoc ⟨.input 0, .input 0⟩).snoc
          ⟨.input 1, .input 1⟩).snoc ⟨.gate 0, .gate 1⟩)
        ⟨fun _ => .gate 2⟩).toImplementation
    source := Fin.elim0 }

private def emptyFixture : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 0 0) ⟨Fin.elim0⟩).toImplementation
    source := Fin.elim0 }

private def originalIndex {width : Nat} : DescendantOrigin width → Option Nat
  | .original gate => some gate.val
  | .allocated _ _ _ => none

#eval show IO Unit from do
  let before := State.initial fixture
  let some receipt := WireStructuralState.execute before [(0, 1)]
    | throw (IO.userError "ownership fixture rejected a valid reordering")
  let ledger := receipt.ownership
  if ledger.live.map originalIndex != [some 1, some 0, some 2] then
    throw (IO.userError "ownership did not follow the actual nonidentity physical permutation")
  if !ledger.charged.isEmpty || !ledger.removed.isEmpty then
    throw (IO.userError "structural reordering introduced a charge or removal")
  for gate in List.ofFn (fun gate : Fin before.current.implementation.gateCount => gate) do
    if ledger.origin (before.current.reindexForwardGate receipt.relabeling gate) !=
        .original gate then
      throw (IO.userError "an original gate was not recovered at its computed physical position")
  let some restored := WireStructuralState.execute receipt.next [(0, 1)]
    | throw (IO.userError "a second valid reordering was rejected")
  let recovered := restored.ownership.live.map fun origin =>
    match origin with
    | .original gate => originalIndex (receipt.ownership.origin gate)
    | .allocated _ _ _ => none
  if recovered != [some 0, some 1, some 2] then
    throw (IO.userError "composed local ownership reset or lost a previous gate identity")
  let some empty := WireStructuralState.execute (State.initial emptyFixture) []
    | throw (IO.userError "empty ownership fixture rejected the empty reordering")
  if !empty.ownership.live.isEmpty || !empty.ownership.charged.isEmpty ||
      !empty.ownership.removed.isEmpty then
    throw (IO.userError "zero-width reordering acquired a physical owner or cost")
  if (WireStructuralState.execute before [(0, 1), (0, 3)]).isSome then
    throw (IO.userError "invalid later coordinates received an ownership receipt")
  IO.println "wire-structural-ownership-runtime-regressions: passed"

end PNP.Regression.StructuralOwnership
