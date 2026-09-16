import PNP.NANDWireHistoryPhysicalOwnership

/-!
Kernel checks cover arbitrary history dimensions. Bounded runtime fixtures
exercise actual physical positions, not proof authority through native execution.
-/
namespace PNP.Regression.WireHistoryPhysicalOwnership

open PNP.DirectWire PNP.DirectWire.WireObligationHistory

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    {raw : List (RawEvent fields)} (history : ClosedHistory source raw) :
    let ledger := history.physicalOwnership
    ledger.live.length = history.state.current.implementation.gateCount ∧
      ledger.charged.length = history.execution.charged ∧
      ledger.removed.length = history.execution.removed ∧
      (ledger.live ++ ledger.removed).Nodup ∧
      (ledger.live ++ ledger.removed).Perm
        (sourcePhysicalOrigins source ++ ledger.charged) :=
  history.physical_ownership

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    {before after : State source} {event : RawEvent fields}
    (step : Transition source before event after)
    (ledger : PhysicalOwnership source.implementation.gateCount
      before.current.implementation.gateCount) :
    ((step.physicalOwnership ledger).live ++ (step.physicalOwnership ledger).removed).Perm
      ((ledger.live ++ ledger.removed) ++ step.allocations) :=
  step.physical_conservation ledger

private def source : WireCarrier 2 0 1 :=
  { implementation := (Candidate.ofDirectWireWord
      (.snoc .empty ⟨.input 0, .input 1⟩ : Program 2 1)
      (⟨Fin.elim0⟩ : DirectWireWord 2 1 0)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def chargedThenRemoved : List (RawEvent 1) :=
  [⟨30, [20], .normalize⟩, ⟨20, [], .restoreR8 10⟩, ⟨10, [], .createR5 0⟩]

private def twiceRestored : List (RawEvent 1) :=
  [⟨10, [], .createR5 0⟩, ⟨20, [], .restoreR8 10⟩,
    ⟨30, [20], .createR5 0⟩, ⟨40, [], .restoreR8 30⟩]

private def unary : WireCarrier 1 0 1 :=
  { implementation := (Candidate.ofDirectWireWord
      (.snoc .empty ⟨.input 0, .input 0⟩ : Program 1 1)
      (⟨Fin.elim0⟩ : DirectWireWord 1 1 0)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def aliases : WireCarrier 2 0 2 :=
  { implementation := source.implementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def zeroCarrier : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 0 0)
      (⟨Fin.elim0⟩ : DirectWireWord 0 0 0)).toImplementation
    source := Fin.elim0 }

#eval show IO Unit from do
  let some normalized := compileHistory source chargedThenRemoved
    | throw (IO.userError "valid charged-then-removed history rejected")
  let ledger := normalized.physicalOwnership
  if ledger.live != [.original ⟨0, by decide⟩] || ledger.charged != [.allocated 20 0] ||
      ledger.removed != [.allocated 20 0] then
    throw (IO.userError "normalization erased the historical charge or changed its event owner")
  let some twice := compileHistory source twiceRestored
    | throw (IO.userError "two independent materializer events rejected")
  let twiceLedger := twice.physicalOwnership
  if twiceLedger.live != [.original ⟨0, by decide⟩, .allocated 20 0, .allocated 40 0] ||
      twiceLedger.charged != [.allocated 20 0, .allocated 40 0] ||
      !twiceLedger.removed.isEmpty then
    throw (IO.userError "materializers reused a snapshot ID or failed actual append order")
  let some empty := compileHistory source []
    | throw (IO.userError "empty history rejected")
  if empty.physicalOwnership.live != [.original ⟨0, by decide⟩] ||
      !empty.physicalOwnership.charged.isEmpty || !empty.physicalOwnership.removed.isEmpty then
    throw (IO.userError "empty history fabricated a charge or removal")
  if (compileHistory source
      [⟨10, [], .createR5 0⟩, ⟨10, [], .restoreR8 10⟩]).isSome then
    throw (IO.userError "duplicate executing identity accepted")
  let some pruned := compileHistory source
      [⟨10, [], .createR5 0⟩, ⟨20, [10], .normalize⟩, ⟨30, [20], .restoreR8 10⟩]
    | throw (IO.userError "restoration after original-gate removal rejected")
  if pruned.physicalOwnership.live != [.allocated 30 0] ||
      pruned.physicalOwnership.charged != [.allocated 30 0] ||
      pruned.physicalOwnership.removed != [.original ⟨0, by decide⟩] then
    throw (IO.userError "restoration relabelled a new gate as the removed original")
  let some repeated := compileHistory source
      (twiceRestored ++ [⟨50, [40], .normalize⟩, ⟨60, [50], .normalize⟩])
    | throw (IO.userError "repeated actual normalization rejected")
  if repeated.physicalOwnership.live != [.original ⟨0, by decide⟩] ||
      repeated.physicalOwnership.charged != [.allocated 20 0, .allocated 40 0] ||
      repeated.physicalOwnership.removed != [.allocated 20 0, .allocated 40 0] then
    throw (IO.userError "repeated normalization duplicated a removal or lost an allocation")
  let some realized := compileHistory unary
      [⟨10, [], .createR5 0⟩,
        ⟨20, [], .realizeR7 10 [.gate 0, .boundary 0, .interface 0]⟩,
        ⟨30, [20], .normalize⟩, ⟨40, [30], .readFull 0⟩]
    | throw (IO.userError "computed unary R7 history rejected")
  if realized.physicalOwnership.live != [.original ⟨0, by decide⟩] ||
      realized.physicalOwnership.charged != [.allocated 20 0] ||
      realized.physicalOwnership.removed != [.allocated 20 0] then
    throw (IO.userError "computed R7 materializer ownership was not retained after removal")
  let some cancelled := compileHistory aliases
      [⟨10, [], .createR5 0⟩, ⟨20, [], .cancelR6 10⟩, ⟨30, [20], .readFull 0⟩]
    | throw (IO.userError "matched cancellation and full read rejected")
  if cancelled.physicalOwnership.live != [.original ⟨0, by decide⟩] ||
      !cancelled.physicalOwnership.charged.isEmpty || !cancelled.physicalOwnership.removed.isEmpty then
    throw (IO.userError "creation, cancellation or read minted a physical gate")
  let some zero := compileHistory zeroCarrier [⟨10, [], .normalize⟩]
    | throw (IO.userError "zero-dimensional normalization rejected")
  if !zero.physicalOwnership.live.isEmpty || !zero.physicalOwnership.charged.isEmpty ||
      !zero.physicalOwnership.removed.isEmpty then
    throw (IO.userError "zero-dimensional history fabricated a physical origin")
  IO.println "M266 history-physical-ownership-regressions-passed"

#print axioms PhysicalOwnership.append_origin_left
#print axioms PhysicalOwnership.append_origin_right
#print axioms PhysicalOwnership.append_live
#print axioms PhysicalOwnership.normalize_partition
#print axioms PhysicalOwnership.normalize_removed_length
#print axioms Transition.restore_physical_positions
#print axioms Transition.realize_physical_positions
#print axioms Transition.allocations_nodup
#print axioms Transition.physical_charged
#print axioms Transition.physical_removed_length
#print axioms Transition.physical_conservation
#print axioms Execution.allocations_length
#print axioms Execution.physical_charged
#print axioms Execution.physical_removed_length
#print axioms Execution.physical_conservation
#print axioms Execution.allocations_member
#print axioms Execution.allocations_nodup
#print axioms ClosedHistory.physical_charged
#print axioms ClosedHistory.physical_partition
#print axioms ClosedHistory.physical_ownership

end PNP.Regression.WireHistoryPhysicalOwnership
