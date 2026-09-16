import PNP.NANDWireHistoryOwnershipCharges

/-! Arbitrary-dimension ownership plus actual interleaved exterior/support wiring. -/
namespace PNP.Regression.WireHistoryAmbientOwnership

open PNP.DirectWire WireObligationHistory WireHistoryAmbientOwnership

example {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    {raw : List (RawEvent (terminalInterfacePorts candidate records).length)}
    (owned : OwnedCompilation candidate records raw) :
    let ledger := owned.ledger candidate records
    ledger.live.length = (owned.result candidate records).gateCount ∧
      ledger.charged.length = owned.history.execution.charged ∧
      ledger.removed.length = owned.history.execution.removed ∧
      (ledger.live ++ ledger.removed).Nodup ∧
      (ledger.live ++ ledger.removed).Perm (ambientOriginals gates ++ ledger.charged) :=
  owned.ownership candidate records

example {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (raw : List (RawEvent (terminalInterfacePorts candidate records).length)) :
    (compileOwned candidate records raw).map (OwnedCompilation.result candidate records) =
      WireHistoryArbitrarySupport.compile candidate records raw :=
  compileOwned_result candidate records raw

example {inputs gates outputs profileWidth supportWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    {raw : List (RawEvent (terminalInterfacePorts candidate records).length)}
    (owned : OwnedCompilation candidate records raw)
    (support : List (TerminalPrimitiveRecord inputs (owned.result candidate records).gateCount
      outputs supportWidth)) :
    ((terminalPhysicalOwners raw.length).map (fun owner =>
      (owned.materializer candidate records support owner).gateCount)).sum =
        (extractTerminalSupport (owned.result candidate records).candidate support).gateCount :=
  owned.materializer_chargeIdentity candidate records support

private def interleavedProgram : Program 2 4 :=
  ((((.empty : Program 2 0).snoc ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .input 1⟩).snoc
    ⟨.gate 0, .input 1⟩).snoc ⟨.gate 1, .gate 2⟩

private def ambient : Candidate 2 4 2 :=
  Candidate.ofDirectWireWord interleavedProgram
    ⟨fun output => if output.val = 0 then .gate 3 else .gate 2⟩

private def selected : List (TerminalPrimitiveRecord 2 4 2 0) := [.gate 1]

private def restoredAndNormalized :
    List (RawEvent (terminalInterfacePorts ambient selected).length) :=
  [⟨10, [], .createR5 ⟨0, by decide⟩⟩,
    ⟨20, [], .restoreR8 10⟩, ⟨30, [20], .normalize⟩]

private def prunedAndRestored :
    List (RawEvent (terminalInterfacePorts ambient selected).length) :=
  [⟨10, [], .createR5 ⟨0, by decide⟩⟩,
    ⟨20, [10], .normalize⟩, ⟨30, [20], .restoreR8 10⟩]

private def twiceRestored :
    List (RawEvent (terminalInterfacePorts ambient selected).length) :=
  [⟨10, [], .createR5 ⟨0, by decide⟩⟩, ⟨20, [], .restoreR8 10⟩,
    ⟨30, [20], .createR5 ⟨0, by decide⟩⟩, ⟨40, [], .restoreR8 30⟩]

private def emptyCandidate : Candidate 0 0 0 :=
  Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩

#eval show IO Unit from do
  let some restored := compileOwned ambient selected restoredAndNormalized
    | throw (IO.userError "valid interleaved ambient history rejected")
  let ledger := restored.ledger ambient selected
  if ledger.live != [.original 0, .original 2, .original 1, .original 3] ||
      ledger.charged != [.allocated 20 0] || ledger.removed != [.allocated 20 0] then
    throw (IO.userError "ambient physical order or removed allocation identity changed")
  let restoredSupport : List
      (TerminalPrimitiveRecord 2 (restored.result ambient selected).gateCount 2 0) :=
    (allFin (restored.result ambient selected).gateCount).map TerminalPrimitiveRecord.gate
  let restoredCharges := (terminalPhysicalOwners restoredAndNormalized.length).map fun owner =>
    (restored.materializer ambient selected restoredSupport owner).gateCount
  if restoredCharges != [4, 0, 0, 0] || ledger.charged.length != 1 then
    throw (IO.userError "removed allocation was confused with surviving owned size")
  let some pruned := compileOwned ambient selected prunedAndRestored
    | throw (IO.userError "valid original-removal ambient history rejected")
  let prunedLedger := pruned.ledger ambient selected
  if prunedLedger.live != [.original 0, .original 2, .allocated 30 0, .original 3] ||
      prunedLedger.charged != [.allocated 30 0] || prunedLedger.removed != [.original 1] then
    throw (IO.userError "extracted source position was not lifted to its actual ambient gate")
  let prunedSupport : List
      (TerminalPrimitiveRecord 2 (pruned.result ambient selected).gateCount 2 0) :=
    (allFin (pruned.result ambient selected).gateCount).map TerminalPrimitiveRecord.gate
  let prunedCharges := (terminalPhysicalOwners prunedAndRestored.length).map fun owner =>
    (pruned.materializer ambient selected prunedSupport owner).gateCount
  let requestPositions := (allFin prunedAndRestored.length).map fun owner =>
    (pruned.eventRequests ambient selected owner).map Fin.val
  if prunedCharges != [3, 0, 0, 1] || requestPositions != [[], [], [2]] then
    throw (IO.userError "surviving allocation was not assigned to its executing raw event")
  let restricted := prunedSupport.filter fun record =>
    match record with
    | .gate gate => gate.val = 2 || gate.val = 3
    | _ => false
  let restrictedCharges := (terminalPhysicalOwners prunedAndRestored.length).map fun owner =>
    (pruned.materializer ambient selected (restricted ++ restricted) owner).gateCount
  if restrictedCharges != [1, 0, 0, 1] then
    throw (IO.userError "support restriction reassigned ownership or duplicated a physical charge")
  let some twice := compileOwned ambient selected twiceRestored
    | throw (IO.userError "two live materializer allocations rejected")
  let twiceSupport : List
      (TerminalPrimitiveRecord 2 (twice.result ambient selected).gateCount 2 0) :=
    (allFin (twice.result ambient selected).gateCount).map TerminalPrimitiveRecord.gate
  let twiceCharges := (terminalPhysicalOwners twiceRestored.length).map fun owner =>
    (twice.materializer ambient selected twiceSupport owner).gateCount
  if twiceCharges != [4, 0, 1, 0, 1] then
    throw (IO.userError "distinct executing events merged their live allocation ownership")
  let some exteriorOnly := compileOwned ambient
      ([] : List (TerminalPrimitiveRecord 2 4 2 0)) []
    | throw (IO.userError "empty support rejected")
  if (exteriorOnly.ledger ambient []).live != [.original 0, .original 1, .original 2, .original 3] then
    throw (IO.userError "empty support lost or duplicated an exterior gate")
  let some empty := compileOwned emptyCandidate
      ([] : List (TerminalPrimitiveRecord 0 0 0 0)) [⟨10, [], .normalize⟩]
    | throw (IO.userError "empty whole circuit rejected")
  let emptyLedger := empty.ledger emptyCandidate []
  if !emptyLedger.live.isEmpty || !emptyLedger.charged.isEmpty || !emptyLedger.removed.isEmpty then
    throw (IO.userError "empty ambient circuit fabricated a gate")
  if (compileOwned ambient selected [⟨10, [], .createR5 ⟨0, by decide⟩⟩]).isSome then
    throw (IO.userError "ownership wrapper accepted an unfinished history")
  IO.println "M266 ambient-physical-ownership-and-derived-charges-regressions-passed"

#print axioms liftOrigin_injective
#print axioms original_coordinate_partition
#print axioms rawNodeOrigin_exterior
#print axioms rawNodeOrigin_history
#print axioms physicalOrigin_position
#print axioms physical_partition
#print axioms physical_ownership
#print axioms OwnedCompilation.ownership
#print axioms OwnedCompilation.semantics
#print axioms compileOwned_result

#print axioms OwnedCompilation.eventRequests_member
#print axioms OwnedCompilation.eventRequests_disjoint
#print axioms OwnedCompilation.eventOwner_some_iff
#print axioms OwnedCompilation.charged_origin
#print axioms OwnedCompilation.live_allocated_event
#print axioms OwnedCompilation.eventOwner_none_iff
#print axioms OwnedCompilation.support_membership
#print axioms OwnedCompilation.support_restrict
#print axioms OwnedCompilation.materializer_gateCount
#print axioms OwnedCompilation.materializer_chargeIdentity
#print axioms OwnedCompilation.materializer_wholeCharge
#print axioms OwnedCompilation.materializer_semantics
#print axioms OwnedCompilation.materializer_induced

end PNP.Regression.WireHistoryAmbientOwnership
