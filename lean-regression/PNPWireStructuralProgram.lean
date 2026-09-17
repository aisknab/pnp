import PNP.NANDWireStructuralProgram

namespace PNP.Regression.StructuralProgram

open PNP.DirectWire WireOpenProgram
open WireObligationHistory (State)

example {inputs outputs fields initialGates : Nat}
    {source : WireCarrier inputs outputs fields} {before : State source}
    {event : RawEvent} {raw : List (Nat × Nat)}
    (ledger : ProgramOwnership initialGates before.current.implementation.gateCount)
    (position : Nat) (kind : event.action = .structural raw)
    (receipt : WireStructuralState.Receipt before raw)
    (gate : Fin before.current.implementation.gateCount) :
    (ledger.advance position (.structural before event raw kind receipt)).origin
        (before.current.reindexForwardGate receipt.relabeling gate) = ledger.origin gate :=
  ledger.advance_structural_origin position kind receipt gate

example {inputs outputs fields initialGates : Nat}
    {source : WireCarrier inputs outputs fields} {before : State source}
    {event : RawEvent} {raw : List (Nat × Nat)}
    (ledger : ProgramOwnership initialGates before.current.implementation.gateCount)
    (position : Nat) (kind : event.action = .structural raw)
    (receipt : WireStructuralState.Receipt before raw) :
    (ledger.advance position (.structural before event raw kind receipt)).charged = ledger.charged ∧
      (ledger.advance position (.structural before event raw kind receipt)).removed = ledger.removed :=
  ⟨ledger.advance_structural_charged position kind receipt,
    ledger.advance_structural_removed position kind receipt⟩

#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_origin
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_charged
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_removed
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.physical_ownership
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.creation_lifecycle
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.causalInvariant

private def fixture : WireCarrier 2 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (((.empty : Program 2 0).snoc ⟨.input 0, .input 0⟩).snoc
          ⟨.input 1, .input 1⟩)
        ⟨fun _ => .gate 1⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def emptyFixture : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 0 0) ⟨Fin.elim0⟩).toImplementation
    source := Fin.elim0 }

private def removeGate (gate : Nat) : WireDescendantCertificate.RawCertificate :=
  ⟨[.gate gate], [⟨0, [.gate 0], [⟨7, [], .normalize⟩]⟩]⟩

/-- Raw order is not execution order. A real open snapshot crosses a permutation
and nested removal before restoration; the allocated gate is then renumbered. -/
private def openAcrossReordering : List RawEvent :=
  [⟨50, [40], .primitive (.readFull 0)⟩,
   ⟨40, [30], .structural [(0, 1)]⟩,
   ⟨30, [20], .primitive (.restoreR8 10)⟩,
   ⟨20, [15], .support (removeGate 1)⟩,
   ⟨15, [10], .structural [(0, 1)]⟩,
   ⟨10, [], .primitive (.createR5 0)⟩]

/-- A previously allocated and reordered gate is later removed. Its historical
charge must survive, and the next allocation has a different computed owner. -/
private def historicalAllocations : List RawEvent :=
  [⟨90, [80], .primitive (.readFull 0)⟩,
   ⟨80, [70], .structural [(0, 1)]⟩,
   ⟨70, [60], .primitive (.restoreR8 50)⟩,
   ⟨60, [50], .primitive .normalize⟩,
   ⟨50, [40], .primitive (.createR5 0)⟩,
   ⟨40, [30], .structural [(0, 1)]⟩,
   ⟨30, [20], .primitive (.restoreR8 10)⟩,
   ⟨20, [10], .primitive .normalize⟩,
   ⟨10, [], .primitive (.createR5 0)⟩]

#eval show IO Unit from do
  let some opened := compile fixture openAcrossReordering
    | throw (IO.userError "open snapshot could not cross actual reordering and nested support")
  let records := opened.execution.records
  if records.map (fun event => event.identity) != [10, 15, 20, 30, 40, 50] then
    throw (IO.userError "structural integration omitted or misordered a raw action")
  let [created, firstReorder, support, restored, secondReorder, read] := records
    | throw (IO.userError "complete reordered trace has the wrong event count")
  if created.creation.isNone || support.discharge.isSome || read.fullRead.isNone then
    throw (IO.userError "the actual creation, nested support or final full read was lost")
  for reordered in [firstReorder, secondReorder] do
    if reordered.creation.isSome || reordered.discharge.isSome || reordered.fullRead.isSome ||
        reordered.chargedGates != 0 || reordered.removedGates != 0 then
      throw (IO.userError "reordering fabricated a lifecycle event or physical cost")
  let some discharge := restored.discharge
    | throw (IO.userError "only the actual restoration may discharge the open snapshot")
  if discharge.creation.identity != 10 ||
      discharge.creation.carrier.implementation.gateCount != 2 then
    throw (IO.userError "restoration lost the exact pre-reordering creation snapshot")
  let originalOne : Fin fixture.implementation.gateCount := ⟨1, by decide⟩
  if opened.ownership.live != [.allocated 3 0 30 0, .original originalOne] ||
      opened.ownership.charged != [.allocated 3 0 30 0] ||
      opened.ownership.removed.length != 1 then
    throw (IO.userError "reordering did not retain actual original and newly allocated owners")
  let some historical := compile fixture historicalAllocations
    | throw (IO.userError "complete repeated-allocation reordering program rejected")
  let ledger := historical.ownership
  if historical.execution.records.map (fun event => event.identity) !=
      [10, 20, 30, 40, 50, 60, 70, 80, 90] then
    throw (IO.userError "ownership positions do not follow the complete computed schedule")
  if ledger.live != [.allocated 6 0 70 0, .original originalOne] ||
      ledger.charged != [.allocated 2 0 30 0, .allocated 6 0 70 0] ||
      ledger.removed.length != 2 ||
      !ledger.removed.contains (.allocated 2 0 30 0) ||
      ledger.removed.contains (.allocated 6 0 70 0) then
    throw (IO.userError "a historical allocation was reset, uncharged or conflated after reordering")
  if historical.execution.charged != 2 || historical.execution.removed != 2 ||
      historical.result.implementation.gateCount != 2 then
    throw (IO.userError "reordering changed the exact physical accounting")
  for left in [false, true] do
    for right in [false, true] do
      let valuation : Valuation 2 := fun gate => if gate.val = 0 then left else right
      for result in [opened.result, historical.result] do
        if result.implementation.candidate.semantics valuation 0 !=
            fixture.implementation.candidate.semantics valuation 0 ||
            result.fieldValue valuation 0 != fixture.fieldValue valuation 0 then
          throw (IO.userError "reordered complete program changed full output or field semantics")
  let invalidAfterShrink : List RawEvent :=
    [⟨10, [], .primitive (.createR5 0)⟩,
     ⟨15, [10], .structural [(0, 1)]⟩,
     ⟨20, [15], .support (removeGate 1)⟩,
     ⟨25, [20], .structural [(0, 1)]⟩,
     ⟨30, [25], .primitive (.restoreR8 10)⟩]
  let unclosed : List RawEvent :=
    [⟨10, [], .primitive (.createR5 0)⟩, ⟨15, [10], .structural [(0, 1)]⟩]
  for rejected in [invalidAfterShrink, unclosed,
      historicalAllocations ++ [⟨100, [90], .structural [(0, 1), (0, 2)]⟩]] do
    if (compile fixture rejected).isSome then
      throw (IO.userError "invalid or unclosed structural tail exposed a successful prefix")
  let some empty := compile emptyFixture [⟨1, [], .structural []⟩]
    | throw (IO.userError "zero-dimensional empty structural action rejected")
  if empty.execution.records.length != 1 || !empty.ownership.live.isEmpty ||
      !empty.ownership.charged.isEmpty || !empty.ownership.removed.isEmpty ||
      (compile emptyFixture [⟨1, [], .structural [(0, 0)]⟩]).isSome then
    throw (IO.userError "zero-dimensional structural execution fabricated gates or accepted bad coordinates")
  IO.println "wire-structural-program-runtime-regressions: passed"

end PNP.Regression.StructuralProgram
