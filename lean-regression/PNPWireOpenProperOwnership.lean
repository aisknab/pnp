import PNP.NANDWireOpenProperOwnership

namespace PNP.Regression.WireOpenProperOwnership

open PNP.DirectWire WireOpenProgram WireOpenProperSupport

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    {raw : List RawEvent} (executed : SplicedProgram carrier records raw) :
    let ledger := ownership carrier records executed
    ledger.live.length = executed.result.implementation.gateCount ∧
      ledger.charged.length = executed.program.execution.charged ∧
      ledger.removed.length = executed.program.execution.removed ∧
      (ledger.live ++ ledger.removed).Nodup ∧
      (ledger.live ++ ledger.removed).Perm
        (programOriginals carrier.implementation.gateCount ++ ledger.charged) :=
  physical_ownership carrier records executed

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    {raw : List RawEvent} (executed : SplicedProgram carrier records raw)
    (node : Fin ((ArbitrarySupportSplice.exterior records).length +
      executed.program.result.implementation.gateCount)) :
    (ownership carrier records executed).origin (executed.compiled.position node) =
      ownershipRawNode carrier records executed node :=
  ownership_compiled_position carrier records executed node

private def source : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        ((((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩).snoc
          ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .input 0⟩)
        ⟨fun _ => .constant false⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def records : List (TerminalPrimitiveRecord 1 3 2 0) := [.gate 0, .gate 1]

private def removeGate (gate : Nat) : WireDescendantCertificate.RawCertificate :=
  ⟨[.gate gate], [⟨0, [.gate 0], [⟨7, [], .normalize⟩]⟩]⟩

private def raw : List RawEvent :=
  [⟨50, [40], .primitive (.readFull 0)⟩,
   ⟨30, [20], .support (removeGate 0)⟩,
   ⟨40, [30], .primitive (.restoreR8 7)⟩,
   ⟨7, [], .primitive (.createR5 0)⟩,
   ⟨20, [7], .support (removeGate 1)⟩]

private def temporaryGrowth : List RawEvent :=
  [⟨4, [3], .primitive (.readFull 0)⟩,
   ⟨2, [], .primitive (.restoreR8 1)⟩,
   ⟨3, [2], .primitive .normalize⟩,
   ⟨1, [], .primitive (.createR5 0)⟩]


private def historicalRequest : WireDescendantCertificate.RawCertificate :=
  ⟨[.gate 0, .gate 1], [⟨0, [.gate 0, .gate 1],
    [⟨7, [], .createR5 0⟩, ⟨20, [7], .normalize⟩, ⟨30, [20], .restoreR8 7⟩,
     ⟨40, [30], .createR5 0⟩, ⟨50, [40], .normalize⟩, ⟨60, [50], .restoreR8 40⟩]⟩]⟩

/-- Both nested allocated gates are later removed. The outer restoration
reuses the nested event numeral 60 but must have a distinct global identity. -/
private def repeatedNamespaces : List RawEvent :=
  [⟨60, [8], .primitive (.restoreR8 7)⟩,
   ⟨9, [60], .primitive (.readFull 0)⟩,
   ⟨100, [], .support historicalRequest⟩,
   ⟨8, [7], .primitive .normalize⟩,
   ⟨7, [100], .primitive (.createR5 0)⟩]


#eval show IO Unit from do
  let some executed := WireOpenProperSupport.compile source records raw
    | throw (IO.userError "complete program fixture failed outer compilation")
  let ledger := ownership source records executed
  if ledger.live.length != 2 || ledger.charged != [.allocated 3 0 40 0] ||
      ledger.removed.length != 2 ||
      !(ledger.live.contains (.original ⟨2, by decide⟩)) ||
      !(ledger.live.contains (.allocated 3 0 40 0)) ||
      !(ledger.removed.contains (.original ⟨0, by decide⟩)) ||
      !(ledger.removed.contains (.original ⟨1, by decide⟩)) then
    throw (IO.userError "outer embedding lost an original or allocated physical identity")
  for node in List.finRange
      ((ArbitrarySupportSplice.exterior records).length + executed.program.result.implementation.gateCount) do
    if ledger.origin (executed.compiled.position node) != ownershipRawNode source records executed node then
      throw (IO.userError "ownership did not follow the actual literal compiler position")
  let some historical := WireOpenProperSupport.compile source records repeatedNamespaces
    | throw (IO.userError "historical allocation fixture failed outer compilation")
  let retained := ownership source records historical
  if retained.charged !=
      [.allocated 0 0 30 0, .allocated 0 0 60 0, .allocated 3 0 60 0] ||
      retained.removed.length != 4 || retained.live.length != 2 ||
      !(retained.removed.contains (.allocated 0 0 30 0)) ||
      !(retained.removed.contains (.allocated 0 0 60 0)) ||
      retained.removed.contains (.allocated 3 0 60 0) ||
      !(retained.live.contains (.original ⟨2, by decide⟩)) ||
      !(retained.live.contains (.allocated 3 0 60 0)) then
    throw (IO.userError "outer embedding merged namespaces or erased charges after removal")
  let some identity := WireOpenProperSupport.compile source records []
    | throw (IO.userError "identity fixture failed compilation")
  let unchanged := ownership source records identity
  if unchanged.charged != [] || unchanged.removed != [] || unchanged.live.length != 3 then
    throw (IO.userError "identity embedding invented allocation or removal")
  for gate in List.finRange 3 do
    if !(unchanged.live.contains (.original gate)) then
      throw (IO.userError "identity embedding did not conserve all source gates")
  IO.println "open-proper-ownership-regressions-passed"

#print axioms PNP.DirectWire.WireOpenProperSupport.ownershipLift_original
#print axioms PNP.DirectWire.WireOpenProperSupport.ownershipLift_allocated
#print axioms PNP.DirectWire.WireOpenProperSupport.ownershipLift_injective
#print axioms PNP.DirectWire.WireOpenProperSupport.ownershipRawNode_exterior
#print axioms PNP.DirectWire.WireOpenProperSupport.ownershipRawNode_program
#print axioms PNP.DirectWire.WireOpenProperSupport.ownership_compiled_position
#print axioms PNP.DirectWire.WireOpenProperSupport.ownership_partition
#print axioms PNP.DirectWire.WireOpenProperSupport.ownership_charged_origin
#print axioms PNP.DirectWire.WireOpenProperSupport.ownership_distinct
#print axioms PNP.DirectWire.WireOpenProperSupport.physical_ownership

end PNP.Regression.WireOpenProperOwnership
