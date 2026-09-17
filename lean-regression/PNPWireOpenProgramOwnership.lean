import PNP.NANDWireOpenProgramOwnership

namespace PNP.Regression.WireOpenProgramOwnership

open PNP.DirectWire WireOpenProgram

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    {raw : List RawEvent} (program : CompiledProgram source raw) :
    program.ownership.live.length = program.result.implementation.gateCount ∧
      program.ownership.charged.length = program.execution.charged ∧
      program.ownership.removed.length = program.execution.removed ∧
      (program.ownership.live ++ program.ownership.removed).Nodup ∧
      (program.ownership.live ++ program.ownership.removed).Perm
        (programOriginals source.implementation.gateCount ++ program.ownership.charged) :=
  program.physical_ownership

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    {raw : List RawEvent} (program : CompiledProgram source raw) :
    Function.Injective program.ownership.origin := program.ownership_origin_injective

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    {raw : List RawEvent} (program : CompiledProgram source raw)
    (origin : ProgramOrigin source.implementation.gateCount) (member : origin ∈ program.ownership.charged) :
    ∃ position stage identity localGate,
      position < raw.length ∧ origin = .allocated position stage identity localGate :=
  program.ownership_charge_origin origin member

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

private def removeGate (gate : Nat) : WireDescendantCertificate.RawCertificate :=
  ⟨[.gate gate], [⟨0, [.gate 0], [⟨7, [], .normalize⟩]⟩]⟩

private def openAcrossSupports : List RawEvent :=
  [⟨50, [40], .primitive (.readFull 0)⟩,
   ⟨30, [20], .support (removeGate 0)⟩,
   ⟨40, [30], .primitive (.restoreR8 7)⟩,
   ⟨7, [], .primitive (.createR5 0)⟩,
   ⟨20, [7], .support (removeGate 1)⟩]

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
  let some openProgram := compile source openAcrossSupports
    | throw (IO.userError "complete open-across-supports ownership fixture rejected")
  let openLedger := openProgram.ownership
  if openLedger.live != [.allocated 3 0 40 0] ||
      openLedger.charged != [.allocated 3 0 40 0] || openLedger.removed.length != 2 then
    throw (IO.userError "global ownership did not follow both supports and the real final restoration")
  let originals := openLedger.removed.map fun origin =>
    match origin with
    | .original gate => some gate.val
    | .allocated _ _ _ _ => none
  if !originals.contains (some 0) || !originals.contains (some 1) then
    throw (IO.userError "support sequence reset or lost the original global physical coordinates")
  let some repeated := compile source repeatedNamespaces
    | throw (IO.userError "complete nested-and-ambient ownership fixture rejected")
  let ledger := repeated.ownership
  if repeated.execution.records.map (fun event => event.identity) != [100, 7, 8, 60, 9] then
    throw (IO.userError "ownership namespace did not use the complete computed execution order")
  if repeated.result.implementation.gateCount != 1 ||
      repeated.execution.charged != 3 || repeated.execution.removed != 4 then
    throw (IO.userError "complete execution did not retain all actual allocations and removals")
  if ledger.live != [.allocated 3 0 60 0] ||
      ledger.charged != [.allocated 0 0 30 0, .allocated 0 0 60 0, .allocated 3 0 60 0] ||
      ledger.removed.length != 4 ||
      !ledger.removed.contains (.allocated 0 0 30 0) ||
      !ledger.removed.contains (.allocated 0 0 60 0) ||
      ledger.removed.contains (.allocated 3 0 60 0) then
    throw (IO.userError "nested/ambient allocation names collided or a removed allocation lost its charge")
  for bit in [false, true] do
    let valuation : Valuation 1 := fun _ => bit
    if repeated.result.implementation.candidate.semantics valuation 0 !=
        source.implementation.candidate.semantics valuation 0 ||
        repeated.result.fieldValue valuation 0 != source.fieldValue valuation 0 then
      throw (IO.userError "physical ownership integration changed full program semantics")
  let some identity := compile source []
    | throw (IO.userError "nonempty source identity program rejected")
  if identity.ownership.live != programOriginals source.implementation.gateCount ||
      !identity.ownership.charged.isEmpty || !identity.ownership.removed.isEmpty then
    throw (IO.userError "initial ownership was not derived from the actual source")
  let some empty := compile emptySource
      [⟨4, [], .primitive .normalize⟩, ⟨9, [], .support ⟨[], []⟩⟩]
    | throw (IO.userError "zero-dimensional disconnected actions rejected")
  if empty.execution.records.length != 2 ||
      !empty.ownership.live.isEmpty || !empty.ownership.charged.isEmpty ||
      !empty.ownership.removed.isEmpty then
    throw (IO.userError "zero-dimensional full program omitted actions or fabricated components")
  if (compile source (repeatedNamespaces ++ [⟨101, [9], .primitive (.readFull 1)⟩])).isSome then
    throw (IO.userError "failed final action exposed an ownership certificate for an accepted prefix")
  IO.println "open-program-ownership-regressions-passed"

#print axioms PNP.DirectWire.WireOpenProgram.Transition.local_physical_ownership
#print axioms PNP.DirectWire.WireOpenProgram.Transition.local_charged_origin
#print axioms PNP.DirectWire.WireOpenProgram.bornBefore_mono
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.initial_wellFormed
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.accounted_before
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.origin_before
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.origin_injective
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.liftOrigin_original
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.liftOrigin_allocated
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.liftOrigin_injective
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.lift_originals
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_live
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_charged_length
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_removed_length
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_charge_origin
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_physical_position
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_support_compiled_position
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_partition
#print axioms PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_wellFormed
#print axioms PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_wellFormed
#print axioms PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_charged_length
#print axioms PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_removed_length
#print axioms PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_charge_survives
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_wellFormed
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.physical_ownership
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_origin_injective
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_charge_origin
#print axioms PNP.DirectWire.WireOpenProgram.allocation_namespaces_disjoint

end PNP.Regression.WireOpenProgramOwnership
