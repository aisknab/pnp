import PNP.NANDWireOpenProgram

namespace PNP.Regression.WireOpenProgram

open PNP.DirectWire WireOpenProgram

example {inputs outputs fields : Nat} (source : WireCarrier inputs outputs fields)
    (raw : List RawEvent) :
    (∃ program, compile source raw = some program) ↔
      ∃ ordered, orderEvents raw = some ordered ∧
        ∃ result, execute (WireObligationHistory.State.initial source)
            (ordered.order.map raw.get) = some result ∧ result.1.isClosed = true :=
  compile_exists_iff source raw

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    {raw : List RawEvent} (program : CompiledProgram source raw)
    (valuation : Valuation inputs) (field : Fin fields) :
    program.result.fieldValue valuation field = source.fieldValue valuation field :=
  program.full_field valuation field

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    {raw : List RawEvent} (program : CompiledProgram source raw) :
    program.execution.CreationsClosed := program.creation_lifecycle

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    {raw : List RawEvent} (program : CompiledProgram source raw) (labels : Fin inputs → Nat) :
    program.state.CausalInvariant labels := program.causalInvariant labels

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

private def emptySource : WireCarrier 0 0 0 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 0 0) ⟨Fin.elim0⟩).toImplementation
    source := Fin.elim0 }

/-- Both local programs reuse the ambient creation's numeral. It is a distinct namespace. -/
private def removeGate (gate : Nat) : WireDescendantCertificate.RawCertificate :=
  ⟨[.gate gate], [⟨0, [.gate 0], [⟨7, [], .normalize⟩]⟩]⟩

/-- Deliberately not supplied in execution order. Each support changes the actual carrier. -/
private def raw : List RawEvent :=
  [⟨50, [40], .primitive (.readFull 0)⟩,
   ⟨30, [20], .support (removeGate 0)⟩,
   ⟨40, [30], .primitive (.restoreR8 7)⟩,
   ⟨7, [], .primitive (.createR5 0)⟩,
   ⟨20, [7], .support (removeGate 1)⟩]

private def replaceAction (identity : Nat) (action : Action) : List RawEvent :=
  raw.map fun event => if event.identity = identity then {event with action := action} else event

#eval show IO Unit from do
  let some program := compile source raw
    | throw (IO.userError "complete mixed program rejected valid carried obligations")
  let records := program.execution.records
  if records.map (fun event => event.identity) != [7, 20, 30, 40, 50] then
    throw (IO.userError "dependency scheduler omitted, repeated or misordered an actual action")
  if program.result.implementation.gateCount != 1 ||
      program.execution.charged != 1 || program.execution.removed != 2 then
    throw (IO.userError "mixed program did not count actual restoration and both physical removals")
  let [created, first, second, restored, read] := records
    | throw (IO.userError "complete trace did not contain all five actions")
  if first.before.implementation.gateCount != 2 || first.after.implementation.gateCount != 1 ||
      second.before.implementation.gateCount != 1 || second.after.implementation.gateCount != 0 then
    throw (IO.userError "successive supports were not decoded against the actual descendants")
  if first.discharge.isSome || second.discharge.isSome || first.creation.isSome ||
      second.creation.isSome || read.fullRead.isNone || created.creation.isNone then
    throw (IO.userError "support or read was mistaken for a primitive creation or full discharge")
  let some discharge := restored.discharge
    | throw (IO.userError "real restoration lost its full discharge record")
  if discharge.creation.identity != 7 || discharge.creation.carrier.implementation.gateCount != 2 then
    throw (IO.userError "final discharge did not refer to the original captured creation")
  for bit in [false, true] do
    let valuation : Valuation 1 := fun _ => bit
    if program.result.implementation.candidate.semantics valuation 0 !=
        source.implementation.candidate.semantics valuation 0 ||
        program.result.fieldValue valuation 0 != source.fieldValue valuation 0 ||
        discharge.carrier.fieldValue valuation discharge.field !=
          discharge.creation.carrier.fieldValue valuation discharge.field then
      throw (IO.userError "final full-mode semantics or actual discharge witness changed")
  let openProgram : List RawEvent :=
    [⟨7, [], .primitive (.createR5 0)⟩, ⟨20, [7], .support (removeGate 1)⟩]
  let earlyRead : List RawEvent :=
    raw.map fun event =>
      if event.identity = 40 then {event with predecessorIDs := [50]}
      else if event.identity = 50 then {event with predecessorIDs := [30]} else event
  let missingReference := raw.map fun event =>
    if event.identity = 7 then {event with predecessorIDs := [999]} else event
  let cyclic := raw.map fun event =>
    if event.identity = 7 then {event with predecessorIDs := [50]} else event
  let nestedMissingCreation : WireDescendantCertificate.RawCertificate :=
    ⟨[.gate 1], [⟨0, [.gate 0], [⟨8, [], .restoreR8 7⟩]⟩]⟩
  let nestedFailedTail : WireDescendantCertificate.RawCertificate :=
    { removeGate 1 with stages := (removeGate 1).stages ++ [⟨0, [.gate 99], []⟩] }
  for rejected in
      [openProgram, earlyRead, missingReference, cyclic,
       raw ++ [⟨7, [], .primitive .normalize⟩],
       replaceAction 7 (.primitive (.createR5 1)),
       replaceAction 40 (.primitive (.cancelR6 7)),
       replaceAction 40 (.primitive (.restoreR8 99)),
       replaceAction 40 (.primitive (.realizeR7 99 [])),
       replaceAction 30 (.primitive (.createR5 0)),
       replaceAction 20 (.support ⟨[.gate 99], []⟩),
       replaceAction 20 (.support nestedMissingCreation),
       replaceAction 20 (.support nestedFailedTail),
       raw ++ [⟨60, [50], .primitive (.readFull 1)⟩]] do
    if (compile source rejected).isSome then
      throw (IO.userError "invalid full program returned a certificate or a successful prefix")
  let some cancelled := compile aliasSource
      [⟨7, [], .primitive (.createR5 0)⟩, ⟨8, [], .primitive (.cancelR6 7)⟩]
    | throw (IO.userError "actual full-mode representative cancellation rejected")
  if cancelled.execution.charged != 0 || !cancelled.state.isClosed then
    throw (IO.userError "full representative cancellation fabricated a materializer or left an obligation")
  let some empty := compile emptySource []
    | throw (IO.userError "empty zero-dimensional source program rejected")
  if empty.execution.records.length != 0 then
    throw (IO.userError "empty program fabricated an action")
  let some disconnected := compile emptySource
      [⟨4, [], .primitive .normalize⟩, ⟨9, [], .support ⟨[], []⟩⟩]
    | throw (IO.userError "disconnected zero-dimensional actions rejected")
  if disconnected.execution.records.length != 2 then
    throw (IO.userError "a disconnected action was silently omitted")
  IO.println "open-program-regressions-passed"

#print axioms PNP.DirectWire.WireOpenProgram.uniqueIDs_iff
#print axioms PNP.DirectWire.WireOpenProgram.completeReferences_iff
#print axioms PNP.DirectWire.WireOpenProgram.graph_dependency_iff
#print axioms PNP.DirectWire.WireOpenProgram.OrderedEvents.order_complete
#print axioms PNP.DirectWire.WireOpenProgram.OrderedEvents.order_nodup
#print axioms PNP.DirectWire.WireOpenProgram.OrderedEvents.order_length
#print axioms PNP.DirectWire.WireOpenProgram.OrderedEvents.identities_nodup
#print axioms PNP.DirectWire.WireOpenProgram.orderEvents_success_iff
#print axioms PNP.DirectWire.WireOpenProgram.orderEvents_failure_iff
#print axioms PNP.DirectWire.WireOpenProgram.Transition.charged_eq
#print axioms PNP.DirectWire.WireOpenProgram.Transition.removed_eq
#print axioms PNP.DirectWire.WireOpenProgram.Transition.dischargeRecord_binding
#print axioms PNP.DirectWire.WireOpenProgram.Transition.pending_persists_or_discharged
#print axioms PNP.DirectWire.WireOpenProgram.Transition.created_pending
#print axioms PNP.DirectWire.WireOpenProgram.Transition.causalInvariant
#print axioms PNP.DirectWire.WireOpenProgram.execute_failed_tail
#print axioms PNP.DirectWire.WireOpenProgram.Execution.total_charge
#print axioms PNP.DirectWire.WireOpenProgram.Execution.total_removed
#print axioms PNP.DirectWire.WireOpenProgram.Execution.record_identities
#print axioms PNP.DirectWire.WireOpenProgram.Execution.pending_persists_or_discharged
#print axioms PNP.DirectWire.WireOpenProgram.Execution.creationsClosed_of_finalClosed
#print axioms PNP.DirectWire.WireOpenProgram.Execution.causalInvariant
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.closed
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.full_output
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.full_field
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.gate_balance
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.creation_lifecycle
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.executed_count
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.executed_identities_nodup
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.dependency_before
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.causalInvariant
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.output_causal_bound
#print axioms PNP.DirectWire.WireOpenProgram.CompiledProgram.field_causal_bound
#print axioms PNP.DirectWire.WireOpenProgram.compile_exists_iff
#print axioms PNP.DirectWire.WireOpenProgram.compile_none_iff

end PNP.Regression.WireOpenProgram
