import PNP

/-!
General kernel type checks and bounded executable regressions for M263.
Runtime fixtures are regression evidence, never theorem authority.
-/

namespace PNP.Regression.WireObligationHistory

open PNP.DirectWire PNP.DirectWire.WireObligationHistory

example {nodes : Nat} (graph : PNP.DependencyScheduler.Graph nodes) :
    (∃ schedule, PNP.DependencyScheduler.compile graph = some schedule) ↔
      WellFounded graph.Depends :=
  PNP.DependencyScheduler.compile_success_iff graph

example {nodes : Nat} (graph : PNP.DependencyScheduler.Graph nodes) :
    PNP.DependencyScheduler.compile graph = none ↔ ¬WellFounded graph.Depends :=
  PNP.DependencyScheduler.compile_failure_iff graph

example {nodes : Nat} {graph : PNP.DependencyScheduler.Graph nodes}
    (schedule : PNP.DependencyScheduler.Schedule graph) :
    schedule.order.Nodup ∧ schedule.order.length = nodes ∧
      (∀ node, node ∈ schedule.order) :=
  ⟨schedule.order_nodup, schedule.order_length, schedule.order_complete⟩

example {fields : Nat} (raw : List (RawEvent fields)) :
    (∃ ordered, orderEvents raw = some ordered) ↔
      UniqueIDs raw ∧ CompleteReferences raw ∧ WellFounded (eventGraph raw).Depends :=
  orderEvents_success_iff raw

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    {raw : List (RawEvent fields)} (history : ClosedHistory source raw)
    (valuation : Valuation inputs) (field : Fin fields) :
    history.state.current.fieldValue valuation field = source.fieldValue valuation field :=
  history.full_field valuation field

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    {raw : List (RawEvent fields)} (history : ClosedHistory source raw)
    (valuation : Valuation inputs) (output : Fin outputs) :
    history.state.current.implementation.candidate.semantics valuation output =
      source.implementation.candidate.semantics valuation output :=
  history.full_output valuation output

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    {raw : List (RawEvent fields)} (history : ClosedHistory source raw) :
    history.state.current.implementation.gateCount + history.execution.removed =
      source.implementation.gateCount + history.execution.charged := history.gate_balance

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    {raw : List (RawEvent fields)} (history : ClosedHistory source raw) :
    history.execution.CreationsClosed := history.creation_lifecycle

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    {raw : List (RawEvent fields)} (history : ClosedHistory source raw)
    (producer consumer : Fin raw.length)
    (dependency : (raw.get producer).identity ∈ (raw.get consumer).dependencies) :
    (history.ordered.schedule.position producer).val <
      (history.ordered.schedule.position consumer).val :=
  history.dependency_before producer consumer dependency

private def fanIn : PNP.DependencyScheduler.Graph 4 where
  predecessors := fun node => if node.val = 0 then [1, 2, 3, 1] else []

private def stuckAfterProgress : PNP.DependencyScheduler.Graph 3 where
  predecessors := fun node => if node.val = 0 then [1]
    else if node.val = 1 then [0] else []

private def selfLoop : PNP.DependencyScheduler.Graph 1 where
  predecessors := fun _ => [0]

private def emptyGraph : PNP.DependencyScheduler.Graph 0 where
  predecessors := Fin.elim0

private def forwardRestore : List (RawEvent 1) :=
  [⟨20, [], .restoreR8 10⟩, ⟨10, [], .createR5 0⟩]

private def duplicateIdentity : List (RawEvent 1) :=
  [⟨10, [], .createR5 0⟩, ⟨10, [], .readFull 0⟩]

private def missingExplicit : List (RawEvent 0) := [⟨10, [30], .normalize⟩]
private def missingIntrinsic : List (RawEvent 0) := [⟨10, [], .restoreR8 30⟩]
private def cyclic : List (RawEvent 0) :=
  [⟨10, [20], .normalize⟩, ⟨20, [10], .normalize⟩]
private def selfReference : List (RawEvent 0) := [⟨10, [], .cancelR6 10⟩]

#eval show IO Unit from do
  match PNP.DependencyScheduler.compile fanIn with
  | none => throw (IO.userError "acyclic fan-in graph was rejected")
  | some schedule =>
      if schedule.order.map Fin.val != [1, 2, 3, 0] then
        throw (IO.userError "computed order lost a predecessor or duplicated a node")
  if (PNP.DependencyScheduler.compile stuckAfterProgress).isSome ||
      (PNP.DependencyScheduler.compile selfLoop).isSome then
    throw (IO.userError "cyclic or stuck remainder was accepted")
  match PNP.DependencyScheduler.compile emptyGraph with
  | none => throw (IO.userError "empty graph was rejected")
  | some schedule =>
      if !schedule.order.isEmpty then throw (IO.userError "empty graph fabricated an event")
  let order := (orderEvents forwardRestore).map
    (fun (checked : OrderedEvents forwardRestore) => checked.order.map Fin.val)
  if order != some [1, 0] then throw (IO.userError "intrinsic creation dependency was not ordered")
  if (orderEvents duplicateIdentity).isSome then throw (IO.userError "duplicate identity accepted")
  if (orderEvents missingExplicit).isSome then throw (IO.userError "missing explicit reference accepted")
  if (orderEvents missingIntrinsic).isSome then throw (IO.userError "missing intrinsic reference accepted")
  if (orderEvents cyclic).isSome then throw (IO.userError "cycle accepted")
  if (orderEvents selfReference).isSome then throw (IO.userError "self-reference accepted")
  if (orderEvents ([] : List (RawEvent 0))).isNone then throw (IO.userError "empty history order rejected")
  IO.println "M263 dependency-ordering-regressions-passed"

private def historyNandProgram : Program 2 1 := .snoc .empty ⟨.input 0, .input 1⟩

private def fieldsOnly : WireCarrier 2 0 1 :=
  { implementation := (Candidate.ofDirectWireWord historyNandProgram
      (⟨Fin.elim0⟩ : DirectWireWord 2 1 0)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def withOutput : WireCarrier 2 1 1 :=
  { implementation := (Candidate.ofDirectWireWord historyNandProgram
      (⟨fun _ => .gate ⟨0, by decide⟩⟩ : DirectWireWord 2 1 1)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def rebasedShared : WireCarrier 2 0 2 :=
  { implementation := (Candidate.ofDirectWireWord (historyNandProgram.snoc ⟨.input 0, .input 1⟩)
      (⟨Fin.elim0⟩ : DirectWireWord 2 2 0)).toImplementation
    source := fun _ => .gate ⟨1, by decide⟩ }

private def emptyCarrier : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 0 0)
      (⟨Fin.elim0⟩ : DirectWireWord 0 0 0)).toImplementation
    source := Fin.elim0 }

private def restoreAfterNormalize : List (RawEvent 1) :=
  [⟨30, [20], .restoreR8 10⟩, ⟨20, [10], .normalize⟩, ⟨10, [], .createR5 0⟩]

private def repeatedField : List (RawEvent 1) :=
  [⟨10, [], .createR5 0⟩, ⟨20, [], .restoreR8 10⟩, ⟨30, [20], .createR5 0⟩,
    ⟨40, [30], .normalize⟩, ⟨50, [40], .restoreR8 30⟩]

private def rebasedCancel : List (RawEvent 2) :=
  [⟨10, [], .createR5 0⟩, ⟨20, [10], .normalize⟩, ⟨30, [20], .cancelR6 10⟩,
    ⟨40, [30], .readFull 0⟩]

private def creationSize {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    (record : EventRecord source) : Option Nat :=
  match record.creation with
  | none => none
  | some binding => some binding.2.carrier.implementation.gateCount

#eval show IO Unit from do
  let some restored := compileHistory fieldsOnly restoreAfterNormalize
    | throw (IO.userError "dependency-ordered physical restoration rejected")
  if restored.execution.records.map (fun (record : EventRecord fieldsOnly) => record.identity) != [10, 20, 30] then
    throw (IO.userError "not every event executed in dependency order")
  if restored.execution.charged != 1 || restored.execution.removed != 1 ||
      restored.state.current.implementation.gateCount != 1 then
    throw (IO.userError "actual normalization and restoration charges changed")
  if !restored.state.current.fieldValue (fun _ => false) 0 ||
      restored.state.current.fieldValue (fun _ => true) 0 then
    throw (IO.userError "restoration substituted quotient padding for the full NAND value")
  let some repeated := compileHistory fieldsOnly repeatedField
    | throw (IO.userError "fresh creation identity on reused field rejected")
  if repeated.execution.records.filterMap creationSize != [1, 2] then
    throw (IO.userError "creation snapshots did not capture the evolving physical carriers")
  if repeated.execution.charged != 2 || repeated.execution.removed != 2 ||
      repeated.state.current.implementation.gateCount != 1 then
    throw (IO.userError "separate restorations acquired free cross-snapshot sharing")
  let some cancelled := compileHistory rebasedShared rebasedCancel
    | throw (IO.userError "visible R6 cancellation after physical rebasing rejected")
  if cancelled.execution.charged != 0 || cancelled.execution.removed != 1 ||
      cancelled.state.current.implementation.gateCount != 1 then
    throw (IO.userError "R6 did not retain the actually normalized shared source")
  if !cancelled.state.current.fieldValue (fun _ => false) 0 ||
      cancelled.state.current.fieldValue (fun _ => true) 0 then
    throw (IO.userError "rebased cancellation lost its original full value")
  let some ordinary := compileHistory withOutput restoreAfterNormalize
    | throw (IO.userError "history with an ordinary output rejected")
  if ordinary.execution.charged != 1 || ordinary.execution.removed != 0 ||
      ordinary.state.current.implementation.gateCount != 2 then
    throw (IO.userError "ordinary output dependency was removed or restoration was uncharged")
  if !ordinary.state.current.implementation.candidate.semantics (fun _ => false) 0 ||
      ordinary.state.current.implementation.candidate.semantics (fun _ => true) 0 then
    throw (IO.userError "ordinary output lost its full value")
  for invalid in [
      [⟨10, [], .createR5 0⟩],
      [⟨10, [], .createR5 0⟩, ⟨20, [10], .readFull 0⟩, ⟨30, [20], .restoreR8 10⟩],
      [⟨10, [], .normalize⟩, ⟨20, [], .restoreR8 10⟩],
      [⟨10, [], .createR5 0⟩, ⟨20, [], .restoreR8 10⟩, ⟨30, [20], .restoreR8 10⟩],
      [⟨10, [], .createR5 0⟩, ⟨20, [10], .createR5 0⟩, ⟨30, [20], .restoreR8 10⟩],
      [⟨10, [], .createR5 0⟩, ⟨20, [], .cancelR6 10⟩],
      [⟨10, [], .createR5 0⟩, ⟨20, [], .restoreR8 10⟩, ⟨30, [20], .createR5 0⟩,
        ⟨40, [30], .restoreR8 10⟩, ⟨50, [40], .restoreR8 30⟩]
    ] do
    if (compileHistory fieldsOnly invalid).isSome then
      throw (IO.userError "invalid, stale-identity or incompletely discharged lifecycle accepted")
  if (compileHistory fieldsOnly []).isNone then
    throw (IO.userError "empty full history rejected")
  let some empty := compileHistory emptyCarrier [⟨10, [], .normalize⟩]
    | throw (IO.userError "zero-dimensional physical history rejected")
  if empty.state.current.implementation.gateCount != 0 || empty.execution.records.length != 1 then
    throw (IO.userError "zero-dimensional history fabricated gates or lost an event")
  IO.println "M263 physical-history-execution-regressions-passed"

end PNP.Regression.WireObligationHistory
