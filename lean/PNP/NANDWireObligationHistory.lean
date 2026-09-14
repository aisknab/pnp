/-
Copyright (c) 2026 PNP Labs.

Raw wire-history events name actual finite coordinates and event identities,
never a supplied order, witness, closed ledger, materializer or gate charge.
Validate every identity and dependency before computing the event order.

Dependency ordering is not semantic lifecycle admissibility, confluence,
complete Package E, unconditional ZeroSlack or polynomial execution.
-/

import PNP.FiniteDependencyScheduler
import PNP.NANDWireObligationHistoryState

namespace PNP.DirectWire.WireObligationHistory

variable {inputs outputs fields : Nat}

inductive Action (fields : Nat) where
  | createR5 (field : Fin fields)
  | cancelR6 (creationID : Nat)
  | restoreR8 (creationID : Nat)
  | normalize
  | readFull (field : Fin fields)
  deriving Repr, DecidableEq

/-- A discharge's reference is a dependency even if omitted from the explicit list. -/
def Action.creationDependencies : Action fields → List Nat
  | .cancelR6 identity => [identity]
  | .restoreR8 identity => [identity]
  | _ => []

structure RawEvent (fields : Nat) where
  identity : Nat
  predecessorIDs : List Nat
  action : Action fields
  deriving Repr, DecidableEq

def RawEvent.dependencies (event : RawEvent fields) : List Nat :=
  event.predecessorIDs ++ event.action.creationDependencies

def UniqueIDs (raw : List (RawEvent fields)) : Prop :=
  ∀ left right : Fin raw.length,
    (raw.get left).identity = (raw.get right).identity → left = right

def CompleteReferences (raw : List (RawEvent fields)) : Prop :=
  ∀ consumer : Fin raw.length, ∀ identity,
    identity ∈ (raw.get consumer).dependencies →
      ∃ producer : Fin raw.length, (raw.get producer).identity = identity

/-- A finite all-pairs check derives injectivity of the raw identity map. -/
def uniqueIDs (raw : List (RawEvent fields)) : Bool :=
  (allFin raw.length).all fun left => (allFin raw.length).all fun right =>
    decide ((raw.get left).identity = (raw.get right).identity → left = right)

theorem uniqueIDs_iff (raw : List (RawEvent fields)) : uniqueIDs raw = true ↔ UniqueIDs raw := by
  constructor
  · intro accepted left right same
    have row := (List.all_eq_true.mp accepted) left (mem_allFin left)
    have entry := (List.all_eq_true.mp row) right (mem_allFin right)
    exact (of_decide_eq_true entry) same
  · intro unique
    apply List.all_eq_true.mpr
    intro left _member
    apply List.all_eq_true.mpr
    intro right _member
    simpa only [decide_eq_true_eq] using unique left right

/-- Missing explicit or intrinsic references reject; they are never filtered away. -/
def completeReferences (raw : List (RawEvent fields)) : Bool :=
  (allFin raw.length).all fun consumer => (raw.get consumer).dependencies.all fun identity =>
    (allFin raw.length).any fun producer => decide ((raw.get producer).identity = identity)

theorem completeReferences_iff (raw : List (RawEvent fields)) :
    completeReferences raw = true ↔ CompleteReferences raw := by
  constructor
  · intro accepted consumer identity dependency
    have row := (List.all_eq_true.mp accepted) consumer (mem_allFin consumer)
    have present := (List.all_eq_true.mp row) identity dependency
    obtain ⟨producer, _member, same⟩ := List.any_eq_true.mp present
    exact ⟨producer, of_decide_eq_true same⟩
  · intro complete
    apply List.all_eq_true.mpr
    intro consumer _member
    apply List.all_eq_true.mpr
    intro identity dependency
    obtain ⟨producer, same⟩ := complete consumer identity dependency
    apply List.any_eq_true.mpr
    exact ⟨producer, mem_allFin producer, by simpa only [decide_eq_true_eq] using same⟩

/-- Index all actual predecessor events; duplicate mentions do not create new events. -/
def eventGraph (raw : List (RawEvent fields)) : PNP.DependencyScheduler.Graph raw.length where
  predecessors := fun consumer => (allFin raw.length).filter fun producer =>
    decide ((raw.get producer).identity ∈ (raw.get consumer).dependencies)

theorem graph_dependency_iff (raw : List (RawEvent fields)) (producer consumer : Fin raw.length) :
    (eventGraph raw).Depends producer consumer ↔
      (raw.get producer).identity ∈ (raw.get consumer).dependencies := by
  change producer ∈ (allFin raw.length).filter _ ↔ _
  constructor
  · intro edge
    exact of_decide_eq_true (List.mem_filter.mp edge).2
  · intro dependency
    exact List.mem_filter.mpr ⟨mem_allFin producer,
      by simpa only [decide_eq_true_eq] using dependency⟩

/-- Validation evidence and a computed full order, not a supplied input certificate. -/
structure OrderedEvents (raw : List (RawEvent fields)) where
  unique : UniqueIDs raw
  references : CompleteReferences raw
  schedule : PNP.DependencyScheduler.Schedule (eventGraph raw)

def OrderedEvents.order {raw : List (RawEvent fields)} (ordered : OrderedEvents raw) :
    List (Fin raw.length) := ordered.schedule.order

theorem OrderedEvents.order_complete {raw : List (RawEvent fields)} (ordered : OrderedEvents raw)
    (event : Fin raw.length) : event ∈ ordered.order := ordered.schedule.order_complete event

theorem OrderedEvents.order_nodup {raw : List (RawEvent fields)} (ordered : OrderedEvents raw) :
    ordered.order.Nodup := ordered.schedule.order_nodup

theorem OrderedEvents.order_length {raw : List (RawEvent fields)} (ordered : OrderedEvents raw) :
    ordered.order.length = raw.length := ordered.schedule.order_length

theorem OrderedEvents.identities_nodup {raw : List (RawEvent fields)} (ordered : OrderedEvents raw) :
    (ordered.order.map (fun event => (raw.get event).identity)).Nodup :=
  List.Pairwise.map (fun event => (raw.get event).identity)
    (fun left right different same => different (ordered.unique left right same))
    ordered.order_nodup

/-- Only raw identities, dependencies and operations enter this ordering constructor. -/
def orderEvents (raw : List (RawEvent fields)) : Option (OrderedEvents raw) :=
  if unique : uniqueIDs raw = true then
    if complete : completeReferences raw = true then
      match PNP.DependencyScheduler.compile (eventGraph raw) with
      | none => none
      | some schedule => some
          { unique := (uniqueIDs_iff raw).1 unique
            references := (completeReferences_iff raw).1 complete
            schedule := schedule }
    else none
  else none

/-- This is ordering completeness, not acceptance of an arbitrary semantic lifecycle. -/
theorem orderEvents_success_iff (raw : List (RawEvent fields)) :
    (∃ ordered, orderEvents raw = some ordered) ↔
      UniqueIDs raw ∧ CompleteReferences raw ∧ WellFounded (eventGraph raw).Depends := by
  constructor
  · rintro ⟨ordered, _accepted⟩
    exact ⟨ordered.unique, ordered.references, ordered.schedule.wellFounded⟩
  · rintro ⟨unique, references, acyclic⟩
    have uniqueCheck := (uniqueIDs_iff raw).2 unique
    have referenceCheck := (completeReferences_iff raw).2 references
    obtain ⟨schedule, compiled⟩ := (PNP.DependencyScheduler.compile_success_iff (eventGraph raw)).2 acyclic
    refine ⟨⟨unique, references, schedule⟩, ?_⟩
    unfold orderEvents
    rw [dif_pos uniqueCheck, dif_pos referenceCheck, compiled]

theorem orderEvents_failure_iff (raw : List (RawEvent fields)) :
    orderEvents raw = none ↔
      ¬(UniqueIDs raw ∧ CompleteReferences raw ∧ WellFounded (eventGraph raw).Depends) := by
  constructor
  · intro rejected valid
    obtain ⟨ordered, accepted⟩ := (orderEvents_success_iff raw).2 valid
    rw [rejected] at accepted
    cases accepted
  · intro invalid
    cases found : orderEvents raw with
    | none => rfl
    | some ordered =>
        exact False.elim (invalid ((orderEvents_success_iff raw).1 ⟨ordered, found⟩))

end PNP.DirectWire.WireObligationHistory
