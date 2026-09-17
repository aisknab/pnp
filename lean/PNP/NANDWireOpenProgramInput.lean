/-
Copyright (c) 2026 PNP Labs.

Raw mixed programs interleave primitive obligation operations with complete
descendant-support programs. Their global dependency graph includes intrinsic
creation references. Nested event identities stay inside their local programs;
they are never interpreted as ambient creation identities.

This is ordering of offered finite data, not a successful global strategy,
full manuscript profiles, unconditional ZeroSlack or polynomial execution.
-/

import PNP.NANDWireOpenSupportSplice

namespace PNP.DirectWire.WireOpenProgram

inductive Action where
  | primitive (action : WireDescendantHistory.RawAction)
  | support (program : WireDescendantCertificate.RawCertificate)
  deriving Repr, DecidableEq

/-- Intrinsic discharge references are required even when the caller omits them. -/
def Action.creationDependencies : Action → List Nat
  | .primitive (.cancelR6 identity) => [identity]
  | .primitive (.restoreR8 identity) => [identity]
  | .primitive (.realizeR7 identity _) => [identity]
  | _ => []

structure RawEvent where
  identity : Nat
  predecessorIDs : List Nat
  action : Action
  deriving Repr, DecidableEq

def RawEvent.dependencies (event : RawEvent) : List Nat :=
  event.predecessorIDs ++ event.action.creationDependencies

def UniqueIDs (raw : List RawEvent) : Prop :=
  ∀ left right : Fin raw.length,
    (raw.get left).identity = (raw.get right).identity → left = right

def CompleteReferences (raw : List RawEvent) : Prop :=
  ∀ consumer : Fin raw.length, ∀ identity,
    identity ∈ (raw.get consumer).dependencies →
      ∃ producer : Fin raw.length, (raw.get producer).identity = identity

def uniqueIDs (raw : List RawEvent) : Bool :=
  (allFin raw.length).all fun left => (allFin raw.length).all fun right =>
    decide ((raw.get left).identity = (raw.get right).identity → left = right)

theorem uniqueIDs_iff (raw : List RawEvent) : uniqueIDs raw = true ↔ UniqueIDs raw := by
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

def completeReferences (raw : List RawEvent) : Bool :=
  (allFin raw.length).all fun consumer => (raw.get consumer).dependencies.all fun identity =>
    (allFin raw.length).any fun producer => decide ((raw.get producer).identity = identity)

theorem completeReferences_iff (raw : List RawEvent) :
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

def eventGraph (raw : List RawEvent) : PNP.DependencyScheduler.Graph raw.length where
  predecessors := fun consumer => (allFin raw.length).filter fun producer =>
    decide ((raw.get producer).identity ∈ (raw.get consumer).dependencies)

theorem graph_dependency_iff (raw : List RawEvent) (producer consumer : Fin raw.length) :
    (eventGraph raw).Depends producer consumer ↔
      (raw.get producer).identity ∈ (raw.get consumer).dependencies := by
  change producer ∈ (allFin raw.length).filter _ ↔ _
  constructor
  · intro edge
    exact of_decide_eq_true (List.mem_filter.mp edge).2
  · intro dependency
    exact List.mem_filter.mpr ⟨mem_allFin producer,
      by simpa only [decide_eq_true_eq] using dependency⟩

/-- The order and its validation evidence are computed, never caller inputs. -/
structure OrderedEvents (raw : List RawEvent) where
  unique : UniqueIDs raw
  references : CompleteReferences raw
  schedule : PNP.DependencyScheduler.Schedule (eventGraph raw)

def OrderedEvents.order {raw : List RawEvent} (ordered : OrderedEvents raw) :
    List (Fin raw.length) := ordered.schedule.order

theorem OrderedEvents.order_complete {raw : List RawEvent} (ordered : OrderedEvents raw)
    (event : Fin raw.length) : event ∈ ordered.order := ordered.schedule.order_complete event

theorem OrderedEvents.order_nodup {raw : List RawEvent} (ordered : OrderedEvents raw) :
    ordered.order.Nodup := ordered.schedule.order_nodup

theorem OrderedEvents.order_length {raw : List RawEvent} (ordered : OrderedEvents raw) :
    ordered.order.length = raw.length := ordered.schedule.order_length

theorem OrderedEvents.identities_nodup {raw : List RawEvent} (ordered : OrderedEvents raw) :
    (ordered.order.map (fun event => (raw.get event).identity)).Nodup :=
  List.Pairwise.map (fun event => (raw.get event).identity)
    (fun left right different same => different (ordered.unique left right same))
    ordered.order_nodup

def orderEvents (raw : List RawEvent) : Option (OrderedEvents raw) :=
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

theorem orderEvents_success_iff (raw : List RawEvent) :
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

theorem orderEvents_failure_iff (raw : List RawEvent) :
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

end PNP.DirectWire.WireOpenProgram
