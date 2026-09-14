/-
Copyright (c) 2026 PNP Labs.

Computed scheduling for arbitrary finite dependency lists. An input contains
edges, not a rank or a successful ordering. A nonempty stuck remainder rejects.
This is an event-ordering component, not a physical circuit, a full obligation
history, Package E, or a polynomial execution theorem.
-/

import PNP.NANDTopologicalCompiler

namespace PNP.DependencyScheduler

structure Graph (nodes : Nat) where
  predecessors : Fin nodes → List (Fin nodes)

def Graph.Depends {nodes : Nat} (graph : Graph nodes)
    (producer consumer : Fin nodes) : Prop :=
  producer ∈ graph.predecessors consumer

/-- The inverse order is built with the positions, never supplied by a caller. -/
structure State {nodes : Nat} (graph : Graph nodes) where
  count : Nat
  position : Fin nodes → Option (Fin count)
  nodeAt : Fin count → Fin nodes
  remaining : List (Fin nodes)
  remainingNodup : remaining.Nodup
  pending : ∀ node, node ∈ remaining ↔ position node = none
  accounting : count + remaining.length = nodes
  atPosition : ∀ node index, position node = some index → nodeAt index = node
  positionAt : ∀ index, position (nodeAt index) = some index
  ordered : ∀ node index, position node = some index →
    ∀ producer, graph.Depends producer node →
      ∃ earlier, position producer = some earlier ∧ earlier.val < index.val

private theorem finRange_nodup (nodes : Nat) : (List.finRange nodes).Nodup := by
  induction nodes with
  | zero =>
      rw [List.finRange_zero]
      exact List.nodup_nil
  | succ nodes ih =>
      rw [List.finRange_succ, List.nodup_cons]
      constructor
      · intro member
        obtain ⟨index, _present, same⟩ := List.mem_map.mp member
        have impossible := congrArg Fin.val same
        change index.val + 1 = 0 at impossible
        omega
      · exact List.Pairwise.map Fin.succ
          (fun left right different same =>
            different (Fin.ext (Nat.succ.inj (congrArg Fin.val same)))) ih

def State.initial {nodes : Nat} (graph : Graph nodes) : State graph :=
  { count := 0
    position := fun _ => none
    nodeAt := Fin.elim0
    remaining := List.finRange nodes
    remainingNodup := finRange_nodup nodes
    pending := by intro node; simp
    accounting := by simp
    atPosition := by intro node index impossible; cases impossible
    positionAt := by intro index; exact Fin.elim0 index
    ordered := by intro node index impossible; cases impossible }

def State.ready {nodes : Nat} {graph : Graph nodes}
    (state : State graph) (node : Fin nodes) : Bool :=
  (graph.predecessors node).all (fun producer => (state.position producer).isSome)

structure ReadyStep {nodes : Nat} {graph : Graph nodes} (state : State graph) where
  node : Fin nodes
  member : node ∈ state.remaining
  ready : ∀ producer, graph.Depends producer node →
    (state.position producer).isSome = true

private theorem erase_length {nodes : Nat}
    (items : List (Fin nodes)) (erased : Fin nodes) (member : erased ∈ items) :
    (items.erase erased).length + 1 = items.length := by
  revert member
  induction items with
  | nil => intro member; cases member
  | cons head tail ih =>
      intro member
      by_cases same : head = erased
      · subst head
        rw [List.erase_cons_head, List.length_cons]
      · have tailMember := (List.mem_cons.mp member).resolve_left
          (fun equal => same equal.symm)
        rw [List.erase_cons_tail (fun equal => same (eq_of_beq equal)),
          List.length_cons, List.length_cons]
        have exactTail := ih tailMember
        omega

private theorem erase_mem {nodes : Nat}
    (items : List (Fin nodes)) (erased item : Fin nodes) (distinct : items.Nodup) :
    item ∈ items.erase erased ↔ item ≠ erased ∧ item ∈ items := by
  revert distinct
  induction items with
  | nil =>
      intro _distinct
      simp only [List.erase_nil, List.not_mem_nil, and_false]
  | cons head tail ih =>
      intro distinct
      have headTail := List.nodup_cons.mp distinct
      by_cases same : head = erased
      · subst head
        rw [List.erase_cons_head]
        constructor
        · intro inTail
          constructor
          · intro equal
            subst item
            exact headTail.1 inTail
          · exact List.mem_cons.mpr (Or.inr inTail)
        · intro both
          exact (List.mem_cons.mp both.2).resolve_left both.1
      · rw [List.erase_cons_tail (fun equal => same (eq_of_beq equal))]
        rw [List.mem_cons, ih headTail.2, List.mem_cons]
        constructor
        · intro present
          rcases present with atHead | inTail
          · exact ⟨fun equal => same (atHead.symm.trans equal), Or.inl atHead⟩
          · exact ⟨inTail.1, Or.inr inTail.2⟩
        · intro both
          rcases both.2 with atHead | inTail
          · exact Or.inl atHead
          · exact Or.inr ⟨both.1, inTail⟩

def ReadyStep.apply {nodes : Nat} {graph : Graph nodes} {state : State graph}
    (step : ReadyStep state) : State graph := by
  let binding : Fin nodes → Option (Fin (state.count + 1)) := fun node =>
    if node = step.node then some (Fin.last state.count)
    else (state.position node).map Fin.castSucc
  let ordering : Fin (state.count + 1) → Fin nodes := fun index =>
    if within : index.val < state.count then state.nodeAt ⟨index.val, within⟩
    else step.node
  have selectedNone : state.position step.node = none :=
    (state.pending step.node).1 step.member
  have oldBound (node : Fin nodes) (index : Fin state.count)
      (placed : state.position node = some index) :
      binding node = some index.castSucc := by
    have different : node ≠ step.node := by
      intro same
      subst node
      rw [selectedNone] at placed
      cases placed
    simp only [binding, if_neg different, placed, Option.map_some]
  have orderingOld (index : Fin state.count) : ordering index.castSucc = state.nodeAt index := by
    change (if within : index.val < state.count then
      state.nodeAt ⟨index.val, within⟩ else step.node) = state.nodeAt index
    rw [dif_pos index.isLt]
  have orderingLast : ordering (Fin.last state.count) = step.node := by
    change (if within : state.count < state.count then
      state.nodeAt ⟨state.count, within⟩ else step.node) = step.node
    rw [dif_neg (Nat.lt_irrefl state.count)]
  refine
    { count := state.count + 1
      position := binding
      nodeAt := ordering
      remaining := state.remaining.erase step.node
      remainingNodup := List.Nodup.erase step.node state.remainingNodup
      pending := ?_
      accounting := ?_
      atPosition := ?_
      positionAt := ?_
      ordered := ?_ }
  · intro node
    rw [erase_mem state.remaining step.node node state.remainingNodup]
    by_cases same : node = step.node
    · simp only [same, ne_eq, not_true_eq_false, false_and, binding, if_pos rfl,
        reduceCtorEq]
    · rw [and_iff_right same, state.pending node]
      simp only [binding, if_neg same]
      cases state.position node <;> simp
  · have erased := erase_length state.remaining step.node step.member
    have original := state.accounting
    omega
  · intro node index placed
    by_cases chosen : node = step.node
    · subst node
      simp only [binding, if_pos rfl, Option.some.injEq] at placed
      subst index
      exact orderingLast
    · simp only [binding, if_neg chosen] at placed
      cases oldAt : state.position node with
      | none => simp only [oldAt, Option.map_none] at placed; cases placed
      | some oldIndex =>
          simp only [oldAt, Option.map_some, Option.some.injEq] at placed
          subst index
          rw [orderingOld]
          exact state.atPosition node oldIndex oldAt
  · intro index
    by_cases within : index.val < state.count
    · let oldIndex : Fin state.count := ⟨index.val, within⟩
      have indexEq : oldIndex.castSucc = index := Fin.ext rfl
      rw [← indexEq, orderingOld]
      exact oldBound (state.nodeAt oldIndex) oldIndex (state.positionAt oldIndex)
    · have indexEq : index = Fin.last state.count := by
        apply Fin.ext
        have bounded := index.isLt
        change index.val = state.count
        omega
      rw [indexEq, orderingLast]
      simp only [binding, if_pos rfl]
  · intro node index placed producer edge
    by_cases chosen : node = step.node
    · subst node
      simp only [binding, if_pos rfl, Option.some.injEq] at placed
      subst index
      have ready := step.ready producer edge
      cases earlierAt : state.position producer with
      | none => rw [earlierAt] at ready; cases ready
      | some earlier =>
          exact ⟨earlier.castSucc, oldBound producer earlier earlierAt, earlier.isLt⟩
    · simp only [binding, if_neg chosen] at placed
      cases oldAt : state.position node with
      | none => simp only [oldAt, Option.map_none] at placed; cases placed
      | some oldIndex =>
          simp only [oldAt, Option.map_some, Option.some.injEq] at placed
          subst index
          obtain ⟨earlier, earlierAt, before⟩ := state.ordered node oldIndex oldAt producer edge
          exact ⟨earlier.castSucc, oldBound producer earlier earlierAt, before⟩

theorem ReadyStep.remaining_lt {nodes : Nat} {graph : Graph nodes}
    {state : State graph} (step : ReadyStep state) :
    step.apply.remaining.length < state.remaining.length := by
  change (state.remaining.erase step.node).length < state.remaining.length
  have erased := erase_length state.remaining step.node step.member
  omega

private def findReady {nodes : Nat} {graph : Graph nodes} (state : State graph) :
    (todo : List (Fin nodes)) →
    (∀ node, node ∈ todo → node ∈ state.remaining) → Option (ReadyStep state)
  | [], _subset => none
  | node :: tail, subset =>
      match found : state.ready node with
      | true => some
          { node := node
            member := subset node (List.Mem.head tail)
            ready := fun producer edge => (List.all_eq_true.mp found) producer edge }
      | false => findReady state tail
          (fun other member => subset other (List.Mem.tail node member))

private theorem findReady_none {nodes : Nat} {graph : Graph nodes} (state : State graph) :
    (todo : List (Fin nodes)) →
    (subset : ∀ node, node ∈ todo → node ∈ state.remaining) →
    findReady state todo subset = none → ∀ node, node ∈ todo → state.ready node = false
  | [], _subset, _failed, _node, member => by cases member
  | head :: tail, subset, failed, node, member => by
      unfold findReady at failed
      split at failed
      · cases failed
      · rename_i missing
        rcases List.mem_cons.mp member with same | later
        · subst node; exact missing
        · exact findReady_none state tail
            (fun other present => subset other (List.Mem.tail head present)) failed node later

structure Stop {nodes : Nat} (graph : Graph nodes) where
  state : State graph
  stopped : ∀ node, node ∈ state.remaining → state.ready node = false

def run {nodes : Nat} {graph : Graph nodes} (state : State graph) : Stop graph :=
  match found : findReady state state.remaining (fun _ member => member) with
  | none => ⟨state, findReady_none state state.remaining (fun _ member => member) found⟩
  | some step => run step.apply
termination_by state.remaining.length
decreasing_by exact ReadyStep.remaining_lt _

private theorem missing_predecessor {nodes : Nat} {graph : Graph nodes}
    (state : State graph) (todo : List (Fin nodes))
    (missing : todo.all (fun producer => (state.position producer).isSome) = false) :
    ∃ producer, producer ∈ todo ∧ state.position producer = none := by
  induction todo with
  | nil => cases missing
  | cons head tail ih =>
      cases placed : state.position head with
      | none => exact ⟨head, List.Mem.head tail, placed⟩
      | some index =>
          change ((state.position head).isSome &&
            tail.all (fun producer => (state.position producer).isSome)) = false at missing
          rw [placed] at missing
          change tail.all (fun producer => (state.position producer).isSome) = false at missing
          obtain ⟨producer, member, absent⟩ := ih missing
          exact ⟨producer, List.Mem.tail head member, absent⟩

theorem Stop.unresolved_predecessor {nodes : Nat} {graph : Graph nodes}
    (stop : Stop graph) (node : Fin nodes) (member : node ∈ stop.state.remaining) :
    ∃ producer, producer ∈ stop.state.remaining ∧ graph.Depends producer node := by
  obtain ⟨producer, edge, absent⟩ :=
    missing_predecessor stop.state (graph.predecessors node) (stop.stopped node member)
  exact ⟨producer, (stop.state.pending producer).2 absent, edge⟩

theorem Stop.complete_of_wellFounded {nodes : Nat} {graph : Graph nodes}
    (stop : Stop graph) (acyclic : WellFounded graph.Depends) : stop.state.remaining = [] := by
  have absent (node : Fin nodes) (accessible : Acc graph.Depends node) :
      node ∉ stop.state.remaining := by
    induction accessible with
    | intro node previous ih =>
        intro member
        obtain ⟨producer, pending, edge⟩ := stop.unresolved_predecessor node member
        exact ih producer edge pending
  cases remainingAt : stop.state.remaining with
  | nil => rfl
  | cons node tail =>
      exact False.elim (absent node (acyclic.apply node)
        (by rw [remainingAt]; exact List.Mem.head tail))

structure Schedule {nodes : Nat} (graph : Graph nodes) where
  count : Nat
  nodeAt : Fin count → Fin nodes
  position : Fin nodes → Fin count
  count_eq : count = nodes
  at_position : ∀ node, nodeAt (position node) = node
  position_at : ∀ index, position (nodeAt index) = index
  ordered : ∀ producer consumer, graph.Depends producer consumer →
    (position producer).val < (position consumer).val

private def State.completedPosition {nodes : Nat} {graph : Graph nodes}
    (state : State graph) (complete : state.remaining = []) (node : Fin nodes) : Fin state.count :=
  match found : state.position node with
  | some index => index
  | none => False.elim (by
      have member := (state.pending node).2 found
      rw [complete] at member
      cases member)

private theorem State.completedPosition_spec {nodes : Nat} {graph : Graph nodes}
    (state : State graph) (complete : state.remaining = []) (node : Fin nodes) :
    state.position node = some (state.completedPosition complete node) := by
  unfold completedPosition
  split
  · assumption
  · rename_i missing
    have member := (state.pending node).2 missing
    rw [complete] at member
    cases member

def State.finish {nodes : Nat} {graph : Graph nodes}
    (state : State graph) (complete : state.remaining = []) : Schedule graph :=
  { count := state.count
    nodeAt := state.nodeAt
    position := state.completedPosition complete
    count_eq := by
      have accounting := state.accounting
      rw [complete, List.length_nil, Nat.add_zero] at accounting
      exact accounting
    at_position := fun node =>
      state.atPosition node _ (state.completedPosition_spec complete node)
    position_at := fun index => Option.some.inj
      ((state.completedPosition_spec complete (state.nodeAt index)).symm.trans (state.positionAt index))
    ordered := by
      intro producer consumer edge
      obtain ⟨earlier, placed, before⟩ := state.ordered consumer
        (state.completedPosition complete consumer)
        (state.completedPosition_spec complete consumer) producer edge
      have same := Option.some.inj
        ((state.completedPosition_spec complete producer).symm.trans placed)
      rw [same]
      exact before }

private def accessible {nodes : Nat} {graph : Graph nodes}
    (rank : Fin nodes → Nat)
    (decreases : ∀ producer consumer, graph.Depends producer consumer →
      rank producer < rank consumer) (node : Fin nodes) : Acc graph.Depends node :=
  Acc.intro node (fun producer _edge => accessible rank decreases producer)
termination_by rank node
decreasing_by exact decreases _ _ _edge

theorem Schedule.wellFounded {nodes : Nat} {graph : Graph nodes}
    (schedule : Schedule graph) : WellFounded graph.Depends :=
  ⟨fun node => accessible (fun item => (schedule.position item).val) schedule.ordered node⟩

def Schedule.order {nodes : Nat} {graph : Graph nodes}
    (schedule : Schedule graph) : List (Fin nodes) :=
  (List.finRange schedule.count).map schedule.nodeAt

theorem Schedule.at_injective {nodes : Nat} {graph : Graph nodes}
    (schedule : Schedule graph) (left right : Fin schedule.count)
    (same : schedule.nodeAt left = schedule.nodeAt right) : left = right := by
  have indices := congrArg schedule.position same
  simpa only [schedule.position_at] using indices

theorem Schedule.order_complete {nodes : Nat} {graph : Graph nodes}
    (schedule : Schedule graph) (node : Fin nodes) : node ∈ schedule.order := by
  exact List.mem_map.mpr ⟨schedule.position node, by simp, schedule.at_position node⟩

theorem Schedule.order_nodup {nodes : Nat} {graph : Graph nodes}
    (schedule : Schedule graph) : schedule.order.Nodup :=
  List.Pairwise.map schedule.nodeAt
    (fun left right different same => different (schedule.at_injective left right same))
    (finRange_nodup schedule.count)

theorem Schedule.order_length {nodes : Nat} {graph : Graph nodes}
    (schedule : Schedule graph) : schedule.order.length = nodes := by
  simp only [order, List.length_map, List.length_finRange, schedule.count_eq]

/-- The only input is the actual graph. A stuck nonempty remainder rejects. -/
def compile {nodes : Nat} (graph : Graph nodes) : Option (Schedule graph) :=
  let stop := run (State.initial graph)
  if complete : stop.state.remaining = [] then some (stop.state.finish complete)
  else none

theorem compile_success_iff {nodes : Nat} (graph : Graph nodes) :
    (∃ schedule, compile graph = some schedule) ↔ WellFounded graph.Depends := by
  constructor
  · intro ⟨schedule, _accepted⟩
    exact schedule.wellFounded
  · intro acyclic
    let stop := run (State.initial graph)
    have complete := stop.complete_of_wellFounded acyclic
    refine ⟨stop.state.finish complete, ?_⟩
    change (if complete : stop.state.remaining = [] then
      some (stop.state.finish complete) else none) = _
    rw [dif_pos complete]

theorem compile_failure_iff {nodes : Nat} (graph : Graph nodes) :
    compile graph = none ↔ ¬WellFounded graph.Depends := by
  constructor
  · intro rejected acyclic
    obtain ⟨schedule, accepted⟩ := (compile_success_iff graph).2 acyclic
    rw [rejected] at accepted
    cases accepted
  · intro cyclic
    cases found : compile graph with
    | none => rfl
    | some schedule => exact False.elim (cyclic schedule.wellFounded)

end PNP.DependencyScheduler
