/-
Copyright (c) 2026 PNP Labs.

Computed topological compilation of finite raw NAND dependency graphs.
Raw node identifiers need not already be in execution order. The compiler
derives the order from the actual two source fields, never from a supplied
schedule. A nonempty stuck remainder is not a direct-wire implementation.

This is the physical ordering component for arbitrary-support replacement,
not full-profile normalization, Package E, a global route, or a polynomial
PCCMin theorem.
-/

import PNP.NANDSlack
import Init.Data.List.FinRange
import Init.Data.List.Erase

namespace PNP
namespace DirectWire

/-- A finite graph with arbitrary node references, before topological checking. -/
structure RawNandGraph (inputs nodes : Nat) where
  gate : Fin nodes → Gate inputs nodes

/-- A producer occurs in one of the consumer's actual two source fields. -/
def RawNandGraph.Depends {inputs nodes : Nat}
    (graph : RawNandGraph inputs nodes) (producer consumer : Fin nodes) : Prop :=
  (graph.gate consumer).left = .gate producer ∨
    (graph.gate consumer).right = .gate producer

/-- Simultaneous raw graph equations. This does not assume a solution exists. -/
def RawNandGraph.Solution {inputs nodes : Nat}
    (graph : RawNandGraph inputs nodes) (input : Valuation inputs)
    (values : Valuation nodes) : Prop :=
  ∀ node, values node = (graph.gate node).eval input values

/-- Computed partial program, with exact remaining nodes and checked invariants. -/
structure RawNandCompilationState {inputs nodes : Nat}
    (graph : RawNandGraph inputs nodes) where
  count : Nat
  program : Program inputs count
  position : Fin nodes → Option (Fin count)
  remaining : List (Fin nodes)
  remainingNodup : remaining.Nodup
  pending : ∀ node, node ∈ remaining ↔ position node = none
  accounting : count + remaining.length = nodes
  positionInjective : ∀ left right leftIndex rightIndex,
    position left = some leftIndex → position right = some rightIndex →
      leftIndex = rightIndex → left = right
  ordered : ∀ node index, position node = some index →
    ∀ producer, graph.Depends producer node →
      ∃ earlier, position producer = some earlier ∧ earlier.val < index.val
  sound : ∀ input values, graph.Solution input values →
    ∀ node index, position node = some index →
      program.eval input index = values node

private theorem rawNandFinRange_nodup (nodes : Nat) :
    (List.finRange nodes).Nodup := by
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

def RawNandCompilationState.initial {inputs nodes : Nat}
    (graph : RawNandGraph inputs nodes) : RawNandCompilationState graph :=
  { count := 0
    program := .empty
    position := fun _ => none
    remaining := List.finRange nodes
    remainingNodup := rawNandFinRange_nodup nodes
    pending := by intro node; simp
    accounting := by simp
    positionInjective := by
      intro left right leftIndex rightIndex impossible
      cases impossible
    ordered := by intro node index impossible; cases impossible
    sound := by intro input values equations node index impossible; cases impossible }

/-- Constants and primary inputs are immediately available; nodes must be placed. -/
def RawNandCompilationState.readSource {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph) :
    Source inputs nodes → Option (Source inputs state.count)
  | .input index => some (.input index)
  | .constant value => some (.constant value)
  | .gate node => (state.position node).map Source.gate

def RawNandCompilationState.readGate {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph)
    (node : Fin nodes) : Option (Gate inputs state.count) :=
  match state.readSource (graph.gate node).left,
      state.readSource (graph.gate node).right with
  | some left, some right => some ⟨left, right⟩
  | _, _ => none

theorem RawNandCompilationState.readSource_sound {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph)
    (source : Source inputs nodes) (translated : Source inputs state.count)
    (found : state.readSource source = some translated)
    (input : Valuation inputs) (values : Valuation nodes)
    (equations : graph.Solution input values) :
    translated.eval input (state.program.eval input) = source.eval input values := by
  cases source with
  | input index => cases found; rfl
  | constant value => cases found; rfl
  | gate node =>
      cases placed : state.position node with
      | none => simp only [readSource, placed, Option.map_none] at found; cases found
      | some index =>
          simp only [readSource, placed, Option.map_some, Option.some.injEq] at found
          subst translated
          exact state.sound input values equations node index placed

theorem RawNandCompilationState.readGate_sound {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph)
    (node : Fin nodes) (translated : Gate inputs state.count)
    (found : state.readGate node = some translated)
    (input : Valuation inputs) (values : Valuation nodes)
    (equations : graph.Solution input values) :
    translated.eval input (state.program.eval input) = values node := by
  cases leftAt : state.readSource (graph.gate node).left with
  | none => simp only [readGate, leftAt] at found; cases found
  | some left =>
      cases rightAt : state.readSource (graph.gate node).right with
      | none => simp only [readGate, leftAt, rightAt] at found; cases found
      | some right =>
          simp only [readGate, leftAt, rightAt, Option.some.injEq] at found
          subst translated
          change boolNand _ _ = values node
          rw [state.readSource_sound _ _ leftAt input values equations,
            state.readSource_sound _ _ rightAt input values equations]
          exact (equations node).symm

theorem RawNandCompilationState.readGate_predecessor {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph)
    (node : Fin nodes) (translated : Gate inputs state.count)
    (found : state.readGate node = some translated)
    (producer : Fin nodes) (edge : graph.Depends producer node) :
    ∃ index, state.position producer = some index := by
  cases leftAt : state.readSource (graph.gate node).left with
  | none => simp only [readGate, leftAt] at found; cases found
  | some left =>
      cases rightAt : state.readSource (graph.gate node).right with
      | none => simp only [readGate, leftAt, rightAt] at found; cases found
      | some right =>
          rcases edge with isLeft | isRight
          · rw [isLeft] at leftAt
            cases placed : state.position producer with
            | none => simp only [readSource, placed, Option.map_none] at leftAt; cases leftAt
            | some index => exact ⟨index, rfl⟩
          · rw [isRight] at rightAt
            cases placed : state.position producer with
            | none => simp only [readSource, placed, Option.map_none] at rightAt; cases rightAt
            | some index => exact ⟨index, rfl⟩

/-- One actual pending node whose two sources have been translated. -/
structure RawNandReadyStep {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph) where
  node : Fin nodes
  gate : Gate inputs state.count
  member : node ∈ state.remaining
  compiled : state.readGate node = some gate

private theorem rawNandErase_length {nodes : Nat}
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

private theorem rawNandErase_mem {nodes : Nat}
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

def RawNandReadyStep.apply {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} {state : RawNandCompilationState graph}
    (step : RawNandReadyStep state) : RawNandCompilationState graph := by
  let binding : Fin nodes → Option (Fin (state.count + 1)) := fun node =>
    if node = step.node then some (Fin.last state.count)
    else (state.position node).map Fin.castSucc
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
  refine
    { count := state.count + 1
      program := state.program.snoc step.gate
      position := binding
      remaining := state.remaining.erase step.node
      remainingNodup := List.Nodup.erase step.node state.remainingNodup
      pending := ?_
      accounting := ?_
      positionInjective := ?_
      ordered := ?_
      sound := ?_ }
  · intro node
    rw [rawNandErase_mem state.remaining step.node node state.remainingNodup]
    by_cases same : node = step.node
    · simp only [same, ne_eq, not_true_eq_false, false_and, binding, if_pos rfl,
        reduceCtorEq]
    · rw [and_iff_right same, state.pending node]
      simp only [binding, if_neg same]
      cases state.position node <;> simp
  · have erased := rawNandErase_length state.remaining step.node step.member
    have original := state.accounting
    omega
  · intro left right leftIndex rightIndex leftAt rightAt sameIndex
    by_cases leftChosen : left = step.node
    · subst left
      simp only [binding, if_pos rfl, Option.some.injEq] at leftAt
      cases leftAt
      by_cases rightChosen : right = step.node
      · exact rightChosen.symm
      · simp only [binding, if_neg rightChosen] at rightAt
        cases oldRightAt : state.position right with
        | none => simp only [oldRightAt, Option.map_none] at rightAt; cases rightAt
        | some oldRight =>
            simp only [oldRightAt, Option.map_some, Option.some.injEq] at rightAt
            cases rightAt
            have impossible := congrArg Fin.val sameIndex
            change state.count = oldRight.val at impossible
            have smaller := oldRight.isLt
            omega
    · simp only [binding, if_neg leftChosen] at leftAt
      cases oldLeftAt : state.position left with
      | none => simp only [oldLeftAt, Option.map_none] at leftAt; cases leftAt
      | some oldLeft =>
          simp only [oldLeftAt, Option.map_some, Option.some.injEq] at leftAt
          cases leftAt
          by_cases rightChosen : right = step.node
          · subst right
            simp only [binding, if_pos rfl, Option.some.injEq] at rightAt
            cases rightAt
            have impossible := congrArg Fin.val sameIndex
            change oldLeft.val = state.count at impossible
            have smaller := oldLeft.isLt
            omega
          · simp only [binding, if_neg rightChosen] at rightAt
            cases oldRightAt : state.position right with
            | none => simp only [oldRightAt, Option.map_none] at rightAt; cases rightAt
            | some oldRight =>
                simp only [oldRightAt, Option.map_some, Option.some.injEq] at rightAt
                cases rightAt
                exact state.positionInjective left right oldLeft oldRight
                  oldLeftAt oldRightAt (Fin.ext (congrArg (fun index : Fin (state.count + 1) => index.val) sameIndex))
  · intro node index placed producer edge
    by_cases same : node = step.node
    · subst node
      simp only [binding, if_pos rfl, Option.some.injEq] at placed
      subst index
      obtain ⟨earlier, earlierAt⟩ :=
        state.readGate_predecessor step.node step.gate step.compiled producer edge
      exact ⟨earlier.castSucc, oldBound producer earlier earlierAt, earlier.isLt⟩
    · simp only [binding, if_neg same] at placed
      cases oldAt : state.position node with
      | none => simp only [oldAt, Option.map_none] at placed; cases placed
      | some oldIndex =>
          simp only [oldAt, Option.map_some, Option.some.injEq] at placed
          subst index
          obtain ⟨earlier, earlierAt, earlierLT⟩ :=
            state.ordered node oldIndex oldAt producer edge
          exact ⟨earlier.castSucc, oldBound producer earlier earlierAt, earlierLT⟩
  · intro input values equations node index placed
    by_cases same : node = step.node
    · subst node
      simp only [binding, if_pos rfl, Option.some.injEq] at placed
      subst index
      rw [Program.eval_snoc_last]
      exact state.readGate_sound step.node step.gate step.compiled input values equations
    · simp only [binding, if_neg same] at placed
      cases oldAt : state.position node with
      | none => simp only [oldAt, Option.map_none] at placed; cases placed
      | some oldIndex =>
          simp only [oldAt, Option.map_some, Option.some.injEq] at placed
          subst index
          rw [Program.eval_snoc_castSucc]
          exact state.sound input values equations node oldIndex oldAt

theorem RawNandReadyStep.apply_remaining_lt {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} {state : RawNandCompilationState graph}
    (step : RawNandReadyStep state) :
    step.apply.remaining.length < state.remaining.length := by
  change (state.remaining.erase step.node).length < state.remaining.length
  have erased := rawNandErase_length state.remaining step.node step.member
  omega

private def findRawNandReadyIn {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph) :
    (todo : List (Fin nodes)) →
      (∀ node, node ∈ todo → node ∈ state.remaining) →
      Option (RawNandReadyStep state)
  | [], _subset => none
  | node :: tail, subset =>
      match found : state.readGate node with
      | some gate => some
          { node := node, gate := gate, member := subset node (List.Mem.head tail)
            compiled := found }
      | none => findRawNandReadyIn state tail
          (fun other member => subset other (List.Mem.tail node member))

private theorem findRawNandReadyIn_none {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph) :
    (todo : List (Fin nodes)) →
    (subset : ∀ node, node ∈ todo → node ∈ state.remaining) →
    findRawNandReadyIn state todo subset = none →
    ∀ node, node ∈ todo → state.readGate node = none
  | [], _subset, _failed, _node, member => by cases member
  | head :: tail, subset, failed, node, member => by
      unfold findRawNandReadyIn at failed
      split at failed
      · cases failed
      · rename_i missing
        rcases List.mem_cons.mp member with same | later
        · subst node; exact missing
        · exact findRawNandReadyIn_none state tail
            (fun other present => subset other (List.Mem.tail head present))
            failed node later

/-- The terminal partial program and the exact absence of any ready remaining node. -/
structure RawNandCompilationStop {inputs nodes : Nat}
    (graph : RawNandGraph inputs nodes) where
  state : RawNandCompilationState graph
  stopped : ∀ node, node ∈ state.remaining → state.readGate node = none

/-- Each recursive call emits one actual node and removes it from the remainder. -/
def runRawNandCompilation {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph) :
    RawNandCompilationStop graph :=
  match found : findRawNandReadyIn state state.remaining (fun _ member => member) with
  | none => ⟨state, findRawNandReadyIn_none state state.remaining
      (fun _ member => member) found⟩
  | some step => runRawNandCompilation step.apply
termination_by state.remaining.length
decreasing_by exact RawNandReadyStep.apply_remaining_lt _

theorem RawNandCompilationState.readSource_none {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph)
    (source : Source inputs nodes) (missing : state.readSource source = none) :
    ∃ producer, source = .gate producer ∧ producer ∈ state.remaining := by
  cases source with
  | input index => cases missing
  | constant value => cases missing
  | gate producer =>
      refine ⟨producer, rfl, (state.pending producer).2 ?_⟩
      cases placed : state.position producer with
      | none => rfl
      | some index => simp only [readSource, placed, Option.map_some] at missing; cases missing

/-- Every stuck pending node has an actual pending predecessor, not a fabricated edge. -/
theorem RawNandCompilationStop.unresolved_predecessor {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (stop : RawNandCompilationStop graph)
    (node : Fin nodes) (member : node ∈ stop.state.remaining) :
    ∃ producer, producer ∈ stop.state.remaining ∧ graph.Depends producer node := by
  have missing := stop.stopped node member
  cases leftAt : stop.state.readSource (graph.gate node).left with
  | none =>
      obtain ⟨producer, sourceAt, pending⟩ := stop.state.readSource_none _ leftAt
      exact ⟨producer, pending, Or.inl sourceAt⟩
  | some left =>
      cases rightAt : stop.state.readSource (graph.gate node).right with
      | none =>
          obtain ⟨producer, sourceAt, pending⟩ := stop.state.readSource_none _ rightAt
          exact ⟨producer, pending, Or.inr sourceAt⟩
      | some right =>
          simp only [RawNandCompilationState.readGate, leftAt, rightAt] at missing
          cases missing

/-- Well-founded source dependencies cannot leave a stuck nonempty remainder. -/
theorem RawNandCompilationStop.complete_of_wellFounded {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (stop : RawNandCompilationStop graph)
    (acyclic : WellFounded graph.Depends) : stop.state.remaining = [] := by
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

/-- A completed compilation supplies an injective order for every original node. -/
structure CompiledRawNandGraph {inputs nodes : Nat}
    (graph : RawNandGraph inputs nodes) where
  count : Nat
  program : Program inputs count
  position : Fin nodes → Fin count
  count_eq : count = nodes
  position_injective : ∀ left right, position left = position right → left = right
  ordered : ∀ producer consumer, graph.Depends producer consumer →
    (position producer).val < (position consumer).val
  sound : ∀ input values, graph.Solution input values →
    ∀ node, program.eval input (position node) = values node

private def RawNandCompilationState.completedPosition {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph)
    (complete : state.remaining = []) (node : Fin nodes) : Fin state.count :=
  match found : state.position node with
  | some index => index
  | none => False.elim (by
      have member := (state.pending node).2 found
      rw [complete] at member
      cases member)

private theorem RawNandCompilationState.completedPosition_spec {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph)
    (complete : state.remaining = []) (node : Fin nodes) :
    state.position node = some (state.completedPosition complete node) := by
  unfold completedPosition
  split
  · assumption
  · rename_i missing
    have member := (state.pending node).2 missing
    rw [complete] at member
    cases member

def RawNandCompilationState.finish {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph)
    (complete : state.remaining = []) : CompiledRawNandGraph graph :=
  { count := state.count
    program := state.program
    position := state.completedPosition complete
    count_eq := by
      have exactCount := state.accounting
      rw [complete, List.length_nil, Nat.add_zero] at exactCount
      exact exactCount
    position_injective := by
      intro left right same
      exact state.positionInjective left right _ _
        (state.completedPosition_spec complete left)
        (state.completedPosition_spec complete right) same
    ordered := by
      intro producer consumer edge
      obtain ⟨earlier, placed, earlierLT⟩ := state.ordered consumer
        (state.completedPosition complete consumer)
        (state.completedPosition_spec complete consumer) producer edge
      have same := Option.some.inj
        ((state.completedPosition_spec complete producer).symm.trans placed)
      rw [same]
      exact earlierLT
    sound := by
      intro input values equations node
      exact state.sound input values equations node _
        (state.completedPosition_spec complete node) }

/-- Finishing retains the actual computed position of every original node. -/
theorem RawNandCompilationState.finish_position {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph)
    (complete : state.remaining = []) (node : Fin nodes) :
    state.position node = some ((state.finish complete).position node) :=
  state.completedPosition_spec complete node

private theorem rawNandRank_accessible {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (rank : Fin nodes → Nat)
    (decreases : ∀ producer consumer, graph.Depends producer consumer →
      rank producer < rank consumer) (node : Fin nodes) :
    Acc graph.Depends node :=
  Acc.intro node (fun producer _edge => rawNandRank_accessible rank decreases producer)
termination_by rank node
decreasing_by exact decreases _ _ _edge

/-- Accepted output ordering rules out cyclic input graphs independently of semantics. -/
theorem CompiledRawNandGraph.wellFounded {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (compiled : CompiledRawNandGraph graph) :
    WellFounded graph.Depends :=
  ⟨fun node => rawNandRank_accessible
    (fun item => (compiled.position item).val) compiled.ordered node⟩

/-- Compile from graph data alone; unresolved nonempty remainders fail closed. -/
def compileRawNandGraph {inputs nodes : Nat} (graph : RawNandGraph inputs nodes) :
    Option (CompiledRawNandGraph graph) :=
  let stop := runRawNandCompilation (RawNandCompilationState.initial graph)
  if complete : stop.state.remaining = [] then
    some (stop.state.finish complete)
  else none

/-- Success is equivalent to well-foundedness of the actual source-edge relation. -/
theorem compileRawNandGraph_success_iff {inputs nodes : Nat}
    (graph : RawNandGraph inputs nodes) :
    (∃ compiled, compileRawNandGraph graph = some compiled) ↔
      WellFounded graph.Depends := by
  constructor
  · intro ⟨compiled, _accepted⟩
    exact compiled.wellFounded
  · intro acyclic
    let stop := runRawNandCompilation (RawNandCompilationState.initial graph)
    have complete := stop.complete_of_wellFounded acyclic
    refine ⟨stop.state.finish complete, ?_⟩
    change (if complete : stop.state.remaining = [] then
      some (stop.state.finish complete) else none) = _
    rw [dif_pos complete]

theorem compileRawNandGraph_failure_iff {inputs nodes : Nat}
    (graph : RawNandGraph inputs nodes) :
    compileRawNandGraph graph = none ↔ ¬WellFounded graph.Depends := by
  constructor
  · intro rejected acyclic
    obtain ⟨compiled, accepted⟩ := (compileRawNandGraph_success_iff graph).2 acyclic
    rw [rejected] at accepted
    cases accepted
  · intro cyclic
    cases found : compileRawNandGraph graph with
    | none => rfl
    | some compiled => exact False.elim (cyclic compiled.wellFounded)

def CompiledRawNandGraph.translateSource {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (compiled : CompiledRawNandGraph graph) :
    Source inputs nodes → Source inputs compiled.count
  | .input index => .input index
  | .constant value => .constant value
  | .gate node => .gate (compiled.position node)

theorem CompiledRawNandGraph.translateSource_sound {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (compiled : CompiledRawNandGraph graph)
    (source : Source inputs nodes) (input : Valuation inputs) (values : Valuation nodes)
    (equations : graph.Solution input values) :
    (compiled.translateSource source).eval input (compiled.program.eval input) =
      source.eval input values := by
  cases source with
  | input index => rfl
  | constant value => rfl
  | gate node => exact compiled.sound input values equations node

/-- Reconnect every original ordered output through the computed node positions. -/
def CompiledRawNandGraph.candidate {inputs nodes outputs : Nat}
    {graph : RawNandGraph inputs nodes} (compiled : CompiledRawNandGraph graph)
    (word : DirectWireWord inputs nodes outputs) :
    Candidate inputs compiled.count outputs :=
  Candidate.ofDirectWireWord compiled.program
    ⟨fun output => compiled.translateSource (word.source output)⟩

theorem CompiledRawNandGraph.candidate_gateCount {inputs nodes outputs : Nat}
    {graph : RawNandGraph inputs nodes} (compiled : CompiledRawNandGraph graph)
    (word : DirectWireWord inputs nodes outputs) :
    (compiled.candidate word).toImplementation.gateCount = nodes :=
  compiled.count_eq

/-- Complete ordered-output semantics, for every solution of the raw equations. -/
theorem CompiledRawNandGraph.candidate_semantics {inputs nodes outputs : Nat}
    {graph : RawNandGraph inputs nodes} (compiled : CompiledRawNandGraph graph)
    (word : DirectWireWord inputs nodes outputs) (input : Valuation inputs)
    (values : Valuation nodes) (equations : graph.Solution input values)
    (output : Fin outputs) :
    (compiled.candidate word).semantics input output =
      (word.source output).eval input values := by
  unfold candidate
  rw [Candidate.ofDirectWireWord_semantics]
  exact compiled.translateSource_sound (word.source output) input values equations

end DirectWire
end PNP
