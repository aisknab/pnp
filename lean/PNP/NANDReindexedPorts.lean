/-
Copyright (c) 2026 PNP Labs.

Compute ordered-port bijections for every descendant support of the actual
structural reindexer. Canonical source and target list orders need not agree.
The returned maps include literal lookup, both inverse laws and exact counts;
they are derived, never caller-supplied support certificates.

Arbitrary boundary valuations are reindexed bijectively. Preservation of the
open support function and literal replacement programs are separate obligations.
-/

import PNP.NANDReindexedSupport

namespace PNP.DirectWire.StructuralReindexing

/-- An executable index correspondence with the actual listed values retained. -/
structure OrderedPortBijection {alpha beta : Type}
    (source : List alpha) (target : List beta)
    (forwardValue : alpha → beta) (backwardValue : beta → alpha) where
  forward : Fin source.length → Fin target.length
  backward : Fin target.length → Fin source.length
  forward_get : ∀ index, target.get (forward index) = forwardValue (source.get index)
  backward_get : ∀ index, source.get (backward index) = backwardValue (target.get index)
  backward_forward : ∀ index, backward (forward index) = index
  forward_backward : ∀ index, forward (backward index) = index
  width_eq : source.length = target.length

private def locate {alpha : Type} [DecidableEq alpha] (item : alpha) :
    (items : List alpha) → item ∈ items →
      {index : Fin items.length // items.get index = item}
  | [], member => False.elim (by cases member)
  | head :: tail, member =>
      if same : item = head then
        ⟨⟨0, Nat.zero_lt_succ _⟩, by subst item; rfl⟩
      else
        let found := locate item tail ((List.mem_cons.mp member).resolve_left same)
        ⟨found.1.succ, found.2⟩

private theorem get_injective_of_nodup {alpha : Type} {items : List alpha}
    (distinct : items.Nodup) {left right : Fin items.length}
    (equal : items.get left = items.get right) : left = right := by
  apply Fin.ext
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro rightBeforeLeft
    have separated := (List.pairwise_iff_getElem.mp distinct) right.val left.val
      right.isLt left.isLt rightBeforeLeft
    change items.get right ≠ items.get left at separated
    exact separated equal.symm
  · apply Nat.le_of_not_gt
    intro leftBeforeRight
    have separated := (List.pairwise_iff_getElem.mp distinct) left.val right.val
      left.isLt right.isLt leftBeforeRight
    change items.get left ≠ items.get right at separated
    exact separated equal

private theorem nodup_length_le_subset {alpha : Type} [DecidableEq alpha]
    {left right : List alpha} (distinct : left.Nodup)
    (included : ∀ item, item ∈ left → item ∈ right) : left.length ≤ right.length := by
  induction right generalizing left with
  | nil =>
      cases left with
      | nil => exact Nat.le_refl 0
      | cons head tail =>
          have impossible := included head (List.Mem.head tail)
          cases impossible
  | cons head tail ih =>
      by_cases member : head ∈ left
      · obtain ⟨before, after, rfl⟩ := List.append_of_mem member
        have reordered : (before ++ head :: after).Perm (head :: (before ++ after)) :=
          List.perm_middle
        obtain ⟨absent, restDistinct⟩ := List.nodup_cons.mp (reordered.nodup distinct)
        have restIncluded : ∀ item, item ∈ before ++ after → item ∈ tail := by
          intro item present
          have belongs := included item (reordered.symm.subset (List.mem_cons_of_mem head present))
          rcases List.mem_cons.mp belongs with same | remaining
          · exact False.elim (absent (same ▸ present))
          · exact remaining
        have bound := ih restDistinct restIncluded
        have length := reordered.length_eq
        simp only [List.length_cons] at length
        change _ ≤ tail.length + 1
        omega
      · have restIncluded : ∀ item, item ∈ left → item ∈ tail := by
          intro item present
          rcases List.mem_cons.mp (included item present) with same | remaining
          · exact False.elim (member (same ▸ present))
          · exact remaining
        exact Nat.le_trans (ih distinct restIncluded) (Nat.le_succ tail.length)

private theorem mapped_length_le {alpha beta : Type} [DecidableEq beta]
    {source : List alpha} {target : List beta} (distinct : source.Nodup)
    (mapping : alpha → beta) (injective : Function.Injective mapping)
    (included : ∀ item, item ∈ source → mapping item ∈ target) :
    source.length ≤ target.length := by
  have mappedDistinct : (source.map mapping).Nodup :=
    List.Pairwise.map mapping (fun _ _ different same => different (injective same)) distinct
  have bound := nodup_length_le_subset mappedDistinct (fun item present => by
    obtain ⟨prior, member, same⟩ := List.mem_map.mp present
    exact same ▸ included prior member)
  simpa only [List.length_map] using bound

private def computedBijection {alpha beta : Type} [DecidableEq alpha] [DecidableEq beta]
    (source : List alpha) (target : List beta)
    (forwardValue : alpha → beta) (backwardValue : beta → alpha)
    (sourceDistinct : source.Nodup) (targetDistinct : target.Nodup)
    (leftInverse : ∀ item, backwardValue (forwardValue item) = item)
    (rightInverse : ∀ item, forwardValue (backwardValue item) = item)
    (forwardMember : ∀ item, item ∈ source → forwardValue item ∈ target)
    (backwardMember : ∀ item, item ∈ target → backwardValue item ∈ source) :
    OrderedPortBijection source target forwardValue backwardValue := by
  let next (index : Fin source.length) : Fin target.length :=
    (locate (forwardValue (source.get index)) target
      (forwardMember (source.get index) (List.get_mem source index))).1
  let prior (index : Fin target.length) : Fin source.length :=
    (locate (backwardValue (target.get index)) source
      (backwardMember (target.get index) (List.get_mem target index))).1
  have nextGet (index : Fin source.length) :
      target.get (next index) = forwardValue (source.get index) :=
    (locate (forwardValue (source.get index)) target
      (forwardMember (source.get index) (List.get_mem source index))).2
  have priorGet (index : Fin target.length) :
      source.get (prior index) = backwardValue (target.get index) :=
    (locate (backwardValue (target.get index)) source
      (backwardMember (target.get index) (List.get_mem target index))).2
  refine ⟨next, prior, nextGet, priorGet, ?_, ?_, ?_⟩
  · intro index
    apply get_injective_of_nodup sourceDistinct
    rw [priorGet, nextGet, leftInverse]
  · intro index
    apply get_injective_of_nodup targetDistinct
    rw [nextGet, priorGet, rightInverse]
  · have forwardInjective : Function.Injective forwardValue := by
      intro left right same
      have recovered := congrArg backwardValue same
      rw [leftInverse, leftInverse] at recovered
      exact recovered
    have backwardInjective : Function.Injective backwardValue := by
      intro left right same
      have recovered := congrArg forwardValue same
      rw [rightInverse, rightInverse] at recovered
      exact recovered
    exact Nat.le_antisymm
      (mapped_length_le sourceDistinct forwardValue forwardInjective forwardMember)
      (mapped_length_le targetDistinct backwardValue backwardInjective backwardMember)

private theorem allFin_nodup (width : Nat) : (allFin width).Nodup := by
  induction width with
  | zero => exact List.nodup_nil
  | succ width ih =>
      change (0 :: (allFin width).map Fin.succ).Nodup
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨index, _, same⟩ := List.mem_map.mp member
        have impossible := congrArg Fin.val same
        change index.val + 1 = 0 at impossible
        omega
      · exact List.Pairwise.map Fin.succ
          (fun left right different same =>
            different (Fin.ext (Nat.succ.inj (congrArg Fin.val same)))) ih

variable {inputs gates outputs profileWidth : Nat}
variable (original : Candidate inputs gates outputs) (relabeling : GateRenaming gates)
variable (records : List
  (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))

/-- The records here are arbitrary descendant records, not a restricted family. -/
def boundaryPorts :
    OrderedPortBijection
      (terminalBoundaryPorts original.program (backwardRecords original.program relabeling records))
      (terminalBoundaryPorts (result original relabeling).program records)
      (forwardWire original.program relabeling) (backwardWire original.program relabeling) :=
  computedBijection _ _ _ _
    (terminalBoundaryPorts_nodup _ _) (terminalBoundaryPorts_nodup _ _)
    (backward_forward_wire original.program relabeling)
    (forward_backward_wire original.program relabeling)
    (fun wire member => by
      apply (descendant_boundary original relabeling records
        (forwardWire original.program relabeling wire)).mpr
      rw [backward_forward_wire]
      exact member)
    (fun wire member => (descendant_boundary original relabeling records wire).mp member)

def interfacePorts :
    OrderedPortBijection
      (terminalInterfacePorts original (backwardRecords original.program relabeling records))
      (terminalInterfacePorts (result original relabeling) records)
      (forwardGate original.program relabeling) (backwardGate original.program relabeling) :=
  computedBijection _ _ _ _
    (List.Pairwise.filter _ (allFin_nodup gates))
    (List.Pairwise.filter _ (allFin_nodup (compiled original.program relabeling).count))
    (backward_forward original.program relabeling) (forward_backward original.program relabeling)
    (fun node member => by
      apply (descendant_interface original relabeling records
        (forwardGate original.program relabeling node)).mpr
      rw [backward_forward]
      exact member)
    (fun node member => (descendant_interface original relabeling records node).mp member)

theorem selected_backward (node : Fin (compiled original.program relabeling).count) :
    terminalGateSelected (backwardRecords original.program relabeling records)
        (backwardGate original.program relabeling node) =
      terminalGateSelected records node := by
  have same := selected_forward original.program relabeling
    (backwardRecords original.program relabeling records)
    (backwardGate original.program relabeling node)
  rw [forward_backward_records, forward_backward] at same
  exact same.symm

/-- Exact selected physical gates correspond, regardless of duplicate records. -/
def selectedPorts :
    OrderedPortBijection
      (terminalSelectedGates (backwardRecords original.program relabeling records))
      (terminalSelectedGates records)
      (forwardGate original.program relabeling) (backwardGate original.program relabeling) :=
  computedBijection _ _ _ _
    (terminalSelectedGates_nodup _) (terminalSelectedGates_nodup _)
    (backward_forward original.program relabeling) (forward_backward original.program relabeling)
    (fun node member => by
      apply (mem_terminalSelectedGates_iff records _).mpr
      have selected := (mem_terminalSelectedGates_iff _ _).mp member
      have same := selected_backward original relabeling records
        (forwardGate original.program relabeling node)
      rw [backward_forward] at same
      exact same.symm.trans selected)
    (fun node member => by
      apply (mem_terminalSelectedGates_iff _ _).mpr
      exact (selected_backward original relabeling records node).trans
        ((mem_terminalSelectedGates_iff records node).mp member))

/-- Retained exterior ownership is also derived at actual physical coordinates. -/
def exteriorPorts :
    OrderedPortBijection
      (ArbitrarySupportSplice.exterior (backwardRecords original.program relabeling records))
      (ArbitrarySupportSplice.exterior records)
      (forwardGate original.program relabeling) (backwardGate original.program relabeling) :=
  computedBijection _ _ _ _
    (terminalSelectedGateIndices_nodup _) (terminalSelectedGateIndices_nodup _)
    (backward_forward original.program relabeling) (forward_backward original.program relabeling)
    (fun node member => by
      apply (ArbitrarySupportSplice.mem_exterior_iff records _).mpr
      have unselected := (ArbitrarySupportSplice.mem_exterior_iff _ _).mp member
      have same := selected_backward original relabeling records
        (forwardGate original.program relabeling node)
      rw [backward_forward] at same
      exact same.symm.trans unselected)
    (fun node member => by
      apply (ArbitrarySupportSplice.mem_exterior_iff _ _).mpr
      exact (selected_backward original relabeling records node).trans
        ((ArbitrarySupportSplice.mem_exterior_iff records node).mp member))

def pushBoundaryValuation
    (valuation : Valuation
      (terminalBoundaryPorts original.program
        (backwardRecords original.program relabeling records)).length) :
    Valuation (terminalBoundaryPorts (result original relabeling).program records).length :=
  fun index => valuation ((boundaryPorts original relabeling records).backward index)

def pullBoundaryValuation
    (valuation : Valuation
      (terminalBoundaryPorts (result original relabeling).program records).length) :
    Valuation
      (terminalBoundaryPorts original.program
        (backwardRecords original.program relabeling records)).length :=
  fun index => valuation ((boundaryPorts original relabeling records).forward index)

/-- Every independent predecessor-boundary valuation survives the round trip. -/
theorem pull_push_boundary_valuation
    (valuation : Valuation
      (terminalBoundaryPorts original.program
        (backwardRecords original.program relabeling records)).length) :
    pullBoundaryValuation original relabeling records
        (pushBoundaryValuation original relabeling records valuation) = valuation := by
  funext index
  change valuation ((boundaryPorts original relabeling records).backward
    ((boundaryPorts original relabeling records).forward index)) = valuation index
  rw [(boundaryPorts original relabeling records).backward_forward]

/-- Every independent descendant-boundary valuation is covered. -/
theorem push_pull_boundary_valuation
    (valuation : Valuation
      (terminalBoundaryPorts (result original relabeling).program records).length) :
    pushBoundaryValuation original relabeling records
        (pullBoundaryValuation original relabeling records valuation) = valuation := by
  funext index
  change valuation ((boundaryPorts original relabeling records).forward
    ((boundaryPorts original relabeling records).backward index)) = valuation index
  rw [(boundaryPorts original relabeling records).forward_backward]

theorem selected_gate_count :
    (terminalSelectedGates (backwardRecords original.program relabeling records)).length =
      (terminalSelectedGates records).length :=
  (selectedPorts original relabeling records).width_eq

theorem exterior_gate_count :
    (ArbitrarySupportSplice.exterior (backwardRecords original.program relabeling records)).length =
      (ArbitrarySupportSplice.exterior records).length :=
  (exteriorPorts original relabeling records).width_eq

end PNP.DirectWire.StructuralReindexing
