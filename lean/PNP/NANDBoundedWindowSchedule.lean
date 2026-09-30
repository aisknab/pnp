/-
Copyright (c) 2026 PNP Labs.

Complete duplicate-free enumeration of bounded physical supports and exact
transport across record representations. Equal selection preserves the
physical search problem, not arbitrary full-profile observers.
-/

import PNP.NANDPhysicalWindowBudget
import PNP.NANDSupportRecordTransport

namespace PNP.DirectWire.BoundedWindowSchedule

/-- Generate increasing physical gate lists; the lower bound excludes repeats. -/
def windowsFrom (gates : Nat) : Nat → Nat → List (List (Fin gates))
  | 0, _floor => [[]]
  | limit + 1, floor =>
      [] :: ((allFin gates).filter (fun gate => decide (floor ≤ gate.val))).flatMap
        (fun first => (windowsFrom gates limit (first.val + 1)).map (List.cons first))

theorem windowsFrom_sound (gates limit floor : Nat)
    (word : List (Fin gates)) (member : word ∈ windowsFrom gates limit floor) :
    word.length ≤ limit ∧ word.Pairwise (fun left right => left.val < right.val) ∧
      ∀ gate, gate ∈ word → floor ≤ gate.val := by
  induction limit generalizing floor word with
  | zero =>
      have empty : word = [] := List.mem_singleton.mp member
      subst word
      exact ⟨Nat.le_refl 0, .nil, fun gate absent => by cases absent⟩
  | succ limit ih =>
      rcases List.mem_cons.mp member with empty | later
      · subst word
        exact ⟨Nat.zero_le _, .nil, fun gate absent => by cases absent⟩
      · obtain ⟨first, firstMember, wordMember⟩ := List.mem_flatMap.mp later
        obtain ⟨tail, tailMember, rfl⟩ := List.mem_map.mp wordMember
        have firstBound := of_decide_eq_true (List.mem_filter.mp firstMember).2
        obtain ⟨lengthBound, ordered, lower⟩ := ih (first.val + 1) tail tailMember
        refine ⟨Nat.succ_le_succ lengthBound, ?_, ?_⟩
        · apply List.pairwise_cons.mpr
          exact ⟨fun gate present => lower gate present, ordered⟩
        · intro gate present
          rcases List.mem_cons.mp present with same | remaining
          · subst gate
            exact firstBound
          · have laterBound := lower gate remaining
            omega

theorem windowsFrom_complete (gates limit floor : Nat) (word : List (Fin gates))
    (bounded : word.length ≤ limit)
    (ordered : word.Pairwise (fun left right => left.val < right.val))
    (lower : ∀ gate, gate ∈ word → floor ≤ gate.val) :
    word ∈ windowsFrom gates limit floor := by
  induction limit generalizing floor word with
  | zero =>
      have empty : word = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero bounded)
      subst word
      exact List.mem_cons_self
  | succ limit ih =>
      cases word with
      | nil => exact List.mem_cons_self
      | cons first tail =>
          obtain ⟨beforeAll, tailOrdered⟩ := List.pairwise_cons.mp ordered
          have tailBound : tail.length ≤ limit := Nat.le_of_succ_le_succ bounded
          have tailLower : ∀ gate, gate ∈ tail → first.val + 1 ≤ gate.val :=
            fun gate present => beforeAll gate present
          apply List.Mem.tail
          exact mem_flatMap_of_mem
            (List.mem_filter.mpr ⟨mem_allFin first,
              decide_eq_true (lower first List.mem_cons_self)⟩)
            (mem_map_of_mem (List.cons first) (ih _ tail tailBound tailOrdered tailLower))

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

/-- Each physical support is searched once, not once per permutation or padding. -/
theorem windowsFrom_nodup (gates limit floor : Nat) :
    (windowsFrom gates limit floor).Nodup := by
  induction limit generalizing floor with
  | zero =>
      exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | succ limit ih =>
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨first, _, present⟩ := List.mem_flatMap.mp member
        obtain ⟨tail, _, impossible⟩ := List.mem_map.mp present
        cases impossible
      · apply List.pairwise_flatMap.mpr
        constructor
        · intro first _member
          exact List.Pairwise.map (List.cons first)
            (fun left right different same => different (List.cons.inj same).2) (ih _)
        · apply (List.Pairwise.filter (fun gate : Fin gates => decide (floor ≤ gate.val))
            (allFin_nodup gates)).imp
          intro left right different leftWord leftMember rightWord rightMember same
          obtain ⟨leftTail, _, rfl⟩ := List.mem_map.mp leftMember
          obtain ⟨rightTail, _, rfl⟩ := List.mem_map.mp rightMember
          exact different (List.cons.inj same).1

private theorem flatMap_length_le {alpha beta : Type}
    (items : List alpha) (mapping : alpha → List beta) (bound : Nat)
    (each : ∀ item, item ∈ items → (mapping item).length ≤ bound) :
    (items.flatMap mapping).length ≤ items.length * bound := by
  induction items with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons head tail ih =>
      have first := each head List.mem_cons_self
      have rest := ih (fun item member => each item (List.mem_cons_of_mem head member))
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
      exact Nat.le_trans (Nat.add_le_add first rest) (Nat.le_of_eq (Nat.add_comm _ _))

/-- Fixed-schema support count; no enumeration of every unbounded subset is used. -/
theorem windowsFrom_length_le (gates limit floor : Nat) :
    (windowsFrom gates limit floor).length ≤ (gates + 1) ^ limit := by
  induction limit generalizing floor with
  | zero => exact Nat.le_refl 1
  | succ limit ih =>
      have rest := flatMap_length_le
        ((allFin gates).filter (fun gate => decide (floor ≤ gate.val)))
        (fun first => (windowsFrom gates limit (first.val + 1)).map (List.cons first))
        ((gates + 1) ^ limit) (fun first _member => by
          rw [List.length_map]
          exact ih _)
      have filtered : ((allFin gates).filter (fun gate => decide (floor ≤ gate.val))).length ≤ gates := by
        simpa only [allFin_length] using
          List.length_filter_le (fun gate : Fin gates => decide (floor ≤ gate.val)) (allFin gates)
      have sumBound := Nat.le_trans rest (Nat.mul_le_mul_right _ filtered)
      have positive : 1 ≤ (gates + 1) ^ limit :=
        Nat.pow_le_pow_right (Nat.zero_lt_succ gates) (Nat.zero_le limit)
      change _ + 1 ≤ (gates + 1) ^ (limit + 1)
      rw [Nat.pow_succ, Nat.mul_succ]
      rw [Nat.mul_comm gates ((gates + 1) ^ limit)] at sumBound
      omega

variable {inputs gates outputs profileWidth : Nat}

/-- The physical support ledger contains only source-derived gate requests. -/
def recordsOf (word : List (Fin gates)) :
    List (TerminalPrimitiveRecord inputs gates outputs 0) :=
  word.map TerminalPrimitiveRecord.gate

theorem recordsOf_selected_iff (word : List (Fin gates)) (gate : Fin gates) :
    terminalGateSelected (recordsOf (inputs := inputs) (outputs := outputs) word) gate = true ↔
      gate ∈ word := by
  rw [terminalGateSelected_eq_true_iff]
  constructor
  · intro member
    obtain ⟨prior, present, same⟩ := List.mem_map.mp member
    have equal : prior = gate := TerminalPrimitiveRecord.gate.inj same
    exact equal ▸ present
  · intro member
    exact List.mem_map.mpr ⟨gate, member, rfl⟩

private theorem nodup_length_le_subset {alpha : Type}
    {left right : List alpha} (distinct : left.Nodup)
    (included : ∀ item, item ∈ left → item ∈ right) :
    left.length ≤ right.length := by
  induction left generalizing right with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
      obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
      obtain ⟨before, after, rfl⟩ :=
        List.append_of_mem (included head (List.Mem.head tail))
      have tailIncluded : ∀ item, item ∈ tail → item ∈ before ++ after := by
        intro item member
        have present := included item (List.Mem.tail head member)
        rcases List.mem_append.mp present with earlier | later
        · exact List.mem_append_left _ earlier
        · rcases List.mem_cons.mp later with same | remaining
          · exact False.elim (absent (same ▸ member))
          · exact List.mem_append_right _ remaining
      have bound := ih tailDistinct tailIncluded
      simp only [List.length_append, List.length_cons] at bound ⊢
      omega

theorem recordsOf_count_le (candidate : Candidate inputs gates outputs)
    (word : List (Fin gates)) :
    (extractTerminalSupport candidate (recordsOf word)).gateCount ≤ word.length := by
  rw [extractTerminalSupport_gateCount]
  apply nodup_length_le_subset (terminalSelectedGates_nodup _)
  intro gate member
  exact (recordsOf_selected_iff word gate).mp
    ((mem_terminalSelectedGates_iff _ gate).mp member)

theorem canonical_selected
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalGateSelected (recordsOf (inputs := inputs) (outputs := outputs)
      (terminalSelectedGates records)) = terminalGateSelected records := by
  funext gate
  have sameTrue := (recordsOf_selected_iff
    (inputs := inputs) (outputs := outputs) (terminalSelectedGates records) gate).trans
      (mem_terminalSelectedGates_iff records gate)
  cases leftAt : terminalGateSelected (recordsOf (inputs := inputs) (outputs := outputs)
      (terminalSelectedGates records)) gate <;>
    cases rightAt : terminalGateSelected records gate
  · rfl
  · have impossible := sameTrue.mpr rightAt
    rw [leftAt] at impossible
    cases impossible
  · have impossible := sameTrue.mp leftAt
    rw [rightAt] at impossible
    cases impossible
  · rfl

/-- The active extractor already places selected gates in strict source order. -/
theorem selected_increasing {gates : Nat} (selected : Fin gates → Bool) :
    (terminalSelectedGateIndices selected).Pairwise
      (fun left right => left.val < right.val) := by
  induction gates with
  | zero => exact .nil
  | succ gates ih =>
      have lifted :
          ((terminalSelectedGateIndices (fun index : Fin gates => selected index.castSucc)).map
            Fin.castSucc).Pairwise (fun left right : Fin (gates + 1) => left.val < right.val) :=
        List.Pairwise.map Fin.castSucc
          (fun left right ordered => ordered) (ih (fun index => selected index.castSucc))
      unfold terminalSelectedGateIndices
      split
      · apply List.pairwise_append.mpr
        refine ⟨lifted, ?_, ?_⟩
        · apply List.pairwise_cons.mpr
          constructor
          · intro item impossible
            cases impossible
          · exact .nil
        · intro left leftMember right rightMember
          obtain ⟨prior, _, rfl⟩ := List.mem_map.mp leftMember
          have last : right = Fin.last gates := List.mem_singleton.mp rightMember
          subst right
          exact prior.isLt
      · exact lifted

/-- Cover every physical selection, irrespective of metadata, order or multiplicity. -/
theorem schedule_covers (candidate : Candidate inputs gates outputs) (limit : Nat)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (bounded : (extractTerminalSupport candidate records).gateCount ≤ limit) :
    ∃ word, word ∈ windowsFrom gates limit 0 ∧
      terminalGateSelected (recordsOf (inputs := inputs) (outputs := outputs) word) =
        terminalGateSelected records := by
  refine ⟨terminalSelectedGates records, ?_, canonical_selected records⟩
  apply windowsFrom_complete
  · simpa only [extractTerminalSupport_gateCount] using bounded
  · exact selected_increasing _
  · intro _gate _member
    exact Nat.zero_le _

private def physicalGainProperty {inputs gates outputs width : Nat}
    {candidate : Candidate inputs gates outputs}
    (support : TerminalExtractedSupport (profileWidth := width) candidate) : Prop :=
  ∃ offered : Implementation support.boundary.length support.interface.length,
    offered.gateCount < support.gateCount ∧
      Equivalent offered.candidate.program offered.candidate.directWireWord
        support.extractedCandidate.program support.extractedCandidate.directWireWord ∧
      ∀ port, CausalBound.outputLevel offered.candidate
        (fun index => (support.boundary.get index).causalLevel
          (fun _ => 0) (fun index => index.val + 1)) port ≤
        (support.interface.get port).val + 1

/-- Equal physical selection preserves the exact local search class across record
widths. This does not assert full-profile observer equivalence. -/
theorem valid_exists_of_selected_eq {fromWidth toWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (left : List (TerminalPrimitiveRecord inputs gates outputs fromWidth))
    (right : List (TerminalPrimitiveRecord inputs gates outputs toWidth))
    (same : terminalGateSelected left = terminalGateSelected right)
    (available : ∃ offered, PhysicalWindowSearch.Valid candidate left offered) :
    ∃ offered, PhysicalWindowSearch.Valid candidate right offered := by
  have first : physicalGainProperty (extractTerminalSupport candidate left) := available
  have equal := extractTerminalSupport_withRecords_of_gateSelected_eq candidate left right same
  have last : physicalGainProperty (extractTerminalSupport candidate right) := by
    rw [← equal]
    exact first
  exact last

end PNP.DirectWire.BoundedWindowSchedule
