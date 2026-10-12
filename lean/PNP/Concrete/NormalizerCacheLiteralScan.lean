/-
Copyright (c) 2026 PNP Labs.

Read an arbitrary literal position from actual encoded clause bytes.
The skip counter is consumed by finite instructions, and each literal read
uses the existing bounded parser. No literal or sign is supplied as an answer.
-/
import PNP.Concrete.NormalizerCacheSlotCall

namespace PNP.Concrete.NormalizerBlocks.CacheLiteral
open BitRegister Occurrence
abbrev State := DenseClauses.State

def skipStep : Block 16 := .seq (.action (.pop 14)) CacheSlot.readLiteral
def skip : Block 16 := .loop 14 skipStep
def skipped : BitString → State → State
  | [], r => {r with remaining := []}
  | _::rest, r => skipped rest (CacheSlot.literalRead {r with remaining := rest})
def skipFuel : BitString → State → Nat
  | [], _ => 1
  | _::rest, r =>
      1 + (1 + CompactClause.readFuel r.core +
        skipFuel rest (CacheSlot.literalRead {r with remaining := rest}))

theorem skip_exec (word : BitString) (r : State) :
    Exec skip ({r with remaining := word}).store (skipFuel word r) (skipped word r).store := by
  induction word generalizing r with
  | nil => exact Exec.loopStop (source := (14 : Fin 16)) rfl
  | cons bit rest ih =>
      exact Exec.loopStep (source := (14 : Fin 16)) rfl
        (Exec.seq (.action _ _) (CacheSlot.readLiteral_exec {r with remaining := rest}))
        (ih (CacheSlot.literalRead {r with remaining := rest}))

theorem read_pending_bound (r : State) :
    (CacheSlot.literalRead r).core.pending.length ≤ r.core.pending.length := by
  change (CompactClause.next r.core.pending).length ≤ r.core.pending.length
  cases h : r.core.pending with
  | nil => exact Nat.le_refl _
  | cons bit rest =>
      exact Nat.le_of_lt (CompactClause.next_shorter _ (by intro impossible; cases impossible))

theorem skipped_fields (word : BitString) (r : State) :
    (skipped word r).formula = r.formula ∧
    (skipped word r).remaining = [] ∧
    (skipped word r).index = r.index ∧
    (skipped word r).core.variables = r.core.variables ∧
    (skipped word r).core.buffer = r.core.buffer := by
  induction word generalizing r with
  | nil => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | cons bit rest ih => exact ih (CacheSlot.literalRead {r with remaining := rest})

theorem skipped_pending_bound (word : BitString) (r : State) :
    (skipped word r).core.pending.length ≤ r.core.pending.length := by
  induction word generalizing r with
  | nil => exact Nat.le_refl _
  | cons bit rest ih =>
      exact Nat.le_trans (ih (CacheSlot.literalRead {r with remaining := rest}))
        (read_pending_bound {r with remaining := rest})

theorem skipFuel_bound (word : BitString) (r : State) :
    skipFuel word r ≤ (3 * r.core.pending.length + 25) * word.length + 1 := by
  induction word generalizing r with
  | nil => simp only [skipFuel,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.le_refl]
  | cons bit rest ih =>
      have cost := CompactClause.readFuel_bound r.core
      have smaller := read_pending_bound {r with remaining := rest}
      change (CacheSlot.literalRead {r with remaining := rest}).core.pending.length ≤ r.core.pending.length at smaller
      have tail := ih (CacheSlot.literalRead {r with remaining := rest})
      have mul := Nat.mul_le_mul_right rest.length
        (Nat.add_le_add_right (Nat.mul_le_mul_left 3 smaller) 25)
      simp only [skipFuel,List.length_cons,Nat.mul_add,Nat.mul_one]
      omega

theorem skipped_canonical (leading : List CNFLiteral) (r : State) (suffix : BitString)
    (pending : r.core.pending = CompactClause.bits leading ++ suffix) :
    (skipped (List.replicate leading.length true) r).core.pending = suffix := by
  induction leading generalizing r with
  | nil => exact pending
  | cons literal rest ih =>
      have read := CompactClause.read_canonical r.core literal
        (CompactClause.bits rest ++ suffix)
        (by rw [CompactClause.bits_cons,List.append_assoc] at pending; exact pending)
      rw [List.length_cons,List.replicate_succ]
      exact ih (CacheSlot.literalRead {r with remaining := List.replicate rest.length true}) read.2.1

def select : Block 16 := .seq skip CacheSlot.readLiteral
def selected (r : State) : State := CacheSlot.literalRead (skipped r.remaining r)
def selectFuel (r : State) : Nat :=
  skipFuel r.remaining r + CompactClause.readFuel (skipped r.remaining r).core
theorem select_exec (r : State) :
    Exec select r.store (selectFuel r) (selected r).store := by
  have same : {r with remaining := r.remaining} = r := rfl
  have first := skip_exec r.remaining r
  rw [same] at first
  exact Exec.seq first (CacheSlot.readLiteral_exec (skipped r.remaining r))
theorem selected_fields (r : State) :
    (selected r).formula = r.formula ∧ (selected r).remaining = [] ∧
    (selected r).index = r.index ∧ (selected r).core.variables = r.core.variables ∧
    (selected r).core.buffer = r.core.buffer := skipped_fields r.remaining r
theorem selectFuel_bound (r : State) :
    selectFuel r ≤ (3 * r.core.pending.length + 25) * (r.remaining.length + 1) := by
  have skipCost := skipFuel_bound r.remaining r
  have next := skipped_pending_bound r.remaining r
  have read := CompactClause.readFuel_bound (skipped r.remaining r).core
  unfold selectFuel
  simp only [Nat.mul_add,Nat.mul_one]
  omega
theorem selected_index_bound (r : State) :
    (selected r).registers.target.length ≤ r.core.pending.length := by
  have index := CompactClause.index_bound (skipped r.remaining r).core.pending
  exact Nat.le_trans index (skipped_pending_bound r.remaining r)
theorem selected_canonical (r : State) (leading : List CNFLiteral)
    (literal : CNFLiteral) (suffix : BitString)
    (pending : r.core.pending = CompactClause.bits leading ++
      (NANDFrontend.literalBits literal.positive literal.variableIndex ++ suffix))
    (position : r.remaining = List.replicate leading.length true) :
    (selected r).registers.target = List.replicate literal.variableIndex true ∧
      ForwardEdge.present (selected r).core.positive = literal.positive := by
  have rest := skipped_canonical leading r
    (NANDFrontend.literalBits literal.positive literal.variableIndex ++ suffix) pending
  rw [← position] at rest
  have read := CompactClause.read_canonical (skipped r.remaining r).core literal suffix rest
  exact ⟨read.1,read.2.2⟩

end PNP.Concrete.NormalizerBlocks.CacheLiteral
