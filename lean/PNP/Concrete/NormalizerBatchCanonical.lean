/-
Copyright (c) 2026 PNP Labs.

Exact semantics of the fixed repeated-update loop for arbitrary finite update
lists, including repeated and out-of-range indices. The list is consumed in
source order, so the last write to a repeated index wins. The input packet
loader and final closed whole-input compiler wrapper remain separate steps.
-/

import PNP.Concrete.NormalizerBatchCanonicalBody

namespace PNP.Concrete.NormalizerBlocks.TableBatch

def encodeUpdates : List (Nat × Nat) → BitString
  | [] => []
  | (index, value) :: rest => encodePair index value (encodeUpdates rest)

theorem encodePair_length (index value : Nat) (rest : BitString) :
    (encodePair index value rest).length = index + value + rest.length + 2 := by
  simp only [encodePair, List.length_append, List.length_replicate, List.length_cons]
  omega

theorem encodePair_nonempty (index value : Nat) (rest : BitString) : encodePair index value rest ≠ [] := by
  intro empty
  have length := encodePair_length index value rest
  rw [empty, List.length_nil] at length
  omega

theorem run_canonical (updates : List (Nat × Nat)) (fuel : Nat) (r : State) (entries : MatchingTable.Entries)
    (pending : r.pending = encodeUpdates updates) (table : r.table = MatchingTable.encode entries)
    (enough : r.pending.length < fuel ∨ r.pending = []) :
    (run fuel r).state.table = MatchingTable.encode (MatchingTable.writeAll entries updates) := by
  induction updates generalizing fuel r entries with
  | nil =>
      have stopped : r.pending = [] := pending
      cases fuel with
      | zero => exact table
      | succ fuel => simpa only [run, stopped, MatchingTable.writeAll] using table
  | cons pair rest ih =>
      rcases pair with ⟨index,value⟩
      have nonempty : r.pending ≠ [] := by
        rw [pending]
        exact encodePair_nonempty index value (encodeUpdates rest)
      cases fuel with
      | zero =>
          cases enough with
          | inl bound => exact False.elim (Nat.not_lt_zero _ bound)
          | inr empty => exact False.elim (nonempty empty)
      | succ fuel =>
          have length : r.pending.length ≤ fuel := by
            cases enough with
            | inl bound => omega
            | inr empty => exact False.elim (nonempty empty)
          have updated := body_canonical r entries index value (encodeUpdates rest) pending table
          have nextEnough := Nat.lt_of_lt_of_le (pending_strict r nonempty) length
          have tail := ih fuel (result r) (MatchingTable.write entries index value)
            updated.1 updated.2 (Or.inl nextEnough)
          cases current : r.pending with
          | nil => exact False.elim (nonempty current)
          | cons bit word => simpa only [run, current, MatchingTable.writeAll] using tail

def initial (pending table : BitString) : State :=
  ⟨Occurrence.initialRegisters [], pending, table⟩

theorem whole_canonical (updates : List (Nat × Nat)) (entries : MatchingTable.Entries) :
    (whole (initial (encodeUpdates updates) (MatchingTable.encode entries))).state.table =
      MatchingTable.encode (MatchingTable.writeAll entries updates) :=
  run_canonical updates _ _ entries rfl rfl (Or.inl (Nat.lt_succ_self _))

theorem empty_updates_preserve (table : BitString) :
    (whole (initial (encodeUpdates []) table)).state.table = table := rfl

theorem repeated_index_last_wins (entries : MatchingTable.Entries) (index first last : Nat) :
    (whole (initial (encodeUpdates [(index,first),(index,last)]) (MatchingTable.encode entries))).state.table =
      MatchingTable.encode (MatchingTable.write entries index last) := by
  rw [whole_canonical]
  simp only [MatchingTable.writeAll, MatchingTable.write_last_wins]

end PNP.Concrete.NormalizerBlocks.TableBatch
