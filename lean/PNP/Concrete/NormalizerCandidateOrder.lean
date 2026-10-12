/-
Copyright (c) 2026 PNP Labs.

Increasing-index order and table membership for the closed candidate machine.
These theorems identify the first eligible finite-range value, independently
of the length or ordering of the supplied tables. Reachability construction
is a separate obligation.
-/

import PNP.Concrete.NormalizerCandidatePolynomial

namespace PNP.Concrete.NormalizerBlocks

namespace TableOwner

theorem ownerFrom_isSome (offset : Nat) (entries : MatchingTable.Entries) (target : Nat) :
    (ownerFrom offset entries target).isSome = entries.any (fun entry => entry == some target) := by
  induction entries generalizing offset with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | none => exact ih (offset + 1)
      | some value =>
          cases same : (value == target) with
          | false =>
              simpa only [ownerFrom, same, Bool.false_eq_true, ite_false, List.any_cons,
                Option.some_beq_some, Bool.false_or] using ih (offset + 1)
          | true =>
              simp only [ownerFrom, same, ite_true, Option.isSome_some, List.any_cons,
                Option.some_beq_some, Bool.true_or]

theorem owner_isSome (entries : MatchingTable.Entries) (target : Nat) :
    (owner entries target).isSome = entries.any (fun entry => entry == some target) :=
  ownerFrom_isSome 0 entries target

end TableOwner

namespace Candidate

def eligible (matching seen : MatchingTable.Entries) (index : Nat) : Bool :=
  (TableOwner.owner matching index).isNone && (TableOwner.owner seen index).isSome

theorem selectFrom_succ (matching seen : MatchingTable.Entries) (count index : Nat) :
    selectFrom matching seen (count + 1) index =
      if eligible matching seen index then some index else selectFrom matching seen count (index + 1) := by
  cases matched : TableOwner.owner matching index <;>
    cases visited : TableOwner.owner seen index <;>
    simp only [selectFrom, eligible, matched, visited, Option.isNone_none, Option.isNone_some,
      Option.isSome_none, Option.isSome_some, Bool.true_and, Bool.false_and,
      Bool.false_eq_true, ite_false, ite_true]

private theorem map_index_shift (found : Option (Fin count)) (offset : Nat) :
    found.map (fun i => offset + 1 + i.val) =
      (found.map Fin.succ).map (fun i => offset + i.val) := by
  cases found with
  | none => rfl
  | some i =>
      simp only [Option.map_some, Fin.val_succ]
      congr 1
      omega

theorem selectFrom_finRange (matching seen : MatchingTable.Entries) (count index : Nat) :
    selectFrom matching seen count index =
      ((List.finRange count).find? (fun i => eligible matching seen (index + i.val))).map
        (fun i => index + i.val) := by
  induction count generalizing index with
  | zero => simp only [selectFrom, List.finRange_zero, List.find?_nil, Option.map_none]
  | succ count ih =>
      rw [selectFrom_succ, List.finRange_succ]
      simp only [List.find?_cons, List.find?_map, Function.comp_def, Fin.val_zero, Nat.add_zero]
      cases first : eligible matching seen index with
      | false =>
          simp only [Bool.false_eq_true, ite_false]
          have shifted :
              (fun i : Fin count => eligible matching seen (index + 1 + i.val)) =
                (fun i : Fin count => eligible matching seen (index + i.succ.val)) := by
            funext i
            congr 1
            simp only [Fin.val_succ]
            omega
          rw [← shifted]
          exact (ih (index + 1)).trans (map_index_shift _ index)
      | true => simp only [ite_true, Option.map_some, Fin.val_zero, Nat.add_zero]

theorem select_finRange (matching seen : MatchingTable.Entries) (count : Nat) :
    selectFrom matching seen count 0 =
      ((List.finRange count).find? (fun i => eligible matching seen i.val)).map Fin.val := by
  simpa only [Nat.zero_add] using selectFrom_finRange matching seen count 0

theorem polynomial_finRange (matching seen : MatchingTable.Entries) (count : Nat) :
    CandidatePacket.polynomial.output (CandidatePacket.encode count matching seen) =
      TableOwner.answer (((List.finRange count).find? (fun i => eligible matching seen i.val)).map Fin.val) := by
  rw [CandidatePacket.polynomial_canonical, select_finRange]

end Candidate

end PNP.Concrete.NormalizerBlocks
