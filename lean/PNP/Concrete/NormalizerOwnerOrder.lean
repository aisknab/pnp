/-
Copyright (c) 2026 PNP Labs.

The owner returned by the concrete scanner is the first finite table index in
source order. This connects recursive byte semantics to the finite-range
selection used by the complete matching search, without an ordering premise.
-/

import PNP.Concrete.NormalizerOwnerCanonical

namespace PNP.Concrete.NormalizerBlocks.TableOwner

private theorem map_index_shift (found : Option (Fin count)) (offset : Nat) :
    found.map (fun i => offset + 1 + i.val) =
      (found.map Fin.succ).map (fun i => offset + i.val) := by
  cases found with
  | none => rfl
  | some i =>
      simp only [Option.map_some, Fin.val_succ]
      congr 1
      omega

theorem ownerFrom_ofFn (f : Fin count → Option Nat) (offset target : Nat) :
    ownerFrom offset (List.ofFn f) target =
      ((List.finRange count).find? (fun i => f i == some target)).map (fun i => offset + i.val) := by
  induction count generalizing offset with
  | zero => simp only [List.ofFn_zero, List.finRange_zero, ownerFrom, List.find?_nil, Option.map_none]
  | succ count ih =>
      rw [List.ofFn_succ, List.finRange_succ]
      simp only [List.find?_cons, List.find?_map, Function.comp_def]
      cases first : f 0 with
      | none =>
          change ownerFrom (offset + 1) (List.ofFn (fun i => f i.succ)) target =
            (((List.finRange count).find? (fun i => f i.succ == some target)).map Fin.succ).map
              (fun i => offset + i.val)
          exact (ih (fun i => f i.succ) (offset + 1)).trans (map_index_shift _ offset)
      | some value =>
          rw [show ((some value : Option Nat) == some target) = (value == target) from rfl]
          cases matched : (value == target)
          · simp only [ownerFrom, matched, Bool.false_eq_true, ite_false]
            exact (ih (fun i => f i.succ) (offset + 1)).trans (map_index_shift _ offset)
          · simp only [ownerFrom, matched, ite_true, Option.map_some, Fin.val_zero, Nat.add_zero]

theorem owner_ofFn (f : Fin count → Option Nat) (target : Nat) :
    owner (List.ofFn f) target =
      ((List.finRange count).find? (fun i => f i == some target)).map Fin.val := by
  simpa only [owner, Nat.zero_add] using ownerFrom_ofFn f 0 target

end PNP.Concrete.NormalizerBlocks.TableOwner
