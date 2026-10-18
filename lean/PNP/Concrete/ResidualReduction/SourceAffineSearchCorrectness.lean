import PNP.Concrete.ResidualReduction.SourceAffineSearchWitness

/-! The complete counter-based search preserves the existing zero-then-unit,
first-success query exactly. No premise supplies a successful candidate or
asserts activity. Failure remains a valid result, including empty dimensions. -/

namespace PNP.Concrete.ResidualReduction.SourceAffineSearch
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourcePlane

theorem firstTrue_append {X : Type} (p : X → Bool) (xs ys : List X) :
    firstTrue p (xs ++ ys) = match firstTrue p xs with
      | none => firstTrue p ys
      | some x => some x := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : p x <;> simp only [List.cons_append, firstTrue, h, ih]

def unitPairs {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (i : Nat) :
    List (Point F.length × Point n) :=
  if h : i < k then candidatePairs F forms (some ⟨i, h⟩) else []
def unitPairsBlock {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (count i : Nat) :
    List (Point F.length × Point n) :=
  (List.range' i count).flatMap (unitPairs F forms)

theorem unitPairs_fin {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (i : Fin k) :
    unitPairs F forms i.val = candidatePairs F forms (some i) := by
  simp only [unitPairs, dif_pos i.isLt]
theorem unitPairsBlock_succ {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (count i : Nat) :
    unitPairsBlock F forms (count + 1) i = unitPairs F forms i ++ unitPairsBlock F forms count (i + 1) := by
  simp only [unitPairsBlock, List.range'_succ, List.flatMap_cons]

theorem unitSearch_exact {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (count i : Nat) (bound : i + count ≤ k) :
    decode F forms (unitSearch F forms count i) =
      firstTrue (fun p => weightedActivity F p.1 p.2) (unitPairsBlock F forms count i) := by
  induction count generalizing i with
  | zero => exact decode_false F forms true i 0
  | succ count ih =>
    have inside : i < k := by omega
    let current : Fin k := ⟨i, inside⟩
    have pairs : unitPairs F forms i = candidatePairs F forms (some current) := unitPairs_fin F forms current
    have flag := unitResult_isSome F forms current
    have result := decode_unit_result F forms current
    cases witness : firstTrue (fun p => weightedActivity F p.1 p.2) (candidatePairs F forms (some current)) with
    | none =>
      have failed : (unitResult F forms i).2 = false := by
        rw [witness] at flag
        exact flag.symm
      simp only [unitSearch, failed, Bool.false_eq_true, if_false, unitPairsBlock_succ, pairs,
        firstTrue_append, witness]
      exact ih (i + 1) (by omega)
    | some w =>
      have found : (unitResult F forms i).2 = true := by
        rw [witness] at flag
        exact flag.symm
      rw [found, witness] at result
      simpa only [unitSearch, found, if_true, unitPairsBlock_succ, pairs, firstTrue_append, witness] using result

theorem unitPairsBlock_exact {n k : Nat} (F : Family n) (forms : AffineMap F.length k) :
    unitPairsBlock F forms k 0 = (List.finRange k).flatMap (fun i => candidatePairs F forms (some i)) := by
  unfold unitPairsBlock
  rw [← SourceMatrixSchedule.finite_range_values k, List.flatMap_map]
  congr 1
  funext i
  exact unitPairs_fin F forms i

def allPairs {n k : Nat} (F : Family n) (forms : AffineMap F.length k) :
    List (Point F.length × Point n) :=
  candidatePairs F forms none ++ unitPairsBlock F forms k 0

theorem allPairs_exact {n : Nat} (F : Family n) (s : Space F.length) :
    allPairs F s.forms = affineTestPairs s n := by
  rw [allPairs, unitPairsBlock_exact]
  simp only [affineTestPairs, affineParameters, List.flatMap_cons, List.flatMap_map,
    candidatePairs, SourceCandidateMapInstructions.parameter]

theorem zeroResult_isSome {n k : Nat} (F : Family n) (forms : AffineMap F.length k) :
    (firstTrue (fun p => weightedActivity F p.1 p.2) (candidatePairs F forms none)).isSome =
      (zeroResult F forms).2 := by
  rw [← directionWitness_exact]
  exact directionWitness_isSome F forms none

theorem outcome_exact {n k : Nat} (F : Family n) (forms : AffineMap F.length k) :
    decode F forms (outcome F forms) = firstTrue (fun p => weightedActivity F p.1 p.2) (allPairs F forms) := by
  have flag := zeroResult_isSome F forms
  have result : decode F forms ⟨false, 0, (zeroResult F forms).1, (zeroResult F forms).2⟩ =
      firstTrue (fun p => weightedActivity F p.1 p.2) (candidatePairs F forms none) :=
    directionWitness_exact F forms none
  cases witness : firstTrue (fun p => weightedActivity F p.1 p.2) (candidatePairs F forms none) with
  | none =>
    have failed : (zeroResult F forms).2 = false := by
      rw [witness] at flag
      exact flag.symm
    simp only [outcome, failed, Bool.false_eq_true, if_false, allPairs, firstTrue_append, witness]
    exact unitSearch_exact F forms k 0 (by omega)
  | some w =>
    have found : (zeroResult F forms).2 = true := by
      rw [witness] at flag
      exact flag.symm
    rw [found, witness] at result
    simpa only [outcome, found, if_true, allPairs, firstTrue_append, witness] using result

theorem affineSpaceQuery_exact {n : Nat} (F : Family n) (s : Space F.length) :
    decode F s.forms (outcome F s.forms) = SourceClosure.affineSpaceQuery F s := by
  rw [outcome_exact, allPairs_exact]
  rfl

theorem computed_query_exact {n : Nat} (F : Family n) (s : Space F.length)
    (computed : solve F.length (SourceClosure.affineMaskRows F) = some s) :
    decode F s.forms (outcome F s.forms) = SourceClosure.sourceAffineQuery F := by
  rw [SourceClosure.sourceAffineQuery, computed]
  exact affineSpaceQuery_exact F s

theorem unitSearch_isSome {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (count i : Nat) (bound : i + count ≤ k) :
    (decode F forms (unitSearch F forms count i)).isSome = (unitSearch F forms count i).found := by
  induction count generalizing i with
  | zero => rw [unitSearch, decode_false]; rfl
  | succ count ih =>
    have inside : i < k := by omega
    let current : Fin k := ⟨i, inside⟩
    have checked := unitResult_isSome F forms current
    rw [← decode_unit_result] at checked
    cases found : (unitResult F forms i).2 with
    | false =>
      simp only [unitSearch, found, Bool.false_eq_true, if_false]
      exact ih (i + 1) (by omega)
    | true =>
      rw [found] at checked
      simpa only [unitSearch, found, if_true] using checked

theorem outcome_isSome {n k : Nat} (F : Family n) (forms : AffineMap F.length k) :
    (decode F forms (outcome F forms)).isSome = (outcome F forms).found := by
  have checked := directionWitness_isSome F forms none
  change (decode F forms ⟨false, 0, (zeroResult F forms).1, (zeroResult F forms).2⟩).isSome =
    (zeroResult F forms).2 at checked
  cases found : (zeroResult F forms).2 with
  | false =>
    simp only [outcome, found, Bool.false_eq_true, if_false]
    exact unitSearch_isSome F forms k 0 (by omega)
  | true =>
    rw [found] at checked
    simpa only [outcome, found, if_true] using checked

end PNP.Concrete.ResidualReduction.SourceAffineSearch
