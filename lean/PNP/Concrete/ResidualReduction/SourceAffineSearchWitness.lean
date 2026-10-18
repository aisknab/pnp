import PNP.Concrete.ResidualReduction.SourceAffineSearchLoop

/-! Interpret the retained search indices without assuming they are valid.
The indexed direction search is exactly the original first-success query,
and a successful result decodes to an actual weight/direction pair. -/

namespace PNP.Concrete.ResidualReduction.SourceAffineSearch
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.SourceCandidateDirectionSearch

def candidatePairs {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k)) :
    List (Point F.length × Point n) :=
  (List.finRange n).map fun j => (mapEval forms (SourceCandidateMapInstructions.parameter q), unitPoint n j)
def directionWitness {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (q : Option (Fin k)) (result : Nat × Bool) : Option (Point F.length × Point n) :=
  if result.2 then
    if h : result.1 < n then some (mapEval forms (SourceCandidateMapInstructions.parameter q), unitPoint n ⟨result.1, h⟩)
    else none
  else none

theorem directionWitness_exact {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k)) :
    directionWitness F forms q (scan (active F forms q) n 0) =
      firstTrue (fun p => weightedActivity F p.1 p.2) (candidatePairs F forms q) := by
  let result := scan (active F forms q) n 0
  let candidate := firstTrue
    (fun j : Fin n => weightedActivity F (mapEval forms (SourceCandidateMapInstructions.parameter q)) (unitPoint n j))
    (List.finRange n)
  have relation : candidate.map Fin.val = if result.2 then some result.1 else none := scan_indices_exact F forms q
  have pairs : firstTrue (fun p => weightedActivity F p.1 p.2) (candidatePairs F forms q) =
      candidate.map (fun j => (mapEval forms (SourceCandidateMapInstructions.parameter q), unitPoint n j)) :=
    firstTrue_map _ _ _
  change directionWitness F forms q result = _
  rw [pairs]
  cases h : candidate with
  | none =>
    cases found : result.2 with
    | false => simp only [directionWitness, found, Bool.false_eq_true, if_false, Option.map_none]
    | true =>
      have bad : (none : Option Nat) = some result.1 := by
        simpa only [h, Option.map_none, found, if_true] using relation
      cases bad
  | some j =>
    cases found : result.2 with
    | false =>
      have bad : some j.val = (none : Option Nat) := by
        simpa only [h, Option.map_some, found, Bool.false_eq_true, if_false] using relation
      cases bad
    | true =>
      have index : j.val = result.1 := Option.some.inj (by
        simpa only [h, Option.map_some, found, if_true] using relation)
      simp only [directionWitness, found, if_true, Option.map_some]
      rw [← index, dif_pos j.isLt]

theorem directionWitness_isSome {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k)) :
    (directionWitness F forms q (scan (active F forms q) n 0)).isSome = (scan (active F forms q) n 0).2 := by
  rw [directionWitness_exact, candidatePairs, firstTrue_map, Option.isSome_map]
  have relation := congrArg Option.isSome (scan_indices_exact F forms q)
  rw [Option.isSome_map] at relation
  cases found : (scan (active F forms q) n 0).2 <;>
    simpa only [found, Bool.false_eq_true, if_false, if_true, Option.isSome] using relation

def decode {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (result : Outcome) :
    Option (Point F.length × Point n) :=
  if result.unitParameter then
    if h : result.parameterIndex < k then
      directionWitness F forms (some ⟨result.parameterIndex, h⟩) (result.directionIndex, result.found)
    else none
  else directionWitness F forms none (result.directionIndex, result.found)

theorem decode_false {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (mode : Bool) (i j : Nat) :
    decode F forms ⟨mode, i, j, false⟩ = none := by
  cases mode with
  | false => rfl
  | true =>
    unfold decode
    simp only [if_true]
    split <;> rfl

theorem decode_unit {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (i : Fin k) (result : Nat × Bool) :
    decode F forms ⟨true, i.val, result.1, result.2⟩ = directionWitness F forms (some i) result := by
  simp only [decode, if_true, dif_pos i.isLt]

theorem decode_zero {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (result : Nat × Bool) :
    decode F forms ⟨false, 0, result.1, result.2⟩ = directionWitness F forms none result := rfl

theorem unitResult_fin {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (i : Fin k) :
    unitResult F forms i.val = scan (active F forms (some i)) n 0 := by
  simp only [unitResult, dif_pos i.isLt]

theorem decode_unit_result {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (i : Fin k) :
    decode F forms ⟨true, i.val, (unitResult F forms i.val).1, (unitResult F forms i.val).2⟩ =
      firstTrue (fun p => weightedActivity F p.1 p.2) (candidatePairs F forms (some i)) := by
  rw [decode_unit, unitResult_fin, directionWitness_exact]

theorem unitResult_isSome {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (i : Fin k) :
    (firstTrue (fun p => weightedActivity F p.1 p.2) (candidatePairs F forms (some i))).isSome =
      (unitResult F forms i.val).2 := by
  rw [unitResult_fin, ← directionWitness_exact]
  exact directionWitness_isSome F forms (some i)

end PNP.Concrete.ResidualReduction.SourceAffineSearch
