import PNP.Concrete.ResidualReduction.SourceAffineEncodedSearch
import PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra

/-! A flat bilinear matrix can be represented by linear source rows without
changing the ordered affine search or its witness bytes. The weight space is
the original supplied representation, not a new affine-mask solver result.
Construction from encoded matrix bytes is charged separately. -/

namespace PNP.Concrete.ResidualReduction.SourceBilinearFamily
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

def row {n : Nat} (f : Fin n → Bool) : Row n :=
  ⟨false, coefficientForm f, aConst n true⟩

theorem row_activity {n : Nat} (f : Fin n → Bool) (x : Point n) :
    activity (row f) x = rowDot f x := by
  simp only [activity, row, Row.eval, aConst_eval, Bool.and_true,
    coefficientForm_eval, rowDot_zero, Bool.xor_false]

def family : {m n : Nat} → Matrix m n → Family n
  | 0, _, _ => []
  | _ + 1, _, M => row (M 0) :: family (fun i => M i.succ)

theorem family_length {m n : Nat} (M : Matrix m n) : (family M).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [family, List.length_cons, ih]

/-- Structural reindexing only; the encoded point is unchanged. -/
def weights : {m n : Nat} → (M : Matrix m n) → Point m → Point (family M).length
  | 0, _, _, _ => ()
  | _ + 1, _, M, (b, w) => (b, weights (fun i => M i.succ) w)

def forms : {m n k : Nat} → (M : Matrix m n) → AffineMap m k → AffineMap (family M).length k
  | 0, _, _, _, _ => ()
  | _ + 1, _, _, M, (a, rest) => (a, forms (fun i => M i.succ) rest)

def space {m n : Nat} (M : Matrix m n) (s : Space m) : Space (family M).length :=
  ⟨s.parameters, forms M s.forms⟩

theorem weights_bits {m n : Nat} (M : Matrix m n) (w : Point m) :
    (SourceEncoding.pointCodec (family M).length).encode (weights M w) =
      (SourceEncoding.pointCodec m).encode w := by
  induction m with
  | zero => cases w; rfl
  | succ m ih =>
    rcases w with ⟨b, w⟩
    change b :: (SourceEncoding.pointCodec _).encode (weights (fun i => M i.succ) w) =
      b :: (SourceEncoding.pointCodec m).encode w
    rw [ih]

theorem forms_bits {m n k : Nat} (M : Matrix m n) (fs : AffineMap m k) :
    mapBits (forms M fs) = mapBits fs := by
  induction m with
  | zero => cases fs; rfl
  | succ m ih =>
    rcases fs with ⟨a, fs⟩
    change affineWord a ++ mapBits (forms (fun i => M i.succ) fs) = affineWord a ++ mapBits fs
    rw [ih]

theorem forms_eval {m n k : Nat} (M : Matrix m n) (fs : AffineMap m k) (z : Point k) :
    mapEval (forms M fs) z = weights M (mapEval fs z) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rcases fs with ⟨a, fs⟩
    change (aEval a z, mapEval (forms (fun i => M i.succ) fs) z) =
      (aEval a z, weights (fun i => M i.succ) (mapEval fs z))
    rw [ih]

theorem weighted_activity {m n : Nat} (M : Matrix m n) (w : Point m) (x : Point n) :
    weightedActivity (family M) (weights M w) x = bilinearEval M w x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rcases w with ⟨b, w⟩
    change Bool.xor (b && activity (row (M 0)) x)
      (weightedActivity (family (fun i => M i.succ)) (weights (fun i => M i.succ) w) x) =
      Bool.xor (b && rowDot (M 0) x) (bilinearEval (fun i => M i.succ) w x)
    rw [row_activity, ih]

def pair {m n : Nat} (M : Matrix m n) (p : Point m × Point n) :
    Point (family M).length × Point n := (weights M p.1, p.2)

theorem testPairs_exact {m n : Nat} (M : Matrix m n) (s : Space m) :
    affineTestPairs (space M s) n = (affineTestPairs s n).map (pair M) := by
  simp only [affineTestPairs, space, List.map_flatMap, List.map_map, Function.comp_def]
  congr 1
  funext z
  congr 1
  funext j
  simp only [pair, forms_eval]

theorem firstTrue_map {X Y : Type} (f : Y → Bool) (g : X → Y) (xs : List X) :
    firstTrue f (xs.map g) = (firstTrue (fun x => f (g x)) xs).map g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f (g x) <;> simp only [List.map_cons, firstTrue, h, ih, Option.map_some]

theorem query_exact {m n : Nat} (M : Matrix m n) (s : Space m) :
    SourceClosure.affineSpaceQuery (family M) (space M s) =
      (affineBilinearQuery s M).map (pair M) := by
  rw [SourceClosure.affineSpaceQuery, testPairs_exact, firstTrue_map]
  simp only [pair, weighted_activity, affineBilinearQuery]

theorem witness_bits {m n : Nat} (M : Matrix m n) (value : Option (Point m × Point n)) :
    (SourceAffineOutput.witnessCodec (family M).length n).encode (value.map (pair M)) =
      (SourceAffineOutput.witnessCodec m n).encode value := by
  cases value with
  | none => rfl
  | some p =>
    change true :: ((SourceEncoding.pointCodec _).encode (weights M p.1) ++
      (SourceEncoding.pointCodec n).encode p.2) =
      true :: ((SourceEncoding.pointCodec m).encode p.1 ++ (SourceEncoding.pointCodec n).encode p.2)
    rw [weights_bits]

theorem search_output_exact {m n : Nat} (M : Matrix m n) (s : Space m) :
    (SourceAffineOutput.witnessCodec (family M).length n).encode
      (SourceAffineSearch.decode (family M) (space M s).forms
        (SourceAffineSearch.outcome (family M) (space M s).forms)) =
      (SourceAffineOutput.witnessCodec m n).encode (affineBilinearQuery s M) := by
  rw [SourceAffineSearch.affineSpaceQuery_exact, query_exact, witness_bits]

theorem coefficient_word {n : Nat} (f : Fin n → Bool) :
    affineWord (coefficientForm f) = (List.finRange n).map f ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [coefficientForm, affineWord_cons, List.finRange_succ,
      List.map_cons, List.map_map, Function.comp_def, List.cons_append, ih]

theorem constant_word (n : Nat) (b : Bool) :
    affineWord (aConst n b) = List.replicate n false ++ [b] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [aConst, affineWord_cons, List.replicate_succ, List.cons_append, ih]

theorem row_word {n : Nat} (f : Fin n → Bool) :
    rowWord (row f) = false :: ((List.finRange n).map f ++
      (false :: (List.replicate n false ++ [true]))) := by
  simp only [rowWord, row, coefficient_word, constant_word, List.append_assoc, List.singleton_append]

theorem family_bits_length {m n : Nat} (M : Matrix m n) :
    (familyBits (family M)).length = (2 * n + 3) * m := by
  rw [familyBits_length, family_length]

/-- Includes failed candidates and canonical witness output, but not the
matrix-to-family construction or the solver/input handoff. -/
theorem query_exec {m n : Nat} (M : Matrix m n) (s : Space m) :
    ∃ used after, Exec SourceAffineOutput.query
      (SourceAffineSearch.ready (family M) (space M s).forms false 0 0 n 0 false).store used after ∧
      after.get 8 = (SourceAffineOutput.witnessCodec m n).encode (affineBilinearQuery s M) ∧
      used ≤ (SourceAffineSearch.directionBudget n s.parameters m + 7) * (s.parameters + 1) +
        SourceAffineOutput.outputBudget n s.parameters m := by
  obtain ⟨used, after, execution, bytes, bound⟩ := SourceAffineOutput.query_exec (family M) (space M s).forms
  rw [search_output_exact] at bytes
  have search := SourceAffineSearch.fuel_bound (family M) (space M s).forms
  have total := Nat.le_trans bound (Nat.add_le_add_right search
    (SourceAffineOutput.outputBudget n s.parameters (family M).length))
  refine ⟨used, after, execution, bytes, ?_⟩
  simpa only [space, family_length] using total

end PNP.Concrete.ResidualReduction.SourceBilinearFamily
