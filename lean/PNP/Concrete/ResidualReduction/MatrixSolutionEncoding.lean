import PNP.Concrete.ResidualReduction.MatrixRowInstructions

/-! Canonical finite coefficients for the complete linear solution space.
These codecs contain actual coefficient data, not a function-valued oracle.
Their size bounds are representation facts; execution costs are proved by the
concrete construction routines rather than inferred from these lengths. -/

namespace PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions

def mapRows : {n k : Nat} → AffineMap n k → System k
  | 0, _, _ => []
  | _ + 1, _, (f, fs) => f :: mapRows fs

def mapBits {n k : Nat} (m : AffineMap n k) : BitString := matrixBits (mapRows m)

theorem mapRows_length {n k : Nat} (m : AffineMap n k) : (mapRows m).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases m with ⟨f, fs⟩
    change (mapRows fs).length + 1 = n + 1
    rw [ih fs]

theorem mapBits_length {n k : Nat} (m : AffineMap n k) :
    (mapBits m).length = n * (k + 1) := by
  rw [mapBits, matrixBits_length, mapRows_length]
  exact Nat.mul_comm _ _

theorem mapBits_cons {n k : Nat} (f : Affine k) (fs : AffineMap n k) :
    mapBits (n := n + 1) (f, fs) = affineWord f ++ mapBits fs := rfl

def mapCodec : (n k : Nat) → Codec (AffineMap n k)
  | 0, _ => SourceEncoding.unitCodec
  | n + 1, k => pairCodec (SourceEncoding.affineCodec k) (mapCodec n k)

theorem mapCodec_bits {n k : Nat} (m : AffineMap n k) :
    (mapCodec n k).encode m = mapBits m := by
  induction n with
  | zero => cases m; rfl
  | succ n ih =>
    rcases m with ⟨f, fs⟩
    change affineWord f ++ (mapCodec n k).encode fs = affineWord f ++ mapBits fs
    rw [ih fs]

def spaceCodec (n : Nat) : Codec (Space n) :=
  mappedCodec (SourceEncoding.dependentCodec natCodec (fun k => mapCodec n k))
    (fun x => ⟨x.1, x.2⟩) (fun s => ⟨s.parameters, s.forms⟩)
    (by intro s; cases s; rfl) (by rintro ⟨k, m⟩; rfl)

theorem spaceCodec_length {n : Nat} (s : Space n) :
    ((spaceCodec n).encode s).length = (n + 1) * (s.parameters + 1) := by
  change (natural s.parameters ++ (mapCodec n s.parameters).encode s.forms).length = _
  simp only [List.length_append, natural_length, mapCodec_bits, mapBits_length,
    Nat.add_mul, Nat.one_mul]
  omega

theorem solve_space_bound {n : Nat} (rows : System n) (s : Space n)
    (computed : solve n rows = some s) :
    ((spaceCodec n).encode s).length ≤ (n + 1) * (n + 1) := by
  rw [spaceCodec_length]
  exact Nat.mul_le_mul_left (n + 1)
    (Nat.succ_le_succ (solve_some_parameter_bound rows s computed))

def optionCodec (C : Codec α) : Codec (Option α) where
  encode
    | none => [false]
    | some a => true :: C.encode a
  parse
    | [] => none
    | false :: rest => some (none, rest)
    | true :: rest => (C.parse rest).map fun (a, suffix) => (some a, suffix)
  roundtrip := by
    intro value suffix
    cases value with
    | none => rfl
    | some a => simp only [List.cons_append, C.roundtrip, Option.map_some]
  sound := by
    intro bits value suffix h
    cases bits with
    | nil => cases h
    | cons b rest =>
      cases b with
      | false => cases h; rfl
      | true =>
        cases hp : C.parse rest with
        | none => simp only [hp, Option.map_none] at h; cases h
        | some pair =>
          rcases pair with ⟨a, tail⟩
          have he : (some a, tail) = (value, suffix) := by
            simpa only [hp, Option.map_some, Option.some.injEq] using h
          cases he
          simpa only [List.cons_append] using congrArg (List.cons true) (C.sound rest a _ hp)

def solutionCodec (n : Nat) : Codec (Option (Space n)) := optionCodec (spaceCodec n)

theorem solution_roundtrip (n : Nat) (s : Option (Space n)) :
    (solutionCodec n).decode ((solutionCodec n).encode s) = some s :=
  PNP.Concrete.NativeNormalization.NativeBitCodec.decode_encode _ _

theorem solution_canonical (n : Nat) (bits : BitString) (s : Option (Space n)) :
    (solutionCodec n).decode bits = some s ↔ (solutionCodec n).encode s = bits :=
  PNP.Concrete.NativeNormalization.NativeBitCodec.decode_eq_some_iff _ _ _

theorem solve_solution_bound (n : Nat) (rows : System n) :
    ((solutionCodec n).encode (solve n rows)).length ≤ (n + 1) * (n + 1) + 1 := by
  cases h : solve n rows with
  | none => change 1 ≤ (n + 1) * (n + 1) + 1; omega
  | some s =>
    have bound := solve_space_bound rows s h
    change ((spaceCodec n).encode s).length + 1 ≤ (n + 1) * (n + 1) + 1
    omega

theorem affineWord_zero (k : Nat) :
    affineWord (aConst k false) = List.replicate (k + 1) false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change false :: affineWord (aConst k false) = List.replicate ((k + 1) + 1) false
    simp only [ih, List.replicate_succ]

theorem raised_cons {n k : Nat} (f : Affine k) (fs : AffineMap n k) :
    mapBits (raiseMap (n := n + 1) (f, fs)) =
      (false :: affineWord f) ++ mapBits (raiseMap fs) := rfl

theorem free_bits {n k : Nat} (m : AffineMap n k) :
    mapBits (freeMap m) = (true :: List.replicate (k + 1) false) ++ mapBits (raiseMap m) := by
  change (true :: affineWord (aConst k false)) ++ mapBits (raiseMap m) = _
  rw [affineWord_zero]

theorem pivot_bits {n k : Nat} (p : Affine n) (m : AffineMap n k) :
    mapBits (pivotMap p m) = affineWord (pullback p m) ++ mapBits m := rfl

theorem affineWord_nonempty {k : Nat} (f : Affine k) :
    ∃ b rest, affineWord f = b :: rest := by
  cases h : affineWord f with
  | nil =>
    exfalso
    have length := affineWord_length f
    rw [h] at length
    simp only [List.length_nil] at length
    omega
  | cons b rest => exact ⟨b, rest, rfl⟩

end PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
