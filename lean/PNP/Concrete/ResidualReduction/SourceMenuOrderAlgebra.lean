import PNP.Concrete.ResidualReduction.SourceMenuFamily
import PNP.Concrete.ResidualReduction.SourceClassCompleteness

/-! The numeric ranks below are specifications only. Runtime comparison scans
encoded coefficient words directly; it never constructs unary normalCode. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuOrder
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.CoefficientComparison
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChain

def Homogeneous {n : Nat} (a : Affine n) : Prop := aConstant a = false

theorem binaryValue_append_false (word : BitString) :
    binaryValue (word ++ [false]) = binaryValue word := by
  induction word with
  | nil => rfl
  | cons b word ih =>
    change bitValue b + 2 * binaryValue (word ++ [false]) =
      bitValue b + 2 * binaryValue word
    rw [ih]

theorem homogeneous_value {n : Nat} (a : Affine n) (ha : Homogeneous a) :
    binaryValue (affineWord a) = normalCode a := by
  rw [SourceMenuRowInput.affine_payload, ha, binaryValue_append_false, binaryValue_normalBits]

def wordLower (xs ys : BitString) : Bool := decide (binaryValue xs ≤ binaryValue ys)
def lower {n : Nat} (a b : Affine n) : Bool := wordLower (affineWord a) (affineWord b)

theorem lower_exact {n : Nat} (a b : Affine n) (ha : Homogeneous a) (hb : Homogeneous b) :
    lower a b = decide (normalCode a ≤ normalCode b) := by
  unfold lower wordLower
  rw [homogeneous_value a ha, homogeneous_value b hb]

theorem equality_flags {n : Nat} (a b : Affine n) (ha : Homogeneous a) (hb : Homogeneous b) :
    aEq a b = (lower a b && lower b a) := by
  rw [lower_exact a b ha hb, lower_exact b a hb ha]
  apply Bool.eq_iff_iff.mpr
  simp only [aEq_true_iff, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h; subst b; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · rintro ⟨hab, hba⟩
    exact SourceClass.normalCode_injective_homogeneous a b ha hb (Nat.le_antisymm hab hba)

theorem insert_by_flags {n : Nat} (a b : Affine n) (us : List (Affine n))
    (ha : Homogeneous a) (hb : Homogeneous b) :
    insertNormal a (b :: us) =
      if lower a b then
        if lower b a then b :: us else a :: b :: us
      else b :: insertNormal a us := by
  rw [insertNormal, equality_flags a b ha hb]
  cases hab : lower a b with
  | false =>
    have hn : ¬normalCode a ≤ normalCode b :=
      of_decide_eq_false ((lower_exact a b ha hb).symm.trans hab)
    simp only [hn, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  | true =>
    have hl : normalCode a ≤ normalCode b :=
      of_decide_eq_true ((lower_exact a b ha hb).symm.trans hab)
    cases hba : lower b a <;>
      simp only [hl, Bool.true_and, Bool.false_eq_true, ↓reduceIte]

theorem row_homogeneous {n : Nat} (r : Row n) (a : Affine n) (h : a ∈ rowNormals r) :
    Homogeneous a := by
  dsimp only [rowNormals] at h
  split at h
  · exact False.elim (List.not_mem_nil h)
  · split at h
    · exact False.elim (List.not_mem_nil h)
    · split at h
      · exact False.elim (List.not_mem_nil h)
      · rcases List.mem_cons.mp h with he | h
        · subst a; exact ConstrainedBilinear.homogeneousRow_constant r.left
        · rcases List.mem_cons.mp h with he | h
          · subst a; exact ConstrainedBilinear.homogeneousRow_constant r.right
          · rcases List.mem_cons.mp h with he | h
            · subst a
              change aConstant (aAdd (homogeneousRow r.left) (homogeneousRow r.right)) = false
              rw [SourceMenuBytes.homogeneous_add]
              exact ConstrainedBilinear.homogeneousRow_constant (aAdd r.left r.right)
            · exact False.elim (List.not_mem_nil h)

theorem family_homogeneous {n : Nat} (F : Family n) (a : Affine n)
    (h : a ∈ F.flatMap rowNormals) : Homogeneous a := by
  obtain ⟨r, _, hr⟩ := List.mem_flatMap.mp h
  exact row_homogeneous r a hr

theorem insert_homogeneous {n : Nat} (a : Affine n) (us : List (Affine n))
    (ha : Homogeneous a) (hu : ∀ b ∈ us, Homogeneous b) :
    ∀ b ∈ insertNormal a us, Homogeneous b := by
  intro b hb
  rcases (mem_insertNormal a b us).mp hb with he | h
  · subst b; exact ha
  · exact hu b h

theorem source_menu_homogeneous {n : Nat} (F : Family n) :
    ∀ a ∈ sourceMenu F, Homogeneous a := by
  intro a ha
  exact family_homogeneous F a ((mem_sortedNormals a (F.flatMap rowNormals)).mp ha)

end PNP.Concrete.ResidualReduction.SourceMenuOrder
