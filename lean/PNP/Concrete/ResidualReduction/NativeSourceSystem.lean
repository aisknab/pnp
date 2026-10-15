import PNP.Concrete.ResidualReduction.NativeSourceCoordinates
import PNP.Concrete.NativeNormalization.NativeSparseSystem

namespace PNP.Concrete.ResidualReduction.NativeSource
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete PNP.Concrete.NativeNormalization

/-- Preserve the stored XOR list, including repeated labels and the empty list. -/
def sparseForm {c : Nat} : NativeCoefficients.Coefficients c → Affine (2*c)
  | [] => aConst (2*c) false
  | r::rs => aAdd (coordinateForm (2*c) (rowIndex r)) (sparseForm rs)

theorem sparseForm_eval {c : Nat} (terms : NativeCoefficients.Coefficients c)
    (x : Point (2*c)) :
    aEval (sparseForm terms) x = NativeCoefficients.eval (pointRows x) terms := by
  induction terms with
  | nil => exact aConst_eval _ _ _
  | cons r rs ih =>
      simp only [sparseForm,aAdd_eval,coordinateForm_eval,ih,NativeCoefficients.eval,pointRows]

def requireZero {n : Nat} (f : Affine n) : FactoredContraction.Row n :=
  ⟨false,f,aConst n true⟩

def requireOne {n : Nat} (f : Affine n) : FactoredContraction.Row n :=
  requireZero (aAdd f (aConst n true))

theorem requireZero_eval {n : Nat} (f : Affine n) (x : Point n) :
    (requireZero f).eval x = aEval f x := by
  simp only [requireZero,FactoredContraction.Row.eval,aConst_eval,Bool.and_true]

theorem requireOne_eval {n : Nat} (f : Affine n) (x : Point n) :
    (requireOne f).eval x = !(aEval f x) := by
  simp only [requireOne,requireZero_eval,aAdd_eval,aConst_eval,Bool.xor_true]

theorem requireOne_zero_iff {n : Nat} (f : Affine n) (x : Point n) :
    (requireOne f).eval x = false ↔ aEval f x = true := by
  rw [requireOne_eval]
  cases aEval f x <;> decide

def productRow {c : Nat}
    (entry : NativeEquations.Row c × NativeCoefficients.Coefficients c) :
    FactoredContraction.Row (2*c) :=
  ⟨false,coordinateForm (2*c) (rowIndex entry.1),
    aAdd (sparseForm entry.2) (aConst (2*c) true)⟩

theorem productRow_eval {c : Nat}
    (entry : NativeEquations.Row c × NativeCoefficients.Coefficients c)
    (x : Point (2*c)) :
    (productRow entry).eval x =
      (pointRows x entry.1 && !(NativeCoefficients.eval (pointRows x) entry.2)) := by
  simp only [productRow,FactoredContraction.Row.eval,coordinateForm_eval,
    aAdd_eval,sparseForm_eval,aConst_eval,Bool.xor_true,pointRows]

/-- All three source components are retained: b=true, every e=0 and every product. -/
def family {c : Nat} (D : NativeSparseSystem.System c) : Family (2*c) :=
  requireOne (sparseForm D.b) ::
    ((D.e.map (fun terms => requireZero (sparseForm terms))) ++ D.a.map productRow)

theorem family_row_count {c : Nat} (D : NativeSparseSystem.System c) :
    (family D).length = 1+D.e.length+D.a.length := by
  simp only [family,List.length_cons,List.length_append,List.length_map]
  omega

theorem models_iff_all {n : Nat} (F : Family n) (x : Point n) :
    models F x = true ↔ ∀ r ∈ F, r.eval x = false := by
  induction F with
  | nil => simp [models]
  | cons r rs ih => simp [models,ih]

theorem family_satisfied {c : Nat} (D : NativeSparseSystem.System c)
    (x : Point (2*c)) :
    models (family D) x = true ↔ D.Satisfied (pointRows x) := by
  rw [models_iff_all]
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · have hb := h (requireOne (sparseForm D.b)) (List.mem_cons_self)
      rw [requireOne_zero_iff,sparseForm_eval] at hb
      exact hb
    · intro terms ht
      have he := h (requireZero (sparseForm terms))
        (List.mem_cons_of_mem _ (List.mem_append.mpr
          (Or.inl (List.mem_map.mpr ⟨terms,ht,rfl⟩))))
      simpa only [requireZero_eval,sparseForm_eval] using he
    · intro entry ht
      have ha := h (productRow entry)
        (List.mem_cons_of_mem _ (List.mem_append.mpr
          (Or.inr (List.mem_map.mpr ⟨entry,ht,rfl⟩))))
      simpa only [productRow_eval] using ha
  · rintro ⟨hb,he,ha⟩ r hr
    rcases List.mem_cons.mp hr with hfirst | hrest
    · subst r
      rw [requireOne_zero_iff,sparseForm_eval]
      exact hb
    · rcases List.mem_append.mp hrest with hz | hp
      · obtain ⟨terms,ht,rfl⟩ := List.mem_map.mp hz
        simpa only [requireZero_eval,sparseForm_eval] using he terms ht
      · obtain ⟨entry,ht,rfl⟩ := List.mem_map.mp hp
        simpa only [productRow_eval] using ha entry ht

theorem family_sourcePoint {c : Nat} (D : NativeSparseSystem.System c)
    (u : NativeEquations.RowValues c) :
    models (family D) (sourcePoint u) = true ↔ D.Satisfied u := by
  rw [family_satisfied,pointRows_sourcePoint]

theorem family_satisfiable_iff {c : Nat} (D : NativeSparseSystem.System c) :
    (∃ x, models (family D) x = true) ↔ ∃ u, D.Satisfied u := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨pointRows x,(family_satisfied D x).mp hx⟩
  · rintro ⟨u,hu⟩
    exact ⟨sourcePoint u,(family_sourcePoint D u).mpr hu⟩

/-- The certificate width and the actual public bit-order are both checked. -/
theorem family_certificate_iff {c : Nat} (D : NativeSparseSystem.System c) :
    (∃ x, models (family D) x = true) ↔
      ∃ bytes : BitString, bytes.length = 2*c ∧
        D.Satisfied (MeasuredBits.rowValues c bytes) := by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨pointBytes x,pointBytes_length x,?_⟩
    rw [rowValues_pointBytes]
    exact (family_satisfied D x).mp hx
  · rintro ⟨bytes,_,h⟩
    exact ⟨sourcePoint (MeasuredBits.rowValues c bytes),
      (family_sourcePoint D _).mpr h⟩

end PNP.Concrete.ResidualReduction.NativeSource
