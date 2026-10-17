import PNP.Concrete.ResidualReduction.SourceDirectionChart
import PNP.Concrete.ResidualReduction.MatrixRowInstructions

/-! Byte-level coordinates for the actual source-derived chart. A successful
first-one search identifies the exact pivot and the unchanged order of all
remaining coordinates; no pivot or reconstruction certificate is supplied. -/

namespace PNP.Concrete.ResidualReduction.SourceChartCoordinates
open PNP.Concrete PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.MatrixInstructions

theorem point_cons {n : Nat} (b : Bool) (x : Point n) :
    (SourceEncoding.pointCodec (n + 1)).encode (b,x) =
      b :: (SourceEncoding.pointCodec n).encode x := rfl

theorem firstOne_none_bytes {n : Nat} (v : Point n) (h : firstOne v = none) :
    (SourceEncoding.pointCodec n).encode v = List.replicate n false := by
  induction n with
  | zero => cases v; rfl
  | succ n ih =>
    rcases v with ⟨b,v⟩
    cases b with
    | true => simp only [firstOne, ↓reduceIte, reduceCtorEq] at h
    | false =>
      cases hv : firstOne v with
      | some j =>
        simp only [firstOne, Bool.false_eq_true, ↓reduceIte, hv,
          Option.map, reduceCtorEq] at h
      | none =>
        simpa only [point_cons,List.replicate_succ] using
          congrArg (List.cons false) (ih v hv)

theorem firstOne_split {n : Nat} (v : Point (n + 1)) (k : Fin (n + 1))
    (h : firstOne v = some k) :
    ∃ suffix : BitString,
      (SourceEncoding.pointCodec (n + 1)).encode v =
        List.replicate k.val false ++ true :: suffix ∧
      (SourceEncoding.pointCodec n).encode (cut n k v).2 =
        List.replicate k.val false ++ suffix := by
  induction n with
  | zero =>
    rcases v with ⟨b,v⟩
    cases v
    have hk : k = 0 := Fin.ext (by omega)
    subst k
    cases b with
    | false => simp only [firstOne, Bool.false_eq_true, ↓reduceIte,
        Option.map, reduceCtorEq] at h
    | true => exact ⟨[],rfl,rfl⟩
  | succ n ih =>
    rcases v with ⟨b,v⟩
    cases b with
    | true =>
      have hk : (0 : Fin (n + 2)) = k := by
        simpa only [firstOne, ↓reduceIte, Option.some.injEq] using h
      subst k
      refine ⟨(SourceEncoding.pointCodec (n + 1)).encode v,rfl,?_⟩
      rw [cut_zero]
      rfl
    | false =>
      cases hv : firstOne v with
      | none =>
        simp only [firstOne, Bool.false_eq_true, ↓reduceIte, hv,
          Option.map, reduceCtorEq] at h
      | some j =>
        have hk : j.succ = k := by
          simpa only [firstOne, Bool.false_eq_true, ↓reduceIte, hv,
            Option.map, Option.some.injEq] using h
        subst k
        obtain ⟨suffix,whole,tail⟩ := ih v j hv
        refine ⟨suffix,?_,?_⟩
        · simpa only [point_cons,Fin.val_succ,List.replicate_succ,
            List.cons_append] using congrArg (List.cons false) whole
        · simpa only [cut_succ,point_cons,Fin.val_succ,List.replicate_succ,
            List.cons_append] using congrArg (List.cons false) tail

theorem chosen_split {n : Nat} (v : Point (n + 1))
    (c : Fin (n + 1) × Point n) (h : chooseChart v = some c) :
    ∃ suffix : BitString,
      (SourceEncoding.pointCodec (n + 1)).encode v =
        List.replicate c.1.val false ++ true :: suffix ∧
      (SourceEncoding.pointCodec n).encode c.2 =
        List.replicate c.1.val false ++ suffix := by
  cases hv : firstOne v with
  | none => simp only [chooseChart,hv,Option.map,reduceCtorEq] at h
  | some k =>
    have hc : (k,(cut n k v).2) = c := by
      simpa only [chooseChart,hv,Option.map,Option.some.injEq] using h
    cases hc
    exact firstOne_split v k hv

theorem absent_bytes {n : Nat} (v : Point (n + 1)) (h : chooseChart v = none) :
    (SourceEncoding.pointCodec (n + 1)).encode v = List.replicate (n + 1) false := by
  cases hv : firstOne v with
  | none => exact firstOne_none_bytes v hv
  | some k => simp only [chooseChart,hv,Option.map,reduceCtorEq] at h

end PNP.Concrete.ResidualReduction.SourceChartCoordinates
