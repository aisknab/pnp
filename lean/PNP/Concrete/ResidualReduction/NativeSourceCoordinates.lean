import PNP.Concrete.ResidualReduction.FactoredContraction
import PNP.Concrete.NativeNormalization.MeasuredBits

namespace PNP.Concrete.ResidualReduction.NativeSource
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete PNP.Concrete.NativeNormalization

def pointValue : {n : Nat} → Point n → Fin n → Bool
  | 0, _, i => Fin.elim0 i
  | _+1, (b,_), ⟨0,_⟩ => b
  | _+1, (_,x), ⟨i+1,h⟩ => pointValue x ⟨i,Nat.lt_of_succ_lt_succ h⟩

def pointFromFn : (n : Nat) → (Fin n → Bool) → Point n
  | 0, _ => ()
  | n+1, f => (f 0,pointFromFn n (fun i => f i.succ))

theorem pointValue_fromFn (n : Nat) (f : Fin n → Bool) (i : Fin n) :
    pointValue (pointFromFn n f) i = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact ih (fun k => f k.succ) j

theorem pointFromFn_value (n : Nat) (x : Point n) :
    pointFromFn n (pointValue x) = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
      rcases x with ⟨b,x⟩
      change (b,pointFromFn n (pointValue x)) = (b,x)
      rw [ih]

/-- Exactly the false-labelled then true-labelled coordinate order used by the packet. -/
def rowIndex {c : Nat} (r : NativeEquations.Row c) : Fin (2*c) :=
  ⟨2*r.1.val+(if r.2 then 1 else 0),by
    have h := r.1.isLt
    cases r.2 <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega⟩

def indexRow {c : Nat} (i : Fin (2*c)) : NativeEquations.Row c :=
  (⟨i.val/2,by have h := i.isLt; omega⟩,decide (i.val%2=1))

theorem indexRow_rowIndex {c : Nat} (r : NativeEquations.Row c) :
    indexRow (rowIndex r) = r := by
  rcases r with ⟨i,b⟩
  cases b <;> apply Prod.ext
  · apply Fin.ext
    simp only [indexRow,rowIndex,Bool.false_eq_true,if_false]
    omega
  · simp [indexRow,rowIndex]
  · apply Fin.ext
    simp only [indexRow,rowIndex,if_true]
    omega
  · simp [indexRow,rowIndex]

theorem rowIndex_indexRow {c : Nat} (i : Fin (2*c)) :
    rowIndex (indexRow i) = i := by
  apply Fin.ext
  change 2*(i.val/2)+(if decide (i.val%2=1) then 1 else 0) = i.val
  by_cases h : i.val%2=1
  · simp only [h,decide_true,if_true]
    omega
  · simp only [h,decide_false,Bool.false_eq_true,if_false]
    omega

def sourcePoint {c : Nat} (u : NativeEquations.RowValues c) : Point (2*c) :=
  pointFromFn (2*c) (fun i => u (indexRow i))

def pointRows {c : Nat} (x : Point (2*c)) : NativeEquations.RowValues c :=
  fun r => pointValue x (rowIndex r)

theorem pointRows_sourcePoint {c : Nat} (u : NativeEquations.RowValues c) :
    pointRows (sourcePoint u) = u := by
  funext r
  simp only [pointRows,sourcePoint,pointValue_fromFn,indexRow_rowIndex]

theorem sourcePoint_pointRows {c : Nat} (x : Point (2*c)) :
    sourcePoint (pointRows x) = x := by
  unfold sourcePoint pointRows
  simp only [rowIndex_indexRow,pointFromFn_value]

def pointBytes : {n : Nat} → Point n → BitString
  | 0, _ => []
  | _+1, (b,x) => b::pointBytes x

theorem pointBytes_length {n : Nat} (x : Point n) :
    (pointBytes x).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rcases x with ⟨b,x⟩
      simp only [pointBytes,List.length_cons,ih]

theorem pointBytes_get {n : Nat} (x : Point n) (i : Fin n) :
    ((pointBytes x)[i.val]?).getD false = pointValue x i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rcases x with ⟨b,x⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · change ((b::pointBytes x)[j.val+1]?).getD false = pointValue x j
        simpa only [List.getElem?_cons_succ] using ih x j

theorem rowValues_pointBytes {c : Nat} (x : Point (2*c)) :
    MeasuredBits.rowValues c (pointBytes x) = pointRows x := by
  funext r
  exact pointBytes_get x (rowIndex r)

theorem rowValues_sourcePoint {c : Nat} (u : NativeEquations.RowValues c) :
    MeasuredBits.rowValues c (pointBytes (sourcePoint u)) = u := by
  rw [rowValues_pointBytes,pointRows_sourcePoint]

/-- A coefficient constructor, not a supplied evaluation function. -/
def coordinateForm : (n : Nat) → Fin n → Affine n
  | 0, i => Fin.elim0 i
  | n+1, ⟨0,_⟩ => (true,aConst n false)
  | n+1, ⟨i+1,h⟩ => (false,coordinateForm n ⟨i,Nat.lt_of_succ_lt_succ h⟩)

theorem coordinateForm_eval (n : Nat) (i : Fin n) (x : Point n) :
    aEval (coordinateForm n i) x = pointValue x i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rcases x with ⟨b,x⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · change Bool.xor (true && b) (aEval (aConst n false) x) = b
        simp only [aConst_eval,Bool.true_and,Bool.xor_false]
      · change Bool.xor (false && b) (aEval (coordinateForm n j) x) = pointValue x j
        simpa only [Bool.false_and,Bool.false_xor] using ih j x

end PNP.Concrete.ResidualReduction.NativeSource
