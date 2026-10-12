import PNP.Concrete.NativeNormalization.MeasuredRecoveryPolynomial

namespace PNP.Concrete.NativeNormalization.MeasuredRowEncoding

open PNP.Concrete NativeEquations NativeSparseSystem

def indexRow (j : Fin (2*c)) : Row c :=
  (⟨j.val/2,by have h := j.isLt; omega⟩,decide (j.val%2 = 1))

theorem index_even (i : Fin c) (h : 2*i.val < 2*c) :
    indexRow ⟨2*i.val,h⟩ = (i,false) := by
  apply Prod.ext
  · apply Fin.ext
    simp only [indexRow]
    omega
  · have hm : (2*i.val)%2 = 0 := by omega
    simp [indexRow,hm]

theorem index_odd (i : Fin c) (h : 2*i.val+1 < 2*c) :
    indexRow ⟨2*i.val+1,h⟩ = (i,true) := by
  apply Prod.ext
  · apply Fin.ext
    simp only [indexRow]
    omega
  · have hm : (2*i.val+1)%2 = 1 := by omega
    simp [indexRow,hm]

/-- Proof-facing finite representation of every row assignment, not a witness search. -/
def encode (u : RowValues c) : BitString := List.ofFn (fun j : Fin (2*c) => u (indexRow j))

theorem encode_length (u : RowValues c) : (encode u).length = 2*c := by
  simp only [encode,List.length_ofFn]

theorem rowValues_encode (u : RowValues c) : MeasuredBits.rowValues c (encode u) = u := by
  funext r
  rcases r with ⟨i,b⟩
  cases b with
  | false =>
      have hi := i.isLt
      have h : 2*i.val < (encode u).length := by rw [encode_length]; omega
      simp only [MeasuredBits.rowValues,Bool.false_eq_true,if_false,Nat.add_zero]
      rw [List.getElem?_eq_getElem h]
      simp only [encode,List.getElem_ofFn,Option.getD_some]
      rw [index_even]
  | true =>
      have hi := i.isLt
      have h : 2*i.val+1 < (encode u).length := by rw [encode_length]; omega
      simp only [MeasuredBits.rowValues,if_true]
      rw [List.getElem?_eq_getElem h]
      simp only [encode,List.getElem_ofFn,Option.getD_some]
      rw [index_odd]

theorem representable (u : RowValues c) :
    ∃ a : BitString, a.length = 2*c ∧ MeasuredBits.rowValues c a = u :=
  ⟨encode u,encode_length u,rowValues_encode u⟩

theorem system_iff (D : System c) :
    (∃ u : RowValues c, D.Satisfied u) ↔
      ∃ a : BitString, a.length = 2*c ∧ D.Satisfied (MeasuredBits.rowValues c a) := by
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨encode u,encode_length u,?_⟩
    rw [rowValues_encode]
    exact hu
  · rintro ⟨a,_,ha⟩
    exact ⟨MeasuredBits.rowValues c a,ha⟩


end PNP.Concrete.NativeNormalization.MeasuredRowEncoding
