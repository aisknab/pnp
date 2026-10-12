import PNP.Concrete.NativeNormalization.NativeBitCodec

namespace PNP.Concrete.NativeNormalization.NativeSystemCodec

open PNP.Concrete NativeBitCodec NativeEquations NativeCoefficients NativeSparseSystem

def rowCodec (c : Nat) : Codec (Row c) := pairCodec (finCodec c) bitCodec
def coefficientsCodec (c : Nat) : Codec (Coefficients c) := listCodec (rowCodec c)
def entryCodec (c : Nat) : Codec (Row c × Coefficients c) :=
  pairCodec (rowCodec c) (coefficientsCodec c)

def systemCodec (c : Nat) : Codec (System c) :=
  mappedCodec
    (pairCodec (coefficientsCodec c)
      (pairCodec (listCodec (entryCodec c)) (listCodec (coefficientsCodec c))))
    (fun value => ⟨value.1,value.2.1,value.2.2⟩)
    (fun D => (D.b,D.a,D.e))
    (by intro D; cases D; rfl)
    (by rintro ⟨b,a,e⟩; rfl)

theorem system_roundtrip (D : System c) :
    (systemCodec c).decode ((systemCodec c).encode D) = some D :=
  decode_encode _ _

theorem system_canonical (bits : BitString) (D : System c) :
    (systemCodec c).decode bits = some D ↔ (systemCodec c).encode D = bits :=
  decode_eq_some_iff _ _ _

theorem system_injective :
    Function.Injective (systemCodec c).encode := encode_injective _

theorem row_length (r : Row c) : ((rowCodec c).encode r).length ≤ c+1 := by
  have h := r.1.isLt
  simp only [rowCodec,pairCodec,finCodec,bitCodec,List.length_append,natural_length,
    List.length_cons,List.length_nil]
  omega

theorem coefficients_length (xs : Coefficients c) :
    ((coefficientsCodec c).encode xs).length ≤ (c+2)*xs.length+1 :=
  list_length_bound (rowCodec c) xs (c+1) (fun x _ => row_length x)

theorem entry_length (entry : Row c × Coefficients c) :
    ((entryCodec c).encode entry).length ≤ (c+2)*(entry.2.length+1) := by
  have hr := row_length entry.1
  have hc := coefficients_length entry.2
  simp only [entryCodec,pairCodec,List.length_append,Nat.mul_succ]
  omega

theorem system_length (D : System c) :
    ((systemCodec c).encode D).length =
      ((coefficientsCodec c).encode D.b).length+
      (((listCodec (entryCodec c)).encode D.a).length+
       ((listCodec (coefficientsCodec c)).encode D.e).length) := by
  simp only [systemCodec,mappedCodec,pairCodec,List.length_append]

/-- A factored natural polynomial, so no encoding coordinate is treated as free. -/
def systemBound (c : Nat) : Nat :=
  ((c+2)*3+1)+(((c+2)*8+1)*(2*c)+1)+(((c+2)*6+2)*c+1)

theorem system_length_bound (D : System c) (bounds : NativeFrontend.SparseBounds D) :
    ((systemCodec c).encode D).length ≤ systemBound c := by
  obtain ⟨hb,ha,he,na,ne,_⟩ := bounds
  have cb := coefficients_length D.b
  have cb' := Nat.mul_le_mul_left (c+2) hb
  have ca := list_length_bound (entryCodec c) D.a ((c+2)*8) (by
    intro entry member
    have size := ha entry member
    exact Nat.le_trans (entry_length entry)
      (Nat.mul_le_mul_left (c+2) (by omega)))
  have ce := list_length_bound (coefficientsCodec c) D.e ((c+2)*6+1) (by
    intro terms member
    have size := he terms member
    exact Nat.le_trans (coefficients_length terms)
      (Nat.add_le_add_right (Nat.mul_le_mul_left (c+2) size) 1))
  change ((listCodec (coefficientsCodec c)).encode D.e).length ≤
    ((c+2)*6+2)*D.e.length+1 at ce
  have ce' := Nat.mul_le_mul_left ((c+2)*6+2) ne
  rw [na] at ca
  rw [system_length]
  unfold systemBound
  omega

theorem systemBound_mono (a b : Nat) (h : a ≤ b) : systemBound a ≤ systemBound b := by
  have h2 : a+2 ≤ b+2 := by omega
  have h3 := Nat.mul_le_mul_right 3 h2
  have h8 := Nat.mul_le_mul_right 8 h2
  have h6 := Nat.mul_le_mul_right 6 h2
  have ha := Nat.mul_le_mul (Nat.add_le_add_right h8 1) (Nat.mul_le_mul_left 2 h)
  have he := Nat.mul_le_mul (Nat.add_le_add_right h6 2) h
  unfold systemBound
  omega

theorem system_check_roundtrip (D : System c) (u : RowValues c) :
    ((systemCodec c).decode ((systemCodec c).encode D)).map (fun E => E.check u) =
      some (D.check u) := by
  rw [system_roundtrip]
  rfl


end PNP.Concrete.NativeNormalization.NativeSystemCodec
