import PNP.Concrete.NativeNormalization.MeasuredCutRecovery

namespace PNP.Concrete.NativeNormalization.MeasuredParity

open MeasuredReach NativeBasis NativeEquations NativeCoefficients MeasuredOperations

def eval (read : Row c → Measured Bool) : Coefficients c → Measured Bool
  | [] => ⟨false,1⟩
  | r::rs =>
      let head := read r
      let tail := eval read rs
      ⟨Bool.xor head.value tail.value,head.cost+tail.cost+2⟩

theorem eval_value (read : Row c → Measured Bool) (terms : Coefficients c) :
    (eval read terms).value = NativeCoefficients.eval (fun r => (read r).value) terms := by
  induction terms with
  | nil => rfl
  | cons r rs ih => simp only [eval,NativeCoefficients.eval,ih]

theorem eval_cost (read : Row c → Measured Bool) (terms : Coefficients c) (R : Nat)
    (bound : ∀ r, (read r).cost ≤ R) :
    (eval read terms).cost ≤ (R+2)*terms.length+1 := by
  induction terms with
  | nil => simp [eval]
  | cons r rs ih =>
      have hr := bound r
      simp only [eval,List.length_cons,Nat.mul_succ]
      omega

theorem eval_ell {S : Selection n c} (ops : Operations S) (failed : Fin c)
    (read : Row c → Measured Bool) (v : Fin n) :
    (eval read (MeasuredTerms.ellTerms ops failed v).value).value =
      ellFrom S (pick S failed (fun r => (read r).value)) v := by
  rw [eval_value,MeasuredTerms.ellTerms_value,NativeCoefficients.eval_ellTerms]

theorem eval_b {S : Selection n c} (ops : Operations S) (failed : Fin c)
    (read : Row c → Measured Bool) :
    (eval read (MeasuredTerms.bTerms ops failed).value).value =
      NativeEquations.bRow S failed (fun r => (read r).value) := by
  rw [eval_value,MeasuredTerms.bTerms_value,NativeCoefficients.eval_bTerms]


end PNP.Concrete.NativeNormalization.MeasuredParity
