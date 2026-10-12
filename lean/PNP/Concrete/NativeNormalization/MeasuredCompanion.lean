import PNP.Concrete.NativeNormalization.MeasuredTerms

namespace PNP.Concrete.NativeNormalization.MeasuredCompanion

open MeasuredReach MeasuredOperations NativeBasis NativeEquations NativeCoefficients MeasuredTerms

def companionTerms {S : Selection n c} (ops : Operations S) (failed : Fin c) (r : Row c) :
    Measured (Coefficients c) :=
  let mode := ops.mode r.1
  if r.2 then
    match mode.value with
    | some .last =>
        let terms := MeasuredTerms.auxiliaryTerms ops failed r.1
        ⟨terms.value,mode.cost+terms.cost+2⟩
    | _ =>
        let terms := MeasuredTerms.literalTerms ops failed r.1 .last
        ⟨terms.value,mode.cost+terms.cost+2⟩
  else
    match mode.value with
    | some .middle | some .last =>
        let terms := MeasuredTerms.literalTerms ops failed r.1 .first
        ⟨terms.value,mode.cost+terms.cost+2⟩
    | _ =>
        let literal := MeasuredTerms.literalTerms ops failed r.1 .middle
        let auxiliary := MeasuredTerms.auxiliaryTerms ops failed r.1
        let joined := MeasuredCollections.append literal.value auxiliary.value
        ⟨joined.value,mode.cost+literal.cost+auxiliary.cost+joined.cost+2⟩

theorem companionTerms_value {S : Selection n c} (ops : Operations S)
    (failed : Fin c) (r : Row c) :
    (companionTerms ops failed r).value = NativeCoefficients.companionTerms S failed r := by
  cases hb : r.2 <;> cases hm : S.mode r.1 with
  | none =>
      simp [companionTerms,ops.mode_eq,NativeCoefficients.companionTerms,hb,hm,
        MeasuredTerms.literalTerms_value,MeasuredTerms.auxiliaryTerms_value,
        MeasuredCollections.append_value]
  | some s =>
      cases s <;> simp [companionTerms,ops.mode_eq,NativeCoefficients.companionTerms,hb,hm,
        MeasuredTerms.literalTerms_value,MeasuredTerms.auxiliaryTerms_value,
        MeasuredCollections.append_value]

def companionBound (L O D M : Nat) : Nat :=
  M+literalBound L O D M+auxiliaryBound L O D M+8

theorem companionTerms_cost {S : Selection n c} (ops : Operations S) (L O D M : Nat)
    (bounds : Bounded ops L O D M) (failed : Fin c) (r : Row c) :
    (companionTerms ops failed r).cost ≤ companionBound L O D M := by
  have hmBound := bounds.2.2.2 r.1
  have h₁ := MeasuredTerms.literalTerms_cost ops L O D M bounds failed r.1 .first
  have h₂ := MeasuredTerms.literalTerms_cost ops L O D M bounds failed r.1 .middle
  have h₃ := MeasuredTerms.literalTerms_cost ops L O D M bounds failed r.1 .last
  have ha := MeasuredTerms.auxiliaryTerms_cost ops L O D M bounds failed r.1
  have hlen := MeasuredTerms.literalTerms_length ops failed r.1 .middle
  cases hb : r.2 <;> cases hm : (ops.mode r.1).value with
  | none =>
      simp only [companionTerms,hb,hm,Bool.false_eq_true,if_false,if_true,
        MeasuredCollections.append_cost,companionBound]
      omega
  | some s =>
      cases s <;> simp only [companionTerms,hb,hm,Bool.false_eq_true,if_false,if_true,
        MeasuredCollections.append_cost,companionBound] <;> omega

theorem companionTerms_length {S : Selection n c} (ops : Operations S)
    (failed : Fin c) (r : Row c) :
    (companionTerms ops failed r).value.length ≤ 6 := by
  rw [companionTerms_value]
  exact NativeCoefficients.companionTerms_length S failed r

def aTerms {S : Selection n c} (ops : Operations S) (failed : Fin c) (r : Row c) :
    Measured (Coefficients c) :=
  let terms := companionTerms ops failed r
  ⟨r::terms.value,terms.cost+1⟩

theorem aTerms_value {S : Selection n c} (ops : Operations S) (failed : Fin c) (r : Row c) :
    (aTerms ops failed r).value = NativeCoefficients.aTerms S failed r := by
  simp only [aTerms,companionTerms_value,NativeCoefficients.aTerms]

theorem aTerms_cost {S : Selection n c} (ops : Operations S) (L O D M : Nat)
    (bounds : Bounded ops L O D M) (failed : Fin c) (r : Row c) :
    (aTerms ops failed r).cost ≤ companionBound L O D M+1 := by
  have h := companionTerms_cost ops L O D M bounds failed r
  simp only [aTerms]
  omega

theorem aTerms_length {S : Selection n c} (ops : Operations S) (failed : Fin c) (r : Row c) :
    (aTerms ops failed r).value.length ≤ 7 := by
  rw [aTerms_value]
  exact NativeCoefficients.aTerms_length S failed r

def imageTerms {S : Selection n c} (ops : Operations S) (failed i : Fin c) :
    Measured (Coefficients c) :=
  let terms := MeasuredTerms.literalTerms ops failed i .first
  ⟨(i,false)::terms.value,terms.cost+2⟩

theorem imageTerms_value {S : Selection n c} (ops : Operations S) (failed i : Fin c) :
    (imageTerms ops failed i).value = NativeCoefficients.imageTerms S failed i := by
  simp only [imageTerms,MeasuredTerms.literalTerms_value,NativeCoefficients.imageTerms]

theorem imageTerms_cost {S : Selection n c} (ops : Operations S) (L O D M : Nat)
    (bounds : Bounded ops L O D M) (failed i : Fin c) :
    (imageTerms ops failed i).cost ≤ literalBound L O D M+2 := by
  have h := MeasuredTerms.literalTerms_cost ops L O D M bounds failed i .first
  simp only [imageTerms]
  omega

theorem imageTerms_length {S : Selection n c} (ops : Operations S) (failed i : Fin c) :
    (imageTerms ops failed i).value.length ≤ 6 := by
  rw [imageTerms_value]
  exact NativeCoefficients.imageTerms_length S failed i


end PNP.Concrete.NativeNormalization.MeasuredCompanion
