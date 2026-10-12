import PNP.Concrete.NativeNormalization.MeasuredRows

namespace PNP.Concrete.NativeNormalization.MeasuredTerms

open MeasuredReach MeasuredOperations NativeBasis NativeEquations NativeCoefficients

def ellTerms {S : Selection n c} (ops : Operations S) (_failed : Fin c) (v : Fin n) :
    Measured (Coefficients c) :=
  let slot := ops.slot v
  let row := MeasuredRows.variableRow ops v
  if slot.value = .middle then
    let owner := ops.owner v
    let aux := MeasuredRows.auxiliaryRow ops owner.value
    ⟨[row.value,aux.value],slot.cost+row.cost+owner.cost+aux.cost+3⟩
  else ⟨[row.value],slot.cost+row.cost+2⟩

theorem ellTerms_value {S : Selection n c} (ops : Operations S) (failed : Fin c) (v : Fin n) :
    (ellTerms ops failed v).value = NativeCoefficients.ellTerms S failed v := by
  by_cases h : S.slot v = .middle <;>
    simp [ellTerms,ops.slot_eq,ops.owner_eq,MeasuredRows.variableRow_value ops failed,
      MeasuredRows.auxiliaryRow_value ops failed,NativeCoefficients.ellTerms,h]

def ellBound (O D M : Nat) : Nat := D+(O+D+2)+O+(M+2)+3

theorem ellTerms_cost {S : Selection n c} (ops : Operations S) (L O D M : Nat)
    (bounds : Bounded ops L O D M) (failed : Fin c) (v : Fin n) :
    (ellTerms ops failed v).cost ≤ ellBound O D M := by
  have hs := bounds.2.2.1 v
  have hr := MeasuredRows.variableRow_cost ops L O D M bounds v
  have ho := bounds.2.1 v
  have ha := MeasuredRows.auxiliaryRow_cost ops L O D M bounds (ops.owner v).value
  unfold ellTerms
  dsimp only
  split <;> dsimp only <;> unfold ellBound <;> omega

theorem ellTerms_length {S : Selection n c} (ops : Operations S) (failed : Fin c) (v : Fin n) :
    (ellTerms ops failed v).value.length ≤ 2 := by
  rw [ellTerms_value]
  exact NativeCoefficients.ellTerms_length S failed v

def bTerms {S : Selection n c} (ops : Operations S) (failed : Fin c) :
    Measured (Coefficients c) :=
  let extra := MeasuredRows.extraRow failed
  let anchor := ops.literal failed .first
  let terms := ellTerms ops failed anchor.value.index
  ⟨extra.value::terms.value,extra.cost+anchor.cost+terms.cost+2⟩

theorem bTerms_value {S : Selection n c} (ops : Operations S) (failed : Fin c) :
    (bTerms ops failed).value = NativeCoefficients.bTerms S failed := by
  simp only [bTerms,MeasuredRows.extraRow_value S,ellTerms_value,ops.literal_eq,
    NativeCoefficients.bTerms,NativeBasis.anchor]

def bBound (L O D M : Nat) : Nat := L+ellBound O D M+3

theorem bTerms_cost {S : Selection n c} (ops : Operations S) (L O D M : Nat)
    (bounds : Bounded ops L O D M) (failed : Fin c) :
    (bTerms ops failed).cost ≤ bBound L O D M := by
  have hl := bounds.1 failed .first
  have he := ellTerms_cost ops L O D M bounds failed (ops.literal failed .first).value.index
  simp only [bTerms,MeasuredRows.extraRow_cost,bBound]
  omega

theorem bTerms_length {S : Selection n c} (ops : Operations S) (failed : Fin c) :
    (bTerms ops failed).value.length ≤ 3 := by
  rw [bTerms_value]
  exact NativeCoefficients.bTerms_length S failed

/-- Reuse one fetched literal and charge concatenation explicitly on the active branch. -/
def literalTerms {S : Selection n c} (ops : Operations S) (failed i : Fin c) (s : Slot) :
    Measured (Coefficients c) :=
  let literal := ops.literal i s
  let ell := ellTerms ops failed literal.value.index
  let sign := MeasuredCandidate.sigma ops literal.value.index
  if Bool.xor sign.value literal.value.positive then
    let b := bTerms ops failed
    let joined := MeasuredCollections.append ell.value b.value
    ⟨joined.value,literal.cost+ell.cost+sign.cost+b.cost+joined.cost+2⟩
  else ⟨ell.value,literal.cost+ell.cost+sign.cost+2⟩

theorem literalTerms_value {S : Selection n c} (ops : Operations S)
    (failed i : Fin c) (s : Slot) :
    (literalTerms ops failed i s).value = NativeCoefficients.literalTerms S failed i s := by
  cases h : Bool.xor (NativeBasis.sigma S (S.literal i s).index) (S.literal i s).positive <;>
    simp [literalTerms,ops.literal_eq,ellTerms_value,MeasuredCandidate.sigma_value,bTerms_value,
      MeasuredCollections.append_value,NativeCoefficients.literalTerms,NativeCoefficients.masked,h]

def literalBound (L O D M : Nat) : Nat :=
  L+ellBound O D M+(O+D+L+1)+bBound L O D M+5

theorem literalTerms_cost {S : Selection n c} (ops : Operations S) (L O D M : Nat)
    (bounds : Bounded ops L O D M) (failed i : Fin c) (s : Slot) :
    (literalTerms ops failed i s).cost ≤ literalBound L O D M := by
  have hl := bounds.1 i s
  have he := ellTerms_cost ops L O D M bounds failed (ops.literal i s).value.index
  have hs := MeasuredCandidate.sigma_cost ops L O D M bounds (ops.literal i s).value.index
  have hb := bTerms_cost ops L O D M bounds failed
  have hlen := ellTerms_length ops failed (ops.literal i s).value.index
  unfold literalTerms
  dsimp only
  split <;> dsimp only <;> simp only [MeasuredCollections.append_cost,literalBound] <;> omega

theorem literalTerms_length {S : Selection n c} (ops : Operations S)
    (failed i : Fin c) (s : Slot) :
    (literalTerms ops failed i s).value.length ≤ 5 := by
  rw [literalTerms_value]
  exact NativeCoefficients.literalTerms_length S failed i s

def auxiliaryTerms {S : Selection n c} (ops : Operations S) (failed i : Fin c) :
    Measured (Coefficients c) :=
  let mode := ops.mode i
  let row := MeasuredRows.auxiliaryRow ops i
  if mode.value = some .last then
    let terms := literalTerms ops failed i .middle
    ⟨row.value::terms.value,mode.cost+row.cost+terms.cost+2⟩
  else ⟨[row.value],mode.cost+row.cost+2⟩

theorem auxiliaryTerms_value {S : Selection n c} (ops : Operations S) (failed i : Fin c) :
    (auxiliaryTerms ops failed i).value = NativeCoefficients.auxiliaryTerms S failed i := by
  by_cases h : S.mode i = some .last <;>
    simp [auxiliaryTerms,ops.mode_eq,MeasuredRows.auxiliaryRow_value ops failed,
      literalTerms_value,NativeCoefficients.auxiliaryTerms,h]

def auxiliaryBound (L O D M : Nat) : Nat := M+(M+2)+literalBound L O D M+2

theorem auxiliaryTerms_cost {S : Selection n c} (ops : Operations S) (L O D M : Nat)
    (bounds : Bounded ops L O D M) (failed i : Fin c) :
    (auxiliaryTerms ops failed i).cost ≤ auxiliaryBound L O D M := by
  have hm := bounds.2.2.2 i
  have hr := MeasuredRows.auxiliaryRow_cost ops L O D M bounds i
  have ht := literalTerms_cost ops L O D M bounds failed i .middle
  unfold auxiliaryTerms
  dsimp only
  split <;> dsimp only <;> unfold auxiliaryBound <;> omega

theorem auxiliaryTerms_length {S : Selection n c} (ops : Operations S) (failed i : Fin c) :
    (auxiliaryTerms ops failed i).value.length ≤ 6 := by
  rw [auxiliaryTerms_value]
  exact NativeCoefficients.auxiliaryTerms_length S failed i


end PNP.Concrete.NativeNormalization.MeasuredTerms
