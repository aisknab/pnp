import PNP.Concrete.NativeNormalization.MeasuredSourceCachePolynomial

namespace PNP.Concrete.NativeNormalization.MeasuredCandidate

open MeasuredReach MeasuredOperations NativeBasis

def sigma {S : Selection n c} (ops : Operations S) (v : Fin n) : Measured Bool :=
  let owner := ops.owner v
  let slot := ops.slot v
  let literal := ops.literal owner.value slot.value
  ⟨literal.value.positive,owner.cost+slot.cost+literal.cost+1⟩

theorem sigma_value {S : Selection n c} (ops : Operations S) (v : Fin n) :
    (sigma ops v).value = NativeBasis.sigma S v := by
  simp only [sigma,ops.literal_eq,ops.owner_eq,ops.slot_eq,NativeBasis.sigma]

theorem sigma_cost {S : Selection n c} (ops : Operations S) (L O D M : Nat)
    (bounds : Bounded ops L O D M) (v : Fin n) :
    (sigma ops v).cost ≤ O+D+L+1 := by
  have ho := bounds.2.1 v
  have hs := bounds.2.2.1 v
  have hl := bounds.1 (ops.owner v).value (ops.slot v).value
  simp only [sigma]
  omega

def literalTrue {S : Selection n c} (ops : Operations S)
    (x : Fin n → Measured Bool) (i : Fin c) (s : Slot) : Measured Bool :=
  let literal := ops.literal i s
  let bit := x literal.value.index
  ⟨decide (bit.value = literal.value.positive),literal.cost+bit.cost+1⟩

theorem literalTrue_value {S : Selection n c} (ops : Operations S)
    (x : Fin n → Measured Bool) (i : Fin c) (s : Slot) :
    (literalTrue ops x i s).value =
      decide ((x (S.literal i s).index).value = (S.literal i s).positive) := by
  simp only [literalTrue,ops.literal_eq]

theorem literalTrue_cost {S : Selection n c} (ops : Operations S)
    (x : Fin n → Measured Bool) (L X : Nat)
    (hl : ∀ i s, (ops.literal i s).cost ≤ L)
    (hx : ∀ v, (x v).cost ≤ X) (i : Fin c) (s : Slot) :
    (literalTrue ops x i s).cost ≤ L+X+1 := by
  have a := hl i s
  have b := hx (ops.literal i s).value.index
  simp only [literalTrue]
  omega

/-- A thunk preserves short-circuit execution; the skipped branch is not charged. -/
def orElse (a : Measured Bool) (b : Unit → Measured Bool) : Measured Bool :=
  if a.value then ⟨true,a.cost+1⟩
  else
    let next := b ()
    ⟨next.value,a.cost+next.cost+1⟩

theorem orElse_value (a : Measured Bool) (b : Unit → Measured Bool) :
    (orElse a b).value = (a.value || (b ()).value) := by
  cases h : a.value <;> simp [orElse,h]

theorem orElse_cost (a : Measured Bool) (b : Unit → Measured Bool)
    (A B : Nat) (ha : a.cost ≤ A) (hb : (b ()).cost ≤ B) :
    (orElse a b).cost ≤ A+B+1 := by
  cases h : a.value <;>
    simp only [orElse,h,Bool.false_eq_true,if_false,if_true] <;> omega

def clauseTrue {S : Selection n c} (ops : Operations S)
    (x : Fin n → Measured Bool) (i : Fin c) : Measured Bool :=
  orElse (literalTrue ops x i .first) (fun _ =>
    orElse (literalTrue ops x i .middle) (fun _ => literalTrue ops x i .last))

theorem clauseTrue_value {S : Selection n c} (ops : Operations S)
    (x : Fin n → Measured Bool) (i : Fin c) :
    (clauseTrue ops x i).value =
      NativeSource.clauseTrue S (fun v => (x v).value) i := by
  simp only [clauseTrue,orElse_value,literalTrue_value,NativeSource.clauseTrue]

theorem clauseTrue_cost {S : Selection n c} (ops : Operations S)
    (x : Fin n → Measured Bool) (L X : Nat)
    (hl : ∀ i s, (ops.literal i s).cost ≤ L)
    (hx : ∀ v, (x v).cost ≤ X) (i : Fin c) :
    (clauseTrue ops x i).cost ≤ 3*(L+X+1)+2 := by
  have h₁ := literalTrue_cost ops x L X hl hx i .first
  have h₂ := literalTrue_cost ops x L X hl hx i .middle
  have h₃ := literalTrue_cost ops x L X hl hx i .last
  have hm := orElse_cost (literalTrue ops x i .middle)
    (fun _ => literalTrue ops x i .last) (L+X+1) (L+X+1) h₂ h₃
  have ht := orElse_cost (literalTrue ops x i .first)
    (fun _ => orElse (literalTrue ops x i .middle) (fun _ => literalTrue ops x i .last))
    (L+X+1) ((L+X+1)+(L+X+1)+1) h₁ hm
  change _ ≤ _ at ht
  unfold clauseTrue
  omega

def failed {S : Selection n c} (ops : Operations S) (i : Fin c) : Measured Bool :=
  let truth := clauseTrue ops (sigma ops) i
  ⟨!truth.value,truth.cost+1⟩

theorem failed_value {S : Selection n c} (ops : Operations S) (i : Fin c) :
    (failed ops i).value = !NativeSource.clauseTrue S (NativeBasis.sigma S) i := by
  simp only [failed,clauseTrue_value,sigma_value]

def truthBound (L O D : Nat) : Nat := 3*(L+(O+D+L+1)+1)+2

theorem failed_cost {S : Selection n c} (ops : Operations S) (L O D M : Nat)
    (bounds : Bounded ops L O D M) (i : Fin c) :
    (failed ops i).cost ≤ truthBound L O D+1 := by
  have h := clauseTrue_cost ops (sigma ops) L (O+D+L+1)
    bounds.1 (sigma_cost ops L O D M bounds) i
  simp only [failed,truthBound]
  omega

def firstFailed {S : Selection n c} (ops : Operations S) : Measured (Option (Fin c)) :=
  let indices := MeasuredCollections.range c
  let found := MeasuredReach.find (failed ops) indices.value
  ⟨found.value,indices.cost+found.cost+1⟩

theorem firstFailed_value {S : Selection n c} (ops : Operations S) :
    (firstFailed ops).value =
      (List.finRange c).find? (fun i => !NativeSource.clauseTrue S (NativeBasis.sigma S) i) := by
  simp only [firstFailed,MeasuredReach.find_value,MeasuredCollections.range_value,failed_value]

def searchBound (B L O D : Nat) : Nat := 3*B*B+(truthBound L O D+2)*B+3

theorem firstFailed_cost {S : Selection n c} (ops : Operations S) (B L O D M : Nat)
    (hc : c ≤ B) (bounds : Bounded ops L O D M) :
    (firstFailed ops).cost ≤ searchBound B L O D := by
  have hr := MeasuredCollections.range_cost c
  have hf := MeasuredReach.find_cost (failed ops) (MeasuredCollections.range c).value
    (truthBound L O D+1) (failed_cost ops L O D M bounds)
  rw [MeasuredCollections.range_value,List.length_finRange] at hf
  have hcc := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hc hc)
  have hlinear := Nat.mul_le_mul_left (truthBound L O D+2) hc
  simp only [firstFailed,searchBound]
  simp only [MeasuredCollections.range_value,Nat.add_assoc,Nat.reduceAdd,Nat.mul_assoc] at *
  omega

def assignment {S : Selection n c} (ops : Operations S) : Measured (List Bool) :=
  let indices := MeasuredCollections.range n
  let bits := MeasuredCollections.map (sigma ops) indices.value
  ⟨bits.value,indices.cost+bits.cost+1⟩

theorem assignment_value {S : Selection n c} (ops : Operations S) :
    (assignment ops).value = List.ofFn (NativeBasis.sigma S) := by
  simp only [assignment,MeasuredCollections.map_value,MeasuredCollections.range_value,sigma_value]
  simp [List.finRange,List.map_ofFn,Function.comp_def]

def assignmentBound (B L O D : Nat) : Nat := 3*B*B+(O+D+L+3)*B+3

theorem assignment_cost {S : Selection n c} (ops : Operations S) (B L O D M : Nat)
    (hn : n ≤ B) (bounds : Bounded ops L O D M) :
    (assignment ops).cost ≤ assignmentBound B L O D := by
  have hr := MeasuredCollections.range_cost n
  have hm := MeasuredCollections.map_cost (sigma ops) (MeasuredCollections.range n).value
    (O+D+L+1) (sigma_cost ops L O D M bounds)
  rw [MeasuredCollections.range_value,List.length_finRange] at hm
  have hnn := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hn hn)
  have hlinear := Nat.mul_le_mul_left (O+D+L+3) hn
  simp only [assignment,assignmentBound]
  simp only [MeasuredCollections.range_value,Nat.add_assoc,Nat.reduceAdd,Nat.mul_assoc] at *
  omega


end PNP.Concrete.NativeNormalization.MeasuredCandidate
