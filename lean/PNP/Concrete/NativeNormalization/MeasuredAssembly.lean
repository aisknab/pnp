import PNP.Concrete.NativeNormalization.MeasuredCompanion

namespace PNP.Concrete.NativeNormalization.MeasuredAssembly

open MeasuredReach MeasuredOperations NativeBasis NativeEquations NativeCoefficients NativeSparseSystem

def doubleRows : List (Fin c) → Measured (List (Row c))
  | [] => ⟨[],1⟩
  | i::xs =>
      let tail := doubleRows xs
      ⟨(i,false)::(i,true)::tail.value,tail.cost+5⟩

theorem doubleRows_value (xs : List (Fin c)) :
    (doubleRows xs).value = xs.flatMap (fun i => [(i,false),(i,true)]) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [doubleRows,ih]

theorem doubleRows_cost (xs : List (Fin c)) :
    (doubleRows xs).cost = 5*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [doubleRows,ih,List.length_cons]; omega

def allRows (c : Nat) : Measured (List (Row c)) :=
  let indices := MeasuredCollections.range c
  let rows := doubleRows indices.value
  ⟨rows.value,indices.cost+rows.cost+1⟩

theorem allRows_value (c : Nat) : (allRows c).value = NativeSparseSystem.allRows c := by
  simp only [allRows,doubleRows_value,MeasuredCollections.range_value,NativeSparseSystem.allRows]

theorem allRows_length (c : Nat) : (allRows c).value.length = 2*c := by
  rw [allRows_value,NativeSparseSystem.allRows_length]

def rowsBound (B : Nat) : Nat := 3*B*B+5*B+3

theorem allRows_cost (c B : Nat) (hc : c ≤ B) : (allRows c).cost ≤ rowsBound B := by
  have hr := MeasuredCollections.range_cost c
  have hcc := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hc hc)
  simp only [allRows,doubleRows_cost,MeasuredCollections.range_value,List.length_finRange,rowsBound]
  simp only [Nat.mul_assoc] at *
  omega

def remainingTest {S : Selection n c} (ops : Operations S) (failed i : Fin c) : Measured Bool :=
  let mode := ops.mode i
  ⟨decide (mode.value = none ∧ i ≠ failed),mode.cost+3⟩

theorem remainingTest_value {S : Selection n c} (ops : Operations S) (failed i : Fin c) :
    (remainingTest ops failed i).value = decide (S.mode i = none ∧ i ≠ failed) := by
  simp only [remainingTest,ops.mode_eq]

theorem remainingTest_cost {S : Selection n c} (ops : Operations S) (L O D M : Nat)
    (bounds : Bounded ops L O D M) (failed i : Fin c) :
    (remainingTest ops failed i).cost ≤ M+3 := by
  have hm := bounds.2.2.2 i
  simp only [remainingTest]
  omega

def remaining {S : Selection n c} (ops : Operations S) (failed : Fin c) :
    Measured (List (Fin c)) :=
  let indices := MeasuredCollections.range c
  let kept := MeasuredSelection.filter (remainingTest ops failed) indices.value
  ⟨kept.value,indices.cost+kept.cost+1⟩

theorem remaining_value {S : Selection n c} (ops : Operations S) (failed : Fin c) :
    (remaining ops failed).value = NativeSparseSystem.remaining S failed := by
  simp only [remaining,MeasuredSelection.filter_value,MeasuredCollections.range_value,
    remainingTest_value,NativeSparseSystem.remaining]

theorem remaining_length {S : Selection n c} (ops : Operations S) (failed : Fin c) :
    (remaining ops failed).value.length ≤ c := by
  rw [remaining_value]
  exact NativeSparseSystem.remaining_length S failed

def remainingBound (B M : Nat) : Nat := 3*B*B+(M+5)*B+3

theorem remaining_cost {S : Selection n c} (ops : Operations S) (B L O D M : Nat)
    (hc : c ≤ B) (bounds : Bounded ops L O D M) (failed : Fin c) :
    (remaining ops failed).cost ≤ remainingBound B M := by
  have hr := MeasuredCollections.range_cost c
  have hf := MeasuredSelection.filter_cost (remainingTest ops failed)
    (MeasuredCollections.range c).value (M+3) (remainingTest_cost ops L O D M bounds failed)
  rw [MeasuredCollections.range_value,List.length_finRange] at hf
  have hcc := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hc hc)
  have hlinear := Nat.mul_le_mul_left (M+5) hc
  simp only [remaining,remainingBound]
  simp only [MeasuredCollections.range_value,Nat.add_assoc,Nat.reduceAdd,Nat.mul_assoc] at *
  omega

def entry {S : Selection n c} (ops : Operations S) (failed : Fin c) (r : Row c) :
    Measured (Row c × Coefficients c) :=
  let terms := MeasuredCompanion.aTerms ops failed r
  ⟨(r,terms.value),terms.cost+1⟩

theorem entry_value {S : Selection n c} (ops : Operations S) (failed : Fin c) (r : Row c) :
    (entry ops failed r).value = (r,NativeCoefficients.aTerms S failed r) := by
  simp only [entry,MeasuredCompanion.aTerms_value]

theorem entry_cost {S : Selection n c} (ops : Operations S) (L O D M : Nat)
    (bounds : Bounded ops L O D M) (failed : Fin c) (r : Row c) :
    (entry ops failed r).cost ≤ MeasuredCompanion.companionBound L O D M+2 := by
  have h := MeasuredCompanion.aTerms_cost ops L O D M bounds failed r
  simp only [entry]
  omega

def assemble {S : Selection n c} (ops : Operations S) (failed : Fin c) : Measured (System c) :=
  let b := MeasuredTerms.bTerms ops failed
  let rows := allRows c
  let a := MeasuredCollections.map (entry ops failed) rows.value
  let indices := remaining ops failed
  let e := MeasuredCollections.map (MeasuredCompanion.imageTerms ops failed) indices.value
  ⟨⟨b.value,a.value,e.value⟩,b.cost+rows.cost+a.cost+indices.cost+e.cost+1⟩

theorem assemble_value {S : Selection n c} (ops : Operations S) (failed : Fin c) :
    (assemble ops failed).value = NativeSparseSystem.assemble S failed := by
  simp only [assemble,MeasuredTerms.bTerms_value,MeasuredCollections.map_value,
    allRows_value,entry_value,remaining_value,MeasuredCompanion.imageTerms_value,
    NativeSparseSystem.assemble]

def assemblyBound (B L O D M : Nat) : Nat :=
  MeasuredTerms.bBound L O D M+rowsBound B+
    (MeasuredCompanion.companionBound L O D M+4)*(2*B)+remainingBound B M+
    (MeasuredTerms.literalBound L O D M+4)*B+3

theorem assemble_cost {S : Selection n c} (ops : Operations S) (B L O D M : Nat)
    (hc : c ≤ B) (bounds : Bounded ops L O D M) (failed : Fin c) :
    (assemble ops failed).cost ≤ assemblyBound B L O D M := by
  have hb := MeasuredTerms.bTerms_cost ops L O D M bounds failed
  have hr := allRows_cost c B hc
  have ha := MeasuredCollections.map_cost (entry ops failed) (allRows c).value
    (MeasuredCompanion.companionBound L O D M+2) (entry_cost ops L O D M bounds failed)
  rw [allRows_length] at ha
  have hi := remaining_cost ops B L O D M hc bounds failed
  have he := MeasuredCollections.map_cost (MeasuredCompanion.imageTerms ops failed)
    (remaining ops failed).value (MeasuredTerms.literalBound L O D M+2)
    (MeasuredCompanion.imageTerms_cost ops L O D M bounds failed)
  have hlen := remaining_length ops failed
  have hla := Nat.mul_le_mul_left (MeasuredCompanion.companionBound L O D M+4)
    (Nat.mul_le_mul_left 2 hc)
  have hle := Nat.mul_le_mul_left (MeasuredTerms.literalBound L O D M+4) (Nat.le_trans hlen hc)
  simp only [assemble,assemblyBound]
  simp only [Nat.add_assoc,Nat.reduceAdd] at *
  omega


end PNP.Concrete.NativeNormalization.MeasuredAssembly
