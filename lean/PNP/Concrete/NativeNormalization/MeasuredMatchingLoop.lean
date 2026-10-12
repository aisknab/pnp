import PNP.Concrete.NativeNormalization.MeasuredAugment

namespace PNP.Concrete.NativeNormalization.MeasuredMatchingLoop

open PNP.Concrete Matching MatchingCache MeasuredReach

/-- Count every matching round, including path decoding and table materialization. -/
def finish (F : CNFFormula) :
    Nat → Table F.clauses.length F.variableCount →
      Measured (Table F.clauses.length F.variableCount)
  | 0, T => ⟨T,1⟩
  | fuel+1, T =>
      let searched := MeasuredSearch.search F T
      match searched.value with
      | .terminal _ => ⟨T,searched.cost+1⟩
      | .augment _ route =>
          let pairs := MeasuredAugment.decodePairs route
          let updated := MeasuredAugment.update T pairs.value
          let next := finish F fuel updated.value
          ⟨next.value,searched.cost+pairs.cost+updated.cost+next.cost+2⟩

theorem finish_value (F : CNFFormula) (fuel : Nat)
    (T : Table F.clauses.length F.variableCount) :
    (finish F fuel T).value =
      MatchingCache.finishTable (CNFCore.incidence F) fuel T := by
  induction fuel generalizing T with
  | zero => rfl
  | succ fuel ih =>
      cases h : Matching.search (CNFCore.incidence F) T.get with
      | terminal tr =>
          simp only [finish,MeasuredSearch.search_value,h,MatchingCache.finishTable]
      | augment v route =>
          simp only [finish,MeasuredSearch.search_value,h,MeasuredAugment.update_value,
            MeasuredAugment.decodePairs_value,MatchingCache.finishTable,ih]

def roundBound (B : Nat) : Nat :=
  MeasuredSearch.searchBound B+2*B+MeasuredAugment.updateBound B+3

theorem finish_cost (F : CNFFormula)
    (shape : ∀ i, (CNFCore.clause F i).length ≤ 3) (B : Nat)
    (size : F.clauses.length+F.variableCount ≤ B) (fuel : Nat)
    (T : Table F.clauses.length F.variableCount) :
    (finish F fuel T).cost ≤ fuel*roundBound B+1 := by
  induction fuel generalizing T with
  | zero => simp [finish]
  | succ fuel ih =>
      have hs := MeasuredSearch.search_cost F T shape B size
      cases h : (MeasuredSearch.search F T).value with
      | terminal tr =>
          have hb : MeasuredSearch.searchBound B ≤ roundBound B := by
            simp only [roundBound]
            omega
          simp only [finish,h]
          rw [Nat.succ_mul]
          omega
      | augment v route =>
          have hl := MeasuredSearch.search_path_bound F T v route h
          have hp := MeasuredAugment.decodePairs_cost route
          have hx := MeasuredAugment.decodePairs_length route
          have hu := MeasuredAugment.update_cost T
            (MeasuredAugment.decodePairs route).value B (by omega) (by omega)
          have hn := ih (MeasuredAugment.update T (MeasuredAugment.decodePairs route).value).value
          have step :
              (MeasuredSearch.search F T).cost+(MeasuredAugment.decodePairs route).cost+
                (MeasuredAugment.update T (MeasuredAugment.decodePairs route).value).cost+2 ≤
                  roundBound B := by
            simp only [roundBound]
            omega
          simp only [finish,h]
          rw [Nat.succ_mul]
          omega

/-- The initial empty table is built internally and charged, not supplied. -/
def fullTable (F : CNFFormula) : Measured (Table F.clauses.length F.variableCount) :=
  let initial := MeasuredAugment.emptyTable F.clauses.length F.variableCount
  let completed := finish F (F.clauses.length+1) initial.value
  ⟨completed.value,initial.cost+completed.cost+1⟩

theorem fullTable_value (F : CNFFormula) :
    (fullTable F).value = MatchingCache.fullTable (CNFCore.incidence F) := by
  simp only [fullTable,finish_value,MeasuredAugment.emptyTable_value,MatchingCache.fullTable]

theorem fullTable_get (F : CNFFormula) :
    (fullTable F).value.get = Matching.fullMatching (CNFCore.incidence F) := by
  rw [fullTable_value,MatchingCache.fullTable_get]

theorem fullTable_valid_terminal (F : CNFFormula) :
    IsMatching (CNFCore.incidence F) (fullTable F).value.get ∧
      Matching.freeCandidate (CNFCore.incidence F) (fullTable F).value.get = none := by
  rw [fullTable_get]
  exact Matching.fullMatching_valid_terminal (CNFCore.incidence F)

def fullBound (B : Nat) : Nat :=
  3*B*B+3*B+(B+1)*roundBound B+5

theorem fullTable_cost (F : CNFFormula)
    (shape : ∀ i, (CNFCore.clause F i).length ≤ 3) (B : Nat)
    (size : F.clauses.length+F.variableCount ≤ B) :
    (fullTable F).cost ≤ fullBound B := by
  have hi := MeasuredAugment.emptyTable_cost F.clauses.length F.variableCount B (by omega)
  have hf := finish_cost F shape B size (F.clauses.length+1)
    (MeasuredAugment.emptyTable F.clauses.length F.variableCount).value
  have hm := Nat.mul_le_mul_right (roundBound B)
    (show F.clauses.length+1 ≤ B+1 by omega)
  simp only [fullTable,fullBound]
  omega

/-- This covers the whole matching phase on the converted formula, not conversion,
serialization or concrete tape-machine runtime. It does not decide satisfiability. -/
theorem decoded_fullTable_cost (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (fullTable (NativeTseitin.frontend F)).cost ≤ fullBound (21*bits.length+9) := by
  have shape : ∀ i, (CNFCore.clause (NativeTseitin.frontend F) i).length ≤ 3 := by
    intro i
    exact Nat.le_of_eq
      (NativeTseitin.frontend_shape F _ (CNFCore.source_member (NativeTseitin.frontend F) i)).1
  have sizes := MeasuredFrontendCost.frontend_encoded_counts bits F decoded
  exact fullTable_cost (NativeTseitin.frontend F) shape (21*bits.length+9) (by omega)


end PNP.Concrete.NativeNormalization.MeasuredMatchingLoop
