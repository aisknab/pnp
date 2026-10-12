import PNP.Concrete.NativeNormalization.MeasuredAccess

namespace PNP.Concrete.NativeNormalization.MeasuredChoice

open PNP.Concrete MeasuredReach NativeContext NativeSource NativeBasis

theorem ownerLookup_value {F : CNFFormula} (C : CutData F)
    (v : Fin (CNFCore.variables F).length) :
    (MeasuredSearch.owner (MeasuredAccess.table C) (MeasuredAccess.atVariable C v).value).value =
      Matching.owner (CNFCore.matching F) (CNFCore.atVariable F v) := by
  rw [MeasuredSearch.owner_value,MeasuredAccess.table_get,MeasuredAccess.atVariable_value,C.atVariable_eq]
  rw [show C.matchAt = CNFCore.matching F from funext C.matchAt_eq]

def partner {F : CNFFormula} (C : CutData F) (v : Fin (CNFCore.variables F).length) :
    Measured (Fin (CNFCore.positions F).length) :=
  let original := MeasuredAccess.atVariable C v
  let found := MeasuredSearch.owner (MeasuredAccess.table C) original.value
  match hf : found.value with
  | none => False.elim (CNFCore.core_owner_exists F v (by
      simpa only [found,original,ownerLookup_value] using hf))
  | some i =>
      let index := MeasuredSelection.position i C.clauseData
      ⟨⟨index.value,by
        simp only [index,MeasuredSelection.position_value,C.clause_eq]
        apply PNP.Concrete.NormalizerBlocks.ConstructiveLists.finiteIndexBound
        apply (CNFCore.positions_mem F i).mpr
        apply CNFCore.core_owner_kept F v i
        simpa only [found,original,ownerLookup_value] using hf⟩,
        original.cost+found.cost+index.cost+3⟩

theorem partner_value {F : CNFFormula} (C : CutData F)
    (v : Fin (CNFCore.variables F).length) : (partner C v).value = C.partner v := by
  rw [C.partner_eq]
  unfold partner CNFCore.partner
  dsimp only
  split
  · rename_i h
    exact False.elim (CNFCore.core_owner_exists F v ((ownerLookup_value C v).symm.trans h))
  · rename_i i hi
    have hs := (ownerLookup_value C v).symm.trans hi
    split
    · rename_i hn
      exact False.elim (CNFCore.core_owner_exists F v hn)
    · rename_i j hj
      have eq : j = i := Option.some.inj (hj.symm.trans hs)
      cases eq
      apply Fin.ext
      simp only [MeasuredSelection.position_value,C.clause_eq,CNFCore.denseClause]

def partnerBound (B : Nat) : Nat := MeasuredSearch.ownerBound B+3*B+4

theorem partner_cost {F : CNFFormula} (C : CutData F) (B : Nat)
    (size : F.clauses.length+F.variableCount ≤ B) (v : Fin (CNFCore.variables F).length) :
    (partner C v).cost ≤ partnerBound B := by
  have ha := MeasuredAccess.atVariable_cost C v
  have ho := MeasuredSearch.owner_cost (MeasuredAccess.table C)
    (MeasuredAccess.atVariable C v).value B (by omega)
  have hc := MeasuredAccess.clauseData_bound C
  unfold partner
  dsimp only
  split
  · rename_i h
    exact False.elim (CNFCore.core_owner_exists F v ((ownerLookup_value C v).symm.trans h))
  · rename_i i hi
    have hp := MeasuredSelection.position_cost i C.clauseData
    simp only [partnerBound]
    omega

theorem matchingLookup_value {F : CNFFormula} (C : CutData F)
    (i : Fin (CNFCore.positions F).length) :
    (MeasuredAccess.matchAt C (MeasuredAccess.atClause C i).value).value =
      CNFCore.matching F (CNFCore.atClause F i) := by
  simp only [MeasuredAccess.matchAt_value,MeasuredAccess.atClause_value,
    NativeContext.CutData.matchAt_eq,NativeContext.CutData.atClause_eq]

def transported {F : CNFFormula} (C : CutData F) (i : Fin (CNFCore.positions F).length) :
    Measured (Option (Fin (CNFCore.variables F).length)) :=
  let original := MeasuredAccess.atClause C i
  let found := MeasuredAccess.matchAt C original.value
  match hf : found.value with
  | none => ⟨none,original.cost+found.cost+1⟩
  | some v =>
      let index := MeasuredSelection.position v C.variableData
      ⟨some ⟨index.value,by
        simp only [index,MeasuredSelection.position_value,C.variable_eq]
        apply PNP.Concrete.NormalizerBlocks.ConstructiveLists.finiteIndexBound
        apply (CNFCore.variables_mem F v).mpr
        apply CNFCore.matched_inside F i v
        simpa only [found,original,matchingLookup_value] using hf⟩,
        original.cost+found.cost+index.cost+2⟩

theorem transported_value {F : CNFFormula} (C : CutData F)
    (i : Fin (CNFCore.positions F).length) : (transported C i).value = C.transported i := by
  rw [C.transported_eq]
  unfold transported CNFCore.transported
  dsimp only
  split
  · rename_i hn
    have hs := (matchingLookup_value C i).symm.trans hn
    split
    · rfl
    · rename_i v hv
      rw [hs] at hv
      cases hv
  · rename_i v hv
    have hs := (matchingLookup_value C i).symm.trans hv
    split
    · rename_i hn
      rw [hs] at hn
      cases hn
    · rename_i w hw
      have eq : w = v := Option.some.inj (hw.symm.trans hs)
      cases eq
      dsimp only
      apply congrArg some
      apply Fin.ext
      simp only [MeasuredSelection.position_value,C.variable_eq,CNFCore.denseVariable]

theorem transported_cost {F : CNFFormula} (C : CutData F) (B : Nat)
    (size : F.clauses.length+F.variableCount ≤ B) (i : Fin (CNFCore.positions F).length) :
    (transported C i).cost ≤ 4*B+3 := by
  have ha := MeasuredAccess.atClause_cost C i
  have hm := MeasuredAccess.matchAt_cost C (MeasuredAccess.atClause C i).value
  have hv := MeasuredAccess.variableData_bound C
  unfold transported
  dsimp only
  split
  · dsimp only
    omega
  · rename_i v h
    have hi := MeasuredSelection.position_cost v C.variableData
    dsimp only
    omega

def choose (ls : Slot → Measured (Literal n)) (v : Fin n) : Measured Slot :=
  let first := ls .first
  if first.value.index = v then ⟨.first,first.cost+2⟩ else
    let middle := ls .middle
    ⟨if middle.value.index = v then .middle else .last,first.cost+middle.cost+3⟩

theorem choose_value (ls : Slot → Measured (Literal n)) (v : Fin n) :
    (choose ls v).value = chooseSlot (fun s => (ls s).value) v := by
  by_cases hf : (ls .first).value.index = v <;>
    by_cases hm : (ls .middle).value.index = v <;>
    simp [choose,chooseSlot,hf,hm]

theorem choose_cost (ls : Slot → Measured (Literal n)) (v : Fin n) (L : Nat)
    (bound : ∀ s, (ls s).cost ≤ L) : (choose ls v).cost ≤ 2*L+3 := by
  have hf := bound .first
  have hm := bound .middle
  by_cases h : (ls .first).value.index = v
  · simp only [choose,if_pos h]
    omega
  · simp only [choose,if_neg h]
    omega

def slot {F : CNFFormula} (C : Prepared F) (three : ThreeCore F)
    (v : Fin (CNFCore.variables F).length) : Measured Slot :=
  let owner := partner C.toCutData v
  let chosen := choose (MeasuredAccess.literal C three owner.value) v
  ⟨chosen.value,owner.cost+chosen.cost+1⟩

theorem slot_value {F : CNFFormula} (C : Prepared F) (three : ThreeCore F)
    (v : Fin (CNFCore.variables F).length) :
    (slot C three v).value = (C.rawSelection three).slot v := by
  simp only [slot,choose_value,MeasuredAccess.literal_value,partner_value,
    NativeContext.Prepared.rawSelection]

def slotBound (B : Nat) : Nat := partnerBound B+2*B+12

theorem slot_cost {F : CNFFormula} (C : Prepared F) (three : ThreeCore F)
    (B : Nat) (size : F.clauses.length+F.variableCount ≤ B) (v : Fin (CNFCore.variables F).length) :
    (slot C three v).cost ≤ slotBound B := by
  have hp := partner_cost C.toCutData B size v
  have hc := choose_cost (MeasuredAccess.literal C three (partner C.toCutData v).value)
    v (B+4) (by intro s; have h := MeasuredAccess.literal_cost C three (partner C.toCutData v).value s; omega)
  simp only [slot,slotBound]
  omega

def mode {F : CNFFormula} (C : Prepared F) (three : ThreeCore F)
    (i : Fin (CNFCore.positions F).length) : Measured (Option Slot) :=
  let matched := transported C.toCutData i
  match matched.value with
  | none => ⟨none,matched.cost+1⟩
  | some v =>
      let chosen := choose (MeasuredAccess.literal C three i) v
      ⟨some chosen.value,matched.cost+chosen.cost+2⟩

theorem mode_value {F : CNFFormula} (C : Prepared F) (three : ThreeCore F)
    (i : Fin (CNFCore.positions F).length) :
    (mode C three i).value = (C.rawSelection three).mode i := by
  simp only [mode,transported_value,choose_value,MeasuredAccess.literal_value,
    NativeContext.Prepared.rawSelection]
  cases C.toCutData.transported i <;> simp only [Option.map]

theorem mode_cost {F : CNFFormula} (C : Prepared F) (three : ThreeCore F)
    (B : Nat) (size : F.clauses.length+F.variableCount ≤ B) (i : Fin (CNFCore.positions F).length) :
    (mode C three i).cost ≤ 6*B+16 := by
  have ht := transported_cost C.toCutData B size i
  cases h : (transported C.toCutData i).value with
  | none =>
      simp only [mode,h]
      omega
  | some v =>
      have hc := choose_cost (MeasuredAccess.literal C three i) v (B+4)
        (by intro s; have hl := MeasuredAccess.literal_cost C three i s; omega)
      simp only [mode,h]
      omega


end PNP.Concrete.NativeNormalization.MeasuredChoice
