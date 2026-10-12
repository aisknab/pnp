import PNP.Concrete.NativeNormalization.NativeSparseChecker

namespace PNP.Concrete.NativeNormalization.NativeSourceCache

open PNP.Concrete CNFCore NativeBasis NativeEquations NativeSparseSystem NativeSource

/-- Materialized finite lookup tables; no search result or proof premise is supplied. -/
def cacheSelection (S : Selection n c) : Selection n c :=
  let literals := List.ofFn fun i : Fin c =>
    (S.literal i .first, S.literal i .middle, S.literal i .last)
  let owners := List.ofFn S.owner
  let slots := List.ofFn S.slot
  let modes := List.ofFn S.mode
  { literal := fun i s => match s with
      | .first => (literals[i.val]'(by simp [literals])).1
      | .middle => (literals[i.val]'(by simp [literals])).2.1
      | .last => (literals[i.val]'(by simp [literals])).2.2
    owner := fun j => owners[j.val]'(by simp [owners])
    slot := fun j => slots[j.val]'(by simp [slots])
    mode := fun i => modes[i.val]'(by simp [modes])
    ownerVariable := by
      intro j
      simp only [literals, owners, slots, List.getElem_ofFn]
      cases h : S.slot j <;> simpa only [h] using S.ownerVariable j
    ownerMode := by
      intro j
      simpa only [modes, owners, slots, List.getElem_ofFn] using S.ownerMode j }

theorem cacheSelection_eq (S : Selection n c) : cacheSelection S = S := by
  cases S with
  | mk literal owner slot mode hv hm =>
      simp only [cacheSelection, List.getElem_ofFn]
      congr 1
      funext i s
      cases s <;> rfl

/-- The proved shape need not be decided again; all source fields are cached once. -/
def produceThree (F : CNFFormula) (three : ThreeCore F) :
    NativeSparseSystem.Output (positions F).length :=
  let S := cacheSelection (selection F three)
  match (List.finRange (positions F).length).find?
      (fun i => !(clauseTrue S (sigma S) i)) with
  | none => .model (recover F (List.ofFn (sigma S)))
  | some i => .system (assemble S i)
      (fun u => recover F (List.ofFn (recovered S i u).x))

theorem produceThree_eq (F : CNFFormula) (three : ThreeCore F) :
    produceThree F three = NativeSparseSystem.produce F := by
  simp only [produceThree, cacheSelection_eq, NativeSparseSystem.produce,
    NativeSource.build, dif_pos three, firstFailed]
  split
  · rename_i h
    rw [h]
  · rename_i i h
    rw [h]

theorem produceThree_correct (F : CNFFormula) (three : ThreeCore F) :
    OutputCorrect F (produceThree F three) := by
  rw [produceThree_eq]
  exact NativeSparseSystem.produce_correct F

/-- Cached witness projection used for execution, with exact extensional equality. -/
def projectThree (F : CNFFormula) (three : ThreeCore F) (a : BitString) :
    RowValues (positions F).length :=
  let S := cacheSelection (selection F three)
  selected S (extend S (NativeSourceEquations.vector (variables F).length (projectValues F a)))

theorem projectThree_eq (F : CNFFormula) (three : ThreeCore F) (a : BitString) :
    projectThree F three a = NativeSourceEquations.projectSolution F three a := by
  simp only [projectThree, cacheSelection_eq]
  rfl


end PNP.Concrete.NativeNormalization.NativeSourceCache
