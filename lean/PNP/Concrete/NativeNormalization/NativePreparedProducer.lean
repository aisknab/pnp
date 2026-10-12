import PNP.Concrete.NativeNormalization.NativeContext

namespace PNP.Concrete.NativeNormalization.NativePreparedProducer

open PNP.Concrete CNFCore NativeBasis NativeEquations NativeSource NativeSparseSystem

def produceThree (F : CNFFormula) (three : ThreeCore F) :
    NativeSparseSystem.Output (positions F).length :=
  let C := NativeContext.prepare F
  let S := NativeSourceCache.cacheSelection (C.rawSelection three)
  match (List.finRange (positions F).length).find?
      (fun i => !(clauseTrue S (sigma S) i)) with
  | none => .model (C.toCutData.recover (List.ofFn (sigma S)))
  | some i => .system (assemble S i)
      (fun u => C.toCutData.recover (List.ofFn (recovered S i u).x))

theorem produceThree_eq (F : CNFFormula) (three : ThreeCore F) :
    produceThree F three = NativeSourceCache.produceThree F three := by
  simp only [produceThree, NativeSourceCache.produceThree,
    NativeContext.Prepared.rawSelection_eq, NativeContext.CutData.recover_eq]
  rfl

theorem produceThree_correct (F : CNFFormula) (three : ThreeCore F) :
    OutputCorrect F (produceThree F three) := by
  rw [produceThree_eq]
  exact NativeSourceCache.produceThree_correct F three

def projectThree (F : CNFFormula) (three : ThreeCore F) (a : BitString) :
    RowValues (positions F).length :=
  let C := NativeContext.prepare F
  let S := NativeSourceCache.cacheSelection (C.rawSelection three)
  selected S (extend S (NativeSourceEquations.vector (variables F).length (C.toCutData.projectValues a)))

theorem projectThree_eq (F : CNFFormula) (three : ThreeCore F) (a : BitString) :
    projectThree F three a = NativeSourceCache.projectThree F three a := by
  simp only [projectThree, NativeSourceCache.projectThree,
    NativeContext.Prepared.rawSelection_eq, NativeContext.CutData.projectValues_eq]


end PNP.Concrete.NativeNormalization.NativePreparedProducer
