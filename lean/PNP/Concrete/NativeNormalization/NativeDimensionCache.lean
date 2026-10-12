import PNP.Concrete.NativeNormalization.NativePreparedProducer

namespace PNP.Concrete.NativeNormalization.NativeDimensionCache

open PNP.Concrete CNFCore NativeBasis NativeEquations NativeSource NativeSparseSystem

def transportSelection {n c n' c' : Nat} (hn : n = n') (hc : c = c')
    (S : Selection n c) : Selection n' c' := hn ▸ hc ▸ S

def transportOutput {c c' : Nat} (hc : c = c') (r : Output c) : Output c' := hc ▸ r

def transportValues {c c' : Nat} (hc : c = c') (u : RowValues c) : RowValues c' := hc ▸ u

/-- All dimensions supplied to computation are materialized numbers. -/
def runSelection (S : Selection n c) (recover : BitString → BitString) : Output c :=
  match (List.finRange c).find? (fun i => !(clauseTrue S (sigma S) i)) with
  | none => .model (recover (List.ofFn (sigma S)))
  | some i => .system (assemble S i)
      (fun u => recover (List.ofFn (recovered S i u).x))

theorem runSelection_transport {n c n' c' : Nat} (hn : n = n') (hc : c = c')
    (S : Selection n c) (recover : BitString → BitString) :
    transportOutput hc.symm
      (runSelection (NativeSourceCache.cacheSelection (transportSelection hn hc S)) recover) =
      runSelection (NativeSourceCache.cacheSelection S) recover := by
  subst n'
  subst c'
  rfl

structure Produced (F : CNFFormula) where
  rows : Nat
  result : Output rows
  rows_eq : rows = (positions F).length
  correct : OutputCorrect F (transportOutput rows_eq result)

def build (F : CNFFormula) (three : ThreeCore F) : Produced F :=
  let C := NativeContext.prepare F
  let hn := congrArg List.length C.variable_eq
  let hc := congrArg List.length C.clause_eq
  let S := NativeSourceCache.cacheSelection
    (transportSelection hn.symm hc.symm (C.rawSelection three))
  let r := runSelection S C.toCutData.recover
  { rows := C.clauseData.length
    result := r
    rows_eq := hc
    correct := by
      have eq : transportOutput hc r = NativePreparedProducer.produceThree F three := by
        dsimp only [r, S]
        rw [runSelection_transport]
        simp only [runSelection, NativePreparedProducer.produceThree, C]
        split
        · rename_i h
          rw [h]
        · rename_i i h
          rw [h]
      rw [eq]
      exact NativePreparedProducer.produceThree_correct F three }

/-- Proof transport is erased; the concrete constructor retains its cached row count. -/
theorem build_correct (F : CNFFormula) (three : ThreeCore F) :
    OutputCorrect F (transportOutput (build F three).rows_eq (build F three).result) :=
  (build F three).correct

def projectSelection (S : Selection n c) (a : BitString) : RowValues c :=
  selected S (extend S (NativeSourceEquations.vector n a))

theorem projectSelection_transport {n c n' c' : Nat} (hn : n = n') (hc : c = c')
    (S : Selection n c) (a : BitString) :
    transportValues hc.symm
      (projectSelection (NativeSourceCache.cacheSelection (transportSelection hn hc S)) a) =
      projectSelection (NativeSourceCache.cacheSelection S) a := by
  subst n'
  subst c'
  rfl

structure Projected (F : CNFFormula) (three : ThreeCore F) (a : BitString) where
  rows : Nat
  values : RowValues rows
  rows_eq : rows = (positions F).length
  values_eq : transportValues rows_eq values = NativeSourceCache.projectThree F three a

def project (F : CNFFormula) (three : ThreeCore F) (a : BitString) :
    Projected F three a :=
  let C := NativeContext.prepare F
  let hn := congrArg List.length C.variable_eq
  let hc := congrArg List.length C.clause_eq
  let S := NativeSourceCache.cacheSelection
    (transportSelection hn.symm hc.symm (C.rawSelection three))
  let u := projectSelection S (C.toCutData.projectValues a)
  { rows := C.clauseData.length
    values := u
    rows_eq := hc
    values_eq := by
      dsimp only [u, S]
      rw [projectSelection_transport]
      simp only [projectSelection, NativeSourceCache.projectThree,
        NativeContext.Prepared.rawSelection_eq, NativeContext.CutData.projectValues_eq] }


end PNP.Concrete.NativeNormalization.NativeDimensionCache
