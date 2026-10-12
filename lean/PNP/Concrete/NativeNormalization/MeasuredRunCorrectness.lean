import PNP.Concrete.NativeNormalization.MeasuredRowEncoding

namespace PNP.Concrete.NativeNormalization.MeasuredRunCorrectness

open PNP.Concrete NativeBasis NativeEquations NativeSource NativeSparseSystem MeasuredOperations

def CoreCorrect (F : CNFFormula) (S : Selection n c) (recover : BitString → BitString) :
    MeasuredRun.Output c → Prop
  | .candidate a => F.Satisfied (recover a)
  | .system failed D =>
      (F.Satisfiable ↔ ∃ u, D.Satisfied u) ∧
      (∀ u, D.Satisfied u → F.Satisfied (recover (List.ofFn (recovered S failed u).x))) ∧
      NativeFrontend.SparseBounds D

theorem assembled_bounds (S : Selection n c) (failed : Fin c) :
    NativeFrontend.SparseBounds (assemble S failed) := by
  obtain ⟨hb,ha,he⟩ := assembled_row_bounds S failed
  obtain ⟨na,ne⟩ := assembled_row_counts S failed
  exact ⟨hb,ha,he,na,ne,assembled_size_bound S failed⟩

theorem source_spec_correct (F : CNFFormula) (three : ThreeCore F) :
    CoreCorrect F (selection F three) (CNFCore.recover F) (MeasuredRun.spec (selection F three)) := by
  unfold MeasuredRun.spec
  split
  · rename_i h
    have hf : NativeSource.firstFailed F three = none := h
    exact firstFailed_none F three hf
  · rename_i i h
    have hf : NativeSource.firstFailed F three = some i := h
    refine ⟨source_assembled_iff F three i hf,?_,assembled_bounds _ i⟩
    intro u hu
    exact source_assembled_recovery F three i hf u hu

def transportOutput {c c' : Nat} (hc : c = c') (r : MeasuredRun.Output c) :
    MeasuredRun.Output c' := hc ▸ r

theorem spec_transport {n c n' c' : Nat} (hn : n = n') (hc : c = c')
    (S : Selection n c) :
    MeasuredRun.spec (NativeDimensionCache.transportSelection hn hc S) =
      transportOutput hc (MeasuredRun.spec S) := by
  cases hn
  cases hc
  rfl

theorem correct_transport {n c n' c' : Nat} (F : CNFFormula)
    (hn : n = n') (hc : c = c') (S : Selection n c)
    (recover : BitString → BitString) (r : MeasuredRun.Output c) :
    CoreCorrect F (NativeDimensionCache.transportSelection hn hc S) recover (transportOutput hc r) ↔
      CoreCorrect F S recover r := by
  cases hn
  cases hc
  rfl

theorem cache_spec_correct (F : CNFFormula) (three : ThreeCore F)
    (b : MeasuredSourceCache.Built F three) :
    CoreCorrect F (MeasuredCache.selection b.data) b.context.toCutData.recover
      (MeasuredRun.spec (MeasuredCache.selection b.data)) := by
  have h := source_spec_correct F three
  have hs :
      NativeDimensionCache.transportSelection b.columns_eq b.rows_eq (MeasuredCache.selection b.data) =
        selection F three := MeasuredSourceCache.canonicalSelection_eq b
  have hr : b.context.toCutData.recover = CNFCore.recover F := funext b.context.toCutData.recover_eq
  rw [← hs,← hr,spec_transport] at h
  exact (correct_transport F b.columns_eq b.rows_eq (MeasuredCache.selection b.data)
    b.context.toCutData.recover (MeasuredRun.spec (MeasuredCache.selection b.data))).mp h

theorem cache_run_correct (F : CNFFormula) (three : ThreeCore F)
    (b : MeasuredSourceCache.Built F three) :
    CoreCorrect F (MeasuredCache.selection b.data) b.context.toCutData.recover
      (MeasuredRun.run (MeasuredCache.operations b.data)).value := by
  rw [MeasuredRun.run_value]
  simpa only [MeasuredCache.selection_eq] using cache_spec_correct F three b

def Sized (n : Nat) : MeasuredRun.Output c → Prop
  | .candidate a => a.length = n
  | .system _ _ => True

theorem run_size {S : Selection n c} (ops : Operations S) :
    Sized n (MeasuredRun.run ops).value := by
  rw [MeasuredRun.run_value]
  unfold MeasuredRun.spec
  split <;> simp [Sized]

theorem source_size (F : CNFFormula) :
    Sized (MeasuredRun.fromSource F).value.cache.columns (MeasuredRun.fromSource F).value.output :=
  run_size (MeasuredCache.operations (MeasuredSourceCache.fromSource F).value.data)

theorem source_correct (F : CNFFormula) :
    CoreCorrect (NativeTseitin.frontend F)
      (MeasuredCache.selection (MeasuredRun.fromSource F).value.cache.data)
      (MeasuredRun.fromSource F).value.cache.context.toCutData.recover
      (MeasuredRun.fromSource F).value.output :=
  cache_run_correct _ _ _


end PNP.Concrete.NativeNormalization.MeasuredRunCorrectness
