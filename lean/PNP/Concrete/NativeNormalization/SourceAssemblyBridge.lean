import PNP.Concrete.NativeNormalization.SystemAssemblyBridge
import PNP.Concrete.NormalizerSourceAssemblyPolynomial

namespace PNP.Concrete.NativeNormalization.SourceAssemblySourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks
open NativeBasis NativeSource SourceCacheSourceBridge CoefficientSourceBridge

abbrev encodedInput (F : CNFFormula) : BitString := MatchingDriver.encode F.variableCount F.clauses
theorem checked_source (F : CNFFormula) (three : ThreeCore F) :
    (SourceAssembly.checked (encodedInput F)).registers.output =
      TableOwner.answer ((MeasuredCandidate.firstFailed
        (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value.map Fin.val) := by
  change (SourceCheck.result (encodedInput F)).registers.output = _
  exact CheckSourceBridge.result_source F three

attribute [local irreducible] SourceCheck.result SourceAssembly.migrated SourceAssembly.extended

theorem migrated_encoded (F : CNFFormula) (three : ThreeCore F)
    (failed : Fin (MeasuredSourceCache.build F three).value.rows)
    (found : (MeasuredCandidate.firstFailed
      (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value = some failed) :
    (context (MeasuredSourceCache.build F three).value.data failed).Encoded
      (SourceAssembly.migrated (SourceAssembly.checked (encodedInput F))).core.core := by
  have fields := SourceAssembly.migrated_source_data (SourceCheck.result (encodedInput F))
  have cache := CheckSourceBridge.cache_retained F three
  have candidate := CheckSourceBridge.candidate_retained F three
  rw [MeasuredCandidate.assignment_value] at candidate
  have output := CheckSourceBridge.result_source F three
  rw [found] at output
  have failure : (SourceCheck.result (encodedInput F)).registers.output.tail = List.replicate failed.val true := by
    rw [output]
    rfl
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [Coefficient.State.data,context,SourceAssembly.checked] using
      (congrArg Coefficient.Data.literals fields).trans cache.literalRead
  · simpa only [Coefficient.State.data,context,SourceAssembly.checked] using
      (congrArg Coefficient.Data.owners fields).trans cache.ownerRead
  · simpa only [Coefficient.State.data,context,SourceAssembly.checked] using
      (congrArg Coefficient.Data.slots fields).trans cache.slotRead
  · simpa only [Coefficient.State.data,context,SourceAssembly.checked] using
      (congrArg Coefficient.Data.modes fields).trans cache.modeRead
  · simpa only [Coefficient.State.data,context,SourceAssembly.checked] using
      (congrArg Coefficient.Data.assignment fields).trans candidate
  · simpa only [Coefficient.State.data,context,SourceAssembly.checked] using
      (congrArg Coefficient.Data.failed fields).trans failure

theorem migrated_rows (F : CNFFormula) (three : ThreeCore F) :
    (SourceAssembly.migrated (SourceAssembly.checked (encodedInput F))).core.rows.length =
      (MeasuredSourceCache.build F three).value.rows := by
  have cache := CheckSourceBridge.cache_retained F three
  change (SourceAssembly.migrated (SourceAssembly.extended (SourceCheck.result (encodedInput F)))).core.rows.length = _
  rw [SourceAssembly.migrated_source_rows,cache.rowsRead,List.length_replicate]

theorem result_none_state (F : CNFFormula) (three : ThreeCore F)
    (found : (MeasuredCandidate.firstFailed
      (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value = none) :
    SourceAssembly.result (encodedInput F) = SourceAssembly.checked (encodedInput F) := by
  have output := checked_source F three
  rw [found] at output
  exact SourceAssembly.dispatched_none (SourceAssembly.checked (encodedInput F)) output

theorem result_some (F : CNFFormula) (three : ThreeCore F)
    (failed : Fin (MeasuredSourceCache.build F three).value.rows)
    (found : (MeasuredCandidate.firstFailed
      (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value = some failed) :
    (SourceAssembly.result (encodedInput F)).registers.output =
      (NativeSystemCodec.systemCodec (MeasuredSourceCache.build F three).value.rows).encode
        (MeasuredAssembly.assemble
          (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data) failed).value := by
  have output := checked_source F three
  rw [found] at output
  change (SourceAssembly.dispatched (SourceAssembly.checked (encodedInput F))).registers.output = _
  rw [SourceAssembly.dispatched_some _ failed.val output]
  exact SystemRowsSourceBridge.complete_measured_system (MeasuredSourceCache.build F three).value.data failed
    (SourceAssembly.migrated (SourceAssembly.checked (encodedInput F)))
    (migrated_encoded F three failed found) (migrated_rows F three)

def expected (F : CNFFormula) (three : ThreeCore F) : BitString :=
  let built := (MeasuredSourceCache.build F three).value
  match (MeasuredCandidate.firstFailed (MeasuredCache.operations built.data)).value with
  | none => TableOwner.answer none
  | some failed => (NativeSystemCodec.systemCodec built.rows).encode
      (MeasuredAssembly.assemble (MeasuredCache.operations built.data) failed).value

theorem result_source (F : CNFFormula) (three : ThreeCore F) :
    (SourceAssembly.result (encodedInput F)).registers.output = expected F three := by
  dsimp only [expected]
  cases h : (MeasuredCandidate.firstFailed
      (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value with
  | none =>
      rw [result_none_state F three h,checked_source F three,h]
      rfl
  | some failed => exact result_some F three failed h
theorem result_fromSource (F : CNFFormula) :
    (SourceAssembly.result (encodedInput (NativeTseitin.frontend F))).registers.output =
      expected (NativeTseitin.frontend F) (NativeFrontend.frontend_three F) :=
  result_source (NativeTseitin.frontend F) (NativeFrontend.frontend_three F)
theorem polynomial_source (F : CNFFormula) (three : ThreeCore F) :
    SourceAssembly.polynomial.output (encodedInput F) = expected F three := by
  rw [SourceAssembly.polynomial_output,result_source F three]
theorem polynomial_fromSource (F : CNFFormula) :
    SourceAssembly.polynomial.output (encodedInput (NativeTseitin.frontend F)) =
      expected (NativeTseitin.frontend F) (NativeFrontend.frontend_three F) :=
  polynomial_source (NativeTseitin.frontend F) (NativeFrontend.frontend_three F)
theorem machine_source (F : CNFFormula) (three : ThreeCore F) :
    machineOutput (BitRegister.CompilerIO.rawMachine SourceAssembly.program)
      ((BitRegister.CompilerIO.runtimePolynomial 38 SourceAssembly.sourceFuel).eval (encodedInput F).length)
      (encodedInput F) = expected F three := by
  rw [SourceAssembly.machine_output,polynomial_source F three]
theorem machine_fromSource (F : CNFFormula) :
    machineOutput (BitRegister.CompilerIO.rawMachine SourceAssembly.program)
      ((BitRegister.CompilerIO.runtimePolynomial 38 SourceAssembly.sourceFuel).eval
        (encodedInput (NativeTseitin.frontend F)).length)
      (encodedInput (NativeTseitin.frontend F)) =
      expected (NativeTseitin.frontend F) (NativeFrontend.frontend_three F) :=
  machine_source (NativeTseitin.frontend F) (NativeFrontend.frontend_three F)

end PNP.Concrete.NativeNormalization.SourceAssemblySourceBridge
