import PNP.Concrete.NativeNormalization.MeasuredAssembly

namespace PNP.Concrete.NativeNormalization.MeasuredRun

open PNP.Concrete MeasuredReach MeasuredOperations NativeBasis NativeSparseSystem

/-- A dense candidate is not yet the recovered original-source model. -/
inductive Output (c : Nat) where
  | candidate (bits : List Bool)
  | system (failed : Fin c) (data : System c)

def spec (S : Selection n c) : Output c :=
  match (List.finRange c).find? (fun i => !NativeSource.clauseTrue S (NativeBasis.sigma S) i) with
  | none => .candidate (List.ofFn (NativeBasis.sigma S))
  | some i => .system i (NativeSparseSystem.assemble S i)

def run {S : Selection n c} (ops : Operations S) : Measured (Output c) :=
  let found := MeasuredCandidate.firstFailed ops
  match found.value with
  | none =>
      let bits := MeasuredCandidate.assignment ops
      ⟨.candidate bits.value,found.cost+bits.cost+1⟩
  | some i =>
      let system := MeasuredAssembly.assemble ops i
      ⟨.system i system.value,found.cost+system.cost+1⟩

theorem run_value {S : Selection n c} (ops : Operations S) : (run ops).value = spec S := by
  simp only [run,MeasuredCandidate.firstFailed_value,MeasuredCandidate.assignment_value,
    MeasuredAssembly.assemble_value,spec]
  split <;> rfl

/-- A polynomial sum bounds either executed branch; this does not execute both. -/
def runBound (B L O D M : Nat) : Nat :=
  MeasuredCandidate.searchBound B L O D+MeasuredCandidate.assignmentBound B L O D+
    MeasuredAssembly.assemblyBound B L O D M+1

theorem run_cost {S : Selection n c} (ops : Operations S) (B L O D M : Nat)
    (hn : n ≤ B) (hc : c ≤ B) (bounds : Bounded ops L O D M) :
    (run ops).cost ≤ runBound B L O D M := by
  have hf := MeasuredCandidate.firstFailed_cost ops B L O D M hc bounds
  cases h : (MeasuredCandidate.firstFailed ops).value with
  | none =>
      have hb := MeasuredCandidate.assignment_cost ops B L O D M hn bounds
      simp only [run,h,runBound]
      omega
  | some i =>
      have hs := MeasuredAssembly.assemble_cost ops B L O D M hc bounds i
      simp only [run,h,runBound]
      omega

theorem built_dimensions {F : CNFFormula} {three : NativeSource.ThreeCore F}
    (b : MeasuredSourceCache.Built F three) (B : Nat)
    (size : F.clauses.length+F.variableCount ≤ B) : b.columns ≤ B ∧ b.rows ≤ B := by
  have hn := CNFCore.variables_bound F
  have hc := MeasuredAccess.clauseData_bound b.context.toCutData
  rw [b.context.clause_eq] at hc
  rw [b.columns_eq,b.rows_eq]
  omega

structure SourceOutput (F : CNFFormula) where
  cache : MeasuredSourceCache.Built (NativeTseitin.frontend F) (NativeFrontend.frontend_three F)
  output : Output cache.rows

/-- Execute only over stored dimensions and internally constructed cached operations.
Decoder, frontend conversion and original-model recovery costs are not included here. -/
def fromSource (F : CNFFormula) : Measured (SourceOutput F) :=
  let cache := MeasuredSourceCache.fromSource F
  let result := run (MeasuredCache.operations cache.value.data)
  ⟨⟨cache.value,result.value⟩,cache.cost+result.cost+1⟩

theorem fromSource_cache (F : CNFFormula) :
    (fromSource F).value.cache = (MeasuredSourceCache.fromSource F).value := rfl

theorem fromSource_result (F : CNFFormula) :
    (fromSource F).value.output =
      spec (MeasuredCache.selection (MeasuredSourceCache.fromSource F).value.data) := by
  change (run (MeasuredCache.operations (MeasuredSourceCache.fromSource F).value.data)).value = _
  rw [run_value,MeasuredCache.selection_eq]

def sourceBound (B : Nat) : Nat :=
  MeasuredSourceCache.buildBound B+runBound B (B+1) B B B+1

theorem decoded_fromSource_cost (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (fromSource F).cost ≤ sourceBound (21*bits.length+9) := by
  let cache := MeasuredSourceCache.fromSource F
  let B := 21*bits.length+9
  have hb : cache.cost ≤ MeasuredSourceCache.buildBound B :=
    MeasuredSourceCache.decoded_fromSource_cost bits F decoded
  have sizes := MeasuredFrontendCost.frontend_encoded_counts bits F decoded
  have size : (NativeTseitin.frontend F).clauses.length+
      (NativeTseitin.frontend F).variableCount ≤ B := by dsimp [B]; omega
  have dims := built_dimensions cache.value B size
  have ops := MeasuredSourceCache.cached_operations_bounded cache.value B size
  have hr := run_cost (MeasuredCache.operations cache.value.data) B (B+1) B B B
    dims.1 dims.2 ops
  change cache.cost+(run (MeasuredCache.operations cache.value.data)).cost+1 ≤ sourceBound B
  unfold sourceBound
  omega


end PNP.Concrete.NativeNormalization.MeasuredRun
