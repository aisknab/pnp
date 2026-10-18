import PNP.Concrete.ResidualReduction.SourceFamilyReductionRow

/-! Count-controlled reduction of an arbitrary source family. Failed rows
do not terminate input consumption or restore validity. Accumulation retains
the original relative order of all successfully constructed rows. -/

namespace PNP.Concrete.ResidualReduction.SourceFamilyReductionLoop
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (familyBits)
open PNP.Concrete.ResidualReduction.SourceRowReductionState (work parameters emptyData reduceRow)
open PNP.Concrete.ResidualReduction.SourceFamilyReductionEncoding (emitted retained valid retained_bits_cons)
open PNP.Concrete.ResidualReduction.SourceFamilyReductionState

def block : Block 23 := .loop 19 SourceFamilyReductionRow.block
def fuel {n : Nat} (t : TailForm n) : Family (n + 1) → Nat
  | [] => 1
  | r :: F => 1 + (SourceFamilyReductionRow.fuel t r + fuel t F)

theorem block_exec {n : Nat} (t : TailForm n) (F : Family (n + 1))
    (suffix accumulator : BitString) (flag : Bool) (count : BitString) :
    Exec block (loopState t F suffix accumulator flag count) (fuel t F)
      (done t suffix ((familyBits (retained t F)).reverse ++ accumulator)
        (flag && valid t F) count) := by
  induction F generalizing accumulator flag with
  | nil => cases flag <;> exact Exec.loopStop rfl
  | cons r F ih =>
    have first : Exec SourceFamilyReductionRow.block (loopState t (r :: F) suffix accumulator flag count)
        (SourceFamilyReductionRow.fuel t r)
        (loopState t F suffix ((emitted (reduceRow t r)).reverse ++ accumulator)
          (flag && (reduceRow t r).isSome) count) := by
      simpa only [loopState,familyBits,List.append_assoc,List.length_cons,List.replicate_succ] using
        SourceFamilyReductionRow.block_exec t r (familyBits F ++ suffix)
          (List.replicate F.length true) accumulator flag count
    have rest := ih ((emitted (reduceRow t r)).reverse ++ accumulator) (flag && (reduceRow t r).isSome)
    have checked := Exec.loopStep (source := (19 : Fin 23)) rfl first rest
    simpa only [block,fuel,retained_bits_cons,List.reverse_append,List.append_assoc,
      valid,Bool.and_assoc] using checked

theorem fuel_bound {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    fuel t F ≤ (313 * (n + 1) + 236) * F.length + 1 := by
  induction F with
  | nil => exact Nat.le_refl _
  | cons r F ih =>
    have head := SourceFamilyReductionRow.fuel_bound t r
    simp only [fuel,List.length_cons,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc] at *
    omega

def headerTail : Block 23 := .seq (.action (.push 8 false)) <|
  .seq (.action (.copy 20 8)) (.action (.clear 8))
def header : Block 23 := .seq (.action (.copy 2 22)) <|
  .seq (core MatrixSolutionSerialization.unaryLoop) headerTail

theorem header_exec {n : Nat} (t : TailForm n) (F : Family (n + 1)) (suffix : BitString) :
    Exec header (SourceFamilyReductionState.initial t F suffix) (3 * F.length + 5)
      (loopState t F suffix (natural F.length).reverse true (List.replicate F.length true)) := by
  let before := work n (familyBits F ++ suffix)
  let d := emptyData t []
  let s : Saved := ⟨List.replicate F.length true,[],[true],List.replicate F.length true⟩
  let loaded := {before with remaining := List.replicate F.length true}
  let scanned := {before with output := List.replicate F.length true}
  have load : Exec (.action (.copy (2 : Fin 23) 22))
      (full (SourceRowReductionState.full before (parameters t) d) s) 1
      (full (SourceRowReductionState.full loaded (parameters t) d) s) := .action _ _
  have scan : Exec MatrixSolutionSerialization.unaryLoop loaded.store (3 * F.length + 1) scanned.store := by
    simpa only [loaded,scanned,before,work,List.length_replicate,List.append_nil] using
      SourceChartFamily.unary_exec before (List.replicate F.length true)
  have tail : Exec headerTail (full (SourceRowReductionState.full scanned (parameters t) d) s) 3
      (loopState t F suffix (natural F.length).reverse true (List.replicate F.length true)) := by
    simp only [natural,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.reverse_replicate,List.nil_append,List.singleton_append]
    exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have cost : 3 * F.length + 5 = 1 + ((3 * F.length + 1) + 3) := by omega
  simpa only [header,cost,SourceFamilyReductionState.initial,loopState,state,base,before,d,s] using
    Exec.seq load (Exec.seq (core_exec scan (parameters t) d s) tail)

end PNP.Concrete.ResidualReduction.SourceFamilyReductionLoop
