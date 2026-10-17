import PNP.Concrete.ResidualReduction.SourceNativeTerm

/-! Complete arbitrary-count sparse-list iteration. Each successful step reads
and consumes an actual source label. Failure empties the loop counter and marks
the result invalid. The bound is uniform in the original encoded input length. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeTermsLoop
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceNativeTermsSpec
open PNP.Concrete.ResidualReduction.SourceNativeTermsState

def block : Block 14 := .loop 11 SourceNativeTerm.block
def finished {n : Nat} (result : Result n) : Store 14 :=
  state result.input result.accumulator 0 result.valid
def fuel (n : Nat) : Nat → BitString → Nat
  | 0,_ => 1
  | count + 1,input =>
    1 + (SourceNativeTerm.fuel input n +
      match selected input n with
      | none => 1
      | some _ => fuel n count (remaining input))

theorem block_exec {n : Nat} (count : Nat) (input : BitString) (a : Affine n) :
    Exec block (state input a count true) (fuel n count input) (finished (scan count input a)) := by
  induction count generalizing input a with
  | zero => exact Exec.loopStop rfl
  | succ count ih =>
    have step := SourceNativeTerm.block_exec input a count
    cases chosen : selected input n with
    | none =>
      simp only [SourceNativeTerm.after,chosen] at step
      have stop : Exec block (state (remaining input) a 0 false) 1
          (state (remaining input) a 0 false) := Exec.loopStop rfl
      simpa only [block,fuel,scan,chosen,finished] using
        Exec.loopStep (source := (11 : Fin 14)) rfl step stop
    | some j =>
      simp only [SourceNativeTerm.after,chosen] at step
      have rest := ih (remaining input) (aAdd (NativeSource.coordinateForm n j) a)
      simpa only [block,fuel,scan,chosen] using
        Exec.loopStep (source := (11 : Fin 14)) rfl step rest

theorem fuel_bound_at (n count : Nat) (input : BitString) (limit : Nat)
    (size : input.length ≤ limit) :
    fuel n count input ≤ count * (15 * limit + 18 * n + 72) + 1 := by
  induction count generalizing input with
  | zero => simpa only [fuel,Nat.zero_mul,Nat.zero_add] using (Nat.le_refl 1)
  | succ count ih =>
    have step := SourceNativeTerm.fuel_bound input n
    have restSize := Nat.le_trans (remaining_bound input) size
    have rest := ih (remaining input) restSize
    have amount : (count + 1) * (15 * limit + 18 * n + 72) =
        count * (15 * limit + 18 * n + 72) + (15 * limit + 18 * n + 72) := Nat.succ_mul _ _
    cases chosen : selected input n <;> simp only [fuel,chosen] <;> rw [amount] <;> omega

theorem fuel_bound (n count : Nat) (input : BitString) :
    fuel n count input ≤ count * (15 * input.length + 18 * n + 72) + 1 :=
  fuel_bound_at n count input input.length (Nat.le_refl _)

theorem canonical_exec {c : Nat} (xs : NativeCoefficients.Coefficients c)
    (suffix : BitString) (a : Affine (2 * c)) :
    Exec block (state (encodeSeq (NativeSystemCodec.rowCodec c).encode xs ++ suffix) a xs.length true)
      (fuel (2 * c) xs.length (encodeSeq (NativeSystemCodec.rowCodec c).encode xs ++ suffix))
      (state suffix (SourceNativeEncoding.accumulate xs a) 0 true) := by
  simpa only [scan_canonical,finished] using
    block_exec xs.length (encodeSeq (NativeSystemCodec.rowCodec c).encode xs ++ suffix) a

end PNP.Concrete.ResidualReduction.SourceNativeTermsLoop
