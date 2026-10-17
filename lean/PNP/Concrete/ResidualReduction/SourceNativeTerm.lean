import PNP.Concrete.ResidualReduction.SourceNativeTermsAdd

/-! One complete sparse-list iteration. It obtains the coordinate from the
actual source bytes, accumulates its affine word, and consumes one pending term.
A malformed or out-of-range label clears both the pending count and validity. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeTerm
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceNativeTermsSpec
open PNP.Concrete.ResidualReduction.SourceNativeTermsState

def dispatch : Block 14 := .branch 4 reject SourceNativeTermsAdd.block SourceNativeTermsAdd.block
def block : Block 14 := .seq (label SourceNativeLabel.block) (.seq retain dispatch)
def fuel (input : BitString) (n : Nat) : Nat :=
  SourceNativeLabel.fuel input n + (1 + (1 +
    match selected input n with
    | none => 13
    | some _ => SourceNativeTermsAdd.fuel n))
def after {n : Nat} (input : BitString) (a : Affine n) (count : Nat) : Store 14 :=
  match selected input n with
  | none => state (remaining input) a 0 false
  | some j => state (remaining input) (aAdd (NativeSource.coordinateForm n j) a) count true

theorem block_exec {n : Nat} (input : BitString) (a : Affine n) (count : Nat) :
    Exec block (state input a (count + 1) true) (fuel input n) (after input a count) := by
  let saved := data input a (count + 1) true
  let kept := data (remaining input) a (count + 1) true
  have reader : Exec (label SourceNativeLabel.block) (state input a (count + 1) true)
      (SourceNativeLabel.fuel input n) (full (readCore input n) saved) := by
    have checked := SourceNativeLabel.block_exec input n
    rw [label_result] at checked
    exact label_exec saved checked
  have keep : Exec retain (full (readCore input n) saved) 1 (full (readCore input n) kept) := by
    simpa only [saved,kept,data,readCore_input] using retain_exec (readCore input n) saved
  cases chosen : selected input n with
  | none =>
    have bad : Exec reject (full (readCore input n) kept) 13
        (state (remaining input) a 0 false) := by
      simpa only [kept,state,data,List.replicate_zero,Bool.false_eq_true,↓reduceIte] using reject_exec (readCore input n) kept
    have last : Exec dispatch (full (readCore input n) kept) (1 + 13)
        (state (remaining input) a 0 false) :=
      Exec.empty (readCore_none input n chosen) bad
    simpa only [block,fuel,after,chosen] using Exec.seq reader (Exec.seq keep last)
  | some j =>
    have good : Exec SourceNativeTermsAdd.block (full (readCore input n) kept)
        (SourceNativeTermsAdd.fuel n)
        (state (remaining input) (aAdd (NativeSource.coordinateForm n j) a) count true) := by
      rw [readCore_some input n j chosen]
      exact SourceNativeTermsAdd.block_exec (remaining input) (NativeSource.coordinateForm n j) a count
    have read : (full (readCore input n) kept).get 4 = [true] := by
      rw [readCore_some input n j chosen]
      rfl
    have last : Exec dispatch (full (readCore input n) kept) (1 + SourceNativeTermsAdd.fuel n)
        (state (remaining input) (aAdd (NativeSource.coordinateForm n j) a) count true) :=
      Exec.one read good
    simpa only [block,fuel,after,chosen] using Exec.seq reader (Exec.seq keep last)

theorem fuel_bound (input : BitString) (n : Nat) :
    fuel input n ≤ 15 * input.length + 18 * n + 71 := by
  have reader := SourceNativeLabel.fuel_bound input n
  unfold fuel
  cases selected input n <;> simp only [SourceNativeTermsAdd.fuel] <;> omega

end PNP.Concrete.ResidualReduction.SourceNativeTerm
