import PNP.Concrete.ResidualReduction.SourceNativeSystemCapture

/-! Complete coefficient-list calls inside the protected system parser. The
dimension is read from the actual outer header. The callee constructs its own
count and accumulator; its actual remaining source, validity and affine bytes
are retained before scratch is cleared. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeSystemTerms
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceNativeSystemState

def block (constant : Bool) : Block 24 :=
  .seq (load .dimension 9)
    (.seq (use14 (SourceNativeTermsInput.block constant)) (SourceNativeSystemCapture.block .payload))
def result (input : BitString) (n : Nat) (constant : Bool) (s : Saved) : Saved :=
  SourceNativeSystemCapture.captured .payload (SourceNativeTermsInput.result input n constant) s
def fuel (input : BitString) (n : Nat) (constant : Bool) : Nat :=
  1 + (SourceNativeTermsInput.fuel input n +
    SourceNativeSystemCapture.fuel (SourceNativeTermsInput.result input n constant))

theorem prepare_exec (input : BitString) (n : Nat) (s : Saved)
    (dimension : s.dimension = List.replicate n true) :
    Exec (load .dimension 9) (work input [] s) 1 (full (SourceNativeTermsInput.initial input n) s) := by
  have checked := load_exec .dimension
    (Frame.join (SourceScalarState.work input).store (Store.empty 5)) s 9
  have setup : (Frame.join (SourceScalarState.work input).store (Store.empty 5)).set 9
      (List.replicate n true) = SourceNativeTermsInput.initial input n := by rfl
  rw [show Field.word .dimension s = s.dimension from rfl,dimension,setup] at checked
  exact checked

theorem block_exec (input : BitString) (n : Nat) (constant : Bool) (s : Saved)
    (dimension : s.dimension = List.replicate n true) :
    Exec (block constant) (work input [] s) (fuel input n constant)
      (work (result input n constant s).stream [] (result input n constant s)) := by
  have first := prepare_exec input n s dimension
  have middle := use14_exec (SourceNativeTermsInput.block_exec input n constant) s
  have last := SourceNativeSystemCapture.block_exec .payload (SourceNativeTermsInput.result input n constant) s
  simpa only [block,fuel,result,SourceNativeSystemCapture.captured_stream] using
    Exec.seq first (Exec.seq middle last)

theorem dimension_preserved (input : BitString) (n : Nat) (constant : Bool) (s : Saved) :
    (result input n constant s).dimension = s.dimension :=
  SourceNativeSystemCapture.captured_dimension _ _ _

theorem parsed_input_bound (input : BitString) (n : Nat) (constant : Bool) :
    ((SourceNativeTermsInput.result input n constant).get 0).length ≤ input.length := by
  have header := MatrixStrictHeader.scan_size input
  have rest : (MatrixStrictHeader.scan input).rest.length ≤ input.length := by omega
  unfold SourceNativeTermsInput.result
  dsimp only
  split
  · exact Nat.le_trans
      (SourceNativeTermsSpec.scan_input_bound _ _ (aConst n constant)) rest
  · exact rest

theorem parsed_output_bound (input : BitString) (n : Nat) (constant : Bool) :
    ((SourceNativeTermsInput.result input n constant).get 8).length ≤ n + 1 := by
  unfold SourceNativeTermsInput.result
  dsimp only
  split
  · let r := SourceNativeTermsSpec.scan (MatrixStrictHeader.scan input).count
      (MatrixStrictHeader.scan input).rest (aConst n constant)
    change (if r.valid then SourceNativeEncoding.affineWord r.accumulator else []).length ≤ n + 1
    split
    · exact Nat.le_of_eq (SourceEncoding.affine_length _)
    · exact Nat.zero_le _
  · exact Nat.zero_le _

theorem stream_bound (input : BitString) (n : Nat) (constant : Bool) (s : Saved) :
    (result input n constant s).stream.length ≤ input.length := by
  simpa only [result,SourceNativeSystemCapture.captured_stream] using parsed_input_bound input n constant

theorem payload_bound (input : BitString) (n : Nat) (constant : Bool) (s : Saved) :
    (result input n constant s).payload.length ≤ n + 1 := by
  have shape : (result input n constant s).payload =
      (SourceNativeTermsInput.result input n constant).get 8 := by
    unfold result SourceNativeSystemCapture.captured
    split <;> rfl
  rw [shape]
  exact parsed_output_bound input n constant

theorem fuel_bound (input : BitString) (n : Nat) (constant : Bool) :
    fuel input n constant ≤ SourceNativeTermsInput.fuel input n + 22 := by
  have checked := SourceNativeSystemCapture.fuel_bound (SourceNativeTermsInput.result input n constant)
  unfold fuel
  omega

theorem polynomial_bound (input : BitString) (n limit : Nat) (constant : Bool)
    (size : input.length ≤ limit) (dimension : n ≤ 2 * limit) :
    fuel input n constant ≤ 51 * (limit * limit) + 90 * limit + 62 := by
  have parsed := SourceNativeTermsInput.polynomial_bound input n limit size dimension
  have wrapper := fuel_bound input n constant
  omega

theorem canonical_result {c : Nat} (xs : NativeCoefficients.Coefficients c)
    (suffix : BitString) (constant : Bool) (s : Saved) :
    result ((NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix) (2 * c) constant s =
      {s with stream := suffix,payload := SourceNativeEncoding.termsWord xs constant} := by
  rw [result,SourceNativeTermsInput.canonical_result]
  change {s with stream := suffix,payload := SourceNativeEncoding.affineWord (SourceNativeEncoding.accumulate xs (aConst (2 * c) constant))} = _
  rw [SourceNativeEncoding.accumulate_word]

theorem canonical_exec {c : Nat} (xs : NativeCoefficients.Coefficients c)
    (suffix : BitString) (constant : Bool) (s : Saved)
    (dimension : s.dimension = List.replicate (2 * c) true) :
    Exec (block constant)
      (work ((NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix) [] s)
      (fuel ((NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix) (2 * c) constant)
      (work suffix [] {s with stream := suffix,payload := SourceNativeEncoding.termsWord xs constant}) := by
  simpa only [canonical_result] using
    block_exec ((NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix) (2 * c) constant s dimension

end PNP.Concrete.ResidualReduction.SourceNativeSystemTerms
