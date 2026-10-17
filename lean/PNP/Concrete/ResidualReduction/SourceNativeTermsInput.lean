import PNP.Concrete.ResidualReduction.SourceNativeTermsSeed

/-! Complete strict sparse coefficient-list conversion. Only the input stream
and the outer parser's unary dimension are present initially. The count, affine
accumulator and validity are constructed by literal instructions. The output
flag is false and output word empty on any malformed or out-of-range term. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeTermsInput
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceNativeTermsSpec
open PNP.Concrete.ResidualReduction.SourceNativeTermsState

def initial (input : BitString) (n : Nat) : Store 14 :=
  work input (SourceNativeTermsSeed.blank [] n)
def headers : Block 14 := .seq (core MatrixStrictHeader.block) retain
def headerResult (input : BitString) (n : Nat) : Store 14 :=
  let h := MatrixStrictHeader.scan input
  full (SourceNativeRowIndex.state h.rest h.count h.terminated) (SourceNativeTermsSeed.blank h.rest n)

theorem headers_exec (input : BitString) (n : Nat) :
    Exec headers (initial input n) (MatrixStrictHeader.blockFuel input + 1) (headerResult input n) := by
  let h := MatrixStrictHeader.scan input
  let saved := SourceNativeTermsSeed.blank [] n
  have first : Exec MatrixStrictHeader.block (SourceScalarState.work input).store
      (MatrixStrictHeader.blockFuel input) (SourceNativeRowIndex.state h.rest h.count h.terminated).store := by
    simpa only [h,SourceNativeRowIndex.state,SourceScalarState.work,MatrixStrictHeader.result,
      List.replicate_zero,List.append_nil] using MatrixStrictHeader.block_exec input (SourceScalarState.work [])
  have second := retain_exec (SourceNativeRowIndex.state h.rest h.count h.terminated) saved
  simpa only [headers,initial,headerResult,saved,h,SourceNativeTermsSeed.blank,
    SourceNativeRowIndex.state,work] using Exec.seq (core_exec first saved) second

def emitted {n : Nat} (r : Result n) : Store 14 :=
  full {SourceScalarState.work r.input with sign := if r.valid then [true] else [], output := if r.valid then SourceNativeEncoding.affineWord r.accumulator else []}
    (data r.input r.accumulator 0 r.valid)
def emit : Block 14 := .seq (.action (.copy 4 13))
  (.branch 13 .skip (.action (.copy 8 10)) (.action (.copy 8 10)))

theorem emit_exec {n : Nat} (r : Result n) :
    Exec emit (SourceNativeTermsLoop.finished r) 3 (emitted r) := by
  rcases r with ⟨input,a,valid⟩
  cases valid with
  | false => exact Exec.seq (.action _ _) (Exec.empty rfl (Exec.skip _))
  | true => exact Exec.seq (.action _ _) (Exec.one rfl (.action _ _))

def accepted (constant : Bool) : Block 14 :=
  .seq (SourceNativeTermsSeed.block constant) (.seq SourceNativeTermsLoop.block emit)
def acceptedFuel (input : BitString) (n count : Nat) : Nat :=
  SourceNativeTermsSeed.fuel n + (SourceNativeTermsLoop.fuel n count input + 3)

theorem accepted_exec (input : BitString) (n count : Nat) (constant : Bool) :
    Exec (accepted constant)
      (full (SourceNativeRowIndex.state input count true) (SourceNativeTermsSeed.blank input n))
      (acceptedFuel input n count) (emitted (scan count input (aConst n constant))) :=
  Exec.seq (SourceNativeTermsSeed.block_exec input n count constant)
    (Exec.seq (SourceNativeTermsLoop.block_exec count input (aConst n constant))
      (emit_exec (scan count input (aConst n constant))))

def dispatch (constant : Bool) : Block 14 := .branch 4 reject (accepted constant) (accepted constant)
def block (constant : Bool) : Block 14 := .seq headers (dispatch constant)
def fuel (input : BitString) (n : Nat) : Nat :=
  MatrixStrictHeader.blockFuel input + 1 +
    (1 + if (MatrixStrictHeader.scan input).terminated then
      acceptedFuel (MatrixStrictHeader.scan input).rest n (MatrixStrictHeader.scan input).count else 13)
def result (input : BitString) (n : Nat) (constant : Bool) : Store 14 :=
  let h := MatrixStrictHeader.scan input
  if h.terminated then emitted (scan h.count h.rest (aConst n constant))
  else work h.rest (SourceNativeTermsSeed.blank h.rest n)

theorem block_exec (input : BitString) (n : Nat) (constant : Bool) :
    Exec (block constant) (initial input n) (fuel input n) (result input n constant) := by
  have first := headers_exec input n
  cases flag : (MatrixStrictHeader.scan input).terminated with
  | false =>
    let r := SourceNativeRowIndex.state (MatrixStrictHeader.scan input).rest
      (MatrixStrictHeader.scan input).count false
    let saved := SourceNativeTermsSeed.blank (MatrixStrictHeader.scan input).rest n
    have bad : Exec reject (full r saved) 13 (work saved.stream saved) := by
      simpa only [saved,SourceNativeTermsSeed.blank] using reject_exec r saved
    have last : Exec (dispatch constant) (full r saved) (1 + 13) (work saved.stream saved) :=
      Exec.empty rfl bad
    simp only [headerResult,flag] at first
    simpa only [block,fuel,result,flag,Bool.false_eq_true,↓reduceIte,r,saved,
      SourceNativeTermsSeed.blank] using Exec.seq first last
  | true =>
    have last : Exec (dispatch constant) (headerResult input n)
        (1 + acceptedFuel (MatrixStrictHeader.scan input).rest n (MatrixStrictHeader.scan input).count)
        (emitted (scan (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest
          (aConst n constant))) := by
      simp only [headerResult,flag]
      exact Exec.one rfl (accepted_exec (MatrixStrictHeader.scan input).rest n
        (MatrixStrictHeader.scan input).count constant)
    simpa only [block,fuel,result,flag,↓reduceIte] using Exec.seq first last

theorem fuel_bound (input : BitString) (n : Nat) :
    fuel input n ≤ input.length * (15 * input.length + 18 * n + 72) + 4 * input.length + 7 * n + 40 := by
  have header := MatrixStrictHeader.blockFuel_bound input
  have counts := MatrixStrictHeader.scan_size input
  have countBound : (MatrixStrictHeader.scan input).count ≤ input.length := by omega
  have restBound : (MatrixStrictHeader.scan input).rest.length ≤ input.length := by omega
  have loop := SourceNativeTermsLoop.fuel_bound_at n (MatrixStrictHeader.scan input).count
    (MatrixStrictHeader.scan input).rest input.length restBound
  have product := Nat.mul_le_mul_right (15 * input.length + 18 * n + 72) countBound
  unfold fuel acceptedFuel SourceNativeTermsSeed.fuel
  split <;> omega

theorem polynomial_bound (input : BitString) (n limit : Nat)
    (size : input.length ≤ limit) (dimension : n ≤ 2 * limit) :
    fuel input n ≤ 51 * (limit * limit) + 90 * limit + 40 := by
  have checked := fuel_bound input n
  have width : 15 * input.length + 18 * n + 72 ≤ 51 * limit + 72 := by omega
  have product := Nat.mul_le_mul width size
  rw [Nat.mul_comm (15 * input.length + 18 * n + 72) input.length] at product
  have expanded : (51 * limit + 72) * limit = 51 * (limit * limit) + 72 * limit := by
    rw [Nat.add_mul,Nat.mul_assoc]
  rw [expanded] at product
  omega

theorem canonical_result {c : Nat} (xs : NativeCoefficients.Coefficients c)
    (suffix : BitString) (constant : Bool) :
    result ((NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix) (2 * c) constant =
      emitted ⟨suffix,SourceNativeEncoding.accumulate xs (aConst (2 * c) constant),true⟩ := by
  change result ((natural xs.length ++ encodeSeq (NativeSystemCodec.rowCodec c).encode xs) ++ suffix)
    (2 * c) constant = _
  rw [List.append_assoc]
  simp only [result,MatrixStrictHeader.scan_canonical,↓reduceIte,scan_canonical]

theorem canonical_exec {c : Nat} (xs : NativeCoefficients.Coefficients c)
    (suffix : BitString) (constant : Bool) :
    Exec (block constant)
      (initial ((NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix) (2 * c))
      (fuel ((NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix) (2 * c))
      (emitted ⟨suffix,SourceNativeEncoding.accumulate xs (aConst (2 * c) constant),true⟩) := by
  simpa only [canonical_result] using
    block_exec ((NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix) (2 * c) constant

theorem canonical_output {c : Nat} (xs : NativeCoefficients.Coefficients c)
    (suffix : BitString) (constant : Bool) :
    (result ((NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix) (2 * c) constant).get 8 =
      SourceNativeEncoding.termsWord xs constant := by
  rw [canonical_result]
  exact SourceNativeEncoding.accumulate_word xs constant

theorem canonical_flag {c : Nat} (xs : NativeCoefficients.Coefficients c)
    (suffix : BitString) (constant : Bool) :
    (result ((NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix) (2 * c) constant).get 4 = [true] := by
  rw [canonical_result]
  rfl

end PNP.Concrete.ResidualReduction.SourceNativeTermsInput
