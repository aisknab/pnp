import PNP.Concrete.ResidualReduction.SourceNativeSystemCanonical

/-! The complete native system body: initial one-row, product group, zero group.
All three readers consume the current source and preserve the protected input
dimension. Their buffers retain the target's b/e/a order, not source b/a/e order. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeSystemBody
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceNativeSystemState
open PNP.Concrete.ResidualReduction.SourceNativeSystemCanonical

def first (input : BitString) (n : Nat) (s : Saved) : Saved :=
  SourceNativeSystemRow.result input n .one s
def second (input : BitString) (n : Nat) (s : Saved) : Saved :=
  let b := first input n s
  SourceNativeSystemGroup.result b.stream n .product b
def result (input : BitString) (n : Nat) (s : Saved) : Saved :=
  let a := second input n s
  SourceNativeSystemGroup.result a.stream n .zero a
def block : Block 24 := .seq (SourceNativeSystemRow.block .one)
  (.seq (SourceNativeSystemGroup.block .product) (SourceNativeSystemGroup.block .zero))
def fuel (input : BitString) (n : Nat) (s : Saved) : Nat :=
  SourceNativeSystemRow.fuel input n .one s +
    (SourceNativeSystemGroup.fuel (first input n s).stream n .product (first input n s) +
      SourceNativeSystemGroup.fuel (second input n s).stream n .zero (second input n s))

theorem block_exec (input : BitString) (n : Nat) (s : Saved)
    (dimension : s.dimension = List.replicate n true) :
    Exec block (work input [] s) (fuel input n s)
      (work (result input n s).stream [] (result input n s)) := by
  have b := SourceNativeSystemRow.block_exec input n .one s dimension
  have bdim : (first input n s).dimension = List.replicate n true :=
    (SourceNativeSystemRow.dimension_preserved input n .one s).trans dimension
  have a := SourceNativeSystemGroup.block_exec (first input n s).stream n .product (first input n s) bdim
  have adim : (second input n s).dimension = List.replicate n true :=
    (SourceNativeSystemGroup.dimension_preserved _ _ _ _).trans bdim
  have e := SourceNativeSystemGroup.block_exec (second input n s).stream n .zero (second input n s) adim
  exact Exec.seq b (Exec.seq a e)

theorem dimension_preserved (input : BitString) (n : Nat) (s : Saved) :
    (result input n s).dimension = s.dimension := by
  simp only [result,second,first,SourceNativeSystemGroup.dimension_preserved,SourceNativeSystemRow.dimension_preserved]
theorem constant_preserved (input : BitString) (n : Nat) (s : Saved) :
    (result input n s).constant = s.constant := by
  simp only [result,second,first,SourceNativeSystemGroup.constant_preserved,SourceNativeSystemRow.constant_preserved]
theorem pending_empty (input : BitString) (n : Nat) (s : Saved) :
    (result input n s).pending = [] := SourceNativeSystemGroup.pending_empty _ _ _ _
theorem stream_bound (input : BitString) (n : Nat) (s : Saved) :
    (result input n s).stream.length ≤ input.length :=
  Nat.le_trans (SourceNativeSystemGroup.stream_bound _ _ _ _)
    (Nat.le_trans (SourceNativeSystemGroup.stream_bound _ _ _ _) (SourceNativeSystemRow.stream_bound _ _ _ _))

theorem polynomial_bound (input : BitString) (n limit : Nat) (s : Saved)
    (size : input.length ≤ limit) (dimension : n ≤ 2 * limit)
    (constant : s.constant.length ≤ n + 1) :
    fuel input n s ≤
      2 * (limit * (51 * (limit * limit) + 151 * limit + 179)) +
        51 * (limit * limit) + 159 * limit + 235 := by
  have b := SourceNativeSystemRow.polynomial_bound input n limit .one s size dimension constant
  have bsize : (first input n s).stream.length ≤ limit :=
    Nat.le_trans (SourceNativeSystemRow.stream_bound _ _ _ _) size
  have bc : (first input n s).constant.length ≤ n + 1 := by
    rw [first,SourceNativeSystemRow.constant_preserved]
    exact constant
  have a := SourceNativeSystemGroup.polynomial_bound (first input n s).stream n limit .product
    (first input n s) bsize dimension bc
  have asize : (second input n s).stream.length ≤ limit :=
    Nat.le_trans (SourceNativeSystemGroup.stream_bound _ _ _ _) bsize
  have ac : (second input n s).constant.length ≤ n + 1 := by
    rw [second,SourceNativeSystemGroup.constant_preserved]
    exact bc
  have e := SourceNativeSystemGroup.polynomial_bound (second input n s).stream n limit .zero
    (second input n s) asize dimension ac
  unfold fuel
  omega

def canonicalFirst {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString) (s : Saved) : Saved :=
  SourceNativeSystemRows.result .linear {s with stream := (listCodec (NativeSystemCodec.entryCodec c)).encode D.a ++ ((listCodec (NativeSystemCodec.coefficientsCodec c)).encode D.e ++ suffix),payload := SourceNativeEncoding.termsWord D.b true}
def canonicalSecond {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString) (s : Saved) : Saved :=
  {productRows D.a (canonicalFirst D suffix s) with stream := (listCodec (NativeSystemCodec.coefficientsCodec c)).encode D.e ++ suffix,pending := []}
def canonical {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString) (s : Saved) : Saved :=
  {linearRows D.e (canonicalSecond D suffix s) with stream := suffix,pending := []}

theorem first_canonical {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString)
    (s : Saved) (valid : s.active = [true]) :
    first ((NativeSystemCodec.systemCodec c).encode D ++ suffix) (2 * c) s =
      canonicalFirst D suffix s := by
  change SourceNativeSystemRow.result
    (((NativeSystemCodec.coefficientsCodec c).encode D.b ++
      ((listCodec (NativeSystemCodec.entryCodec c)).encode D.a ++
        (listCodec (NativeSystemCodec.coefficientsCodec c)).encode D.e)) ++ suffix) (2 * c) .one s = _
  simp only [List.append_assoc]
  exact SourceNativeSystemRow.canonical_linear_result D.b _ true s valid

theorem second_canonical {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString)
    (s : Saved) (valid : s.active = [true]) :
    second ((NativeSystemCodec.systemCodec c).encode D ++ suffix) (2 * c) s =
      canonicalSecond D suffix s := by
  unfold second
  rw [first_canonical D suffix s valid]
  exact product_group D.a _ (canonicalFirst D suffix s) valid

theorem canonical_active {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString) (s : Saved) :
    (canonical D suffix s).active = s.active := by
  simp only [canonical,canonicalSecond,linearRows_active,productRows_active]
  rfl

theorem canonical_result {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString)
    (s : Saved) (valid : s.active = [true]) :
    result ((NativeSystemCodec.systemCodec c).encode D ++ suffix) (2 * c) s =
      canonical D suffix s := by
  unfold result
  rw [second_canonical D suffix s valid]
  have good : (canonicalSecond D suffix s).active = [true] :=
    (productRows_active D.a (canonicalFirst D suffix s)).trans valid
  exact linear_group D.e suffix (canonicalSecond D suffix s) good

theorem canonical_exec {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString)
    (s : Saved) (dimension : s.dimension = List.replicate (2 * c) true) (valid : s.active = [true]) :
    Exec block (work ((NativeSystemCodec.systemCodec c).encode D ++ suffix) [] s)
      (fuel ((NativeSystemCodec.systemCodec c).encode D ++ suffix) (2 * c) s)
      (work suffix [] (canonical D suffix s)) := by
  simpa only [canonical_result D suffix s valid,canonical] using
    block_exec ((NativeSystemCodec.systemCodec c).encode D ++ suffix) (2 * c) s dimension

end PNP.Concrete.ResidualReduction.SourceNativeSystemBody
