import PNP.Concrete.ResidualReduction.SourceNativeSystemBody

/-! Closed system parser from the actual input alone. The dimension header
initializes the protected frame, then the complete body readers build both row
buffers and the row counter. Generic register-growth bounds retain a polynomial
bound for every final field, including malformed and partially consumed input. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeSystemParse
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceNativeSystemState
open PNP.Concrete.ResidualReduction.SourceNativeSystemCanonical

def result (input : BitString) : Saved :=
  let h := MatrixStrictHeader.scan input
  if h.terminated then SourceNativeSystemBody.result h.rest (2 * h.count) (SourceNativeSystemHeader.data h.rest h.count)
  else {emptySaved with stream := h.rest}
def dispatch : Block 24 := .branch Field.active.slot .skip .skip SourceNativeSystemBody.block
def block : Block 24 := .seq SourceNativeSystemHeader.block dispatch
def fuel (input : BitString) : Nat :=
  let h := MatrixStrictHeader.scan input
  SourceNativeSystemHeader.fuel input +
    (if h.terminated then 1 + SourceNativeSystemBody.fuel h.rest (2 * h.count) (SourceNativeSystemHeader.data h.rest h.count) else 2)
def budget (L : Nat) : Nat :=
  2 * (L * (51 * (L * L) + 151 * L + 179)) + 51 * (L * L) + 180 * L + 298

theorem block_exec (input : BitString) :
    Exec block (initial input) (fuel input) (work (result input).stream [] (result input)) := by
  have first := SourceNativeSystemHeader.block_exec input
  cases flag : (MatrixStrictHeader.scan input).terminated with
  | false =>
    let saved := {emptySaved with stream := (MatrixStrictHeader.scan input).rest}
    have last : Exec dispatch (work saved.stream [] saved) 2 (work saved.stream [] saved) :=
      Exec.empty rfl (Exec.skip _)
    simp only [SourceNativeSystemHeader.result,flag,Bool.false_eq_true,↓reduceIte] at first
    simpa only [block,result,fuel,flag,Bool.false_eq_true,↓reduceIte,saved] using Exec.seq first last
  | true =>
    let h := MatrixStrictHeader.scan input
    let saved := SourceNativeSystemHeader.data h.rest h.count
    have body := SourceNativeSystemBody.block_exec h.rest (2 * h.count) saved rfl
    have last : Exec dispatch (work h.rest [] saved)
        (1 + SourceNativeSystemBody.fuel h.rest (2 * h.count) saved)
        (work (SourceNativeSystemBody.result h.rest (2 * h.count) saved).stream []
          (SourceNativeSystemBody.result h.rest (2 * h.count) saved)) := Exec.one rfl body
    simp only [SourceNativeSystemHeader.result,flag,↓reduceIte] at first
    simpa only [block,result,fuel,flag,↓reduceIte,h,saved] using Exec.seq first last

theorem fuel_bound (input : BitString) : fuel input ≤ budget input.length := by
  have header := SourceNativeSystemHeader.fuel_bound input
  have counts := MatrixStrictHeader.scan_size input
  have size : (MatrixStrictHeader.scan input).rest.length ≤ input.length := by omega
  have dimension : 2 * (MatrixStrictHeader.scan input).count ≤ 2 * input.length := by omega
  have constant : (SourceNativeSystemHeader.data (MatrixStrictHeader.scan input).rest
      (MatrixStrictHeader.scan input).count).constant.length ≤ 2 * (MatrixStrictHeader.scan input).count + 1 :=
    Nat.le_of_eq (SourceEncoding.affine_length _)
  have body := SourceNativeSystemBody.polynomial_bound (MatrixStrictHeader.scan input).rest
    (2 * (MatrixStrictHeader.scan input).count) input.length
    (SourceNativeSystemHeader.data (MatrixStrictHeader.scan input).rest (MatrixStrictHeader.scan input).count)
    size dimension constant
  unfold fuel budget
  dsimp only
  split <;> omega

def program : Program 24 := block.program 0 8
private theorem initial_eq (input : BitString) :
    BitRegister.initial program input = ⟨.running 0,SourceNativeSystemState.initial input⟩ := rfl

theorem result_bounded (input : BitString) :
    (work (result input).stream [] (result input)).Bounded (input.length + (fuel input + 1)) := by
  have run : BitRegister.run program (fuel input + 1) (BitRegister.initial program input) =
      ⟨.accepted,work (result input).stream [] (result input)⟩ := by
    rw [initial_eq]
    exact (block_exec input).program_run 0 8
  have bound := BitRegister.run_bounded program (fuel input + 1) (BitRegister.initial program input)
    (BitRegister.initial_bounded program input)
  rw [run] at bound
  exact bound

theorem field_bound (input : BitString) (field : Field) :
    (field.word (result input)).length ≤ input.length + budget input.length + 1 := by
  have bound := Store.get_length_le (work (result input).stream [] (result input)) field.slot (result_bounded input)
  rw [work,withCore,field_get] at bound
  have cost := fuel_bound input
  omega

def canonical {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString) : Saved :=
  SourceNativeSystemBody.canonical D suffix (SourceNativeSystemHeader.data ((NativeSystemCodec.systemCodec c).encode D ++ suffix) c)

theorem canonical_result {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString) :
    result (natural c ++ ((NativeSystemCodec.systemCodec c).encode D ++ suffix)) = canonical D suffix := by
  simp only [result,MatrixStrictHeader.scan_canonical,↓reduceIte]
  exact SourceNativeSystemBody.canonical_result D suffix _ rfl

theorem canonical_dimension {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString) :
    (canonical D suffix).dimension = List.replicate (2 * c) true := by
  simp only [canonical,SourceNativeSystemBody.canonical,SourceNativeSystemBody.canonicalSecond,
    linearRows_dimension,productRows_dimension]
  rfl
theorem canonical_stream {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString) :
    (canonical D suffix).stream = suffix := rfl
theorem canonical_active {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString) :
    (canonical D suffix).active = [true] := SourceNativeSystemBody.canonical_active D suffix _
private theorem counter_join (left right : Nat) :
    List.replicate left true ++ List.replicate right true = List.replicate (left + right) true := by
  induction left with
  | zero => simp only [List.replicate_zero,List.nil_append,Nat.zero_add]
  | succ left ih => simp only [List.replicate_succ,List.cons_append,Nat.succ_add,ih]

theorem canonical_total {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString) :
    (canonical D suffix).total = List.replicate (1 + D.e.length + D.a.length) true := by
  simp only [canonical,SourceNativeSystemBody.canonical,SourceNativeSystemBody.canonicalSecond,
    linearRows_total,productRows_total]
  change List.replicate D.e.length true ++ (List.replicate D.a.length true ++ [true]) = _
  rw [counter_push D.a.length [],List.append_nil,counter_join]
  congr 1
  omega
theorem canonical_rows {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString) :
    (canonical D suffix).rows =
      (SourceNativeEncoding.oneRow D.b ++ encodeSeq SourceNativeEncoding.zeroRow D.e).reverse := by
  let initial := SourceNativeSystemHeader.data ((NativeSystemCodec.systemCodec c).encode D ++ suffix) c
  have constant : (SourceNativeSystemBody.canonicalSecond D suffix initial).constant =
      SourceNativeEncoding.affineWord (aConst (2 * c) true) :=
    productRows_constant D.a (SourceNativeSystemBody.canonicalFirst D suffix initial)
  change (linearRows D.e (SourceNativeSystemBody.canonicalSecond D suffix initial)).rows = _
  rw [linearRows_rows D.e _ constant]
  simp only [SourceNativeSystemBody.canonicalSecond,productRows_rows]
  change (encodeSeq SourceNativeEncoding.zeroRow D.e).reverse ++
    ((false :: (SourceNativeEncoding.termsWord D.b true ++ SourceNativeEncoding.affineWord (aConst (2 * c) true))).reverse ++ []) = _
  rw [List.append_nil,SourceNativeEncoding.constant_word,List.reverse_append]
  rfl
theorem canonical_products {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString) :
    (canonical D suffix).products = (encodeSeq SourceNativeEncoding.productRow D.a).reverse := by
  simp only [canonical,SourceNativeSystemBody.canonical,SourceNativeSystemBody.canonicalSecond,
    linearRows_products,productRows_products]
  exact List.append_nil _

theorem canonical_exec {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString) :
    Exec block (initial (natural c ++ ((NativeSystemCodec.systemCodec c).encode D ++ suffix)))
      (fuel (natural c ++ ((NativeSystemCodec.systemCodec c).encode D ++ suffix)))
      (work suffix [] (canonical D suffix)) := by
  simpa only [canonical_result,canonical_stream] using
    block_exec (natural c ++ ((NativeSystemCodec.systemCodec c).encode D ++ suffix))

end PNP.Concrete.ResidualReduction.SourceNativeSystemParse
