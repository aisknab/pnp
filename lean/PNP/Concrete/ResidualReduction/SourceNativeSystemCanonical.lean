import PNP.Concrete.ResidualReduction.SourceNativeSystemGroup

/-! Exact canonical semantics for arbitrary native row groups. These folds
describe the actual per-row append routine; the loop theorems derive them from
source bytes and the strict source count. No family or coverage witness is
supplied to the executable converter. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeSystemCanonical
open PNP.Concrete PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceNativeSystemState

def linearOne {c : Nat} (xs : NativeCoefficients.Coefficients c) (s : Saved) : Saved :=
  SourceNativeSystemRows.result .linear {s with payload := SourceNativeEncoding.termsWord xs false}
def productOne {c : Nat} (entry : NativeEquations.Row c × NativeCoefficients.Coefficients c) (s : Saved) : Saved :=
  SourceNativeSystemRows.result .product {s with left := SourceNativeEncoding.affineWord (NativeSource.coordinateForm (2 * c) (NativeSource.rowIndex entry.1)),payload := SourceNativeEncoding.termsWord entry.2 true}
def linearRows {c : Nat} : List (NativeCoefficients.Coefficients c) → Saved → Saved
  | [],s => s
  | x :: xs,s => linearRows xs (linearOne x s)
def productRows {c : Nat} : List (NativeEquations.Row c × NativeCoefficients.Coefficients c) → Saved → Saved
  | [],s => s
  | x :: xs,s => productRows xs (productOne x s)

theorem linearRows_frame {c : Nat} (xs : List (NativeCoefficients.Coefficients c))
    (s : Saved) (input pending : BitString) :
    linearRows xs {s with stream := input,pending := pending} =
      {linearRows xs s with stream := input,pending := pending} := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (linearOne x s)
theorem productRows_frame {c : Nat}
    (xs : List (NativeEquations.Row c × NativeCoefficients.Coefficients c))
    (s : Saved) (input pending : BitString) :
    productRows xs {s with stream := input,pending := pending} =
      {productRows xs s with stream := input,pending := pending} := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (productOne x s)

theorem linear_loop {c : Nat} (xs : List (NativeCoefficients.Coefficients c))
    (suffix : BitString) (s : Saved)
    (stream : s.stream = encodeSeq (NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix)
    (pending : s.pending = List.replicate xs.length true) (valid : s.active = [true]) :
    SourceNativeSystemLoop.result xs.length (2 * c) .zero s =
      {linearRows xs s with stream := suffix,pending := []} := by
  induction xs generalizing s with
  | nil =>
    simp only [encodeSeq,List.nil_append] at stream
    simp only [List.length_nil,List.replicate_zero] at pending
    simp only [List.length_nil,SourceNativeSystemLoop.result,linearRows]
    rw [← stream,← pending]
  | cons x xs ih =>
    let rest := encodeSeq (NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix
    let next := {linearOne x s with stream := rest,pending := List.replicate xs.length true}
    have input : s.stream = (NativeSystemCodec.coefficientsCodec c).encode x ++ rest := by
      simpa only [encodeSeq,List.append_assoc,rest] using stream
    have row : SourceNativeSystemRow.result s.stream (2 * c) .zero s =
        {linearOne x s with stream := rest} := by
      rw [input]
      exact SourceNativeSystemRow.canonical_linear_result x rest false s valid
    have nonempty : (SourceNativeSystemRow.result s.stream (2 * c) .zero s).pending ≠ [] := by
      rw [row]
      change s.pending ≠ []
      rw [pending,List.length_cons,List.replicate_succ]
      exact List.cons_ne_nil _ _
    have step : SourceNativeSystemLoop.after (2 * c) .zero s = next := by
      unfold SourceNativeSystemLoop.after
      rw [row]
      change {linearOne x s with stream := rest,pending := s.pending.tail} = next
      rw [pending,List.length_cons,List.replicate_succ,List.tail_cons]
    have nextValid : next.active = [true] := valid
    have checked := ih next rfl rfl nextValid
    simp only [List.length_cons,SourceNativeSystemLoop.result,nonempty,↓reduceIte]
    rw [step,checked]
    simp only [next,linearRows_frame,linearRows]

theorem product_loop {c : Nat}
    (xs : List (NativeEquations.Row c × NativeCoefficients.Coefficients c))
    (suffix : BitString) (s : Saved)
    (stream : s.stream = encodeSeq (NativeSystemCodec.entryCodec c).encode xs ++ suffix)
    (pending : s.pending = List.replicate xs.length true) (valid : s.active = [true]) :
    SourceNativeSystemLoop.result xs.length (2 * c) .product s =
      {productRows xs s with stream := suffix,pending := []} := by
  induction xs generalizing s with
  | nil =>
    simp only [encodeSeq,List.nil_append] at stream
    simp only [List.length_nil,List.replicate_zero] at pending
    simp only [List.length_nil,SourceNativeSystemLoop.result,productRows]
    rw [← stream,← pending]
  | cons x xs ih =>
    let rest := encodeSeq (NativeSystemCodec.entryCodec c).encode xs ++ suffix
    let next := {productOne x s with stream := rest,pending := List.replicate xs.length true}
    have input : s.stream = (NativeSystemCodec.entryCodec c).encode x ++ rest := by
      simpa only [encodeSeq,List.append_assoc,rest] using stream
    have row : SourceNativeSystemRow.result s.stream (2 * c) .product s =
        {productOne x s with stream := rest} := by
      rw [input]
      exact SourceNativeSystemRow.canonical_product_result x rest s valid
    have nonempty : (SourceNativeSystemRow.result s.stream (2 * c) .product s).pending ≠ [] := by
      rw [row]
      change s.pending ≠ []
      rw [pending,List.length_cons,List.replicate_succ]
      exact List.cons_ne_nil _ _
    have step : SourceNativeSystemLoop.after (2 * c) .product s = next := by
      unfold SourceNativeSystemLoop.after
      rw [row]
      change {productOne x s with stream := rest,pending := s.pending.tail} = next
      rw [pending,List.length_cons,List.replicate_succ,List.tail_cons]
    have nextValid : next.active = [true] := valid
    have checked := ih next rfl rfl nextValid
    simp only [List.length_cons,SourceNativeSystemLoop.result,nonempty,↓reduceIte]
    rw [step,checked]
    simp only [next,productRows_frame,productRows]

theorem linear_group {c : Nat} (xs : List (NativeCoefficients.Coefficients c))
    (suffix : BitString) (s : Saved) (valid : s.active = [true]) :
    SourceNativeSystemGroup.result
        ((listCodec (NativeSystemCodec.coefficientsCodec c)).encode xs ++ suffix) (2 * c) .zero s =
      {linearRows xs s with stream := suffix,pending := []} := by
  change SourceNativeSystemGroup.result
    ((natural xs.length ++ encodeSeq (NativeSystemCodec.coefficientsCodec c).encode xs) ++ suffix)
    (2 * c) .zero s = _
  rw [List.append_assoc]
  simp only [SourceNativeSystemGroup.result,MatrixStrictHeader.scan_canonical,↓reduceIte]
  rw [linear_loop xs suffix (SourceNativeSystemGroup.prepared
    (encodeSeq (NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix) xs.length s) rfl rfl valid]
  simp only [SourceNativeSystemGroup.prepared,linearRows_frame]

theorem product_group {c : Nat}
    (xs : List (NativeEquations.Row c × NativeCoefficients.Coefficients c))
    (suffix : BitString) (s : Saved) (valid : s.active = [true]) :
    SourceNativeSystemGroup.result
        ((listCodec (NativeSystemCodec.entryCodec c)).encode xs ++ suffix) (2 * c) .product s =
      {productRows xs s with stream := suffix,pending := []} := by
  change SourceNativeSystemGroup.result
    ((natural xs.length ++ encodeSeq (NativeSystemCodec.entryCodec c).encode xs) ++ suffix)
    (2 * c) .product s = _
  rw [List.append_assoc]
  simp only [SourceNativeSystemGroup.result,MatrixStrictHeader.scan_canonical,↓reduceIte]
  rw [product_loop xs suffix (SourceNativeSystemGroup.prepared
    (encodeSeq (NativeSystemCodec.entryCodec c).encode xs ++ suffix) xs.length s) rfl rfl valid]
  simp only [SourceNativeSystemGroup.prepared,productRows_frame]

theorem linearRows_dimension {c : Nat} (xs : List (NativeCoefficients.Coefficients c)) (s : Saved) :
    (linearRows xs s).dimension = s.dimension := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (linearOne x s)
theorem linearRows_constant {c : Nat} (xs : List (NativeCoefficients.Coefficients c)) (s : Saved) :
    (linearRows xs s).constant = s.constant := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (linearOne x s)
theorem linearRows_active {c : Nat} (xs : List (NativeCoefficients.Coefficients c)) (s : Saved) :
    (linearRows xs s).active = s.active := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (linearOne x s)
theorem linearRows_products {c : Nat} (xs : List (NativeCoefficients.Coefficients c)) (s : Saved) :
    (linearRows xs s).products = s.products := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (linearOne x s)

theorem productRows_dimension {c : Nat}
    (xs : List (NativeEquations.Row c × NativeCoefficients.Coefficients c)) (s : Saved) :
    (productRows xs s).dimension = s.dimension := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (productOne x s)
theorem productRows_constant {c : Nat}
    (xs : List (NativeEquations.Row c × NativeCoefficients.Coefficients c)) (s : Saved) :
    (productRows xs s).constant = s.constant := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (productOne x s)
theorem productRows_active {c : Nat}
    (xs : List (NativeEquations.Row c × NativeCoefficients.Coefficients c)) (s : Saved) :
    (productRows xs s).active = s.active := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (productOne x s)
theorem productRows_rows {c : Nat}
    (xs : List (NativeEquations.Row c × NativeCoefficients.Coefficients c)) (s : Saved) :
    (productRows xs s).rows = s.rows := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (productOne x s)

theorem counter_push (count : Nat) (word : BitString) :
    List.replicate count true ++ true :: word = List.replicate (count + 1) true ++ word := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons true) ih

theorem linearRows_total {c : Nat} (xs : List (NativeCoefficients.Coefficients c)) (s : Saved) :
    (linearRows xs s).total = List.replicate xs.length true ++ s.total := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    change (linearRows xs (linearOne x s)).total = _
    rw [ih]
    exact counter_push xs.length s.total
theorem productRows_total {c : Nat}
    (xs : List (NativeEquations.Row c × NativeCoefficients.Coefficients c)) (s : Saved) :
    (productRows xs s).total = List.replicate xs.length true ++ s.total := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    change (productRows xs (productOne x s)).total = _
    rw [ih]
    exact counter_push xs.length s.total

theorem linearOne_rows {c : Nat} (x : NativeCoefficients.Coefficients c) (s : Saved)
    (constant : s.constant = SourceNativeEncoding.affineWord (aConst (2 * c) true)) :
    (linearOne x s).rows = (SourceNativeEncoding.zeroRow x).reverse ++ s.rows := by
  change (false :: (SourceNativeEncoding.termsWord x false ++ s.constant)).reverse ++ s.rows = _
  rw [constant,SourceNativeEncoding.constant_word]
  rfl

theorem linearRows_rows {c : Nat} (xs : List (NativeCoefficients.Coefficients c)) (s : Saved)
    (constant : s.constant = SourceNativeEncoding.affineWord (aConst (2 * c) true)) :
    (linearRows xs s).rows = (encodeSeq SourceNativeEncoding.zeroRow xs).reverse ++ s.rows := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    change (linearRows xs (linearOne x s)).rows = _
    rw [ih (linearOne x s) constant,linearOne_rows x s constant]
    simp only [encodeSeq,List.reverse_append,List.append_assoc]

theorem productRows_products {c : Nat}
    (xs : List (NativeEquations.Row c × NativeCoefficients.Coefficients c)) (s : Saved) :
    (productRows xs s).products = (encodeSeq SourceNativeEncoding.productRow xs).reverse ++ s.products := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    change (productRows xs (productOne x s)).products = _
    rw [ih]
    change (encodeSeq SourceNativeEncoding.productRow xs).reverse ++
      ((SourceNativeEncoding.productRow x).reverse ++ s.products) = _
    simp only [encodeSeq,List.reverse_append,List.append_assoc]

end PNP.Concrete.ResidualReduction.SourceNativeSystemCanonical
