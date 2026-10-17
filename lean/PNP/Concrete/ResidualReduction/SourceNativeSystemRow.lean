import PNP.Concrete.ResidualReduction.SourceNativeSystemRows

/-! One complete source-row step. Sparse lists and product labels are read from
the current bytes, and a row is appended only while validity remains true.
Failure cannot revive a rejected system or earn an emitted-row count. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeSystemRow
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization
open PNP.Concrete.ResidualReduction.SourceNativeSystemState

def active (s : Saved) : Bool := match s.active with | true :: _ => true | _ => false
def commit (kind : SourceNativeSystemRows.Kind) : Block 24 :=
  .branch Field.active.slot .skip .skip (SourceNativeSystemRows.block kind)
def committed (kind : SourceNativeSystemRows.Kind) (s : Saved) : Saved :=
  if active s then SourceNativeSystemRows.result kind s else s
def commitFuel (kind : SourceNativeSystemRows.Kind) (s : Saved) : Nat :=
  1 + if active s then SourceNativeSystemRows.fuel kind s else 1

theorem commit_exec (kind : SourceNativeSystemRows.Kind) (s : Saved) :
    Exec (commit kind) (work s.stream [] s) (commitFuel kind s)
      (work (committed kind s).stream [] (committed kind s)) := by
  have read : (work s.stream [] s).get Field.active.slot = s.active :=
    field_get .active _ s
  cases flag : s.active with
  | nil =>
    rw [flag] at read
    simpa only [commit,commitFuel,committed,active,flag,Bool.false_eq_true,↓reduceIte] using
      (Exec.empty read (Exec.skip (work s.stream [] s)) :
        Exec (commit kind) _ (1 + 1) _)
  | cons bit rest =>
    rw [flag] at read
    cases bit with
    | false =>
      simpa only [commit,commitFuel,committed,active,flag,Bool.false_eq_true,↓reduceIte] using
        (Exec.zero read (Exec.skip (work s.stream [] s)) :
          Exec (commit kind) _ (1 + 1) _)
    | true =>
      simpa only [commit,commitFuel,committed,active,flag,↓reduceIte,SourceNativeSystemRows.stream_preserved] using
        (Exec.one read (SourceNativeSystemRows.block_exec kind s.stream s) :
          Exec (commit kind) _ (1 + SourceNativeSystemRows.fuel kind s) _)

inductive Kind where | zero | one | product
def Kind.buffer : Kind → SourceNativeSystemRows.Kind | .zero => .linear | .one => .linear | .product => .product
def source : Kind → Block 24
  | .zero => SourceNativeSystemTerms.block false
  | .one => SourceNativeSystemTerms.block true
  | .product => .seq SourceNativeSystemLabel.block (SourceNativeSystemTerms.block true)
def sourced (input : BitString) (n : Nat) (kind : Kind) (s : Saved) : Saved :=
  match kind with
  | .zero => SourceNativeSystemTerms.result input n false s
  | .one => SourceNativeSystemTerms.result input n true s
  | .product =>
    let label := SourceNativeSystemLabel.result input n s
    SourceNativeSystemTerms.result label.stream n true label
def sourceFuel (input : BitString) (n : Nat) (kind : Kind) (s : Saved) : Nat :=
  match kind with
  | .zero => SourceNativeSystemTerms.fuel input n false
  | .one => SourceNativeSystemTerms.fuel input n true
  | .product => SourceNativeSystemLabel.fuel input n +
      SourceNativeSystemTerms.fuel (SourceNativeSystemLabel.result input n s).stream n true

theorem source_exec (input : BitString) (n : Nat) (kind : Kind) (s : Saved)
    (dimension : s.dimension = List.replicate n true) :
    Exec (source kind) (work input [] s) (sourceFuel input n kind s)
      (work (sourced input n kind s).stream [] (sourced input n kind s)) := by
  cases kind with
  | zero => exact SourceNativeSystemTerms.block_exec input n false s dimension
  | one => exact SourceNativeSystemTerms.block_exec input n true s dimension
  | product =>
    have preserved : (SourceNativeSystemLabel.result input n s).dimension = List.replicate n true :=
      (SourceNativeSystemLabel.dimension_preserved input n s).trans dimension
    exact Exec.seq (SourceNativeSystemLabel.block_exec input n s dimension)
      (SourceNativeSystemTerms.block_exec _ n true _ preserved)

def block (kind : Kind) : Block 24 := .seq (source kind) (commit kind.buffer)
def result (input : BitString) (n : Nat) (kind : Kind) (s : Saved) : Saved :=
  committed kind.buffer (sourced input n kind s)
def fuel (input : BitString) (n : Nat) (kind : Kind) (s : Saved) : Nat :=
  sourceFuel input n kind s + commitFuel kind.buffer (sourced input n kind s)

theorem block_exec (input : BitString) (n : Nat) (kind : Kind) (s : Saved)
    (dimension : s.dimension = List.replicate n true) :
    Exec (block kind) (work input [] s) (fuel input n kind s)
      (work (result input n kind s).stream [] (result input n kind s)) :=
  Exec.seq (source_exec input n kind s dimension) (commit_exec kind.buffer (sourced input n kind s))

theorem terms_constant (input : BitString) (n : Nat) (constant : Bool) (s : Saved) :
    (SourceNativeSystemTerms.result input n constant s).constant = s.constant := by
  unfold SourceNativeSystemTerms.result SourceNativeSystemCapture.captured
  split <;> rfl
theorem terms_left (input : BitString) (n : Nat) (constant : Bool) (s : Saved) :
    (SourceNativeSystemTerms.result input n constant s).left = s.left := by
  unfold SourceNativeSystemTerms.result SourceNativeSystemCapture.captured
  split <;> rfl
theorem label_constant (input : BitString) (n : Nat) (s : Saved) :
    (SourceNativeSystemLabel.result input n s).constant = s.constant := by
  unfold SourceNativeSystemLabel.result SourceNativeSystemCapture.captured
  split <;> rfl

theorem sourced_dimension (input : BitString) (n : Nat) (kind : Kind) (s : Saved) :
    (sourced input n kind s).dimension = s.dimension := by
  cases kind <;> simp only [sourced,SourceNativeSystemTerms.dimension_preserved,
    SourceNativeSystemLabel.dimension_preserved]
theorem sourced_constant (input : BitString) (n : Nat) (kind : Kind) (s : Saved) :
    (sourced input n kind s).constant = s.constant := by
  cases kind <;> simp only [sourced,terms_constant,label_constant]
theorem sourced_stream_bound (input : BitString) (n : Nat) (kind : Kind) (s : Saved) :
    (sourced input n kind s).stream.length ≤ input.length := by
  cases kind with
  | zero => exact SourceNativeSystemTerms.stream_bound input n false s
  | one => exact SourceNativeSystemTerms.stream_bound input n true s
  | product =>
    exact Nat.le_trans (SourceNativeSystemTerms.stream_bound _ n true _)
      (SourceNativeSystemLabel.stream_bound input n s)

theorem sourced_left_bound (input : BitString) (n : Nat) (kind : Kind) (s : Saved) :
    (kind.buffer.left.word (sourced input n kind s)).length ≤ n + 1 := by
  cases kind with
  | zero => exact SourceNativeSystemTerms.payload_bound input n false s
  | one => exact SourceNativeSystemTerms.payload_bound input n true s
  | product =>
    change (SourceNativeSystemTerms.result _ n true _).left.length ≤ n + 1
    rw [terms_left]
    exact SourceNativeSystemLabel.left_bound input n s
theorem sourced_right_bound (input : BitString) (n : Nat) (kind : Kind) (s : Saved)
    (constant : s.constant.length ≤ n + 1) :
    (kind.buffer.right.word (sourced input n kind s)).length ≤ n + 1 := by
  cases kind with
  | zero => simpa only [Kind.buffer,SourceNativeSystemRows.Kind.right,Field.word,sourced,terms_constant] using constant
  | one => simpa only [Kind.buffer,SourceNativeSystemRows.Kind.right,Field.word,sourced,terms_constant] using constant
  | product => exact SourceNativeSystemTerms.payload_bound _ n true _

theorem dimension_preserved (input : BitString) (n : Nat) (kind : Kind) (s : Saved) :
    (result input n kind s).dimension = s.dimension := by
  unfold result committed
  split
  · exact (SourceNativeSystemRows.dimension_preserved _ _).trans (sourced_dimension input n kind s)
  · exact sourced_dimension input n kind s

theorem constant_preserved (input : BitString) (n : Nat) (kind : Kind) (s : Saved) :
    (result input n kind s).constant = s.constant := by
  have saved : (SourceNativeSystemRows.result kind.buffer (sourced input n kind s)).constant =
      (sourced input n kind s).constant := by cases kind <;> rfl
  unfold result committed
  split
  · exact saved.trans (sourced_constant input n kind s)
  · exact sourced_constant input n kind s

theorem stream_bound (input : BitString) (n : Nat) (kind : Kind) (s : Saved) :
    (result input n kind s).stream.length ≤ input.length := by
  unfold result committed
  split
  · rw [SourceNativeSystemRows.stream_preserved]
    exact sourced_stream_bound input n kind s
  · exact sourced_stream_bound input n kind s

theorem sourceFuel_bound (input : BitString) (n limit : Nat) (kind : Kind) (s : Saved)
    (size : input.length ≤ limit) (dimension : n ≤ 2 * limit) :
    sourceFuel input n kind s ≤ 51 * (limit * limit) + 119 * limit + 122 := by
  cases kind with
  | zero =>
    have checked := SourceNativeSystemTerms.polynomial_bound input n limit false size dimension
    change SourceNativeSystemTerms.fuel input n false ≤ _
    omega
  | one =>
    have checked := SourceNativeSystemTerms.polynomial_bound input n limit true size dimension
    change SourceNativeSystemTerms.fuel input n true ≤ _
    omega
  | product =>
    have label := SourceNativeSystemLabel.polynomial_bound input n limit size dimension
    have rest := Nat.le_trans (SourceNativeSystemLabel.stream_bound input n s) size
    have terms := SourceNativeSystemTerms.polynomial_bound _ n limit true rest dimension
    change SourceNativeSystemLabel.fuel input n + SourceNativeSystemTerms.fuel _ n true ≤ _
    omega

theorem polynomial_bound (input : BitString) (n limit : Nat) (kind : Kind) (s : Saved)
    (size : input.length ≤ limit) (dimension : n ≤ 2 * limit)
    (constant : s.constant.length ≤ n + 1) :
    fuel input n kind s ≤ 51 * (limit * limit) + 151 * limit + 177 := by
  have parsed := sourceFuel_bound input n limit kind s size dimension
  have appended := SourceNativeSystemRows.fuel_bound kind.buffer (sourced input n kind s) n
    (sourced_left_bound input n kind s) (sourced_right_bound input n kind s constant)
  unfold fuel commitFuel
  split <;> omega

theorem canonical_linear_result {c : Nat} (xs : NativeCoefficients.Coefficients c)
    (suffix : BitString) (constant : Bool) (s : Saved) (valid : s.active = [true]) :
    result ((NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix) (2 * c)
        (if constant then .one else .zero) s =
      SourceNativeSystemRows.result .linear {s with stream := suffix,payload := SourceNativeEncoding.termsWord xs constant} := by
  cases constant <;> simp only [Bool.false_eq_true,↓reduceIte,result,sourced,
    SourceNativeSystemTerms.canonical_result,committed,active,valid,Kind.buffer]

theorem canonical_product_result {c : Nat}
    (entry : NativeEquations.Row c × NativeCoefficients.Coefficients c)
    (suffix : BitString) (s : Saved) (valid : s.active = [true]) :
    result ((NativeSystemCodec.entryCodec c).encode entry ++ suffix) (2 * c) .product s =
      SourceNativeSystemRows.result .product {s with stream := suffix,left := SourceNativeEncoding.affineWord (NativeSource.coordinateForm (2 * c) (NativeSource.rowIndex entry.1)),payload := SourceNativeEncoding.termsWord entry.2 true} := by
  change result (((NativeSystemCodec.rowCodec c).encode entry.1 ++
    (NativeSystemCodec.coefficientsCodec c).encode entry.2) ++ suffix) (2 * c) .product s = _
  rw [List.append_assoc]
  simp only [result,sourced,SourceNativeSystemLabel.canonical_result,
    SourceNativeSystemTerms.canonical_result,committed,active,valid,Kind.buffer,↓reduceIte]

theorem canonical_linear_exec {c : Nat} (xs : NativeCoefficients.Coefficients c)
    (suffix : BitString) (constant : Bool) (s : Saved)
    (dimension : s.dimension = List.replicate (2 * c) true) (valid : s.active = [true]) :
    Exec (block (if constant then .one else .zero))
      (work ((NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix) [] s)
      (fuel ((NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix) (2 * c)
        (if constant then .one else .zero) s)
      (work suffix [] (SourceNativeSystemRows.result .linear {s with stream := suffix,payload := SourceNativeEncoding.termsWord xs constant})) := by
  simpa only [canonical_linear_result xs suffix constant s valid,SourceNativeSystemRows.stream_preserved] using
    block_exec ((NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix) (2 * c)
      (if constant then .one else .zero) s dimension

theorem canonical_product_exec {c : Nat}
    (entry : NativeEquations.Row c × NativeCoefficients.Coefficients c)
    (suffix : BitString) (s : Saved)
    (dimension : s.dimension = List.replicate (2 * c) true) (valid : s.active = [true]) :
    Exec (block .product) (work ((NativeSystemCodec.entryCodec c).encode entry ++ suffix) [] s)
      (fuel ((NativeSystemCodec.entryCodec c).encode entry ++ suffix) (2 * c) .product s)
      (work suffix [] (SourceNativeSystemRows.result .product {s with stream := suffix,left := SourceNativeEncoding.affineWord (NativeSource.coordinateForm (2 * c) (NativeSource.rowIndex entry.1)),payload := SourceNativeEncoding.termsWord entry.2 true})) := by
  simpa only [canonical_product_result entry suffix s valid,SourceNativeSystemRows.stream_preserved] using
    block_exec ((NativeSystemCodec.entryCodec c).encode entry ++ suffix) (2 * c) .product s dimension

end PNP.Concrete.ResidualReduction.SourceNativeSystemRow
