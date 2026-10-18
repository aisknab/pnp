import PNP.Concrete.ResidualReduction.SourceNativeSystemState

/-! Strict native system header and internally constructed dense dimension.
The protected dimension is obtained by doubling the actual unary source header.
The constant affine word is produced by the verified literal initializer, not
supplied as startup data. Malformed headers leave the system inactive. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeSystemHeader
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceNativeSystemState

def headers : Block 24 := .seq (core MatrixStrictHeader.block) (save .stream 0)
def headerResult (input : BitString) (s : Saved) : Store 24 :=
  let h := MatrixStrictHeader.scan input
  withCore (SourceNativeRowIndex.state h.rest h.count h.terminated) {s with stream := h.rest}
theorem headers_exec (input : BitString) (s : Saved) :
    Exec headers (work input [] s) (MatrixStrictHeader.blockFuel input + 1) (headerResult input s) := by
  let h := MatrixStrictHeader.scan input
  let r := SourceNativeRowIndex.state h.rest h.count h.terminated
  have reader : Exec MatrixStrictHeader.block (SourceScalarState.work input).store
      (MatrixStrictHeader.blockFuel input) r.store := by
    simpa only [r,h,SourceNativeRowIndex.state,SourceScalarState.work,MatrixStrictHeader.result,
      List.replicate_zero,List.append_nil] using MatrixStrictHeader.block_exec input (SourceScalarState.work [])
  have capture : Exec (save .stream 0) (withCore r s) 1 (withCore r {s with stream := h.rest}) :=
    save_exec .stream (Frame.join r.store (Store.empty 5)) s 0
  exact Exec.seq (core_exec reader s) capture

def prepared (input : BitString) (c : Nat) : Saved :=
  {emptySaved with dimension := List.replicate (2 * c) true,stream := input}
def data (input : BitString) (c : Nat) : Saved :=
  {prepared input c with constant := SourceNativeEncoding.affineWord (aConst (2 * c) true),active := [true]}
def prepare : Block 24 := .seq (load .dimension 9)
  (.seq (.action (.clear 2)) (.action (.copy 12 0)))
def finish : Block 24 := .seq (save .constant 10) (.seq (push .active true) clean)
def accepted : Block 24 := .seq (core SourceNativeRowIndex.double)
  (.seq (save .dimension 2) (.seq prepare (.seq (use14 (SourceNativeTermsSeed.block true)) finish)))
def acceptedFuel (c : Nat) : Nat := 17 * c + 51

theorem accepted_exec (input : BitString) (c : Nat) :
    Exec accepted (withCore (SourceNativeRowIndex.state input c true) {emptySaved with stream := input})
      (acceptedFuel c) (work input [] (data input c)) := by
  let start := {emptySaved with stream := input}
  let saved := prepared input c
  let doubled := SourceNativeRowIndex.doubled input c
  let ready := SourceNativeTermsState.full (SourceNativeRowIndex.state input 0 true)
    (SourceNativeTermsSeed.blank input (2 * c))
  let made := SourceNativeTermsState.state input (aConst (2 * c) true) 0 true
  let recorded := {saved with constant := SourceNativeEncoding.affineWord (aConst (2 * c) true)}
  have first := core_exec (SourceNativeRowIndex.double_exec input c) start
  have dimension : Exec (save .dimension 2) (withCore doubled start) 1 (withCore doubled saved) :=
    save_exec .dimension (Frame.join doubled.store (Store.empty 5)) start 2
  have setup : Exec prepare (withCore doubled saved) 3 (full ready saved) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have construct := use14_exec (SourceNativeTermsSeed.block_exec input (2 * c) 0 true) saved
  have record : Exec (save .constant 10) (full made saved) 1 (full made recorded) :=
    save_exec .constant made saved 10
  have activate : Exec (push .active true) (full made recorded) 1 (full made (data input c)) :=
    push_exec .active made recorded true
  have cleanup : Exec clean (full made (data input c)) 16 (work input [] (data input c)) :=
    clean_exec made (data input c)
  have last : Exec finish (full made saved) 18 (work input [] (data input c)) :=
    Exec.seq record (Exec.seq activate cleanup)
  have checked := Exec.seq first (Exec.seq dimension (Exec.seq setup (Exec.seq construct last)))
  have cost : acceptedFuel c =
      (3 * c + 4) + (1 + (3 + (SourceNativeTermsSeed.fuel (2 * c) + 18))) := by
    unfold acceptedFuel SourceNativeTermsSeed.fuel
    omega
  simpa only [accepted,cost,start] using checked

def dispatch : Block 24 := .branch 4 reject accepted accepted
def block : Block 24 := .seq headers dispatch
def fuel (input : BitString) : Nat :=
  MatrixStrictHeader.blockFuel input + 1 +
    (1 + if (MatrixStrictHeader.scan input).terminated then acceptedFuel (MatrixStrictHeader.scan input).count else 18)
def result (input : BitString) : Store 24 :=
  let h := MatrixStrictHeader.scan input
  if h.terminated then work h.rest [] (data h.rest h.count)
  else work h.rest [] {emptySaved with stream := h.rest}

theorem block_exec (input : BitString) : Exec block (initial input) (fuel input) (result input) := by
  have first := headers_exec input emptySaved
  cases flag : (MatrixStrictHeader.scan input).terminated with
  | false =>
    let h := MatrixStrictHeader.scan input
    let r := SourceNativeRowIndex.state h.rest h.count false
    let saved := {emptySaved with stream := h.rest}
    have bad : Exec reject (withCore r saved) 18 (work h.rest [] saved) :=
      reject_exec (Frame.join r.store (Store.empty 5)) saved
    have last : Exec dispatch (withCore r saved) (1 + 18) (work h.rest [] saved) :=
      Exec.empty rfl bad
    simp only [headerResult,flag] at first
    simpa only [block,SourceNativeSystemState.initial,fuel,result,flag,Bool.false_eq_true,↓reduceIte,h,r,saved] using
      Exec.seq first last
  | true =>
    have last : Exec dispatch (headerResult input emptySaved)
        (1 + acceptedFuel (MatrixStrictHeader.scan input).count)
        (work (MatrixStrictHeader.scan input).rest []
          (data (MatrixStrictHeader.scan input).rest (MatrixStrictHeader.scan input).count)) := by
      simp only [headerResult,flag]
      exact Exec.one rfl (accepted_exec (MatrixStrictHeader.scan input).rest (MatrixStrictHeader.scan input).count)
    simpa only [block,SourceNativeSystemState.initial,fuel,result,flag,↓reduceIte] using Exec.seq first last

theorem fuel_bound (input : BitString) : fuel input ≤ 21 * input.length + 62 := by
  have header := MatrixStrictHeader.blockFuel_bound input
  have count := MatrixStrictHeader.scan_size input
  unfold fuel acceptedFuel
  split <;> omega
theorem dimension_bound (input : BitString) :
    2 * (MatrixStrictHeader.scan input).count ≤ 2 * input.length := by
  have count := MatrixStrictHeader.scan_size input
  omega
theorem canonical_exec (c : Nat) (suffix : BitString) :
    Exec block (initial (natural c ++ suffix)) (fuel (natural c ++ suffix))
      (work suffix [] (data suffix c)) := by
  simpa only [result,MatrixStrictHeader.scan_canonical,↓reduceIte] using block_exec (natural c ++ suffix)

end PNP.Concrete.ResidualReduction.SourceNativeSystemHeader
