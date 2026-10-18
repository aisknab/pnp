import PNP.Concrete.ResidualReduction.SourceNativeSystemTerms

/-! Read a product row's leading sparse label, construct its affine coordinate,
restore normal byte order and retain it in the protected left-hand payload.
Malformed labels invalidate the system and clear the row loop counter. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeSystemLabel
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization
open PNP.Concrete.ResidualReduction.SourceNativeSystemState
open PNP.Concrete.ResidualReduction.SourceNativeTermsSpec

def scratch (r : Registers) (n : Nat) : Store 14 :=
  SourceNativeTermsState.full r (SourceNativeTermsSeed.blank [] n)
def normal (r : Registers) : Registers := {r with excess := [],output := r.output.reverse}
def reverseBlock : Block 14 :=
  .seq SourceNativeTermsAdd.arrange (Frame.block 5 ClauseQuery.reverseLoop)
def reverseFuel (r : Registers) : Nat := 2 + (4 * r.output.length + 1)

theorem reverse_exec (r : Registers) (n : Nat) :
    Exec reverseBlock (scratch r n) (reverseFuel r) (scratch (normal r) n) := by
  let base := {r with excess := [],output := []}
  let ready := {r with excess := r.output,output := []}
  have first : Exec SourceNativeTermsAdd.arrange (scratch r n) 2 (scratch ready n) :=
    Exec.seq (.action _ _) (.action _ _)
  have reversal : Exec ClauseQuery.reverseLoop ready.store (4 * r.output.length + 1)
      (normal r).store := by
    simpa only [base,ready,normal,List.append_nil] using ClauseQuery.reverse_exec base r.output
  exact Exec.seq first (Frame.execution reversal (SourceNativeTermsSeed.blank [] n).store)

def parsed (input : BitString) (n : Nat) : Store 14 := scratch (normal (readCore input n)) n
def result (input : BitString) (n : Nat) (s : Saved) : Saved :=
  SourceNativeSystemCapture.captured .left (parsed input n) s
def block : Block 24 := .seq (load .dimension 9)
  (.seq (use10 SourceNativeLabel.block)
    (.seq (use14 reverseBlock) (SourceNativeSystemCapture.block .left)))
def fuel (input : BitString) (n : Nat) : Nat :=
  1 + (SourceNativeLabel.fuel input n +
    (reverseFuel (readCore input n) + SourceNativeSystemCapture.fuel (parsed input n)))

theorem block_exec (input : BitString) (n : Nat) (s : Saved)
    (dimension : s.dimension = List.replicate n true) :
    Exec block (work input [] s) (fuel input n)
      (work (result input n s).stream [] (result input n s)) := by
  have first := SourceNativeSystemTerms.prepare_exec input n s dimension
  have reader := use10_exec (SourceNativeLabel.block_exec input n) s
  rw [label_result] at reader
  change Exec (use10 SourceNativeLabel.block) (full (SourceNativeTermsInput.initial input n) s)
    (SourceNativeLabel.fuel input n) (full (scratch (readCore input n) n) s) at reader
  have reversal := use14_exec (reverse_exec (readCore input n) n) s
  have last := SourceNativeSystemCapture.block_exec .left (parsed input n) s
  simpa only [block,fuel,result,SourceNativeSystemCapture.captured_stream,parsed] using
    Exec.seq first (Exec.seq reader (Exec.seq reversal last))

theorem readCore_empty_output (input : BitString) (n : Nat)
    (absent : selected input n = none) : (readCore input n).output = [] := by
  cases flag : (SourceNativeRowIndex.parse input).valid with
  | false =>
    simp only [readCore,flag,Bool.false_eq_true,↓reduceIte]
    rfl
  | true =>
    by_cases bound : (SourceNativeRowIndex.parse input).index < n
    · simp only [selected,flag,↓reduceIte,bound,dif_pos] at absent
      cases absent
    · simp only [readCore,flag,↓reduceIte,SourceNativeCoordinate.result,bound]
      rfl

theorem readCore_output_bound (input : BitString) (n : Nat) :
    (readCore input n).output.length ≤ n + 1 := by
  cases chosen : selected input n with
  | none =>
    rw [readCore_empty_output input n chosen]
    exact Nat.zero_le _
  | some j =>
    rw [readCore_some input n j chosen]
    change (SourceNativeEncoding.affineWord (NativeSource.coordinateForm n j)).reverse.length ≤ n + 1
    rw [List.length_reverse]
    exact Nat.le_of_eq (SourceEncoding.affine_length _)

theorem dimension_preserved (input : BitString) (n : Nat) (s : Saved) :
    (result input n s).dimension = s.dimension := SourceNativeSystemCapture.captured_dimension _ _ _

theorem stream_eq (input : BitString) (n : Nat) (s : Saved) :
    (result input n s).stream = remaining input := by
  rw [result,SourceNativeSystemCapture.captured_stream]
  exact readCore_input input n

theorem stream_bound (input : BitString) (n : Nat) (s : Saved) :
    (result input n s).stream.length ≤ input.length := by
  rw [stream_eq]
  exact remaining_bound input

theorem left_bound (input : BitString) (n : Nat) (s : Saved) :
    (result input n s).left.length ≤ n + 1 := by
  have shape : (result input n s).left = (readCore input n).output.reverse := by
    unfold result SourceNativeSystemCapture.captured
    split <;> rfl
  rw [shape,List.length_reverse]
  exact readCore_output_bound input n

theorem invalid_result (input : BitString) (n : Nat) (s : Saved)
    (absent : selected input n = none) :
    result input n s = {s with stream := remaining input,left := [],active := [],pending := []} := by
  have bad := readCore_none input n absent
  have empty := readCore_empty_output input n absent
  have signal : (parsed input n).get 4 = [] := bad
  have source : (parsed input n).get 0 = remaining input := readCore_input input n
  have output : (parsed input n).get 8 = [] := by
    change (readCore input n).output.reverse = []
    rw [empty]
    rfl
  simp only [result,SourceNativeSystemCapture.captured,SourceNativeSystemCapture.success,
    signal,Bool.false_eq_true,↓reduceIte,SourceNativeSystemCapture.recorded,source,output]

theorem selected_result (input : BitString) (n : Nat) (s : Saved) (j : Fin n)
    (chosen : selected input n = some j) :
    result input n s = {s with stream := remaining input,left := SourceNativeEncoding.affineWord (NativeSource.coordinateForm n j)} := by
  unfold result parsed
  rw [readCore_some input n j chosen]
  change {s with stream := remaining input,left := (SourceNativeEncoding.affineWord (NativeSource.coordinateForm n j)).reverse.reverse} = _
  rw [List.reverse_reverse]

theorem fuel_bound (input : BitString) (n : Nat) :
    fuel input n ≤ 15 * input.length + 7 * n + 60 := by
  have reader := SourceNativeLabel.fuel_bound input n
  have size := readCore_output_bound input n
  have capture := SourceNativeSystemCapture.fuel_bound (parsed input n)
  unfold fuel reverseFuel
  omega

theorem polynomial_bound (input : BitString) (n limit : Nat)
    (size : input.length ≤ limit) (dimension : n ≤ 2 * limit) :
    fuel input n ≤ 29 * limit + 60 := by
  have checked := fuel_bound input n
  omega

theorem canonical_result {c : Nat} (row : NativeEquations.Row c) (suffix : BitString) (s : Saved) :
    result ((NativeSystemCodec.rowCodec c).encode row ++ suffix) (2 * c) s =
      {s with stream := suffix,left := SourceNativeEncoding.affineWord (NativeSource.coordinateForm (2 * c) (NativeSource.rowIndex row))} := by
  rw [selected_result _ _ _ _ (selected_canonical row suffix),remaining_canonical]

theorem canonical_exec {c : Nat} (row : NativeEquations.Row c) (suffix : BitString) (s : Saved)
    (dimension : s.dimension = List.replicate (2 * c) true) :
    Exec block (work ((NativeSystemCodec.rowCodec c).encode row ++ suffix) [] s)
      (fuel ((NativeSystemCodec.rowCodec c).encode row ++ suffix) (2 * c))
      (work suffix [] {s with stream := suffix,left := SourceNativeEncoding.affineWord (NativeSource.coordinateForm (2 * c) (NativeSource.rowIndex row))}) := by
  simpa only [canonical_result] using
    block_exec ((NativeSystemCodec.rowCodec c).encode row ++ suffix) (2 * c) s dimension

end PNP.Concrete.ResidualReduction.SourceNativeSystemLabel
