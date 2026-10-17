import PNP.Concrete.ResidualReduction.SourceReplayRecordStack

/-! Raw counted-history traversal. Every iteration validates the next actual
record and prepends precisely its consumed bytes. Failure stops the scan,
preserving already-read history but never claiming a complete decoded list. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayHistoryFields
open PNP.Concrete PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceChain

structure Result where
  input : BitString
  history : BitString
  valid : Bool

def scan : Nat → BitString → BitString → Result
  | 0,input,history => ⟨input,history,true⟩
  | count + 1,input,history =>
      if SourceReplayRecordFields.valid input then
        scan count (SourceReplayRecordFields.rest input)
          (SourceReplayRecordStack.bytes (SourceReplayRecordState.capture input) ++ history)
      else ⟨SourceReplayRecordFields.rest input,history,false⟩

private theorem seq_append (xs ys : List StepRecord) :
    encodeSeq SourceEncoding.recordCodec.encode (xs ++ ys) =
      encodeSeq SourceEncoding.recordCodec.encode xs ++ encodeSeq SourceEncoding.recordCodec.encode ys := by
  induction xs with
  | nil => rfl
  | cons q xs ih => simp only [List.cons_append,encodeSeq,ih,List.append_assoc]

theorem parse_contract (count : Nat) (input history : BitString) :
    match parseN SourceEncoding.recordCodec.parse count input with
    | none => (scan count input history).valid = false
    | some (records,suffix) => scan count input history =
        ⟨suffix,encodeSeq SourceEncoding.recordCodec.encode records.reverse ++ history,true⟩ := by
  induction count generalizing input history with
  | zero => rfl
  | succ count ih =>
    cases first : SourceEncoding.recordCodec.parse input with
    | none =>
      have bad := SourceReplayRecordFields.parse_contract input
      rw [first] at bad
      simp only [parseN,first,scan,bad,Bool.false_eq_true,↓reduceIte]
    | some pair =>
      rcases pair with ⟨q,rest⟩
      obtain ⟨good,fields,cursor⟩ := SourceReplayRecordFields.parsed_fields input q rest first
      have word : SourceReplayRecordStack.bytes (SourceReplayRecordState.capture input) =
          SourceEncoding.recordCodec.encode q := by
        rw [SourceReplayRecordState.capture,fields,SourceReplayRecordStack.bytes_record]
      have checked := ih rest (SourceEncoding.recordCodec.encode q ++ history)
      cases second : parseN SourceEncoding.recordCodec.parse count rest with
      | none =>
        rw [second] at checked
        simpa only [parseN,first,second,scan,good,↓reduceIte,cursor,word] using checked
      | some pair =>
        rcases pair with ⟨records,suffix⟩
        rw [second] at checked
        simpa only [parseN,first,second,scan,good,↓reduceIte,cursor,word,List.reverse_cons,
          seq_append,encodeSeq,List.append_nil,List.append_assoc] using checked

theorem bounds (count : Nat) (input history : BitString) :
    (scan count input history).input.length ≤ input.length ∧
      (scan count input history).input.length + (scan count input history).history.length ≤
        input.length + history.length := by
  induction count generalizing input history with
  | zero => exact ⟨Nat.le_refl _,Nat.le_refl _⟩
  | succ count ih =>
    obtain ⟨_,_,_,_,_,_,_,_,restBound⟩ := SourceReplayRecordFields.input_bounds input
    cases valid : SourceReplayRecordFields.valid input with
    | false =>
      simp only [scan,valid,Bool.false_eq_true,↓reduceIte]
      exact ⟨restBound,Nat.add_le_add_right restBound history.length⟩
    | true =>
      simp only [scan,valid,↓reduceIte]
      have checked := ih (SourceReplayRecordFields.rest input)
        (SourceReplayRecordStack.bytes (SourceReplayRecordState.capture input) ++ history)
      have splitLength := congrArg List.length (SourceReplayRecordStack.captured_prefix input valid)
      simp only [List.length_append] at splitLength checked
      refine ⟨Nat.le_trans checked.1 restBound,?_⟩
      omega

def readHistory (input history : BitString) : Result :=
  if (MatrixStrictHeader.scan input).terminated then
    scan (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest history
  else ⟨(MatrixStrictHeader.scan input).rest,history,false⟩

theorem prefix_contract (input history : BitString) :
    match (listCodec SourceEncoding.recordCodec).parse input with
    | none => (readHistory input history).valid = false
    | some (records,suffix) => readHistory input history =
        ⟨suffix,encodeSeq SourceEncoding.recordCodec.encode records.reverse ++ history,true⟩ := by
  cases flag : (MatrixStrictHeader.scan input).terminated with
  | false => simp only [listCodec,MatrixStrictHeader.scan_parse,flag,Bool.false_eq_true,↓reduceIte,readHistory]
  | true =>
    have checked := parse_contract (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest history
    simpa only [listCodec,MatrixStrictHeader.scan_parse,flag,↓reduceIte,readHistory] using checked

theorem prefix_canonical (records : List StepRecord) (suffix history : BitString) :
    readHistory ((listCodec SourceEncoding.recordCodec).encode records ++ suffix) history =
      ⟨suffix,encodeSeq SourceEncoding.recordCodec.encode records.reverse ++ history,true⟩ := by
  have checked := prefix_contract ((listCodec SourceEncoding.recordCodec).encode records ++ suffix) history
  rw [(listCodec SourceEncoding.recordCodec).roundtrip records suffix] at checked
  exact checked

theorem prefix_bounds (input history : BitString) :
    (readHistory input history).input.length ≤ input.length ∧
      (readHistory input history).input.length + (readHistory input history).history.length ≤ input.length + history.length := by
  have header := MatrixStrictHeader.scan_size input
  have remaining : (MatrixStrictHeader.scan input).rest.length ≤ input.length :=
    Nat.le_trans (Nat.le_add_left _ _) header
  cases flag : (MatrixStrictHeader.scan input).terminated with
  | false =>
    simp only [readHistory,flag,Bool.false_eq_true,↓reduceIte]
    exact ⟨remaining,Nat.add_le_add_right remaining history.length⟩
  | true =>
    simp only [readHistory,flag,↓reduceIte]
    have checked := bounds (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest history
    exact ⟨Nat.le_trans checked.1 remaining,
      Nat.le_trans checked.2 (Nat.add_le_add_right remaining history.length)⟩

end PNP.Concrete.ResidualReduction.SourceReplayHistoryFields
