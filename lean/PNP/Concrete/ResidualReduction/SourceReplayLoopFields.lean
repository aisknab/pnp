import PNP.Concrete.ResidualReduction.SourceReplayStepMachine

/-! Unbounded raw-history replay semantics. A failed step stops immediately;
a successful step uses its computed witness for the next actual record.
The observed result agrees with decoding the counted record prefix and then
traversing the original maps. No semantic validity of arbitrary records is
assumed or asserted here. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayLoopFields
open PNP.Concrete PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceChain

structure Result where
  input : BitString
  point : BitString
  valid : Bool
def observe (r : Result) : Option (BitString × BitString) :=
  if r.valid then some (r.input,r.point) else none

def scan (recover : Bool) : Nat → BitString → BitString → Result
  | 0,input,point => ⟨input,point,true⟩
  | count + 1,input,point =>
    match SourceReplayStepMachine.answer recover input point with
    | none => ⟨SourceReplayRecordFields.rest input,point,false⟩
    | some (cursor,output) => scan recover count cursor output

theorem parse_contract (recover : Bool) (count : Nat) (input point : BitString) :
    observe (scan recover count input point) =
      (parseN SourceEncoding.recordCodec.parse count input).bind fun (records,cursor) =>
        (SourceReplayTraversal.walk (SourceReplayStepApply.mapOne recover) records point).map fun output => (cursor,output) := by
  induction count generalizing input point with
  | zero => rfl
  | succ count ih =>
    cases first : SourceEncoding.recordCodec.parse input with
    | none =>
      simp only [scan,SourceReplayStepMachine.answer,first,Option.bind_none,observe,
        Bool.false_eq_true,↓reduceIte,parseN]
    | some pair =>
      rcases pair with ⟨q,rest⟩
      cases mapped : SourceReplayStepApply.mapOne recover q point with
      | none =>
        cases later : parseN SourceEncoding.recordCodec.parse count rest <;>
          simp only [scan,SourceReplayStepMachine.answer,first,mapped,Option.bind_some,Option.map_none,
            observe,Bool.false_eq_true,↓reduceIte,parseN,later,Option.bind_none,SourceReplayTraversal.walk]
      | some output =>
        have checked := ih rest output
        cases later : parseN SourceEncoding.recordCodec.parse count rest with
        | none =>
          rw [later] at checked
          simpa only [scan,SourceReplayStepMachine.answer,first,mapped,Option.bind_some,Option.map_some,
            parseN,later,Option.bind_none,SourceReplayTraversal.walk] using checked
        | some pair =>
          rcases pair with ⟨records,cursor⟩
          rw [later] at checked
          simpa only [scan,SourceReplayStepMachine.answer,first,mapped,Option.bind_some,Option.map_some,
            parseN,later,Option.bind_none,SourceReplayTraversal.walk] using checked

theorem canonical (recover : Bool) (records : List StepRecord) (suffix point : BitString) :
    observe (scan recover records.length (encodeSeq SourceEncoding.recordCodec.encode records ++ suffix) point) =
      (SourceReplayTraversal.walk (SourceReplayStepApply.mapOne recover) records point).map fun output => (suffix,output) := by
  have checked := parse_contract recover records.length (encodeSeq SourceEncoding.recordCodec.encode records ++ suffix) point
  rw [parseN_roundtrip] at checked
  exact checked

theorem direction_walk (recover : Bool) (records : List StepRecord) (point : BitString) :
    SourceReplayTraversal.walk (SourceReplayStepApply.mapOne recover) records point =
      if recover then SourceReplayTraversal.walk SourceReplayTraversal.recoverOne records point
      else SourceReplayTraversal.walk SourceReplayTraversal.projectOne records point := by
  cases recover <;> rfl

theorem bounds (recover : Bool) (count : Nat) (input point : BitString) :
    (scan recover count input point).input.length ≤ input.length ∧
      (scan recover count input point).point.length ≤ point.length + count := by
  induction count generalizing input point with
  | zero => exact ⟨Nat.le_refl _,Nat.le_refl _⟩
  | succ count ih =>
    cases first : SourceReplayStepMachine.answer recover input point with
    | none =>
      simp only [scan,first]
      exact ⟨(SourceReplayRecordFields.input_bounds input).2.2.2.2.2.2.2.2,by omega⟩
    | some pair =>
      rcases pair with ⟨cursor,output⟩
      obtain ⟨rest,size⟩ := SourceReplayStepMachine.answer_bounds recover input point cursor output first
      have growth : output.length ≤ point.length + 1 := by cases recover <;> simp only [Bool.false_eq_true,↓reduceIte] at size <;> omega
      have later := ih cursor output
      simp only [scan,first]
      exact ⟨Nat.le_trans later.1 rest,by omega⟩

def readHistory (recover : Bool) (input point : BitString) : Result :=
  if (MatrixStrictHeader.scan input).terminated then
    scan recover (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest point
  else ⟨(MatrixStrictHeader.scan input).rest,point,false⟩

theorem prefix_contract (recover : Bool) (input point : BitString) :
    observe (readHistory recover input point) =
      ((listCodec SourceEncoding.recordCodec).parse input).bind fun (records,cursor) =>
        (SourceReplayTraversal.walk (SourceReplayStepApply.mapOne recover) records point).map fun output => (cursor,output) := by
  cases flag : (MatrixStrictHeader.scan input).terminated with
  | false =>
    simp only [readHistory,listCodec,MatrixStrictHeader.scan_parse,flag,
      Bool.false_eq_true,↓reduceIte,observe,Option.bind_none]
  | true =>
    simpa only [readHistory,listCodec,MatrixStrictHeader.scan_parse,flag,↓reduceIte] using
      parse_contract recover (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest point

theorem prefix_canonical (recover : Bool) (records : List StepRecord) (suffix point : BitString) :
    observe (readHistory recover ((listCodec SourceEncoding.recordCodec).encode records ++ suffix) point) =
      (SourceReplayTraversal.walk (SourceReplayStepApply.mapOne recover) records point).map fun output => (suffix,output) := by
  have checked := prefix_contract recover ((listCodec SourceEncoding.recordCodec).encode records ++ suffix) point
  rw [(listCodec SourceEncoding.recordCodec).roundtrip] at checked
  exact checked

theorem prefix_bounds (recover : Bool) (input point : BitString) :
    (readHistory recover input point).input.length ≤ input.length ∧
      (readHistory recover input point).point.length ≤ point.length + input.length := by
  have header := MatrixStrictHeader.scan_size input
  cases flag : (MatrixStrictHeader.scan input).terminated with
  | false =>
    simp only [readHistory,flag,Bool.false_eq_true,↓reduceIte]
    exact ⟨by omega,by omega⟩
  | true =>
    have later := bounds recover (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest point
    simp only [readHistory,flag,↓reduceIte]
    exact ⟨by omega,by omega⟩

end PNP.Concrete.ResidualReduction.SourceReplayLoopFields
