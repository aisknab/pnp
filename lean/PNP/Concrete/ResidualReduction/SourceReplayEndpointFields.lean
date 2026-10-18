import PNP.Concrete.ResidualReduction.SourceReplayLoopPrefix
import PNP.Concrete.ResidualReduction.SourceReplayParser

/-! Closed replay semantics using only fields derived from the actual
request/data bytes. The original and terminal widths are checked independently.
The history count and forward/reverse streams come from the strict saved-data
reader, not a caller-supplied list. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointFields
open PNP.Concrete PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceChain

def count (data : BitString) : Nat :=
  (MatrixStrictHeader.scan (SourceReplayDataFields.historyInput data)).count
def stream (recover : Bool) (data : BitString) : BitString :=
  if recover then (SourceReplayDataFields.history data).history
  else (MatrixStrictHeader.scan (SourceReplayDataFields.historyInput data)).rest
def startWidth (r : SourceReplayRequest.Request) : Nat :=
  if r.recover then SourceReplayDataFields.dimension r.data else r.dimension
def endWidth (r : SourceReplayRequest.Request) : Nat :=
  if r.recover then r.dimension else SourceReplayDataFields.dimension r.data
def historyResult (recover : Bool) (data point : BitString) : SourceReplayLoopFields.Result :=
  SourceReplayLoopFields.scan recover (count data) (stream recover data) point
def replay (recover : Bool) (data point : BitString) : Option BitString :=
  (SourceReplayLoopFields.observe (historyResult recover data point)).map Prod.snd
def evaluate (r : SourceReplayRequest.Request) : Option BitString :=
  if SourceReplayDataFields.valid r.data then
    (SourceReplayTraversal.finish (startWidth r) r.witness).bind fun point =>
      (replay r.recover r.data point).bind (SourceReplayTraversal.finish (endWidth r))
  else none

theorem decoded_fields (data : BitString) (d : SourceEncoding.ReductionData)
    (decoded : SourceEncoding.dataCodec.decode data = some d) :
    SourceReplayDataFields.dimension data = d.dimension ∧
      SourceReplayDataFields.historyInput data = (listCodec SourceEncoding.recordCodec).encode d.history ∧
      (SourceReplayDataFields.history data).history = encodeSeq SourceEncoding.recordCodec.encode d.history.reverse ∧
      SourceReplayDataFields.valid data = true := by
  have fields := SourceReplayDataFields.decoded_fields data d decoded
  exact ⟨congrArg SourceReplayDataFields.Fields.dimension fields,
    congrArg SourceReplayDataFields.Fields.forward fields,
    congrArg SourceReplayDataFields.Fields.reverse fields,
    congrArg SourceReplayDataFields.Fields.valid fields⟩

theorem count_decoded (data : BitString) (d : SourceEncoding.ReductionData)
    (decoded : SourceEncoding.dataCodec.decode data = some d) : count data = d.history.length := by
  rw [count,(decoded_fields data d decoded).2.1]
  change (MatrixStrictHeader.scan (natural d.history.length ++ encodeSeq SourceEncoding.recordCodec.encode d.history)).count = _
  rw [MatrixStrictHeader.scan_canonical]

theorem stream_decoded (recover : Bool) (data : BitString) (d : SourceEncoding.ReductionData)
    (decoded : SourceEncoding.dataCodec.decode data = some d) :
    stream recover data = encodeSeq SourceEncoding.recordCodec.encode
      (if recover then d.history.reverse else d.history) := by
  obtain ⟨_,forward,reverse,_⟩ := decoded_fields data d decoded
  cases recover with
  | true => exact reverse
  | false =>
    simp only [stream,Bool.false_eq_true,↓reduceIte,forward]
    change (MatrixStrictHeader.scan (natural d.history.length ++ encodeSeq SourceEncoding.recordCodec.encode d.history)).rest = _
    rw [MatrixStrictHeader.scan_canonical]

theorem replay_eq (recover : Bool) (data point : BitString) (d : SourceEncoding.ReductionData)
    (decoded : SourceEncoding.dataCodec.decode data = some d) :
    replay recover data point =
      if recover then SourceReplayTraversal.walk SourceReplayTraversal.recoverOne d.history.reverse point
      else SourceReplayTraversal.walk SourceReplayTraversal.projectOne d.history point := by
  rw [replay,historyResult,count_decoded data d decoded,stream_decoded recover data d decoded]
  cases recover with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte]
    have checked := SourceReplayLoopFields.canonical false d.history [] point
    simp only [List.append_nil,SourceReplayLoopFields.direction_walk,Bool.false_eq_true,↓reduceIte] at checked
    rw [checked]
    cases SourceReplayTraversal.walk SourceReplayTraversal.projectOne d.history point <;> rfl
  | true =>
    have checked := SourceReplayLoopFields.canonical true d.history.reverse [] point
    simp only [List.append_nil,List.length_reverse,SourceReplayLoopFields.direction_walk,↓reduceIte] at checked
    simp only [↓reduceIte]
    rw [checked]
    cases SourceReplayTraversal.walk SourceReplayTraversal.recoverOne d.history.reverse point <;> rfl

theorem evaluate_eq (r : SourceReplayRequest.Request) : evaluate r = SourceReplayRequest.evaluate r := by
  cases decoded : SourceEncoding.dataCodec.decode r.data with
  | none =>
    have bad := SourceReplayDataFields.decode_contract r.data
    rw [decoded] at bad
    simp only [evaluate,bad,Bool.false_eq_true,↓reduceIte,SourceReplayRequest.evaluate,
      ← SourceReplayTraversal.recover_eq,← SourceReplayTraversal.project_eq,
      SourceReplayTraversal.recover,SourceReplayTraversal.project,decoded,Option.bind_none]
    cases r.recover <;> rfl
  | some d =>
    obtain ⟨dimension,_,_,good⟩ := decoded_fields r.data d decoded
    have replayAll : replay r.recover r.data =
        fun point => if r.recover then SourceReplayTraversal.walk SourceReplayTraversal.recoverOne d.history.reverse point
          else SourceReplayTraversal.walk SourceReplayTraversal.projectOne d.history point :=
      funext (fun point => replay_eq r.recover r.data point d decoded)
    simp only [evaluate,good,↓reduceIte,replayAll,SourceReplayRequest.evaluate,
      ← SourceReplayTraversal.recover_eq,← SourceReplayTraversal.project_eq,
      SourceReplayTraversal.recover,SourceReplayTraversal.project,decoded,Option.bind_some,startWidth,endWidth,dimension]
    cases r.recover <;> rfl

def answer (input : BitString) : Option BitString :=
  (SourceReplayParser.view (SourceReplayParser.completedSaved input)).bind evaluate
theorem answer_eq (input : BitString) : answer input = SourceReplayRequest.answer input := by
  rw [answer,SourceReplayParser.parsed_fields]
  have same : evaluate = SourceReplayRequest.evaluate := funext evaluate_eq
  rw [same]
  rfl

theorem input_bounds (recover : Bool) (data : BitString) :
    count data ≤ data.length ∧ (stream recover data).length ≤ data.length ∧
      SourceReplayDataFields.dimension data ≤ data.length := by
  have source := SourceReplayDataFields.bounds data
  have header := MatrixStrictHeader.scan_size (SourceReplayDataFields.historyInput data)
  have countBound : count data ≤ data.length := by unfold count; omega
  refine ⟨countBound,?_,source.1⟩
  cases recover <;> simp only [stream,Bool.false_eq_true,↓reduceIte] <;> omega

theorem outer_bounds (input : BitString) :
    (SourceReplayParser.completedSaved input).dimension.length ≤ input.length ∧
      (SourceReplayParser.completedSaved input).data.length ≤ input.length ∧
      (SourceReplayParser.completedSaved input).witness.length ≤ input.length := by
  have tailBound : input.tail.length ≤ input.length := by
    cases input <;> simp only [List.tail_nil,List.tail_cons,List.length_nil,List.length_cons] <;> omega
  have header := MatrixStrictHeader.scan_size input.tail
  have first := SourceReplayRequest.first_bound input.tail
  have second := SourceReplayRequest.second_bound input.tail
  have data := SourceReplayBlob.bytes_bound (SourceReplayRequest.first input.tail)
  have witness := SourceReplayBlob.bytes_bound (SourceReplayRequest.second input.tail)
  simp only [SourceReplayParser.completedSaved,SourceReplayParser.witnessSaved,SourceReplayParser.dataSaved,
    SourceReplayParser.headerSaved,SourceReplayParserState.restrict,List.length_replicate]
  exact ⟨by omega,by omega,by omega⟩

theorem outer_flag (input : BitString) :
    (SourceReplayParser.completedSaved input).valid = [] ∨
      (SourceReplayParser.completedSaved input).valid = [true] := by
  cases h : (MatrixStrictHeader.scan input.tail).terminated <;>
    cases a : SourceReplayBlob.valid (SourceReplayRequest.first input.tail) <;>
    cases b : SourceReplayBlob.valid (SourceReplayRequest.second input.tail) <;>
    cases c : (SourceReplayRequest.suffix input.tail).isEmpty <;>
    simp only [SourceReplayParser.completedSaved,SourceReplayParser.witnessSaved,SourceReplayParser.dataSaved,
      SourceReplayParser.headerSaved,SourceReplayParserState.restrict,h,a,b,c,Bool.false_eq_true,↓reduceIte] <;>
    first | exact Or.inl True.intro | exact Or.inr True.intro

end PNP.Concrete.ResidualReduction.SourceReplayEndpointFields
