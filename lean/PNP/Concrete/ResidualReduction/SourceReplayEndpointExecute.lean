import PNP.Concrete.ResidualReduction.SourceReplayEndpointReady

/-! Closed raw-input replay execution through the observed optional answer.
The literal request/data loader, actual-field adapter and guarded history
consumer are connected without supplied parsed fields. Output serialization
and physical finite-machine runtime are separate remaining obligations. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointExecute
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks

def data (input : BitString) : BitString := (SourceReplayParser.completedSaved input).data
def parameters (input : BitString) : SourceReplayEndpointRunState.Parameters :=
  let p := SourceReplayParser.completedSaved input
  ⟨p.mode.headD false,p.dimension.length,SourceReplayDataFields.dimension p.data,p.witness⟩
def good (input : BitString) : Bool :=
  ((SourceReplayRequest.codec.decode input).bind (fun r => SourceEncoding.dataCodec.decode r.data)).isSome
def ready (input : BitString) : Store 40 :=
  SourceReplayEndpointRunState.work (SourceReplayEndpointFields.count (data input))
    (SourceReplayEndpointFields.stream (parameters input).recover (data input))
    (parameters input).witness (parameters input) false (good input)

theorem normalized_saved (input : BitString) :
    SourceReplayEndpointReadyState.normalized (SourceReplayEndpointLoad.saved input) =
      SourceReplayEndpointRunState.saved (parameters input) (good input) := by
  let p := SourceReplayParser.completedSaved input
  have valid := SourceReplayEndpointLoad.acceptance_contract input
  rw [SourceReplayEndpointLoad.result,SourceReplayEndpointState.read_valid] at valid
  change (SourceReplayEndpointLoad.saved input).valid = SourceReplayRecordState.flag (good input) at valid
  have dimension : p.dimension = List.replicate p.dimension.length true := by
    change List.replicate (MatrixStrictHeader.scan input.tail).count true =
      List.replicate (List.replicate (MatrixStrictHeader.scan input.tail).count true).length true
    rw [List.length_replicate]
  calc
    SourceReplayEndpointReadyState.normalized (SourceReplayEndpointLoad.saved input) =
        ⟨[p.mode.headD false],p.dimension,p.witness,(SourceReplayEndpointLoad.saved input).valid,
          List.replicate (SourceReplayDataFields.dimension p.data) true⟩ := rfl
    _ = SourceReplayEndpointRunState.saved (parameters input) (good input) := by
      rw [valid,dimension]
      rfl

theorem ready_exec (input : BitString) :
    Exec SourceReplayEndpointReady.block (SourceReplayEndpointLoad.result input)
      (SourceReplayEndpointReady.fuel (data input)) (ready input) := by
  have checked := SourceReplayEndpointReady.block_exec (data input) (SourceReplayEndpointLoad.saved input)
  change Exec SourceReplayEndpointReady.block (SourceReplayEndpointLoad.result input)
    (SourceReplayEndpointReady.fuel (data input))
    (SourceReplayEndpointReadyState.work (SourceReplayEndpointFields.count (data input))
      (SourceReplayEndpointFields.stream (parameters input).recover (data input))
      (parameters input).witness (parameters input).recover
      (SourceReplayEndpointReadyState.normalized (SourceReplayEndpointLoad.saved input))) at checked
  rw [normalized_saved,SourceReplayEndpointReadyState.work_run] at checked
  exact checked

def result (input : BitString) : Store 40 :=
  SourceReplayEndpointRun.result (parameters input) (SourceReplayEndpointFields.count (data input))
    (SourceReplayEndpointFields.stream (parameters input).recover (data input))
    (parameters input).witness (good input)
def block : Block 40 := .seq SourceReplayEndpointLoad.block
  (.seq SourceReplayEndpointReady.block SourceReplayEndpointRun.block)
def fuel (input : BitString) : Nat :=
  SourceReplayEndpointLoad.fuel input + (SourceReplayEndpointReady.fuel (data input) +
    SourceReplayEndpointRun.fuel (parameters input) (SourceReplayEndpointFields.count (data input))
      (SourceReplayEndpointFields.stream (parameters input).recover (data input))
      (parameters input).witness (good input))

theorem block_exec (input : BitString) :
    Exec block (SourceReplayEndpointState.initial input) (fuel input) (result input) :=
  Exec.seq (SourceReplayEndpointLoad.block_exec input) (Exec.seq (ready_exec input)
    (SourceReplayEndpointRun.block_exec (parameters input) (SourceReplayEndpointFields.count (data input))
      (SourceReplayEndpointFields.stream (parameters input).recover (data input))
      (parameters input).witness (good input)))

def requestParameters (r : SourceReplayRequest.Request) : SourceReplayEndpointRunState.Parameters :=
  ⟨r.recover,r.dimension,SourceReplayDataFields.dimension r.data,r.witness⟩

theorem request_answer (r : SourceReplayRequest.Request) :
    SourceReplayEndpointRun.answer (requestParameters r) (SourceReplayEndpointFields.count r.data)
      (SourceReplayEndpointFields.stream r.recover r.data) r.witness (SourceReplayDataFields.valid r.data) =
        SourceReplayEndpointFields.evaluate r := by
  rw [SourceReplayEndpointRun.answer_contract]
  cases flag : SourceReplayDataFields.valid r.data with
  | false => simp only [SourceReplayEndpointFields.evaluate,flag,Bool.false_eq_true,↓reduceIte]
  | true =>
    simp only [SourceReplayEndpointFields.evaluate,flag,↓reduceIte,requestParameters,
      SourceReplayEndpointCheck.width,Bool.false_eq_true,SourceReplayEndpointFields.startWidth,
      SourceReplayEndpointFields.endWidth,SourceReplayEndpointFields.replay,SourceReplayEndpointFields.historyResult]
    apply congrArg (fun f : BitString → Option BitString =>
      (SourceReplayTraversal.finish
        (if r.recover then SourceReplayDataFields.dimension r.data else r.dimension) r.witness).bind f)
    funext point
    cases SourceReplayLoopFields.observe
      (SourceReplayLoopFields.scan r.recover (SourceReplayEndpointFields.count r.data)
        (SourceReplayEndpointFields.stream r.recover r.data) point) <;> rfl

theorem data_acceptance (bytes : BitString) :
    SourceReplayDataFields.valid bytes = (SourceEncoding.dataCodec.decode bytes).isSome := by
  cases parsed : SourceEncoding.dataCodec.decode bytes with
  | none =>
    have checked := SourceReplayDataFields.decode_contract bytes
    rw [parsed] at checked
    exact checked
  | some d =>
    exact congrArg SourceReplayDataFields.Fields.valid (SourceReplayDataFields.decoded_fields bytes d parsed)

theorem answer_eq (input : BitString) :
    SourceReplayEndpointRun.observed (result input) = SourceReplayRequest.answer input := by
  rw [result,SourceReplayEndpointRun.observed_result,← SourceReplayEndpointFields.answer_eq]
  unfold SourceReplayEndpointFields.answer
  rw [SourceReplayParser.parsed_fields]
  cases parsed : SourceReplayRequest.codec.decode input with
  | none =>
    rw [SourceReplayEndpointRun.answer_contract]
    simp only [good,parsed,Option.bind_none,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
  | some r =>
    have fields := SourceReplayEndpointLoad.parsed_saved input r parsed
    have params : parameters input = requestParameters r := by
      simp only [parameters,fields,List.headD_cons,List.length_replicate,requestParameters]
    have bytes : data input = r.data := congrArg SourceReplayParserState.Saved.data fields
    have prior : good input = SourceReplayDataFields.valid r.data := by
      simp only [good,parsed,Option.bind_some]
      exact (data_acceptance r.data).symm
    rw [params,bytes,prior]
    exact request_answer r

theorem input_bounds (input : BitString) :
    SourceReplayEndpointFields.count (data input) ≤ input.length ∧
      (SourceReplayEndpointFields.stream (parameters input).recover (data input)).length ≤ input.length ∧
      (parameters input).original ≤ input.length ∧ (parameters input).terminal ≤ input.length ∧
      (parameters input).witness.length ≤ input.length := by
  obtain ⟨dimension,bytes,witness⟩ := SourceReplayEndpointFields.outer_bounds input
  obtain ⟨count,stream,terminal⟩ := SourceReplayEndpointFields.input_bounds (parameters input).recover (data input)
  exact ⟨Nat.le_trans count bytes,Nat.le_trans stream bytes,dimension,Nat.le_trans terminal bytes,witness⟩

theorem fuel_bound (input : BitString) :
    fuel input ≤ input.length * (SourceReplayHistoryStack.allowance input.length +
      SourceReplayLoopMachine.allowance input.length (2 * input.length)) +
      (16 * input.length + 36) * input.length + 77 * input.length + 373 := by
  have loading := SourceReplayEndpointLoad.fuel_bound input
  have selecting := SourceReplayEndpointReady.fuel_bound (data input)
  have bytes : (data input).length ≤ input.length := (SourceReplayEndpointFields.outer_bounds input).2.1
  obtain ⟨count,stream,original,terminal,witness⟩ := input_bounds input
  have replay := SourceReplayEndpointRun.fuel_bound (parameters input) (SourceReplayEndpointFields.count (data input))
    (SourceReplayEndpointFields.stream (parameters input).recover (data input)) (parameters input).witness (good input)
  have size : (parameters input).witness.length + SourceReplayEndpointFields.count (data input) ≤ 2 * input.length := by omega
  have product := Nat.mul_le_mul count (SourceReplayLoopMachine.allowance_mono stream size)
  simp only [fuel,Nat.mul_add]
  omega

end PNP.Concrete.ResidualReduction.SourceReplayEndpointExecute
