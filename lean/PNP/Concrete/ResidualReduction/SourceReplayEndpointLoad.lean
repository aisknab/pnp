import PNP.Concrete.ResidualReduction.SourceReplayEndpointState

/-! One closed input-loading machine: strict outer request, protected transfer,
strict inner saved-data reader and cumulative acceptance. The raw data buffer is
used only temporarily during transfer. No parsed object is supplied to the
all-input execution theorem. This is the loader, not the final replay machine. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointLoad
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceReplayEndpointState

def parserCore (s : SourceReplayParserState.Saved) : Store 35 :=
  extend14 (SourceReplayParserState.work [] [] s)
def handoff : Block 40 := .seq (.action (.copy 35 9)) <|
  .seq (.action (.copy 36 10)) <| .seq (.action (.copy 37 12)) <|
  .seq (.action (.copy 38 13)) <| .seq (.action (.copy 39 11)) <|
  .seq clearWork (.seq (.action (.copy 0 39)) (.action (.clear 39)))

theorem handoff_exec (p : SourceReplayParserState.Saved) :
    Exec handoff (full (parserCore p) emptySaved) 43 (work p.data (fromParser p)) := by
  let r := parserCore p
  let s1 := {emptySaved with mode := p.mode}
  let s2 := {s1 with dimension := p.dimension}
  let s3 := {s2 with witness := p.witness}
  let s4 := {s3 with valid := p.valid}
  let s5 := {s4 with terminal := p.data}
  have h1 := copy_saved_exec r emptySaved 0 9 p.mode s1 rfl rfl
  have h2 := copy_saved_exec r s1 1 10 p.dimension s2 rfl rfl
  have h3 := copy_saved_exec r s2 2 12 p.witness s3 rfl rfl
  have h4 := copy_saved_exec r s3 3 13 p.valid s4 rfl rfl
  have h5 := copy_saved_exec r s4 4 11 p.data s5 rfl rfl
  have clear := clearWork_exec r s5
  have restore : Exec (.action (.copy (0 : Fin 40) 39)) (work [] s5) 1 (work p.data s5) :=
    copy_core_exec (SourceReplayDataMachine.initial []) s5 0 4 p.data
      (SourceReplayDataMachine.initial p.data) rfl rfl
  have finish : Exec (.action (.clear (39 : Fin 40))) (work p.data s5) 1 (work p.data (fromParser p)) :=
    clear_saved_exec (SourceReplayDataMachine.initial p.data) s5 4 (fromParser p) rfl
  exact Exec.seq h1 (Exec.seq h2 (Exec.seq h3 (Exec.seq h4 (Exec.seq h5
    (Exec.seq clear (Exec.seq restore finish))))))

def outer : Block 40 := .seq (lift14 SourceReplayParser.block) handoff
theorem outer_exec (input : BitString) :
    Exec outer (initial input) (SourceReplayParser.fuel input + 43)
      (work (SourceReplayParser.completedSaved input).data (fromParser (SourceReplayParser.completedSaved input))) :=
  Exec.seq (lift14_exec (SourceReplayParser.block_exec input) emptySaved)
    (handoff_exec (SourceReplayParser.completedSaved input))

private theorem data_dimension (data : BitString) :
    (SourceReplayDataMachine.result data).get 30 = List.replicate (SourceReplayDataFields.dimension data) true :=
  Frame.get_frame (SourceReplayHistoryStack.finalState (SourceReplayDataFields.history data))
    (SourceReplayDataMachine.saved data).store 0
private theorem data_valid (data : BitString) :
    (SourceReplayDataMachine.result data).get 34 = SourceReplayRecordState.flag (SourceReplayDataFields.valid data) :=
  Frame.get_frame (SourceReplayHistoryStack.finalState (SourceReplayDataFields.history data))
    (SourceReplayDataMachine.saved data).store 4

def afterData (data : BitString) (s : Saved) : Saved :=
  restrict {s with terminal := List.replicate (SourceReplayDataFields.dimension data) true}
    (SourceReplayDataFields.valid data)
def dataFinish : Block 40 := .seq (.action (.copy 39 30)) (guard 34)
theorem dataFinish_exec (data : BitString) (s : Saved) :
    Exec dataFinish (full (SourceReplayDataMachine.result data) s) 3
      (full (SourceReplayDataMachine.result data) (afterData data s)) := by
  let r := SourceReplayDataMachine.result data
  let next := {s with terminal := List.replicate (SourceReplayDataFields.dimension data) true}
  have copied := copy_saved_exec r s 4 30 _ next (data_dimension data) rfl
  have read : (full r next).get 34 = SourceReplayRecordState.flag (SourceReplayDataFields.valid data) :=
    (Frame.get_core r next.store 34).trans (data_valid data)
  exact Exec.seq copied (guard_exec r next 34 (SourceReplayDataFields.valid data) read)

def inner : Block 40 := .seq (lift35 SourceReplayDataMachine.block) dataFinish
theorem inner_exec (data : BitString) (s : Saved) :
    Exec inner (work data s) (SourceReplayDataMachine.fuel data + 3)
      (full (SourceReplayDataMachine.result data) (afterData data s)) :=
  Exec.seq (lift35_exec (SourceReplayDataMachine.block_exec data) s) (dataFinish_exec data s)

def saved (input : BitString) : Saved :=
  afterData (SourceReplayParser.completedSaved input).data (fromParser (SourceReplayParser.completedSaved input))
def result (input : BitString) : Store 40 :=
  full (SourceReplayDataMachine.result (SourceReplayParser.completedSaved input).data) (saved input)
def block : Block 40 := .seq outer inner
def fuel (input : BitString) : Nat :=
  (SourceReplayParser.fuel input + 43) +
    (SourceReplayDataMachine.fuel (SourceReplayParser.completedSaved input).data + 3)
theorem block_exec (input : BitString) : Exec block (initial input) (fuel input) (result input) :=
  Exec.seq (outer_exec input)
    (inner_exec (SourceReplayParser.completedSaved input).data (fromParser (SourceReplayParser.completedSaved input)))

theorem fuel_bound (input : BitString) :
    fuel input ≤ input.length * SourceReplayHistoryStack.allowance input.length +
      (16 * input.length + 36) * input.length + 41 * input.length + 279 := by
  have outer := SourceReplayParser.fuel_bound input
  have bound := (SourceReplayEndpointFields.outer_bounds input).2.1
  have inner := SourceReplayDataMachine.fuel_bound (SourceReplayParser.completedSaved input).data
  have square := Nat.mul_le_mul bound bound
  have monotone : SourceReplayHistoryStack.allowance (SourceReplayParser.completedSaved input).data.length ≤
      SourceReplayHistoryStack.allowance input.length := by
    simp only [SourceReplayHistoryStack.allowance,Nat.mul_assoc]
    omega
  have histories := Nat.mul_le_mul bound monotone
  have families := Nat.mul_le_mul (show 16 * (SourceReplayParser.completedSaved input).data.length + 36 ≤
      16 * input.length + 36 by omega) bound
  unfold fuel
  omega

theorem parsed_saved (input : BitString) (r : SourceReplayRequest.Request)
    (parsed : SourceReplayRequest.codec.decode input = some r) :
    SourceReplayParser.completedSaved input =
      ⟨[r.recover],List.replicate r.dimension true,r.data,r.witness,[true]⟩ := by
  let p := SourceReplayParser.completedSaved input
  have matched := SourceReplayParser.parsed_fields input
  rw [parsed] at matched
  change SourceReplayParser.view p = some r at matched
  unfold SourceReplayParser.view at matched
  split at matched
  next good =>
    have same := Option.some.inj matched
    have dimension := congrArg SourceReplayRequest.Request.dimension same
    have data := congrArg SourceReplayRequest.Request.data same
    have witness := congrArg SourceReplayRequest.Request.witness same
    have mode : p.mode = [r.recover] := by
      change input.take 1 = _
      rw [← (decode_eq_some_iff SourceReplayRequest.codec input r).mp parsed]
      rfl
    have dim : p.dimension = List.replicate r.dimension true := by
      have count : p.dimension = List.replicate (MatrixStrictHeader.scan input.tail).count true := rfl
      change p.dimension.length = r.dimension at dimension
      rw [count,List.length_replicate] at dimension
      rw [count,dimension]
    change p.data = r.data at data
    change p.witness = r.witness at witness
    change p = _
    calc
      p = ⟨p.mode,p.dimension,p.data,p.witness,p.valid⟩ := rfl
      _ = ⟨[r.recover],List.replicate r.dimension true,r.data,r.witness,[true]⟩ := by
        rw [mode,dim,data,witness,good]
  next bad => cases matched

theorem loaded_saved (input : BitString) (r : SourceReplayRequest.Request) (d : SourceEncoding.ReductionData)
    (parsed : SourceReplayRequest.codec.decode input = some r)
    (decoded : SourceEncoding.dataCodec.decode r.data = some d) :
    result input = full (SourceReplayDataMachine.result r.data)
      ⟨[r.recover],List.replicate r.dimension true,r.witness,[true],List.replicate d.dimension true⟩ := by
  obtain ⟨dimension,_,_,good⟩ := SourceReplayEndpointFields.decoded_fields r.data d decoded
  simp only [result,saved,parsed_saved input r parsed,afterData,fromParser,restrict,dimension,good,↓reduceIte]

theorem invalid_outer (input : BitString) (bad : SourceReplayRequest.codec.decode input = none) :
    (result input).get 38 = [] := by
  have flag : (SourceReplayParser.completedSaved input).valid = [] := by
    cases possible : SourceReplayEndpointFields.outer_flag input with
    | inl empty => exact empty
    | inr good =>
      have checked := SourceReplayParser.parsed_fields input
      rw [bad] at checked
      simp only [SourceReplayParser.view,good,↓reduceIte] at checked
      cases checked
  simp only [result,read_valid,saved,afterData,fromParser,restrict,flag]
  cases SourceReplayDataFields.valid (SourceReplayParser.completedSaved input).data <;> rfl

theorem invalid_data (input : BitString) (r : SourceReplayRequest.Request)
    (parsed : SourceReplayRequest.codec.decode input = some r)
    (bad : SourceEncoding.dataCodec.decode r.data = none) : (result input).get 38 = [] := by
  have flag := SourceReplayDataFields.decode_contract r.data
  rw [bad] at flag
  simp only [result,read_valid,saved,parsed_saved input r parsed,afterData,fromParser,restrict,
    flag,Bool.false_eq_true,↓reduceIte]

theorem acceptance_contract (input : BitString) :
    (result input).get 38 = SourceReplayRecordState.flag
      ((SourceReplayRequest.codec.decode input).bind (fun r => SourceEncoding.dataCodec.decode r.data)).isSome := by
  cases parsed : SourceReplayRequest.codec.decode input with
  | none => simpa only [Option.bind_none,Option.isSome_none,SourceReplayRecordState.flag,Bool.false_eq_true,↓reduceIte] using invalid_outer input parsed
  | some r =>
    cases decoded : SourceEncoding.dataCodec.decode r.data with
    | none =>
      simpa only [Option.bind_some,decoded,Option.isSome_none,SourceReplayRecordState.flag,Bool.false_eq_true,↓reduceIte] using invalid_data input r parsed decoded
    | some d =>
      rw [loaded_saved input r d parsed decoded,read_valid]
      simp only [Option.bind_some,decoded,Option.isSome_some,SourceReplayRecordState.flag,↓reduceIte]

end PNP.Concrete.ResidualReduction.SourceReplayEndpointLoad
