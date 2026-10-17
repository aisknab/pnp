import PNP.Concrete.ResidualReduction.SourceReplayHistoryStack

/-! Strict decoding of the complete saved reduction data. The terminal
dimension, core and history are all read from the actual input. The history
is retained in both traversal orders, and acceptance requires end of input.
Syntactic acceptance is not a proof that an arbitrary history is a valid
reduction; that separate claim applies to the source-generated chain. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayDataFields
open PNP.Concrete PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceEncoding
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding

def dimension (input : BitString) : Nat := (MatrixStrictHeader.scan input).count
def coreInput (input : BitString) : BitString := (MatrixStrictHeader.scan input).rest
def rows (input : BitString) : Nat := SourceReplayFamilyFields.count (coreInput input)
def core (input : BitString) : BitString := SourceReplayFamilyFields.payload (dimension input) (coreInput input)
def historyInput (input : BitString) : BitString := SourceReplayFamilyFields.rest (dimension input) (coreInput input)
def history (input : BitString) : SourceReplayHistoryFields.Result :=
  SourceReplayHistoryFields.readHistory (historyInput input) []
def priorValid (input : BitString) : Bool :=
  (MatrixStrictHeader.scan input).terminated && SourceReplayFamilyFields.valid (dimension input) (coreInput input)
def valid (input : BitString) : Bool :=
  (priorValid input && (history input).valid) && (history input).input.isEmpty

structure Fields where
  dimension : Nat
  rows : Nat
  core : BitString
  forward : BitString
  reverse : BitString
  remaining : BitString
  valid : Bool

def capture (input : BitString) : Fields :=
  ⟨dimension input,rows input,core input,historyInput input,
    (history input).history,(history input).input,valid input⟩
def dataFields (d : ReductionData) : Fields :=
  ⟨d.dimension,d.core.length,familyBits d.core,(listCodec recordCodec).encode d.history,
    encodeSeq recordCodec.encode d.history.reverse,[],true⟩

theorem encode_bytes (d : ReductionData) :
    dataCodec.encode d = natural d.dimension ++
      ((familyCodec d.dimension).encode d.core ++ (listCodec recordCodec).encode d.history) := rfl

theorem canonical (d : ReductionData) : capture (dataCodec.encode d) = dataFields d := by
  have dim : dimension (dataCodec.encode d) = d.dimension := by
    simp only [dimension,encode_bytes,MatrixStrictHeader.scan_canonical]
  have rest : coreInput (dataCodec.encode d) =
      (familyCodec d.dimension).encode d.core ++ (listCodec recordCodec).encode d.history := by
    simp only [coreInput,encode_bytes,MatrixStrictHeader.scan_canonical]
  have header : (MatrixStrictHeader.scan (dataCodec.encode d)).terminated = true := by
    simp only [encode_bytes,MatrixStrictHeader.scan_canonical]
  obtain ⟨count,payload,cursor,good⟩ :=
    SourceReplayFamilyFields.canonical d.core ((listCodec recordCodec).encode d.history)
  have next : historyInput (dataCodec.encode d) = (listCodec recordCodec).encode d.history := by
    simpa only [historyInput,dim,rest] using cursor
  have parsed : history (dataCodec.encode d) =
      ⟨[],encodeSeq recordCodec.encode d.history.reverse,true⟩ := by
    simpa only [history,next,List.append_nil] using
      SourceReplayHistoryFields.prefix_canonical d.history [] []
  simp only [capture,dataFields,rows,core,dim,rest,count,payload,next,parsed,
    valid,priorValid,header,good,Bool.true_and,List.isEmpty_nil]

theorem valid_decode (input : BitString) (good : valid input = true) :
    ∃ d : ReductionData, dataCodec.decode input = some d := by
  have parts : ((MatrixStrictHeader.scan input).terminated = true ∧
      SourceReplayFamilyFields.valid (dimension input) (coreInput input) = true) ∧
      (history input).valid = true ∧ (history input).input.isEmpty = true := by
    simpa only [valid,priorValid,Bool.and_eq_true,and_assoc] using good
  have head : natCodec.parse input = some (dimension input,coreInput input) := by
    change BitString.decodeLength input = _
    rw [MatrixStrictHeader.scan_parse,parts.1.1]
    rfl
  obtain ⟨F,family⟩ := SourceReplayFamilyFields.valid_parse (dimension input) (coreInput input) parts.1.2
  have after : (familyCodec (dimension input)).parse (coreInput input) = some (F,historyInput input) := family
  have checked := SourceReplayHistoryFields.prefix_contract (historyInput input) []
  cases hp : (listCodec recordCodec).parse (historyInput input) with
  | none =>
    rw [hp] at checked
    have bad : (history input).valid = false := checked
    rw [bad] at parts
    cases parts.2.1
  | some pair =>
    rcases pair with ⟨records,suffix⟩
    rw [hp] at checked
    have fields : history input = ⟨suffix,encodeSeq recordCodec.encode records.reverse,true⟩ := by
      simpa only [history,List.append_nil] using checked
    have empty : suffix = [] := by
      have flag := parts.2.2
      rw [fields] at flag
      cases suffix with
      | nil => rfl
      | cons b tail => cases flag
    subst suffix
    have parsed : dataCodec.parse input = some (⟨dimension input,F,records⟩,[]) := by
      simp only [dataCodec,mappedCodec,dependentCodec,head,Option.bind_some,
        pairCodec,after,hp,Option.map_some]
    exact ⟨⟨dimension input,F,records⟩,by simp only [Codec.decode,parsed]⟩

theorem decoded_fields (input : BitString) (d : ReductionData)
    (decoded : dataCodec.decode input = some d) : capture input = dataFields d := by
  have bytes := (data_canonical input d).mp decoded
  rw [← bytes]
  exact canonical d

theorem decode_contract (input : BitString) :
    match dataCodec.decode input with
    | none => valid input = false
    | some d => capture input = dataFields d := by
  cases decoded : dataCodec.decode input with
  | none =>
    cases flag : valid input with
    | false => rfl
    | true =>
      obtain ⟨d,accepted⟩ := valid_decode input flag
      rw [decoded] at accepted
      cases accepted
  | some d => exact decoded_fields input d decoded

theorem valid_iff (input : BitString) :
    valid input = true ↔ ∃ d : ReductionData, dataCodec.decode input = some d := by
  constructor
  · exact valid_decode input
  · rintro ⟨d,decoded⟩
    exact congrArg Fields.valid (decoded_fields input d decoded)

theorem bounds (input : BitString) :
    dimension input ≤ input.length ∧ (coreInput input).length ≤ input.length ∧
      rows input ≤ input.length ∧ (core input).length ≤ input.length ∧
      (historyInput input).length ≤ input.length ∧
      (history input).input.length + (history input).history.length ≤ input.length := by
  have header := MatrixStrictHeader.scan_size input
  have dim : dimension input ≤ input.length := Nat.le_trans (Nat.le_add_right _ _) header
  have rest : (coreInput input).length ≤ input.length := Nat.le_trans (Nat.le_add_left _ _) header
  have rowBound := SourceReplayFamilyFields.count_bound (coreInput input)
  have bodyBound := SourceReplayFamilyFields.payload_bound (dimension input) (coreInput input)
  have tailBound := SourceReplayFamilyFields.rest_bound (dimension input) (coreInput input)
  have next : (historyInput input).length ≤ input.length := Nat.le_trans tailBound rest
  have reverseBound := SourceReplayHistoryFields.prefix_bounds (historyInput input) []
  simp only [List.length_nil,Nat.add_zero] at reverseBound
  exact ⟨dim,rest,Nat.le_trans rowBound rest,Nat.le_trans bodyBound rest,next,
    Nat.le_trans reverseBound.2 next⟩

end PNP.Concrete.ResidualReduction.SourceReplayDataFields
