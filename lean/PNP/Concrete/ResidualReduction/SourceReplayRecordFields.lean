import PNP.Concrete.ResidualReduction.SourceReplayFixed

/-! The exact raw fields of a serialized contraction record. Syntax requires
the stored source, one weight per source row, a pivot in range, a full tail
and the complete stored output family. It does not assume that an arbitrary
record is mathematically sound or that its output has the source row count. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayRecordFields
open PNP.Concrete PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain

def dimension (input : BitString) : Nat := (MatrixStrictHeader.scan input).count
def sourceInput (input : BitString) : BitString := (MatrixStrictHeader.scan input).rest
def rows (input : BitString) : Nat := SourceReplayFamilyFields.count (sourceInput input)
def afterSource (input : BitString) : BitString :=
  SourceReplayFamilyFields.rest (dimension input + 1) (sourceInput input)
def pivotInput (input : BitString) : BitString := (afterSource input).drop (rows input)
def pivot (input : BitString) : Nat := (MatrixStrictHeader.scan (pivotInput input)).count
def tailInput (input : BitString) : BitString := (MatrixStrictHeader.scan (pivotInput input)).rest
def outputInput (input : BitString) : BitString := (tailInput input).drop (dimension input)
def rest (input : BitString) : BitString := SourceReplayFamilyFields.rest (dimension input) (outputInput input)
def valid (input : BitString) : Bool :=
  (MatrixStrictHeader.scan input).terminated &&
    SourceReplayFamilyFields.valid (dimension input + 1) (sourceInput input) &&
    decide (rows input ≤ (afterSource input).length) &&
    (MatrixStrictHeader.scan (pivotInput input)).terminated &&
    decide (pivot input < dimension input + 1) &&
    decide (dimension input ≤ (tailInput input).length) &&
    SourceReplayFamilyFields.valid (dimension input) (outputInput input)

structure Fields where
  dimension : Nat
  rows : Nat
  source : BitString
  weights : BitString
  pivot : Nat
  tail : BitString
  outputRows : Nat
  output : BitString

def capture (input : BitString) : Fields :=
  ⟨dimension input,rows input,SourceReplayFamilyFields.payload (dimension input + 1) (sourceInput input),
    (afterSource input).take (rows input),pivot input,(tailInput input).take (dimension input),
    SourceReplayFamilyFields.count (outputInput input),SourceReplayFamilyFields.payload (dimension input) (outputInput input)⟩
def recordFields (q : StepRecord) : Fields :=
  ⟨q.dimension,q.source.length,SourceMatrixEncoding.familyBits q.source,
    (SourceEncoding.pointCodec q.source.length).encode q.step.weights,q.step.pivot.val,
    (SourceEncoding.pointCodec q.dimension).encode q.step.tail,q.step.output.length,
    SourceMatrixEncoding.familyBits q.step.output⟩

theorem valid_parts (input : BitString) (good : valid input = true) :
    (MatrixStrictHeader.scan input).terminated = true ∧
    SourceReplayFamilyFields.valid (dimension input + 1) (sourceInput input) = true ∧
    rows input ≤ (afterSource input).length ∧
    (MatrixStrictHeader.scan (pivotInput input)).terminated = true ∧
    pivot input < dimension input + 1 ∧
    dimension input ≤ (tailInput input).length ∧
    SourceReplayFamilyFields.valid (dimension input) (outputInput input) = true := by
  simpa only [valid,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using good

theorem assemble (input a b c d e suffix : BitString) (n : Nat)
    (F : Family (n + 1)) (w : Point F.length) (k : Fin (n + 1)) (v : Point n) (G : Family n)
    (hd : natCodec.parse input = some (n,a))
    (hs : (SourceEncoding.familyCodec (n + 1)).parse a = some (F,b))
    (hw : (SourceEncoding.pointCodec F.length).parse b = some (w,c))
    (hk : (finCodec (n + 1)).parse c = some (k,d))
    (hv : (SourceEncoding.pointCodec n).parse d = some (v,e))
    (ho : (SourceEncoding.familyCodec n).parse e = some (G,suffix)) :
    SourceEncoding.recordCodec.parse input = some (⟨n,F,⟨w,k,v,G⟩⟩,suffix) := by
  simp only [SourceEncoding.recordCodec,mappedCodec,SourceEncoding.dependentCodec,
    SourceEncoding.stepCodec,pairCodec,hd,hs,hw,hk,hv,ho,Option.bind_some,Option.map_some]

theorem valid_parse (input : BitString) (good : valid input = true) :
    ∃ q : StepRecord, SourceEncoding.recordCodec.parse input = some (q,rest input) ∧
      capture input = recordFields q := by
  obtain ⟨hd,hs,hw,hk,hbound,hv,ho⟩ := valid_parts input good
  obtain ⟨F,sourceParsed⟩ := SourceReplayFamilyFields.valid_parse (dimension input + 1) (sourceInput input) hs
  have sourceFields := (SourceReplayFamilyFields.parse_iff (sourceInput input) F (afterSource input)).mp sourceParsed
  have rowCount : rows input = F.length := sourceFields.2.1
  have weightsEnough : F.length ≤ (afterSource input).length := by rw [← rowCount]; exact hw
  obtain ⟨w,weightsParsed⟩ := SourceReplayFixed.valid_parse F.length (afterSource input) weightsEnough
  have weightsTail : (afterSource input).drop F.length = pivotInput input := by rw [← rowCount]; rfl
  rw [weightsTail] at weightsParsed
  let k : Fin (dimension input + 1) := ⟨pivot input,hbound⟩
  have pivotParsed : (finCodec (dimension input + 1)).parse (pivotInput input) = some (k,tailInput input) := by
    simp only [finCodec,MatrixStrictHeader.scan_parse,hk,↓reduceIte]
    have bound : (MatrixStrictHeader.scan (pivotInput input)).count < dimension input + 1 := hbound
    rw [dif_pos bound]
    rfl
  obtain ⟨v,tailParsed⟩ := SourceReplayFixed.valid_parse (dimension input) (tailInput input) hv
  obtain ⟨G,outputParsed⟩ := SourceReplayFamilyFields.valid_parse (dimension input) (outputInput input) ho
  have dimensionParsed : natCodec.parse input = some (dimension input,sourceInput input) := by
    change BitString.decodeLength input = _
    rw [MatrixStrictHeader.scan_parse,hd]
    rfl
  refine ⟨⟨dimension input,F,⟨w,k,v,G⟩⟩,
    assemble input (sourceInput input) (afterSource input) (pivotInput input) (tailInput input)
      (outputInput input) (rest input) (dimension input) F w k v G dimensionParsed sourceParsed
      weightsParsed pivotParsed tailParsed outputParsed,?_⟩
  have weightsFields := (SourceReplayFixed.parse_iff (afterSource input) w (pivotInput input)).mp weightsParsed
  have tailFields := (SourceReplayFixed.parse_iff (tailInput input) v (outputInput input)).mp tailParsed
  have outputFields := (SourceReplayFamilyFields.parse_iff (outputInput input) G (rest input)).mp outputParsed
  simp only [capture,recordFields,rowCount,sourceFields.2.2.1,← weightsFields.2.1,
    ← tailFields.2.1,outputFields.2.1,outputFields.2.2.1,k]

theorem input_bounds (input : BitString) :
    dimension input ≤ input.length ∧ rows input ≤ input.length ∧
      (sourceInput input).length ≤ input.length ∧ (afterSource input).length ≤ input.length ∧
      (pivotInput input).length ≤ input.length ∧ pivot input ≤ input.length ∧
      (tailInput input).length ≤ input.length ∧ (outputInput input).length ≤ input.length ∧
      (rest input).length ≤ input.length := by
  have head := MatrixStrictHeader.scan_size input
  have dimBound : dimension input ≤ input.length :=
    Nat.le_trans (Nat.le_add_right _ _) head
  have sourceBound : (sourceInput input).length ≤ input.length :=
    Nat.le_trans (Nat.le_add_left _ _) head
  have rowBound : rows input ≤ input.length :=
    Nat.le_trans (SourceReplayFamilyFields.count_bound (sourceInput input)) sourceBound
  have afterBound : (afterSource input).length ≤ input.length :=
    Nat.le_trans (SourceReplayFamilyFields.rest_bound (dimension input + 1) (sourceInput input)) sourceBound
  have pivotInputBound : (pivotInput input).length ≤ input.length := by
    change ((afterSource input).drop (rows input)).length ≤ input.length
    rw [List.length_drop]
    exact Nat.le_trans (Nat.sub_le _ _) afterBound
  have pivotHeader := MatrixStrictHeader.scan_size (pivotInput input)
  have pivotBound : pivot input ≤ input.length :=
    Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) pivotHeader) pivotInputBound
  have tailBound : (tailInput input).length ≤ input.length :=
    Nat.le_trans (Nat.le_trans (Nat.le_add_left _ _) pivotHeader) pivotInputBound
  have outputBound : (outputInput input).length ≤ input.length := by
    change ((tailInput input).drop (dimension input)).length ≤ input.length
    rw [List.length_drop]
    exact Nat.le_trans (Nat.sub_le _ _) tailBound
  have restBound : (rest input).length ≤ input.length :=
    Nat.le_trans (SourceReplayFamilyFields.rest_bound (dimension input) (outputInput input)) outputBound
  exact ⟨dimBound,rowBound,sourceBound,afterBound,pivotInputBound,pivotBound,tailBound,outputBound,restBound⟩

theorem canonical (q : StepRecord) (suffix : BitString) :
    let input := SourceEncoding.recordCodec.encode q ++ suffix
    valid input = true ∧ capture input = recordFields q ∧ rest input = suffix := by
  rcases q with ⟨n,F,s⟩
  rcases s with ⟨w,k,v,G⟩
  let outWord := (SourceEncoding.familyCodec n).encode G ++ suffix
  let tailWord := (SourceEncoding.pointCodec n).encode v ++ outWord
  let pivotWord := natural k.val ++ tailWord
  let weightWord := (SourceEncoding.pointCodec F.length).encode w ++ pivotWord
  let sourceWord := (SourceEncoding.familyCodec (n + 1)).encode F ++ weightWord
  let input := natural n ++ sourceWord
  have bytes : SourceEncoding.recordCodec.encode ⟨n,F,⟨w,k,v,G⟩⟩ ++ suffix = input := by
    change (natural n ++ ((SourceEncoding.familyCodec (n + 1)).encode F ++
      ((SourceEncoding.pointCodec F.length).encode w ++
        (natural k.val ++ ((SourceEncoding.pointCodec n).encode v ++ (SourceEncoding.familyCodec n).encode G))))) ++ suffix = _
    simp only [input,sourceWord,weightWord,pivotWord,tailWord,outWord,List.append_assoc]
  dsimp only
  rw [bytes]
  have sourceFields := SourceReplayFamilyFields.canonical F weightWord
  have outputFields := SourceReplayFamilyFields.canonical G suffix
  change SourceReplayFamilyFields.count sourceWord = F.length ∧
    SourceReplayFamilyFields.payload (n + 1) sourceWord = SourceMatrixEncoding.familyBits F ∧
    SourceReplayFamilyFields.rest (n + 1) sourceWord = weightWord ∧
    SourceReplayFamilyFields.valid (n + 1) sourceWord = true at sourceFields
  change SourceReplayFamilyFields.count outWord = G.length ∧
    SourceReplayFamilyFields.payload n outWord = SourceMatrixEncoding.familyBits G ∧
    SourceReplayFamilyFields.rest n outWord = suffix ∧
    SourceReplayFamilyFields.valid n outWord = true at outputFields
  have dimEq : dimension input = n := by simp only [dimension,input,MatrixStrictHeader.scan_canonical]
  have sourceEq : sourceInput input = sourceWord := by simp only [sourceInput,input,MatrixStrictHeader.scan_canonical]
  have rowsEq : rows input = F.length := by rw [rows,sourceEq]; exact sourceFields.1
  have afterEq : afterSource input = weightWord := by
    rw [afterSource,dimEq,sourceEq]
    exact sourceFields.2.2.1
  have pivotWordEq : pivotInput input = pivotWord := by
    rw [pivotInput,afterEq,rowsEq]
    exact List.drop_left' (SourceEncoding.point_length w)
  have pivotEq : pivot input = k.val := by simp only [pivot,pivotWordEq,pivotWord,MatrixStrictHeader.scan_canonical]
  have tailEq : tailInput input = tailWord := by simp only [tailInput,pivotWordEq,pivotWord,MatrixStrictHeader.scan_canonical]
  have outEq : outputInput input = outWord := by
    rw [outputInput,tailEq,dimEq]
    exact List.drop_left' (SourceEncoding.point_length v)
  have weightSize : F.length ≤ weightWord.length := by
    simp only [weightWord,List.length_append,SourceEncoding.point_length]
    omega
  have tailSize : n ≤ tailWord.length := by
    simp only [tailWord,List.length_append,SourceEncoding.point_length]
    omega
  refine ⟨?_,?_,?_⟩
  · simp only [valid,dimEq,sourceEq,rowsEq,afterEq,pivotWordEq,pivotEq,tailEq,outEq,
      input,pivotWord,MatrixStrictHeader.scan_canonical,sourceFields.2.2.2,outputFields.2.2.2,
      weightSize,tailSize,k.isLt,decide_true,Bool.true_and]
  · simp only [capture,dimEq,rowsEq,sourceEq,afterEq,pivotEq,tailEq,outEq,
      sourceFields.2.1,outputFields.1,outputFields.2.1,recordFields]
    rw [List.take_left' (SourceEncoding.point_length w),List.take_left' (SourceEncoding.point_length v)]
  · rw [rest,dimEq,outEq]
    exact outputFields.2.2.1

theorem parsed_fields (input : BitString) (q : StepRecord) (suffix : BitString)
    (parsed : SourceEncoding.recordCodec.parse input = some (q,suffix)) :
    valid input = true ∧ capture input = recordFields q ∧ rest input = suffix := by
  have bytes := SourceEncoding.recordCodec.sound input q suffix parsed
  rw [← bytes]
  exact canonical q suffix

theorem invalid_parse (input : BitString) (bad : valid input = false) :
    SourceEncoding.recordCodec.parse input = none := by
  cases parsed : SourceEncoding.recordCodec.parse input with
  | none => rfl
  | some pair =>
    rcases pair with ⟨q,suffix⟩
    have good := (parsed_fields input q suffix parsed).1
    rw [bad] at good
    cases good

theorem parse_contract (input : BitString) :
    match SourceEncoding.recordCodec.parse input with
    | none => valid input = false
    | some (q,suffix) => valid input = true ∧ capture input = recordFields q ∧ rest input = suffix := by
  cases parsed : SourceEncoding.recordCodec.parse input with
  | none =>
    cases flag : valid input with
    | false => rfl
    | true =>
      obtain ⟨q,accepted,_⟩ := valid_parse input flag
      rw [parsed] at accepted
      cases accepted
  | some pair => exact parsed_fields input pair.1 pair.2 parsed

end PNP.Concrete.ResidualReduction.SourceReplayRecordFields
