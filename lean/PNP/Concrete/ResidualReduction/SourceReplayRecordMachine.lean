import PNP.Concrete.ResidualReduction.SourceReplayRecordState

/-! Literal complete record-prefix parsing. Every counter and saved field is
read from the input. These stages preserve suffixes and cumulative failure;
syntax does not certify that an arbitrary recorded reduction is sound. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayRecordMachine
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.SourceMatrixPacket
open PNP.Concrete.ResidualReduction.SourceReplayRecordState

private theorem header_input (input : BitString) :
    (SourceReplayFamily.header 0 input).core.core.core.input = (MatrixStrictHeader.scan input).rest := rfl
private theorem header_count (input : BitString) :
    (SourceReplayFamily.header 0 input).core.core.core.target = List.replicate (MatrixStrictHeader.scan input).count true := by
  change List.replicate (MatrixStrictHeader.scan input).count true ++ [] = _
  rw [List.append_nil]
private theorem family_input (n : Nat) (input : BitString) :
    (SourceReplayFamily.result n input).core.core.core.input = SourceReplayFamilyFields.rest n input := rfl

def dimensionSaved (input : BitString) (s : Saved) : Saved :=
  restrict {s with dimension := List.replicate (MatrixStrictHeader.scan input).count true}
    (MatrixStrictHeader.scan input).terminated
def dimensionBlock : Block 26 := .seq (core MatrixStrictHeader.block) <|
  .seq (.action (.copy 16 1)) <| .seq (guard 4) reset
def dimensionFuel (input : BitString) : Nat := MatrixStrictHeader.blockFuel input + 23
theorem dimension_exec (input : BitString) (s : Saved) :
    Exec dimensionBlock (work input s) (dimensionFuel input)
      (work (MatrixStrictHeader.scan input).rest (dimensionSaved input s)) := by
  let r := SourceReplayFamily.header 0 input
  let saved := {s with dimension := List.replicate (MatrixStrictHeader.scan input).count true}
  have first := wide_exec (SourceReplayFamily.header_exec 0 input) s
  have copied : Exec (.action (.copy (16 : Fin 26) 1)) (full r s) 1 (full r saved) := by
    have h : Exec (.action (.copy (16 : Fin 26) 1)) (full r s) 1
        (full r {s with dimension := r.core.core.core.target}) := .action _ _
    simpa only [r,saved,header_count] using h
  have read : (full r saved).get 4 = flag (MatrixStrictHeader.scan input).terminated := rfl
  have cost : dimensionFuel input = MatrixStrictHeader.blockFuel input + (1 + (2 + 20)) := by
    unfold dimensionFuel; omega
  simpa only [dimensionBlock,core,cost,r,saved,dimensionSaved,header_input,work,blank] using
    Exec.seq first (Exec.seq copied (Exec.seq (guard_exec 4 r saved _ [] read)
      (reset_exec r (restrict saved (MatrixStrictHeader.scan input).terminated))))

def sourceSaved (n : Nat) (input : BitString) (s : Saved) : Saved :=
  restrict {s with rows := List.replicate (SourceReplayFamilyFields.count input) true,source := SourceReplayFamilyFields.payload (n + 1) input}
    (SourceReplayFamilyFields.valid (n + 1) input)
def sourceBlock : Block 26 := .seq (.action (.copy 9 16)) <|
  .seq (.action (.push 9 true)) <| .seq (wide SourceReplayFamily.block) <|
  .seq (.action (.copy 17 15)) <| .seq (.action (.copy 18 8)) <| .seq (guard 5) reset
def sourceFuel (n : Nat) (input : BitString) : Nat := SourceReplayFamily.fuel (n + 1) input + 26
theorem source_exec (n : Nat) (input : BitString) (s : Saved) :
    let saved := {s with dimension := List.replicate n true}
    Exec sourceBlock (work input saved) (sourceFuel n input)
      (work (SourceReplayFamilyFields.rest (n + 1) input) (sourceSaved n input saved)) := by
  dsimp only
  let saved := {s with dimension := List.replicate n true}
  let r := SourceReplayFamily.result (n + 1) input
  let counted := {saved with rows := List.replicate (SourceReplayFamilyFields.count input) true}
  let stored := {counted with source := SourceReplayFamilyFields.payload (n + 1) input}
  have copied : Exec (.action (.copy (9 : Fin 26) 16)) (work input saved) 1
      (full (SourceReplayFamily.initial n input) saved) := .action _ _
  have pushed : Exec (.action (.push (9 : Fin 26) true))
      (full (SourceReplayFamily.initial n input) saved) 1
      (full (SourceReplayFamily.initial (n + 1) input) saved) := by
    simp only [SourceReplayFamily.initial,List.replicate_succ]
    exact .action _ _
  have rows : Exec (.action (.copy (17 : Fin 26) 15)) (full r saved) 1 (full r counted) := .action _ _
  have payload : Exec (.action (.copy (18 : Fin 26) 8)) (full r counted) 1 (full r stored) := .action _ _
  have read : (full r stored).get 5 = flag (SourceReplayFamilyFields.valid (n + 1) input) := rfl
  have cost : sourceFuel n input = 1 + (1 + (SourceReplayFamily.fuel (n + 1) input + (1 + (1 + (2 + 20))))) := by
    unfold sourceFuel; omega
  simpa only [sourceBlock,cost,r,saved,counted,stored,sourceSaved,family_input] using
    Exec.seq copied (Exec.seq pushed (Exec.seq (wide_exec (SourceReplayFamily.block_exec (n + 1) input) saved)
      (Exec.seq rows (Exec.seq payload (Exec.seq (guard_exec 5 r stored _ [] read)
        (reset_exec r (restrict stored (SourceReplayFamilyFields.valid (n + 1) input))))))))

def fixedPrepared (count : Nat) (input : BitString) : State :=
  setCore (blank input) {SourceReplayParserState.blank input [] with remaining := List.replicate count true}
def fixedResult (count : Nat) (input : BitString) : State :=
  setCore (blank input) (SourceReplayFixed.result (SourceReplayParserState.blank [] []) count input)
private theorem fixed_input (count : Nat) (input : BitString) :
    (fixedResult count input).core.core.core.input = input.drop count := rfl
theorem fixed_exec (count : Nat) (input : BitString) (s : Saved) (backup : BitString := []) :
    Exec (core SourceReplayFixed.block) (full (fixedPrepared count input) s backup)
      (SourceReplayFixed.fuel count input) (full (fixedResult count input) s backup) :=
  core_exec (fixedPrepared count input)
    (SourceReplayFixed.block_exec (SourceReplayParserState.blank [] []) count input) s backup

def weightsSaved (count : Nat) (input : BitString) (s : Saved) : Saved :=
  restrict {s with weights := input.take count} (decide (count ≤ input.length))
def weightsBlock : Block 26 := .seq (.action (.copy 2 17)) <|
  .seq (core SourceReplayFixed.block) <| .seq (.action (.copy 19 8)) <| .seq (guard 5) reset
def weightsFuel (count : Nat) (input : BitString) : Nat := SourceReplayFixed.fuel count input + 24
theorem weights_exec (count : Nat) (input : BitString) (s : Saved) :
    let saved := {s with rows := List.replicate count true}
    Exec weightsBlock (work input saved) (weightsFuel count input)
      (work (input.drop count) (weightsSaved count input saved)) := by
  dsimp only
  let saved := {s with rows := List.replicate count true}
  let r := fixedResult count input
  let stored := {saved with weights := input.take count}
  have prepared : Exec (.action (.copy (2 : Fin 26) 17)) (work input saved) 1
      (full (fixedPrepared count input) saved) := .action _ _
  have copied : Exec (.action (.copy (19 : Fin 26) 8)) (full r saved) 1 (full r stored) := .action _ _
  have read : (full r stored).get 5 = flag (decide (count ≤ input.length)) := by
    simp only [full,r,fixedResult,setCore,SourceReplayFixed.result,flag,decide_eq_true_eq]
    rfl
  have cost : weightsFuel count input = 1 + (SourceReplayFixed.fuel count input + (1 + (2 + 20))) := by
    unfold weightsFuel; omega
  simpa only [weightsBlock,cost,r,saved,stored,weightsSaved,fixed_input] using
    Exec.seq prepared (Exec.seq (fixed_exec count input saved)
      (Exec.seq copied (Exec.seq (guard_exec 5 r stored _ [] read)
        (reset_exec r (restrict stored (decide (count ≤ input.length)))))))

def pivotSaved (input : BitString) (s : Saved) : Saved :=
  restrict {s with pivot := List.replicate (MatrixStrictHeader.scan input).count true}
    (MatrixStrictHeader.scan input).terminated
def pivotBlock : Block 26 := .seq (core MatrixStrictHeader.block) <|
  .seq (.action (.copy 20 1)) <| .seq (guard 4) reset
def pivotFuel (input : BitString) : Nat := MatrixStrictHeader.blockFuel input + 23
theorem pivot_exec (input : BitString) (s : Saved) :
    Exec pivotBlock (work input s) (pivotFuel input)
      (work (MatrixStrictHeader.scan input).rest (pivotSaved input s)) := by
  let r := SourceReplayFamily.header 0 input
  let saved := {s with pivot := List.replicate (MatrixStrictHeader.scan input).count true}
  have first := wide_exec (SourceReplayFamily.header_exec 0 input) s
  have copied : Exec (.action (.copy (20 : Fin 26) 1)) (full r s) 1 (full r saved) := by
    have h : Exec (.action (.copy (20 : Fin 26) 1)) (full r s) 1
        (full r {s with pivot := r.core.core.core.target}) := .action _ _
    simpa only [r,saved,header_count] using h
  have read : (full r saved).get 4 = flag (MatrixStrictHeader.scan input).terminated := rfl
  have cost : pivotFuel input = MatrixStrictHeader.blockFuel input + (1 + (2 + 20)) := by
    unfold pivotFuel; omega
  simpa only [pivotBlock,core,cost,r,saved,pivotSaved,header_input,work,blank] using
    Exec.seq first (Exec.seq copied (Exec.seq (guard_exec 4 r saved _ [] read)
      (reset_exec r (restrict saved (MatrixStrictHeader.scan input).terminated))))

def tailSaved (n : Nat) (input : BitString) (s : Saved) : Saved :=
  restrict {s with tail := input.take n} (decide (n ≤ input.length))
def tailBlock : Block 26 := .seq (.action (.copy 2 16)) <|
  .seq (core SourceReplayFixed.block) <| .seq (.action (.copy 21 8)) <| .seq (guard 5) reset
def tailFuel (n : Nat) (input : BitString) : Nat := SourceReplayFixed.fuel n input + 24
theorem tail_exec (n : Nat) (input : BitString) (s : Saved) :
    let saved := {s with dimension := List.replicate n true}
    Exec tailBlock (work input saved) (tailFuel n input)
      (work (input.drop n) (tailSaved n input saved)) := by
  dsimp only
  let saved := {s with dimension := List.replicate n true}
  let r := fixedResult n input
  let stored := {saved with tail := input.take n}
  have prepared : Exec (.action (.copy (2 : Fin 26) 16)) (work input saved) 1
      (full (fixedPrepared n input) saved) := .action _ _
  have copied : Exec (.action (.copy (21 : Fin 26) 8)) (full r saved) 1 (full r stored) := .action _ _
  have read : (full r stored).get 5 = flag (decide (n ≤ input.length)) := by
    simp only [full,r,fixedResult,setCore,SourceReplayFixed.result,flag,decide_eq_true_eq]
    rfl
  have cost : tailFuel n input = 1 + (SourceReplayFixed.fuel n input + (1 + (2 + 20))) := by
    unfold tailFuel; omega
  simpa only [tailBlock,cost,r,saved,stored,tailSaved,fixed_input] using
    Exec.seq prepared (Exec.seq (fixed_exec n input saved)
      (Exec.seq copied (Exec.seq (guard_exec 5 r stored _ [] read)
        (reset_exec r (restrict stored (decide (n ≤ input.length)))))))

def outputSaved (n : Nat) (input : BitString) (s : Saved) : Saved :=
  restrict {s with outputRows := List.replicate (SourceReplayFamilyFields.count input) true,output := SourceReplayFamilyFields.payload n input} (SourceReplayFamilyFields.valid n input)
def outputBlock : Block 26 := .seq (.action (.copy 9 16)) <| .seq (wide SourceReplayFamily.block) <|
  .seq (.action (.copy 22 15)) <| .seq (.action (.copy 23 8)) <| .seq (guard 5) reset
def outputFuel (n : Nat) (input : BitString) : Nat := SourceReplayFamily.fuel n input + 25
theorem output_exec (n : Nat) (input : BitString) (s : Saved) :
    let saved := {s with dimension := List.replicate n true}
    Exec outputBlock (work input saved) (outputFuel n input)
      (work (SourceReplayFamilyFields.rest n input) (outputSaved n input saved)) := by
  dsimp only
  let saved := {s with dimension := List.replicate n true}
  let r := SourceReplayFamily.result n input
  let counted := {saved with outputRows := List.replicate (SourceReplayFamilyFields.count input) true}
  let stored := {counted with output := SourceReplayFamilyFields.payload n input}
  have prepared : Exec (.action (.copy (9 : Fin 26) 16)) (work input saved) 1
      (full (SourceReplayFamily.initial n input) saved) := .action _ _
  have rows : Exec (.action (.copy (22 : Fin 26) 15)) (full r saved) 1 (full r counted) := .action _ _
  have payload : Exec (.action (.copy (23 : Fin 26) 8)) (full r counted) 1 (full r stored) := .action _ _
  have read : (full r stored).get 5 = flag (SourceReplayFamilyFields.valid n input) := rfl
  have cost : outputFuel n input = 1 + (SourceReplayFamily.fuel n input + (1 + (1 + (2 + 20)))) := by
    unfold outputFuel; omega
  simpa only [outputBlock,cost,r,saved,counted,stored,outputSaved,family_input] using
    Exec.seq prepared (Exec.seq (wide_exec (SourceReplayFamily.block_exec n input) saved)
      (Exec.seq rows (Exec.seq payload (Exec.seq (guard_exec 5 r stored _ [] read)
        (reset_exec r (restrict stored (SourceReplayFamilyFields.valid n input)))))))


def rangeBlock : Block 26 := .seq (.action (.copy 25 0)) <| .seq clearWork <|
  .seq (.action (.copy 0 16)) <| .seq (.action (.push 0 true)) <|
  .seq (.action (.copy 2 20)) <| .seq (.action (.push 2 true)) <|
  .seq (core SourceReplayFixed.block) <| .seq (guard 5) <| .seq clearWork <|
  .seq (.action (.copy 0 25)) (.action (.clear 25))
def rangeFuel (n k : Nat) : Nat := SourceReplayFixed.fuel (k + 1) (List.replicate (n + 1) true) + 43
theorem range_exec (n k : Nat) (input : BitString) (s : Saved) :
    let saved := {s with dimension := List.replicate n true,pivot := List.replicate k true}
    Exec rangeBlock (work input saved) (rangeFuel n k)
      (work input (restrict saved (decide (k < n + 1)))) := by
  dsimp only
  let saved := {s with dimension := List.replicate n true,pivot := List.replicate k true}
  let word := List.replicate (n + 1) true
  let r := fixedResult (k + 1) word
  let good := decide (k < n + 1)
  have save : Exec (.action (.copy (25 : Fin 26) 0)) (work input saved) 1
      (full (blank input) saved input) := .action _ _
  have dim : Exec (.action (.copy (0 : Fin 26) 16)) (full (blank []) saved input) 1
      (full (blank (List.replicate n true)) saved input) := .action _ _
  have limit : Exec (.action (.push (0 : Fin 26) true))
      (full (blank (List.replicate n true)) saved input) 1 (full (blank word) saved input) := by
    simp only [word,List.replicate_succ]
    exact .action _ _
  have pivot : Exec (.action (.copy (2 : Fin 26) 20)) (full (blank word) saved input) 1
      (full (fixedPrepared k word) saved input) := .action _ _
  have request : Exec (.action (.push (2 : Fin 26) true)) (full (fixedPrepared k word) saved input) 1
      (full (fixedPrepared (k + 1) word) saved input) := by
    simp only [fixedPrepared,List.replicate_succ]
    exact .action _ _
  have read : (full r saved input).get 5 = flag good := by
    change (if k + 1 ≤ word.length then [true] else []) = flag (decide (k < n + 1))
    simp only [word,List.length_replicate,flag,decide_eq_true_eq]
    rfl
  have restore : Exec (.action (.copy (0 : Fin 26) 25))
      (full (blank []) (restrict saved good) input) 1
      (full (blank input) (restrict saved good) input) := .action _ _
  have finish : Exec (.action (.clear (25 : Fin 26)))
      (full (blank input) (restrict saved good) input) 1 (work input (restrict saved good)) := .action _ _
  have cost : rangeFuel n k = 1 + (17 + (1 + (1 + (1 + (1 +
      (SourceReplayFixed.fuel (k + 1) word + (2 + (17 + (1 + 1))))))))) := by
    unfold rangeFuel word; omega
  simpa only [rangeBlock,cost,saved,r,good] using
    Exec.seq save (Exec.seq (clearWork_exec (blank input) saved input)
      (Exec.seq dim (Exec.seq limit (Exec.seq pivot (Exec.seq request
        (Exec.seq (fixed_exec (k + 1) word saved input)
          (Exec.seq (guard_exec 5 r saved good input read)
            (Exec.seq (clearWork_exec r (restrict saved good) input) (Exec.seq restore finish)))))))))

def savedDimension (input : BitString) : Saved :=
  dimensionSaved input {emptySaved with valid := [true]}
def savedSource (input : BitString) : Saved :=
  sourceSaved (SourceReplayRecordFields.dimension input) (SourceReplayRecordFields.sourceInput input) (savedDimension input)
def savedWeights (input : BitString) : Saved :=
  weightsSaved (SourceReplayRecordFields.rows input) (SourceReplayRecordFields.afterSource input) (savedSource input)
def savedPivot (input : BitString) : Saved :=
  pivotSaved (SourceReplayRecordFields.pivotInput input) (savedWeights input)
def savedRange (input : BitString) : Saved :=
  restrict (savedPivot input) (decide (SourceReplayRecordFields.pivot input < SourceReplayRecordFields.dimension input + 1))
def savedTail (input : BitString) : Saved :=
  tailSaved (SourceReplayRecordFields.dimension input) (SourceReplayRecordFields.tailInput input) (savedRange input)
def savedOutput (input : BitString) : Saved :=
  outputSaved (SourceReplayRecordFields.dimension input) (SourceReplayRecordFields.outputInput input) (savedTail input)

private theorem combine (a b : Bool) :
    (if b then flag a else []) = flag (a && b) := by cases a <;> cases b <;> rfl
theorem savedOutput_capture (input : BitString) : savedOutput input = capture input := by
  dsimp only [savedOutput,savedTail,savedRange,savedPivot,savedWeights,savedSource,savedDimension,
    outputSaved,tailSaved,pivotSaved,weightsSaved,sourceSaved,dimensionSaved,
    restrict,capture,fromFields,SourceReplayRecordFields.capture]
  congr 1
  change (if SourceReplayFamilyFields.valid (SourceReplayRecordFields.dimension input) (SourceReplayRecordFields.outputInput input) then
    (if decide (SourceReplayRecordFields.dimension input ≤ (SourceReplayRecordFields.tailInput input).length) then
      (if decide (SourceReplayRecordFields.pivot input < SourceReplayRecordFields.dimension input + 1) then
        (if (MatrixStrictHeader.scan (SourceReplayRecordFields.pivotInput input)).terminated then
          (if decide (SourceReplayRecordFields.rows input ≤ (SourceReplayRecordFields.afterSource input).length) then
            (if SourceReplayFamilyFields.valid (SourceReplayRecordFields.dimension input + 1) (SourceReplayRecordFields.sourceInput input) then
              flag (MatrixStrictHeader.scan input).terminated else []) else []) else []) else []) else []) else []) =
    flag (SourceReplayRecordFields.valid input)
  simp only [combine,SourceReplayRecordFields.valid]

def block : Block 26 := .seq (.action (.push 24 true)) <|
  .seq dimensionBlock <| .seq sourceBlock <| .seq weightsBlock <| .seq pivotBlock <|
  .seq rangeBlock <| .seq tailBlock outputBlock
def fuel (input : BitString) : Nat :=
  1 + (dimensionFuel input +
    (sourceFuel (SourceReplayRecordFields.dimension input) (SourceReplayRecordFields.sourceInput input) +
      (weightsFuel (SourceReplayRecordFields.rows input) (SourceReplayRecordFields.afterSource input) +
        (pivotFuel (SourceReplayRecordFields.pivotInput input) +
          (rangeFuel (SourceReplayRecordFields.dimension input) (SourceReplayRecordFields.pivot input) +
            (tailFuel (SourceReplayRecordFields.dimension input) (SourceReplayRecordFields.tailInput input) +
              outputFuel (SourceReplayRecordFields.dimension input) (SourceReplayRecordFields.outputInput input)))))))
theorem block_exec (input : BitString) :
    Exec block (initial input) (fuel input) (result input) := by
  have dimension : Exec dimensionBlock (seeded input) (dimensionFuel input)
      (work (SourceReplayRecordFields.sourceInput input) (savedDimension input)) :=
    dimension_exec input {emptySaved with valid := [true]}
  have source : Exec sourceBlock (work (SourceReplayRecordFields.sourceInput input) (savedDimension input))
      (sourceFuel (SourceReplayRecordFields.dimension input) (SourceReplayRecordFields.sourceInput input))
      (work (SourceReplayRecordFields.afterSource input) (savedSource input)) :=
    source_exec (SourceReplayRecordFields.dimension input) (SourceReplayRecordFields.sourceInput input) (savedDimension input)
  have weights : Exec weightsBlock (work (SourceReplayRecordFields.afterSource input) (savedSource input))
      (weightsFuel (SourceReplayRecordFields.rows input) (SourceReplayRecordFields.afterSource input))
      (work (SourceReplayRecordFields.pivotInput input) (savedWeights input)) :=
    weights_exec (SourceReplayRecordFields.rows input) (SourceReplayRecordFields.afterSource input) (savedSource input)
  have pivot : Exec pivotBlock (work (SourceReplayRecordFields.pivotInput input) (savedWeights input))
      (pivotFuel (SourceReplayRecordFields.pivotInput input))
      (work (SourceReplayRecordFields.tailInput input) (savedPivot input)) :=
    pivot_exec (SourceReplayRecordFields.pivotInput input) (savedWeights input)
  have range : Exec rangeBlock (work (SourceReplayRecordFields.tailInput input) (savedPivot input))
      (rangeFuel (SourceReplayRecordFields.dimension input) (SourceReplayRecordFields.pivot input))
      (work (SourceReplayRecordFields.tailInput input) (savedRange input)) :=
    range_exec (SourceReplayRecordFields.dimension input) (SourceReplayRecordFields.pivot input)
      (SourceReplayRecordFields.tailInput input) (savedPivot input)
  have tail : Exec tailBlock (work (SourceReplayRecordFields.tailInput input) (savedRange input))
      (tailFuel (SourceReplayRecordFields.dimension input) (SourceReplayRecordFields.tailInput input))
      (work (SourceReplayRecordFields.outputInput input) (savedTail input)) :=
    tail_exec (SourceReplayRecordFields.dimension input) (SourceReplayRecordFields.tailInput input) (savedRange input)
  have output : Exec outputBlock (work (SourceReplayRecordFields.outputInput input) (savedTail input))
      (outputFuel (SourceReplayRecordFields.dimension input) (SourceReplayRecordFields.outputInput input))
      (work (SourceReplayRecordFields.rest input) (savedOutput input)) :=
    output_exec (SourceReplayRecordFields.dimension input) (SourceReplayRecordFields.outputInput input) (savedTail input)
  rw [savedOutput_capture] at output
  exact Exec.seq (seed_exec input) (Exec.seq dimension (Exec.seq source (Exec.seq weights
    (Exec.seq pivot (Exec.seq range (Exec.seq tail output))))))



private theorem family_cost (n : Nat) (input : BitString) (length : Nat)
    (dimensionBound : n ≤ length + 1) (inputBound : input.length ≤ length) :
    SourceReplayFamily.fuel n input ≤ (16 * (length + 1) + 36) * length + 3 * (length + 1) + 26 := by
  have checked := SourceReplayFamily.fuel_bound n input
  have coefficient : 16 * n + 36 ≤ 16 * (length + 1) + 36 := by omega
  have product := Nat.mul_le_mul coefficient inputBound
  omega
theorem fuel_bound (input : BitString) :
    fuel input ≤ 32 * input.length * input.length + 145 * input.length + 292 := by
  obtain ⟨hn,hr,hs,ha,hpi,hp,ht,ho,_⟩ := SourceReplayRecordFields.input_bounds input
  have dimension := MatrixStrictHeader.blockFuel_bound input
  have pivot := MatrixStrictHeader.blockFuel_bound (SourceReplayRecordFields.pivotInput input)
  have source := family_cost (SourceReplayRecordFields.dimension input + 1)
    (SourceReplayRecordFields.sourceInput input) input.length (Nat.add_le_add_right hn 1) hs
  have output := family_cost (SourceReplayRecordFields.dimension input)
    (SourceReplayRecordFields.outputInput input) input.length (Nat.le_trans hn (Nat.le_succ _)) ho
  have weights := SourceReplayFixed.fuel_bound (SourceReplayRecordFields.rows input)
    (SourceReplayRecordFields.afterSource input)
  have tail := SourceReplayFixed.fuel_bound (SourceReplayRecordFields.dimension input)
    (SourceReplayRecordFields.tailInput input)
  have range := SourceReplayFixed.fuel_bound (SourceReplayRecordFields.pivot input + 1)
    (List.replicate (SourceReplayRecordFields.dimension input + 1) true)
  simp only [List.length_replicate] at range
  unfold fuel dimensionFuel sourceFuel weightsFuel pivotFuel rangeFuel tailFuel outputFuel
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.one_mul] at *
  omega

private theorem result_flag (input : BitString) :
    (result input).get 24 = flag (SourceReplayRecordFields.valid input) := rfl
theorem parse_result (input : BitString) :
    match SourceEncoding.recordCodec.parse input with
    | none => (result input).get 24 = []
    | some (q,suffix) => result input = work suffix (fromFields (SourceReplayRecordFields.recordFields q) true) := by
  cases parsed : SourceEncoding.recordCodec.parse input with
  | none =>
    have bad := SourceReplayRecordFields.parse_contract input
    rw [parsed] at bad
    rw [result_flag,bad]
    rfl
  | some pair =>
    rcases pair with ⟨q,suffix⟩
    obtain ⟨good,fields,rest⟩ := SourceReplayRecordFields.parsed_fields input q suffix parsed
    simp only [SourceReplayRecordState.result,capture,good,fields,rest]
theorem parsed_exec (input : BitString) (q : SourceChain.StepRecord) (suffix : BitString)
    (parsed : SourceEncoding.recordCodec.parse input = some (q,suffix)) :
    Exec block (initial input) (fuel input)
      (work suffix (fromFields (SourceReplayRecordFields.recordFields q) true)) := by
  have contract := parse_result input
  rw [parsed] at contract
  rw [← contract]
  exact block_exec input


end PNP.Concrete.ResidualReduction.SourceReplayRecordMachine
