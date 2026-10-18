import PNP.Concrete.ResidualReduction.SourceReplayStepState

/-! All-input preparation of a literal witness step. The raw record parser
and exact-width witness reader both contribute to one cumulative flag.
The next phase receives copied actual fields, never a supplied parsed record. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayStepPrepare
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.SourceReplayStepState

def required (recover : Bool) (input : BitString) : Nat :=
  width recover (SourceReplayRecordFields.dimension input)
def valid (recover : Bool) (input point : BitString) : Bool :=
  SourceReplayRecordFields.valid input && SourceReplayWitness.valid (required recover input) point
def captured (recover : Bool) (input point : BitString) : Saved :=
  ⟨point,recover,SourceReplayRecordFields.valid input,SourceReplayRecordFields.rest input⟩
def saved (recover : Bool) (input point : BitString) : Saved :=
  ⟨point,recover,valid recover input point,SourceReplayRecordFields.rest input⟩
def result (recover : Bool) (input point : BitString) : Store 30 :=
  full (SourceReplayState.blank [] []) (mapped (SourceReplayRecordState.capture input) point)
    (SourceReplayRecordState.capture input) (saved recover input point)

def block : Block 30 := .seq (lift26 SourceReplayRecordMachine.block) <|
  .seq captureBlock <| .seq witnessSeed <| .seq (core9 SourceReplayWitness.block) <|
  .seq (guard 5) <| .seq clear9 mapSetup
def fuel (recover : Bool) (input point : BitString) : Nat :=
  SourceReplayRecordMachine.fuel input + SourceReplayWitness.fuel (required recover input) point + 24

theorem block_exec (recover : Bool) (input point : BitString) :
    Exec block (initial input point recover) (fuel recover input point) (result recover input point) := by
  let f := SourceReplayRecordState.capture input
  let empty : Saved := ⟨point,recover,false,[]⟩
  let captured := captured recover input point
  let saved := saved recover input point
  let n := required recover input
  let r := SourceReplayWitness.result (SourceReplayState.blank [] []) n point
  have parsed : Exec (lift26 SourceReplayRecordMachine.block) (initial input point recover)
      (SourceReplayRecordMachine.fuel input)
      (full (SourceReplayState.blank (SourceReplayRecordFields.rest input) []) emptyReplay f empty) :=
    lift26_exec (SourceReplayRecordMachine.block_exec input) empty
  have stashed : Exec captureBlock
      (full (SourceReplayState.blank (SourceReplayRecordFields.rest input) []) emptyReplay f empty) 2
      (full (SourceReplayState.blank (SourceReplayRecordFields.rest input) []) emptyReplay f captured) :=
    capture_exec _ emptyReplay f empty (SourceReplayRecordFields.valid input) rfl
  have seed : Exec witnessSeed
      (full (SourceReplayState.blank (SourceReplayRecordFields.rest input) []) emptyReplay f captured) 4
      (full {SourceReplayState.blank [] [] with input := point,remaining := List.replicate n true} emptyReplay f captured) :=
    witnessSeed_exec (SourceReplayRecordFields.rest input) (SourceReplayRecordFields.dimension input) f captured rfl
  have witness : Exec (core9 SourceReplayWitness.block)
      (full {SourceReplayState.blank [] [] with input := point,remaining := List.replicate n true} emptyReplay f captured)
      (SourceReplayWitness.fuel n point) (full r emptyReplay f captured) :=
    core9_exec (SourceReplayWitness.block_exec (SourceReplayState.blank [] []) n point) emptyReplay f captured
  have checked : Exec (guard 5) (full r emptyReplay f captured) 2 (full r emptyReplay f saved) :=
    guard_exec 5 r emptyReplay f captured (SourceReplayWitness.valid n point) rfl
  have clear : Exec clear9 (full r emptyReplay f saved) 10 (full (SourceReplayState.blank [] []) emptyReplay f saved) :=
    clear9_exec r emptyReplay f saved
  have setup := mapSetup_exec f saved
  have cost : fuel recover input point = SourceReplayRecordMachine.fuel input +
      (2 + (4 + (SourceReplayWitness.fuel n point + (2 + (10 + 6))))) := by
    dsimp only [fuel,n]
    omega
  simpa only [block,cost,result,f,saved,SourceReplayStepPrepare.saved] using Exec.seq parsed (Exec.seq stashed
    (Exec.seq seed (Exec.seq witness (Exec.seq checked (Exec.seq clear setup)))))

theorem required_bound (recover : Bool) (input : BitString) :
    required recover input ≤ input.length + 1 := by
  have bound := (SourceReplayRecordFields.input_bounds input).1
  cases recover <;> simp only [required,width,Bool.false_eq_true,↓reduceIte] <;> omega

theorem fuel_bound (recover : Bool) (input point : BitString) :
    fuel recover input point ≤ 32 * input.length * input.length +
      150 * input.length + 4 * point.length + 329 := by
  have parser := SourceReplayRecordMachine.fuel_bound input
  have witness := SourceReplayWitness.fuel_bound (required recover input) point
  have dimension := required_bound recover input
  unfold fuel
  omega

theorem parsed_capture (input : BitString) (q : SourceChain.StepRecord) (suffix : BitString)
    (parsed : SourceEncoding.recordCodec.parse input = some (q,suffix)) :
    SourceReplayRecordState.capture input =
      SourceReplayRecordState.fromFields (SourceReplayRecordFields.recordFields q) true ∧
      SourceReplayRecordFields.rest input = suffix ∧
      SourceReplayRecordFields.dimension input = q.dimension ∧
      SourceReplayRecordFields.valid input = true := by
  obtain ⟨good,fields,cursor⟩ := SourceReplayRecordFields.parsed_fields input q suffix parsed
  have dimension := congrArg SourceReplayRecordFields.Fields.dimension fields
  exact ⟨by rw [SourceReplayRecordState.capture,fields,good],cursor,dimension,good⟩

theorem invalid_record (recover : Bool) (input point : BitString)
    (bad : SourceEncoding.recordCodec.parse input = none) : valid recover input point = false := by
  have checked := SourceReplayRecordFields.parse_contract input
  rw [bad] at checked
  simp only [valid,checked,Bool.false_and]

theorem parsed_valid (recover : Bool) (input point : BitString) (q : SourceChain.StepRecord) (suffix : BitString)
    (parsed : SourceEncoding.recordCodec.parse input = some (q,suffix)) :
    valid recover input point = SourceReplayWitness.valid (width recover q.dimension) point := by
  obtain ⟨_,_,dimension,good⟩ := parsed_capture input q suffix parsed
  simp only [valid,required,dimension,good,Bool.true_and]

end PNP.Concrete.ResidualReduction.SourceReplayStepPrepare
