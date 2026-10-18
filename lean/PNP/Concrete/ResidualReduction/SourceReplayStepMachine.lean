import PNP.Concrete.ResidualReduction.SourceReplayStepApply

/-! One complete all-input literal replay transition. The machine parses the
actual record, validates the actual witness and computes the next witness.
It preserves the unread stream, clears scratch space, and leaves the original
witness untouched on rejection. This is a loop body, not the complete replay
runtime or a claim of semantic validity for arbitrary encoded records. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayStepMachine
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceReplayStepState

def mappedResult (recover : Bool) (cursor point : BitString) (answer : Option BitString) : Store 30 :=
  match answer with
  | none => work cursor point recover false
  | some output => work cursor output recover true
def prepared (recover : Bool) (q : StepRecord) (cursor point : BitString) : Store 30 :=
  full (SourceReplayState.blank [] []) (mapped (SourceReplayStepApply.fields q) point)
    (SourceReplayStepApply.fields q)
    ⟨point,recover,SourceReplayWitness.valid (width recover q.dimension) point,cursor⟩
def applicationFuel (recover : Bool) (q : StepRecord) (point : BitString) : Nat :=
  if SourceReplayWitness.valid (width recover q.dimension) point then
    SourceReplayStepApply.mapFuel recover q point + 32 else 31

private theorem witness_invalid (n : Nat) (point : BitString)
    (bad : (SourceEncoding.pointCodec n).decode point = none) :
    SourceReplayWitness.valid n point = false := by
  cases good : SourceReplayWitness.valid n point with
  | false => rfl
  | true =>
    obtain ⟨x,parsed⟩ := SourceReplayWitness.decode_complete n point
      ((SourceReplayWitness.valid_iff_width n point).mp good)
    rw [bad] at parsed
    cases parsed

theorem application_exec (recover : Bool) (q : StepRecord) (cursor point : BitString) :
    Exec SourceReplayStepApply.block (prepared recover q cursor point) (applicationFuel recover q point)
      (mappedResult recover cursor point (SourceReplayStepApply.mapOne recover q point)) := by
  cases recover with
  | false =>
    cases parsed : (SourceEncoding.pointCodec (q.dimension + 1)).decode point with
    | none =>
      have bad := witness_invalid (q.dimension + 1) point parsed
      simpa only [prepared,applicationFuel,width,Bool.false_eq_true,↓reduceIte,bad,
        SourceReplayStepApply.mapOne,SourceReplayTraversal.projectOne,parsed,Option.map_none,mappedResult]
        using SourceReplayStepApply.failure_exec (SourceReplayStepApply.fields q) point cursor false
    | some x =>
      have good := (SourceReplayWitness.valid_iff_width (q.dimension + 1) point).mpr
        (SourceReplayWitness.decode_width (q.dimension + 1) point x parsed)
      have bytes := (decode_eq_some_iff (SourceEncoding.pointCodec (q.dimension + 1)) point x).mp parsed
      have checked := SourceReplayStepApply.project_exec q x cursor
      rw [bytes] at checked
      simpa only [prepared,applicationFuel,width,Bool.false_eq_true,↓reduceIte,good,
        SourceReplayStepApply.start,SourceReplayStepApply.mapFuel,SourceReplayStepApply.mapOne,
        SourceReplayTraversal.projectOne,parsed,Option.map_some,mappedResult,SourceReplayStepApply.projected] using checked
  | true =>
    cases parsed : (SourceEncoding.pointCodec q.dimension).decode point with
    | none =>
      have bad := witness_invalid q.dimension point parsed
      simpa only [prepared,applicationFuel,width,↓reduceIte,bad,
        SourceReplayStepApply.mapOne,SourceReplayTraversal.recoverOne,parsed,Option.map_none,mappedResult,Bool.false_eq_true]
        using SourceReplayStepApply.failure_exec (SourceReplayStepApply.fields q) point cursor true
    | some z =>
      have good := (SourceReplayWitness.valid_iff_width q.dimension point).mpr
        (SourceReplayWitness.decode_width q.dimension point z parsed)
      have bytes := (decode_eq_some_iff (SourceEncoding.pointCodec q.dimension) point z).mp parsed
      have checked := SourceReplayStepApply.recover_exec q z cursor
      rw [bytes] at checked
      simpa only [prepared,applicationFuel,width,↓reduceIte,good,
        SourceReplayStepApply.start,SourceReplayStepApply.mapFuel,SourceReplayStepApply.mapOne,
        SourceReplayTraversal.recoverOne,parsed,Option.map_some,mappedResult,SourceReplayStepApply.recovered] using checked

def answer (recover : Bool) (input point : BitString) : Option (BitString × BitString) :=
  (SourceEncoding.recordCodec.parse input).bind fun (q,cursor) =>
    (SourceReplayStepApply.mapOne recover q point).map fun output => (cursor,output)
def result (recover : Bool) (input point : BitString) : Store 30 :=
  match SourceEncoding.recordCodec.parse input with
  | none => work (SourceReplayRecordFields.rest input) point recover false
  | some (q,cursor) => mappedResult recover cursor point (SourceReplayStepApply.mapOne recover q point)
def afterFuel (recover : Bool) (input point : BitString) : Nat :=
  match SourceEncoding.recordCodec.parse input with
  | none => 31
  | some (q,_) => applicationFuel recover q point
def block : Block 30 := .seq SourceReplayStepPrepare.block SourceReplayStepApply.block
def fuel (recover : Bool) (input point : BitString) : Nat :=
  SourceReplayStepPrepare.fuel recover input point + afterFuel recover input point

theorem block_exec (recover : Bool) (input point : BitString) :
    Exec block (initial input point recover) (fuel recover input point) (result recover input point) := by
  have first := SourceReplayStepPrepare.block_exec recover input point
  cases parsed : SourceEncoding.recordCodec.parse input with
  | none =>
    have bad := SourceReplayStepPrepare.invalid_record recover input point parsed
    have second := SourceReplayStepApply.failure_exec (SourceReplayRecordState.capture input) point
      (SourceReplayRecordFields.rest input) recover
    have state : SourceReplayStepPrepare.result recover input point =
        full (SourceReplayState.blank [] []) (mapped (SourceReplayRecordState.capture input) point)
          (SourceReplayRecordState.capture input)
          ⟨point,recover,false,SourceReplayRecordFields.rest input⟩ := by
      simp only [SourceReplayStepPrepare.result,SourceReplayStepPrepare.saved,bad]
    rw [state] at first
    simpa only [block,fuel,afterFuel,result,parsed] using Exec.seq first second
  | some pair =>
    rcases pair with ⟨q,cursor⟩
    obtain ⟨fields,rest,_,_⟩ := SourceReplayStepPrepare.parsed_capture input q cursor parsed
    have good := SourceReplayStepPrepare.parsed_valid recover input point q cursor parsed
    have state : SourceReplayStepPrepare.result recover input point = prepared recover q cursor point := by
      simp only [SourceReplayStepPrepare.result,SourceReplayStepPrepare.saved,fields,rest,good,
        prepared,SourceReplayStepApply.fields]
    rw [state] at first
    simpa only [block,fuel,afterFuel,result,parsed] using Exec.seq first (application_exec recover q cursor point)

theorem result_contract (recover : Bool) (input point : BitString) :
    result recover input point = match answer recover input point with
      | none => work (SourceReplayRecordFields.rest input) point recover false
      | some (cursor,output) => work cursor output recover true := by
  cases parsed : SourceEncoding.recordCodec.parse input with
  | none => simp only [result,answer,parsed,Option.bind_none]
  | some pair =>
    rcases pair with ⟨q,cursor⟩
    have rest := (SourceReplayStepPrepare.parsed_capture input q cursor parsed).2.1
    cases mapped : SourceReplayStepApply.mapOne recover q point <;>
      simp only [result,answer,parsed,mapped,Option.bind_some,Option.map_none,Option.map_some,mappedResult,rest]

theorem source_bounds (input : BitString) (q : StepRecord) (cursor : BitString)
    (parsed : SourceEncoding.recordCodec.parse input = some (q,cursor)) :
    q.dimension ≤ input.length ∧ q.source.length ≤ input.length ∧ cursor.length ≤ input.length := by
  obtain ⟨_,fields,rest⟩ := SourceReplayRecordFields.parsed_fields input q cursor parsed
  have dimension := congrArg SourceReplayRecordFields.Fields.dimension fields
  have rows := congrArg SourceReplayRecordFields.Fields.rows fields
  have bounds := SourceReplayRecordFields.input_bounds input
  change SourceReplayRecordFields.dimension input = q.dimension at dimension
  change SourceReplayRecordFields.rows input = q.source.length at rows
  exact ⟨by rw [← dimension]; exact bounds.1,
    by rw [← rows]; exact bounds.2.1,
    by rw [← rest]; exact bounds.2.2.2.2.2.2.2.2⟩

theorem applicationFuel_bound (recover : Bool) (q : StepRecord) (point : BitString) (L : Nat)
    (dimension : q.dimension ≤ L) (rows : q.source.length ≤ L) :
    applicationFuel recover q point ≤ (18 * L + 49) * L + 29 * L + 77 := by
  have bound := SourceReplayStepApply.mapFuel_bound recover q point L dimension rows
  unfold applicationFuel
  split <;> omega

theorem afterFuel_bound (recover : Bool) (input point : BitString) :
    afterFuel recover input point ≤ (18 * input.length + 49) * input.length + 29 * input.length + 77 := by
  cases parsed : SourceEncoding.recordCodec.parse input with
  | none => simp only [afterFuel,parsed]; omega
  | some pair =>
    rcases pair with ⟨q,cursor⟩
    obtain ⟨dimension,rows,_⟩ := source_bounds input q cursor parsed
    simpa only [afterFuel,parsed] using applicationFuel_bound recover q point input.length dimension rows

theorem fuel_bound (recover : Bool) (input point : BitString) :
    fuel recover input point ≤ 50 * input.length * input.length +
      228 * input.length + 4 * point.length + 406 := by
  have first := SourceReplayStepPrepare.fuel_bound recover input point
  have second := afterFuel_bound recover input point
  simp only [Nat.add_mul,Nat.mul_assoc] at first second ⊢
  unfold fuel
  omega

theorem answer_bounds (recover : Bool) (input point cursor output : BitString)
    (accepted : answer recover input point = some (cursor,output)) :
    cursor.length ≤ input.length ∧
      (if recover then output.length = point.length + 1 else output.length + 1 = point.length) := by
  cases parsed : SourceEncoding.recordCodec.parse input with
  | none => simp only [answer,parsed,Option.bind_none] at accepted; cases accepted
  | some pair =>
    rcases pair with ⟨q,rest⟩
    cases mapped : SourceReplayStepApply.mapOne recover q point with
    | none =>
      simp only [answer,parsed,Option.bind_some,mapped,Option.map_none] at accepted
      cases accepted
    | some value =>
      have same : rest = cursor ∧ value = output := by
        simpa only [answer,parsed,Option.bind_some,mapped,Option.map_some,Option.some.injEq,Prod.mk.injEq] using accepted
      rcases same with ⟨rfl,rfl⟩
      refine ⟨(source_bounds input q rest parsed).2.2,?_⟩
      cases recover with
      | false => exact SourceReplayTraversal.projectOne_length q point value mapped
      | true => exact SourceReplayTraversal.recoverOne_length q point value mapped

end PNP.Concrete.ResidualReduction.SourceReplayStepMachine
