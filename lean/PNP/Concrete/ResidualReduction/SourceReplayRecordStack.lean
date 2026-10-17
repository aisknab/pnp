import PNP.Concrete.ResidualReduction.SourceReplayRecordMachine

/-! Literal reconstruction of a parsed record from its actual saved fields.
The saved bytes are prepended to an existing history stack without changing
the input cursor, fields or validity flag. Instruction counts here are for
the register language; complete physical replay bounds remain separate. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayRecordStack
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceMatrixPacket
open PNP.Concrete.ResidualReduction.SourceReplayRecordState

def registers (input out : BitString) : State :=
  setCore (blank input) (SourceReplayParserState.blank input out)
def writing (input out : BitString) (s : Saved) (backup : BitString := []) : Store 26 :=
  full (registers input out) s backup
def bytes (s : Saved) : BitString :=
  s.dimension ++ [false] ++ s.rows ++ [false] ++ s.source ++ s.weights ++
    s.pivot ++ [false] ++ s.tail ++ s.outputRows ++ [false] ++ s.output
def fuel (s : Saved) : Nat := 8 * (bytes s).length + 56

def wordBlock (index : Fin 26) : Block 26 :=
  .seq (.action (.copy 5 index)) (core SourceChartedSuccessorWords.prepend)
theorem word_exec (index : Fin 26) (word out : BitString) (s : Saved) (backup : BitString)
    (read : (writing [] out s backup).get index = word) :
    Exec (wordBlock index) (writing [] out s backup) (8 * word.length + 10)
      (writing [] (word ++ out) s backup) := by
  let ready := setCore (blank []) (SourceChartedSuccessorWords.prependReady (SourceReplayParserState.blank [] []) word out)
  have copied : Exec (.action (.copy (5 : Fin 26) index)) (writing [] out s backup) 1
      (full ready s backup) := by
    have h : Exec (.action (.copy (5 : Fin 26) index)) (writing [] out s backup) 1
        (full (setCore (registers [] out) {(registers [] out).core.core.core with mode := (writing [] out s backup).get index}) s backup) := .action _ _
    rw [read] at h
    exact h
  have prepend : Exec (core SourceChartedSuccessorWords.prepend) (full ready s backup)
      (8 * word.length + 9) (writing [] (word ++ out) s backup) :=
    core_exec ready (SourceChartedSuccessorWords.prepend_exec (SourceReplayParserState.blank [] []) word out) s backup
  have cost : 8 * word.length + 10 = 1 + (8 * word.length + 9) := by omega
  simpa only [wordBlock,cost] using Exec.seq copied prepend

def headerBlock (index : Fin 26) : Block 26 :=
  .seq (.action (.push 8 false)) (wordBlock index)
theorem header_exec (index : Fin 26) (word out : BitString) (s : Saved) (backup : BitString)
    (read : (writing [] (false :: out) s backup).get index = word) :
    Exec (headerBlock index) (writing [] out s backup) (8 * word.length + 11)
      (writing [] (word ++ false :: out) s backup) := by
  have delimiter : Exec (.action (.push (8 : Fin 26) false)) (writing [] out s backup) 1
      (writing [] (false :: out) s backup) := .action _ _
  have cost : 8 * word.length + 11 = 1 + (8 * word.length + 10) := by omega
  simpa only [headerBlock,cost] using Exec.seq delimiter (word_exec index word (false :: out) s backup read)

def contentBlock : Block 26 := .seq (wordBlock 23) <| .seq (headerBlock 22) <|
  .seq (wordBlock 21) <| .seq (headerBlock 20) <| .seq (wordBlock 19) <|
  .seq (wordBlock 18) <| .seq (headerBlock 17) (headerBlock 16)
def contentFuel (s : Saved) : Nat := 8 * (bytes s).length + 52
theorem content_exec (out : BitString) (s : Saved) (backup : BitString) :
    Exec contentBlock (writing [] out s backup) (contentFuel s)
      (writing [] (bytes s ++ out) s backup) := by
  let a := s.output ++ out
  let b := s.outputRows ++ false :: a
  let c := s.tail ++ b
  let d := s.pivot ++ false :: c
  let e := s.weights ++ d
  let f := s.source ++ e
  let g := s.rows ++ false :: f
  have first := word_exec 23 s.output out s backup rfl
  have second := header_exec 22 s.outputRows a s backup rfl
  have third := word_exec 21 s.tail b s backup rfl
  have fourth := header_exec 20 s.pivot c s backup rfl
  have fifth := word_exec 19 s.weights d s backup rfl
  have sixth := word_exec 18 s.source e s backup rfl
  have seventh := header_exec 17 s.rows f s backup rfl
  have eighth := header_exec 16 s.dimension g s backup rfl
  have cost : contentFuel s = (8 * s.output.length + 10) + ((8 * s.outputRows.length + 11) +
      ((8 * s.tail.length + 10) + ((8 * s.pivot.length + 11) + ((8 * s.weights.length + 10) +
        ((8 * s.source.length + 10) + ((8 * s.rows.length + 11) + (8 * s.dimension.length + 11))))))) := by
    simp only [contentFuel,bytes,List.length_append,List.length_cons,List.length_nil,Nat.mul_add]
    omega
  simpa only [contentBlock,cost,a,b,c,d,e,f,g,bytes,List.append_assoc,List.cons_append,List.nil_append] using
    Exec.seq first (Exec.seq second (Exec.seq third (Exec.seq fourth
      (Exec.seq fifth (Exec.seq sixth (Exec.seq seventh eighth))))))

def block : Block 26 := .seq (.action (.copy 25 0)) <| .seq (.action (.clear 0)) <|
  .seq contentBlock <| .seq (.action (.copy 0 25)) (.action (.clear 25))
theorem block_exec (input out : BitString) (s : Saved) :
    Exec block (writing input out s) (fuel s) (writing input (bytes s ++ out) s) := by
  have save : Exec (.action (.copy (25 : Fin 26) 0)) (writing input out s) 1
      (writing input out s input) := .action _ _
  have clear : Exec (.action (.clear (0 : Fin 26))) (writing input out s input) 1
      (writing [] out s input) := .action _ _
  have restore : Exec (.action (.copy (0 : Fin 26) 25)) (writing [] (bytes s ++ out) s input) 1
      (writing input (bytes s ++ out) s input) := .action _ _
  have finish : Exec (.action (.clear (25 : Fin 26))) (writing input (bytes s ++ out) s input) 1
      (writing input (bytes s ++ out) s) := .action _ _
  have cost : fuel s = 1 + (1 + (contentFuel s + (1 + 1))) := by unfold fuel contentFuel; omega
  simpa only [block,cost] using Exec.seq save (Exec.seq clear
    (Exec.seq (content_exec out s input) (Exec.seq restore finish)))

theorem bytes_record (q : SourceChain.StepRecord) (good : Bool) :
    bytes (fromFields (SourceReplayRecordFields.recordFields q) good) = SourceEncoding.recordCodec.encode q := by
  rcases q with ⟨n,F,w,k,v,G⟩
  change bytes (fromFields (SourceReplayRecordFields.recordFields ⟨n,F,⟨w,k,v,G⟩⟩) good) =
    natural n ++ ((SourceEncoding.familyCodec (n + 1)).encode F ++
      ((SourceEncoding.pointCodec F.length).encode w ++
        (natural k.val ++ ((SourceEncoding.pointCodec n).encode v ++ (SourceEncoding.familyCodec n).encode G))))
  rw [SourceReplayFamilyFields.encode_bytes,SourceReplayFamilyFields.encode_bytes]
  simp only [bytes,fromFields,SourceReplayRecordFields.recordFields,natural,List.append_assoc]

theorem captured_prefix (input : BitString) (good : SourceReplayRecordFields.valid input = true) :
    bytes (capture input) ++ SourceReplayRecordFields.rest input = input := by
  obtain ⟨q,parsed,fields⟩ := SourceReplayRecordFields.valid_parse input good
  rw [capture,fields,bytes_record]
  exact SourceEncoding.recordCodec.sound input q (SourceReplayRecordFields.rest input) parsed
theorem captured_fuel_bound (input : BitString) (good : SourceReplayRecordFields.valid input = true) :
    fuel (capture input) ≤ 8 * input.length + 56 := by
  have length := congrArg List.length (captured_prefix input good)
  simp only [List.length_append] at length
  unfold fuel
  omega


def stacked (s : Store 26) (history : BitString) : Store 27 := Frame.join s (.cons history .nil)
def lift (b : Block 26) : Block 27 := Frame.block 1 b
def appendBlock : Block 27 := .seq (.action (.copy 8 26)) <|
  .seq (lift block) <| .seq (.action (.copy 26 8)) (.action (.clear 8))
theorem append_exec (input history : BitString) (s : Saved) :
    Exec appendBlock (stacked (writing input [] s) history) (fuel s + 3)
      (stacked (writing input [] s) (bytes s ++ history)) := by
  have loaded : Exec (.action (.copy (8 : Fin 27) 26)) (stacked (writing input [] s) history) 1
      (stacked (writing input history s) history) := .action _ _
  have serialized : Exec (lift block) (stacked (writing input history s) history) (fuel s)
      (stacked (writing input (bytes s ++ history) s) history) :=
    Frame.execution (block_exec input history s) (.cons history .nil)
  have stored : Exec (.action (.copy (26 : Fin 27) 8))
      (stacked (writing input (bytes s ++ history) s) history) 1
      (stacked (writing input (bytes s ++ history) s) (bytes s ++ history)) := .action _ _
  have cleared : Exec (.action (.clear (8 : Fin 27)))
      (stacked (writing input (bytes s ++ history) s) (bytes s ++ history)) 1
      (stacked (writing input [] s) (bytes s ++ history)) := .action _ _
  have cost : fuel s + 3 = 1 + (fuel s + (1 + 1)) := by omega
  simpa only [appendBlock,cost] using Exec.seq loaded (Exec.seq serialized (Exec.seq stored cleared))

def select : Block 27 := .branch 24 .skip .skip appendBlock
def oneBlock : Block 27 := .seq (lift SourceReplayRecordMachine.block) select
def oneFuel (input : BitString) : Nat := SourceReplayRecordMachine.fuel input + 1 +
  (if SourceReplayRecordFields.valid input then fuel (capture input) + 3 else 1)
def inputState (input history : BitString) : Store 27 := stacked (SourceReplayRecordState.initial input) history
def outputState (input history : BitString) : Store 27 :=
  stacked (SourceReplayRecordState.result input)
    (if SourceReplayRecordFields.valid input then bytes (capture input) ++ history else history)

theorem one_exec (input history : BitString) :
    Exec oneBlock (inputState input history) (oneFuel input) (outputState input history) := by
  have first : Exec (lift SourceReplayRecordMachine.block) (inputState input history)
      (SourceReplayRecordMachine.fuel input) (stacked (SourceReplayRecordState.result input) history) :=
    Frame.execution (SourceReplayRecordMachine.block_exec input) (.cons history .nil)
  cases valid : SourceReplayRecordFields.valid input with
  | false =>
    have read : (stacked (SourceReplayRecordState.result input) history).get 24 = [] := by
      change flag (SourceReplayRecordFields.valid input) = []
      rw [valid]
      rfl
    have cost : oneFuel input = SourceReplayRecordMachine.fuel input + (1 + 1) := by
      simp only [oneFuel,valid,Bool.false_eq_true,↓reduceIte]
    simpa only [oneBlock,select,cost,outputState,valid,Bool.false_eq_true,↓reduceIte] using
      Exec.seq first (Exec.empty read (.skip _))
  | true =>
    have read : (stacked (SourceReplayRecordState.result input) history).get 24 = [true] := by
      change flag (SourceReplayRecordFields.valid input) = [true]
      rw [valid]
      rfl
    have last : Exec appendBlock (stacked (SourceReplayRecordState.result input) history)
        (fuel (capture input) + 3)
        (stacked (SourceReplayRecordState.result input) (bytes (capture input) ++ history)) :=
      append_exec (SourceReplayRecordFields.rest input) history (capture input)
    have cost : oneFuel input = SourceReplayRecordMachine.fuel input + (1 + (fuel (capture input) + 3)) := by
      simp only [oneFuel,valid,↓reduceIte]
      omega
    simpa only [oneBlock,select,cost,outputState,valid,↓reduceIte] using Exec.seq first (Exec.one read last)

theorem oneFuel_bound (input : BitString) :
    oneFuel input ≤ 32 * input.length * input.length + 153 * input.length + 352 := by
  have parser := SourceReplayRecordMachine.fuel_bound input
  cases valid : SourceReplayRecordFields.valid input with
  | false =>
    simp only [oneFuel,valid,Bool.false_eq_true,↓reduceIte]
    omega
  | true =>
    have writer := captured_fuel_bound input valid
    simp only [oneFuel,valid,↓reduceIte]
    omega

theorem one_parse_contract (input history : BitString) :
    match SourceEncoding.recordCodec.parse input with
    | none => outputState input history = stacked (SourceReplayRecordState.result input) history
    | some (q,suffix) => outputState input history =
        stacked (work suffix (fromFields (SourceReplayRecordFields.recordFields q) true))
          (SourceEncoding.recordCodec.encode q ++ history) := by
  cases parsed : SourceEncoding.recordCodec.parse input with
  | none =>
    have bad := SourceReplayRecordFields.parse_contract input
    rw [parsed] at bad
    simp only [outputState,bad,Bool.false_eq_true,↓reduceIte]
  | some pair =>
    rcases pair with ⟨q,suffix⟩
    have result := SourceReplayRecordMachine.parse_result input
    rw [parsed] at result
    obtain ⟨good,fields,_⟩ := SourceReplayRecordFields.parsed_fields input q suffix parsed
    simp only [outputState,good,↓reduceIte,result,capture,fields,bytes_record]

theorem one_parsed_exec (input history : BitString) (q : SourceChain.StepRecord) (suffix : BitString)
    (parsed : SourceEncoding.recordCodec.parse input = some (q,suffix)) :
    Exec oneBlock (inputState input history) (oneFuel input)
      (stacked (work suffix (fromFields (SourceReplayRecordFields.recordFields q) true))
        (SourceEncoding.recordCodec.encode q ++ history)) := by
  have contract := one_parse_contract input history
  rw [parsed] at contract
  rw [← contract]
  exact one_exec input history


end PNP.Concrete.ResidualReduction.SourceReplayRecordStack
