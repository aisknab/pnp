import PNP.Concrete.ResidualReduction.SourceReplayParserState

/-! Complete literal outer-request parsing. The mode, original dimension,
serialized reduction and witness are extracted from the only populated input
register. All header and payload failures are accumulated and trailing input
is rejected. Inner history validation remains a separate phase. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayParser
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.SourceReplayParserState

def headerSaved (input : BitString) : Saved :=
  {modeSaved input with dimension := List.replicate (MatrixStrictHeader.scan input.tail).count true,valid := if (MatrixStrictHeader.scan input.tail).terminated then [true] else []}
def dataSaved (input : BitString) : Saved :=
  restrict {headerSaved input with data := SourceReplayBlob.bytes (SourceReplayRequest.first input.tail)}
    (SourceReplayBlob.valid (SourceReplayRequest.first input.tail))
def witnessSaved (input : BitString) : Saved :=
  restrict {dataSaved input with witness := SourceReplayBlob.bytes (SourceReplayRequest.second input.tail)}
    (SourceReplayBlob.valid (SourceReplayRequest.second input.tail))
def completedSaved (input : BitString) : Saved :=
  restrict (witnessSaved input) (SourceReplayRequest.suffix input.tail).isEmpty

def headers : Block 14 := .seq (core MatrixStrictHeader.block) saveHeader
theorem headers_exec (input : BitString) :
    Exec headers (work input.tail [] (modeSaved input)) (MatrixStrictHeader.blockFuel input.tail + 10)
      (work (SourceReplayRequest.first input.tail) [] (headerSaved input)) := by
  have read := core_exec (MatrixStrictHeader.block_exec input.tail (blank [] [])) (modeSaved input)
  have saved := saveHeader_exec (MatrixStrictHeader.result input.tail (blank [] [])) (modeSaved input)
  simpa only [headers,work,headerSaved,SourceReplayRequest.first,MatrixStrictHeader.result,blank,List.append_nil] using Exec.seq read saved

def readData : Block 14 := .seq (core SourceReplayBlob.block) dataFinish
theorem readData_exec (input : BitString) (s : Saved) :
    Exec readData (work input [] s) (SourceReplayBlob.fuel input + 11)
      (work (SourceReplayBlob.rest input) [] (restrict {s with data := SourceReplayBlob.bytes input} (SourceReplayBlob.valid input))) := by
  have read := core_exec (SourceReplayBlob.block_exec (blank [] []) input) s
  have saved := dataFinish_exec (SourceReplayBlob.result (blank [] []) input) s (SourceReplayBlob.valid input) rfl
  simpa only [readData,work,SourceReplayBlob.result,blank] using Exec.seq read saved

def readWitness : Block 14 := .seq (core SourceReplayBlob.block) witnessFinish
theorem readWitness_exec (input : BitString) (s : Saved) :
    Exec readWitness (work input [] s) (SourceReplayBlob.fuel input + 11)
      (work (SourceReplayBlob.rest input) [] (restrict {s with witness := SourceReplayBlob.bytes input} (SourceReplayBlob.valid input))) := by
  have read := core_exec (SourceReplayBlob.block_exec (blank [] []) input) s
  have saved := witnessFinish_exec (SourceReplayBlob.result (blank [] []) input) s (SourceReplayBlob.valid input) rfl
  simpa only [readWitness,work,SourceReplayBlob.result,blank] using Exec.seq read saved

def block : Block 14 := .seq modeBlock (.seq headers (.seq readData (.seq readWitness finish)))
def fuel (input : BitString) : Nat :=
  modeFuel input + ((MatrixStrictHeader.blockFuel input.tail + 10) +
    ((SourceReplayBlob.fuel (SourceReplayRequest.first input.tail) + 11) +
      ((SourceReplayBlob.fuel (SourceReplayRequest.second input.tail) + 11) + 3)))
def result (input : BitString) : Store 14 := work [] [] (completedSaved input)

theorem block_exec (input : BitString) : Exec block (initial input) (fuel input) (result input) := by
  have header := headers_exec input
  have data := readData_exec (SourceReplayRequest.first input.tail) (headerSaved input)
  have witness := readWitness_exec (SourceReplayRequest.second input.tail) (dataSaved input)
  have finished := finish_exec (SourceReplayRequest.suffix input.tail) (witnessSaved input)
  simpa only [block,fuel,result,completedSaved,witnessSaved,dataSaved,SourceReplayRequest.second,SourceReplayRequest.suffix] using
    Exec.seq (mode_exec input) (Exec.seq header (Exec.seq data (Exec.seq witness finished)))

theorem fuel_bound (input : BitString) : fuel input ≤ 30 * input.length + 83 := by
  have mode := modeFuel_bound input
  have header := MatrixStrictHeader.blockFuel_bound input.tail
  have first := SourceReplayRequest.first_bound input.tail
  have second := SourceReplayRequest.second_bound input.tail
  have data := SourceReplayBlob.fuel_bound (SourceReplayRequest.first input.tail)
  have witness := SourceReplayBlob.fuel_bound (SourceReplayRequest.second input.tail)
  have tailBound : input.tail.length ≤ input.length := by
    cases input <;> simp only [List.tail_nil,List.tail_cons,List.length_nil,List.length_cons] <;> omega
  unfold fuel
  omega

/-- A semantic observation of the protected output fields, not a machine
callback. The following equality identifies exactly which requests succeed. -/
def view (s : Saved) : Option SourceReplayRequest.Request :=
  if s.valid = [true] then some ⟨s.mode.headD false,s.dimension.length,s.data,s.witness⟩ else none

theorem parsed_fields (input : BitString) :
    view (completedSaved input) = SourceReplayRequest.codec.decode input := by
  cases input with
  | nil => rfl
  | cons mode tail =>
    cases h : (MatrixStrictHeader.scan tail).terminated <;>
      cases a : SourceReplayBlob.valid (SourceReplayRequest.first tail) <;>
      cases b : SourceReplayBlob.valid (SourceReplayRequest.second tail) <;>
      cases suffixEq : SourceReplayRequest.suffix tail <;>
      simp only [completedSaved,witnessSaved,dataSaved,headerSaved,modeSaved,emptySaved,restrict,
        view,List.tail_cons,List.take_succ_cons,List.take_zero,List.length_replicate,
        NativeNormalization.NativeBitCodec.Codec.decode,SourceReplayRequest.codec_parse,
        SourceReplayRequest.parse,SourceReplayRequest.valid,SourceReplayRequest.scanned,
        h,a,b,suffixEq,Bool.false_eq_true,↓reduceIte] <;> rfl

theorem all_input (input : BitString) :
    ∃ after, Exec block (initial input) (fuel input) after ∧
      after = work [] [] (completedSaved input) ∧
      view (completedSaved input) = SourceReplayRequest.codec.decode input ∧
      fuel input ≤ 30 * input.length + 83 :=
  ⟨result input,block_exec input,rfl,parsed_fields input,fuel_bound input⟩

end PNP.Concrete.ResidualReduction.SourceReplayParser
