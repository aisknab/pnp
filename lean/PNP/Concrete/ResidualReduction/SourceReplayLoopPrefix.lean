import PNP.Concrete.ResidualReduction.SourceReplayLoopMachine

/-! Actual encoded-count entry to the replay loop. The unary count is read
from the input; an unterminated header cannot enter replay. Prefix semantics
preserve trailing bytes for the outer strict data/request boundary. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayLoopPrefix
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceReplayLoopFields
open PNP.Concrete.ResidualReduction.SourceReplayLoopMachine

def pack (r : SourceMatrixPacket.State) (s : SourceReplayStepState.Saved) (count : Nat) : Store 31 :=
  full (SourceReplayStepState.enclose (SourceReplayRecordState.full r SourceReplayRecordState.emptySaved) s) count
def initial (recover : Bool) (input point : BitString) : Store 31 := work 0 input point recover false
def headerState (recover : Bool) (input point : BitString) : Store 31 :=
  pack (SourceReplayFamily.header 0 input) ⟨point,recover,false,[]⟩ 0
def headerBlock : Block 31 :=
  lift (SourceReplayStepState.lift26 (SourceReplayRecordState.core MatrixStrictHeader.block))

theorem header_exec (recover : Bool) (input point : BitString) :
    Exec headerBlock (initial recover input point) (MatrixStrictHeader.blockFuel input)
      (headerState recover input point) :=
  lift_exec (SourceReplayStepState.lift26_exec
    (SourceReplayRecordState.wide_exec (SourceReplayFamily.header_exec 0 input) SourceReplayRecordState.emptySaved)
      ⟨point,recover,false,[]⟩) 0

def reset : Block 31 := .seq (.action (.copy 29 0)) (lift SourceReplayStepState.finishBlock)
theorem reset_exec (r : SourceMatrixPacket.State) (s : SourceReplayStepState.Saved) (count : Nat) :
    Exec reset (pack r s count) 30 (work count r.core.core.core.input s.point s.recover s.valid) := by
  have copied : Exec (.action (.copy (29 : Fin 31) 0)) (pack r s count) 1
      (pack r {s with cursor := r.core.core.core.input} count) := .action _ _
  have cleaned := lift_exec
    (SourceReplayStepState.finish_exec (SourceReplayRecordState.full r SourceReplayRecordState.emptySaved)
      {s with cursor := r.core.core.core.input}) count
  exact Exec.seq copied cleaned

private theorem copy_count_exec (r : SourceMatrixPacket.State) (s : SourceReplayStepState.Saved)
    (before after : Nat) (read : r.core.core.core.target = List.replicate after true) :
    Exec (.action (.copy (30 : Fin 31) 1)) (pack r s before) 1 (pack r s after) := by
  have checked : Exec (.action (.copy (30 : Fin 31) 1)) (pack r s before) 1
      (Frame.join (SourceReplayStepState.enclose
        (SourceReplayRecordState.full r SourceReplayRecordState.emptySaved) s)
        (.cons r.core.core.core.target .nil)) := .action _ _
  rw [read] at checked
  exact checked

private theorem copy_flag_exec (r : SourceMatrixPacket.State) (s : SourceReplayStepState.Saved)
    (count : Nat) (good : Bool) (read : r.core.core.core.sign = SourceReplayRecordState.flag good) :
    Exec (.action (.copy (28 : Fin 31) 4)) (pack r s count) 1 (pack r {s with valid := good} count) := by
  have checked : Exec (.action (.copy (28 : Fin 31) 4)) (pack r s count) 1
      (full (SourceReplayHistoryStack.full
        (SourceReplayRecordState.full r SourceReplayRecordState.emptySaved) s.point
        ⟨[s.recover],r.core.core.core.sign,s.cursor⟩) count) := .action _ _
  rw [read] at checked
  exact checked

def headerFinish : Block 31 := .seq (.action (.copy 30 1)) (.seq (.action (.copy 28 4)) reset)
theorem headerFinish_exec (recover : Bool) (input point : BitString) :
    Exec headerFinish (headerState recover input point) 32
      (work (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest point recover
        (MatrixStrictHeader.scan input).terminated) := by
  let r := SourceReplayFamily.header 0 input
  let s : SourceReplayStepState.Saved := ⟨point,recover,false,[]⟩
  let n := (MatrixStrictHeader.scan input).count
  let good := (MatrixStrictHeader.scan input).terminated
  have count : r.core.core.core.target = List.replicate n true := by
    change List.replicate n true ++ [] = _
    rw [List.append_nil]
  have first := copy_count_exec r s 0 n count
  have second := copy_flag_exec r s n good rfl
  have last := reset_exec r {s with valid := good} n
  exact Exec.seq first (Exec.seq second last)

def headerSelect : Block 31 := .branch 28 (.action (.clear 30)) (.action (.clear 30)) SourceReplayLoopMachine.block
def block : Block 31 := .seq headerBlock (.seq headerFinish headerSelect)
def fuel (recover : Bool) (input point : BitString) : Nat :=
  MatrixStrictHeader.blockFuel input + (32 +
    (1 + if (MatrixStrictHeader.scan input).terminated then
      SourceReplayLoopMachine.fuel recover (MatrixStrictHeader.scan input).count
        (MatrixStrictHeader.scan input).rest point else 1))
def result (recover : Bool) (input point : BitString) : Store 31 :=
  finalState recover (readHistory recover input point)

private theorem validity_read (count : Nat) (input point : BitString) (recover good : Bool) :
    (work count input point recover good).get 28 = SourceReplayRecordState.flag good := rfl

theorem block_exec (recover : Bool) (input point : BitString) :
    Exec block (initial recover input point) (fuel recover input point) (result recover input point) := by
  have first := header_exec recover input point
  have second := headerFinish_exec recover input point
  cases good : (MatrixStrictHeader.scan input).terminated with
  | false =>
    rw [good] at second
    have clear : Exec (.action (.clear (30 : Fin 31)))
        (work (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest point recover false) 1
        (work 0 (MatrixStrictHeader.scan input).rest point recover false) := .action _ _
    have branch : Exec headerSelect
        (work (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest point recover false) 2
        (work 0 (MatrixStrictHeader.scan input).rest point recover false) :=
      Exec.empty (validity_read _ _ _ _ false) clear
    simpa only [block,fuel,result,readHistory,good,Bool.false_eq_true,↓reduceIte,finalState] using
      Exec.seq first (Exec.seq second branch)
  | true =>
    rw [good] at second
    have branch : Exec headerSelect
        (work (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest point recover true)
        (1 + SourceReplayLoopMachine.fuel recover (MatrixStrictHeader.scan input).count
          (MatrixStrictHeader.scan input).rest point)
        (finalState recover (scan recover (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest point)) :=
      Exec.one (validity_read _ _ _ _ true)
        (SourceReplayLoopMachine.block_exec recover (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest point)
    simpa only [block,fuel,result,readHistory,good,↓reduceIte] using Exec.seq first (Exec.seq second branch)

theorem fuel_bound (recover : Bool) (input point : BitString) :
    fuel recover input point ≤ input.length * allowance input.length (point.length + input.length) +
      4 * input.length + 43 := by
  have header := MatrixStrictHeader.blockFuel_bound input
  have size := MatrixStrictHeader.scan_size input
  have count : (MatrixStrictHeader.scan input).count ≤ input.length := by omega
  have rest : (MatrixStrictHeader.scan input).rest.length ≤ input.length := by omega
  cases good : (MatrixStrictHeader.scan input).terminated with
  | false => simp only [fuel,good,Bool.false_eq_true,↓reduceIte]; omega
  | true =>
    have later := SourceReplayLoopMachine.fuel_bound recover (MatrixStrictHeader.scan input).count
      (MatrixStrictHeader.scan input).rest point
    have product := Nat.mul_le_mul count (allowance_mono rest (Nat.add_le_add_left count point.length))
    simp only [fuel,good,↓reduceIte]
    omega

def observed (r : Store 31) : Option (BitString × BitString) :=
  if (r.get 28).isEmpty then none else some (r.get 0,r.get 26)
private theorem input_read (count : Nat) (input point : BitString) (recover good : Bool) :
    (work count input point recover good).get 0 = input := rfl
private theorem point_read (count : Nat) (input point : BitString) (recover good : Bool) :
    (work count input point recover good).get 26 = point := rfl
theorem observed_final (recover : Bool) (r : Result) : observed (finalState recover r) = observe r := by
  simp only [observed,finalState,validity_read,input_read,point_read,observe]
  cases r.valid <;> rfl

theorem result_contract (recover : Bool) (input point : BitString) :
    observed (result recover input point) =
      ((listCodec SourceEncoding.recordCodec).parse input).bind fun (records,cursor) =>
        (SourceReplayTraversal.walk (SourceReplayStepApply.mapOne recover) records point).map fun output => (cursor,output) := by
  rw [result,observed_final]
  exact prefix_contract recover input point

theorem recovery_contract (history : List SourceChain.StepRecord) (n d : Nat)
    (z : FactoredContraction.Point d) (suffix : BitString) :
    (observed (result true ((listCodec SourceEncoding.recordCodec).encode history.reverse ++ suffix)
      ((SourceEncoding.pointCodec d).encode z))).bind (fun pair => (SourceEncoding.pointCodec n).decode pair.2) =
        SourceEncoding.liftHistory n d history z := by
  rw [result_contract,(listCodec SourceEncoding.recordCodec).roundtrip]
  simp only [Option.bind_some,direction_walk,↓reduceIte]
  have checked := SourceReplayTraversal.recovery_contract history n d z
  cases walked : SourceReplayTraversal.walk SourceReplayTraversal.recoverOne history.reverse
      ((SourceEncoding.pointCodec d).encode z) <;>
    rw [walked] at checked <;>
    simpa only [Option.map_none,Option.map_some,Option.bind_none,Option.bind_some] using checked

theorem projection_contract (history : List SourceChain.StepRecord) (n d : Nat)
    (x : FactoredContraction.Point n) (suffix : BitString) :
    (observed (result false ((listCodec SourceEncoding.recordCodec).encode history ++ suffix)
      ((SourceEncoding.pointCodec n).encode x))).bind (fun pair => (SourceEncoding.pointCodec d).decode pair.2) =
        SourceEncoding.projectHistory n d history x := by
  rw [result_contract,(listCodec SourceEncoding.recordCodec).roundtrip]
  simp only [Option.bind_some,direction_walk,Bool.false_eq_true,↓reduceIte]
  have checked := SourceReplayTraversal.projection_contract history n d x
  cases walked : SourceReplayTraversal.walk SourceReplayTraversal.projectOne history
      ((SourceEncoding.pointCodec n).encode x) <;>
    rw [walked] at checked <;>
    simpa only [Option.map_none,Option.map_some,Option.bind_none,Option.bind_some] using checked

end PNP.Concrete.ResidualReduction.SourceReplayLoopPrefix
