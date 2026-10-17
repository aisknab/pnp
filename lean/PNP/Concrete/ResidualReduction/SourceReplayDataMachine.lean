import PNP.Concrete.ResidualReduction.SourceReplayDataFields

/-! Literal complete-data reader. Five protected registers retain terminal
dimension, core row count, core payload, forward history and cumulative
validity outside the counted-history workspace. Register 26 retains reverse
history. Acceptance requires every field and the final end-of-input check. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayDataMachine
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.SourceReplayDataFields

structure Saved where
  dimension : BitString
  rows : BitString
  core : BitString
  forward : BitString
  valid : BitString
def Saved.store (s : Saved) : Store 5 :=
  .cons s.dimension (.cons s.rows (.cons s.core (.cons s.forward (.cons s.valid .nil))))
def emptySaved : Saved := ⟨[],[],[],[],[]⟩
def full (r : Store 30) (s : Saved) : Store 35 := Frame.join r s.store
def lift30 (b : Block 30) : Block 35 := Frame.block 5 b
theorem lift30_exec {b : Block 30} {before after : Store 30} {used : Nat}
    (h : Exec b before used after) (s : Saved) :
    Exec (lift30 b) (full before s) used (full after s) := Frame.execution h s.store
def view (r : SourceMatrixPacket.State) : Store 30 :=
  SourceReplayHistoryStack.full (SourceReplayRecordState.full r SourceReplayRecordState.emptySaved)
    [] (SourceReplayHistoryStack.extras 0 false)
def pack (r : SourceMatrixPacket.State) (s : Saved) : Store 35 := full (view r) s
private theorem view_target (r : SourceMatrixPacket.State) : (view r).get 1 = r.core.core.core.target := rfl
private theorem view_header (r : SourceMatrixPacket.State) : (view r).get 4 = r.core.core.core.sign := rfl
private theorem view_mode (r : SourceMatrixPacket.State) : (view r).get 5 = r.core.core.core.mode := rfl
private theorem view_output (r : SourceMatrixPacket.State) : (view r).get 8 = r.core.core.core.output := rfl
private theorem view_rows (r : SourceMatrixPacket.State) : (view r).get 15 = r.rows := rfl

private theorem set_frame {extra count : Nat} (r : Store count) (frame : Store extra)
    (destination : Fin extra) (value : BitString) :
    (Frame.join r frame).set (Frame.frameIndex count destination) value =
      Frame.join r (frame.set destination value) := by
  induction r with
  | nil =>
    have position : Frame.frameIndex 0 destination = destination := by
      apply Fin.ext
      simp only [Frame.frameIndex,Nat.zero_add]
    rw [position]
    rfl
  | @cons count first rest ih =>
    have position : Frame.frameIndex (count + 1) destination = (Frame.frameIndex count destination).succ := by
      apply Fin.ext
      change count + 1 + destination.val = count + destination.val + 1
      omega
    rw [position]
    exact congrArg (Store.cons first) ih

private theorem copy_saved_exec (r : Store 30) (s : Saved) (destination : Fin 5)
    (source : Fin 30) (value : BitString) (after : Saved)
    (read : r.get source = value) (write : s.store.set destination value = after.store) :
    Exec (.action (.copy (Frame.frameIndex 30 destination) (Frame.index 5 source)))
      (full r s) 1 (full r after) := by
  have checked := Exec.action (.copy (Frame.frameIndex 30 destination) (Frame.index 5 source)) (full r s)
  simpa only [Action.update,Action.instruction,Instruction.update,full,Frame.get_core,
    set_frame,read,write] using checked

private theorem clear_valid_exec (r : Store 30) (s : Saved) :
    Exec (.action (.clear (34 : Fin 35))) (full r s) 1 (full r {s with valid := []}) := by
  have position : Frame.frameIndex 30 (4 : Fin 5) = (34 : Fin 35) := rfl
  have write : s.store.set 4 [] = ({s with valid := []} : Saved).store := rfl
  have checked := Exec.action (.clear (Frame.frameIndex 30 (4 : Fin 5))) (full r s)
  simp only [Action.update,Action.instruction,Instruction.update,full,set_frame,write] at checked
  simpa only [full,position] using checked

private theorem read_dimension (r : Store 30) (s : Saved) : (full r s).get 30 = s.dimension :=
  Frame.get_frame r s.store 0
private theorem read_rows (r : Store 30) (s : Saved) : (full r s).get 31 = s.rows :=
  Frame.get_frame r s.store 1
private theorem read_core (r : Store 30) (s : Saved) : (full r s).get 32 = s.core :=
  Frame.get_frame r s.store 2
private theorem read_forward (r : Store 30) (s : Saved) : (full r s).get 33 = s.forward :=
  Frame.get_frame r s.store 3
private theorem read_valid (r : Store 30) (s : Saved) : (full r s).get 34 = s.valid :=
  Frame.get_frame r s.store 4
private theorem read_input (r : SourceReplayHistoryFields.Result) (s : Saved) :
    (full (SourceReplayHistoryStack.finalState r) s).get 0 = r.input :=
  Frame.get_core _ s.store 0
private theorem read_reverse (r : SourceReplayHistoryFields.Result) (s : Saved) :
    (full (SourceReplayHistoryStack.finalState r) s).get 26 = r.history :=
  Frame.get_core _ s.store 26
private theorem read_history_valid (r : SourceReplayHistoryFields.Result) (s : Saved) :
    (full (SourceReplayHistoryStack.finalState r) s).get 28 = SourceReplayRecordState.flag r.valid :=
  Frame.get_core _ s.store 28
def ready (input : BitString) (s : Saved) : Store 35 :=
  full (SourceReplayHistoryStack.work 0 input [] false) s
def initial (input : BitString) : Store 35 := ready input emptySaved

def restrict (s : Saved) (good : Bool) : Saved := {s with valid := if good then s.valid else []}
private theorem restrict_flag (s : Saved) (a b : Bool) (known : s.valid = SourceReplayRecordState.flag a) :
    restrict s b = {s with valid := SourceReplayRecordState.flag (a && b)} := by
  cases a <;> cases b <;> simp only [restrict,known,Bool.false_and,Bool.true_and,
    SourceReplayRecordState.flag,Bool.false_eq_true,↓reduceIte]
def guard (index : Fin 35) : Block 35 :=
  .branch index (.action (.clear 34)) (.action (.clear 34)) .skip
theorem guard_exec (index : Fin 35) (r : Store 30) (s : Saved) (good : Bool)
    (read : (full r s).get index = SourceReplayRecordState.flag good) :
    Exec (guard index) (full r s) 2 (full r (restrict s good)) := by
  cases good with
  | false => exact Exec.empty read (clear_valid_exec r s)
  | true => exact Exec.one read (.skip _)

def endCheck : Block 35 :=
  .branch 0 .skip (.action (.clear 34)) (.action (.clear 34))
theorem endCheck_exec (r : Store 30) (s : Saved) (input : BitString)
    (read : (full r s).get 0 = input) :
    Exec endCheck (full r s) 2 (full r (restrict s input.isEmpty)) := by
  cases input with
  | nil => exact Exec.empty read (.skip _)
  | cons bit rest =>
    cases bit with
    | false => exact Exec.zero read (clear_valid_exec r s)
    | true => exact Exec.one read (clear_valid_exec r s)

def headerSaved (input : BitString) : Saved :=
  ⟨List.replicate (dimension input) true,[],[],[],
    SourceReplayRecordState.flag (MatrixStrictHeader.scan input).terminated⟩
def headerBlock : Block 35 := .seq
  (lift30 (SourceReplayHistoryStack.lift26 (SourceReplayRecordState.core MatrixStrictHeader.block)))
  (.seq (.action (.copy 30 1)) (.seq (.action (.copy 34 4)) (lift30 SourceReplayHistoryStack.reset)))
theorem header_exec (input : BitString) :
    Exec headerBlock (initial input) (MatrixStrictHeader.blockFuel input + 32)
      (ready (coreInput input) (headerSaved input)) := by
  let r := SourceReplayFamily.header 0 input
  let counted : Saved := {emptySaved with dimension := List.replicate (dimension input) true}
  have first : Exec
      (lift30 (SourceReplayHistoryStack.lift26 (SourceReplayRecordState.core MatrixStrictHeader.block)))
      (initial input) (MatrixStrictHeader.blockFuel input) (pack r emptySaved) :=
    lift30_exec (SourceReplayHistoryStack.header_exec input []) emptySaved
  have count : r.core.core.core.target = List.replicate (dimension input) true := by
    change List.replicate (dimension input) true ++ [] = _
    rw [List.append_nil]
  have copied : Exec (.action (.copy (30 : Fin 35) 1)) (pack r emptySaved) 1 (pack r counted) :=
    copy_saved_exec (view r) emptySaved 0 1 _ counted ((view_target r).trans count) rfl
  have flag : Exec (.action (.copy (34 : Fin 35) 4)) (pack r counted) 1
      (pack r (headerSaved input)) :=
    copy_saved_exec (view r) counted 4 4 _ (headerSaved input) (view_header r) rfl
  have reset : Exec (lift30 SourceReplayHistoryStack.reset) (pack r (headerSaved input)) 30
      (ready (coreInput input) (headerSaved input)) :=
    lift30_exec (SourceReplayHistoryStack.reset_exec r SourceReplayRecordState.emptySaved []
      (SourceReplayHistoryStack.extras 0 false)) (headerSaved input)
  exact Exec.seq first (Exec.seq copied (Exec.seq flag reset))

def coreSaved (input : BitString) : Saved :=
  ⟨List.replicate (dimension input) true,List.replicate (rows input) true,core input,[],
    SourceReplayRecordState.flag (priorValid input)⟩
def familyBlock : Block 35 := .seq (.action (.copy 9 30)) <|
  .seq (lift30 (SourceReplayHistoryStack.lift26 (SourceReplayRecordState.wide SourceReplayFamily.block))) <|
  .seq (.action (.copy 31 15)) <| .seq (.action (.copy 32 8)) <|
  .seq (guard 5) (lift30 SourceReplayHistoryStack.reset)
theorem family_exec (input : BitString) :
    Exec familyBlock (ready (coreInput input) (headerSaved input))
      (SourceReplayFamily.fuel (dimension input) (coreInput input) + 35)
      (ready (historyInput input) (coreSaved input)) := by
  let n := dimension input
  let bits := coreInput input
  let r := SourceReplayFamily.result n bits
  let s1 := {headerSaved input with rows := List.replicate (rows input) true}
  let s2 := {s1 with core := core input}
  let good := SourceReplayFamilyFields.valid n bits
  have seed : Exec (.action (.copy (9 : Fin 35) 30)) (ready bits (headerSaved input)) 1
      (pack (SourceReplayFamily.initial n bits) (headerSaved input)) := .action _ _
  have parsed : Exec
      (lift30 (SourceReplayHistoryStack.lift26 (SourceReplayRecordState.wide SourceReplayFamily.block)))
      (pack (SourceReplayFamily.initial n bits) (headerSaved input))
      (SourceReplayFamily.fuel n bits) (pack r (headerSaved input)) :=
    lift30_exec (SourceReplayHistoryStack.lift26_exec
      (SourceReplayRecordState.wide_exec (SourceReplayFamily.block_exec n bits)
        SourceReplayRecordState.emptySaved) [] (SourceReplayHistoryStack.extras 0 false)) (headerSaved input)
  have count : Exec (.action (.copy (31 : Fin 35) 15)) (pack r (headerSaved input)) 1 (pack r s1) :=
    copy_saved_exec (view r) (headerSaved input) 1 15 _ s1 (view_rows r) rfl
  have payload : Exec (.action (.copy (32 : Fin 35) 8)) (pack r s1) 1 (pack r s2) :=
    copy_saved_exec (view r) s1 2 8 _ s2 (view_output r) rfl
  have checked : Exec (guard 5) (pack r s2) 2 (pack r (restrict s2 good)) :=
    guard_exec 5 _ s2 good ((Frame.get_core (view r) s2.store 5).trans (view_mode r))
  have saved : restrict s2 good = coreSaved input := by
    exact restrict_flag s2 (MatrixStrictHeader.scan input).terminated good rfl
  rw [saved] at checked
  have reset : Exec (lift30 SourceReplayHistoryStack.reset) (pack r (coreSaved input)) 30
      (ready (historyInput input) (coreSaved input)) :=
    lift30_exec (SourceReplayHistoryStack.reset_exec r SourceReplayRecordState.emptySaved []
      (SourceReplayHistoryStack.extras 0 false)) (coreSaved input)
  have cost : SourceReplayFamily.fuel n bits + 35 =
      1 + (SourceReplayFamily.fuel n bits + (1 + (1 + (2 + 30)))) := by omega
  simpa only [familyBlock,cost,n,bits] using Exec.seq seed (Exec.seq parsed
    (Exec.seq count (Exec.seq payload (Exec.seq checked reset))))

def historySaved (input : BitString) : Saved :=
  {coreSaved input with forward := historyInput input}
def saved (input : BitString) : Saved :=
  {historySaved input with valid := SourceReplayRecordState.flag (valid input)}
def result (input : BitString) : Store 35 :=
  full (SourceReplayHistoryStack.finalState (history input)) (saved input)
def historyBlock : Block 35 := .seq (.action (.copy 33 0)) <|
  .seq (lift30 SourceReplayHistoryStack.prefixBlock) (.seq (guard 28) endCheck)
theorem history_exec (input : BitString) :
    Exec historyBlock (ready (historyInput input) (coreSaved input))
      (SourceReplayHistoryStack.prefixFuel (historyInput input) + 5) (result input) := by
  let h := history input
  let r := SourceReplayHistoryStack.finalState h
  let s1 := historySaved input
  let s2 := restrict s1 h.valid
  let s3 := restrict s2 h.input.isEmpty
  have copy : Exec (.action (.copy (33 : Fin 35) 0)) (ready (historyInput input) (coreSaved input)) 1
      (ready (historyInput input) s1) :=
    copy_saved_exec (SourceReplayHistoryStack.work 0 (historyInput input) [] false)
      (coreSaved input) 3 0 _ s1 rfl rfl
  have parsed : Exec (lift30 SourceReplayHistoryStack.prefixBlock)
      (ready (historyInput input) s1) (SourceReplayHistoryStack.prefixFuel (historyInput input)) (full r s1) :=
    lift30_exec (SourceReplayHistoryStack.prefix_exec (historyInput input) []) s1
  have checked : Exec (guard 28) (full r s1) 2 (full r s2) := guard_exec 28 r s1 h.valid (read_history_valid h s1)
  have ended : Exec endCheck (full r s2) 2 (full r s3) := endCheck_exec r s2 h.input (read_input h s2)
  have fields : s3 = saved input := by
    have first : s2 = {s1 with valid := SourceReplayRecordState.flag (priorValid input && h.valid)} :=
      restrict_flag s1 (priorValid input) h.valid rfl
    change restrict s2 h.input.isEmpty = saved input
    rw [first]
    exact restrict_flag _ (priorValid input && h.valid) h.input.isEmpty rfl
  rw [fields] at ended
  have cost : SourceReplayHistoryStack.prefixFuel (historyInput input) + 5 =
      1 + (SourceReplayHistoryStack.prefixFuel (historyInput input) + (2 + 2)) := by omega
  simpa only [historyBlock,cost,result,r,h] using Exec.seq copy (Exec.seq parsed (Exec.seq checked ended))

def block : Block 35 := .seq headerBlock (.seq familyBlock historyBlock)
def fuel (input : BitString) : Nat :=
  (MatrixStrictHeader.blockFuel input + 32) +
    ((SourceReplayFamily.fuel (dimension input) (coreInput input) + 35) +
      (SourceReplayHistoryStack.prefixFuel (historyInput input) + 5))
theorem block_exec (input : BitString) : Exec block (initial input) (fuel input) (result input) :=
  Exec.seq (header_exec input) (Exec.seq (family_exec input) (history_exec input))

theorem fuel_bound (input : BitString) :
    fuel input ≤ input.length * SourceReplayHistoryStack.allowance input.length +
      (16 * input.length + 36) * input.length + 11 * input.length + 150 := by
  obtain ⟨dim,rest,_,_,tail,_⟩ := SourceReplayDataFields.bounds input
  have header := MatrixStrictHeader.blockFuel_bound input
  have family := SourceReplayFamily.fuel_bound (dimension input) (coreInput input)
  have history := SourceReplayHistoryStack.prefixFuel_bound (historyInput input)
  have families := Nat.mul_le_mul (show 16 * dimension input + 36 ≤ 16 * input.length + 36 by omega) rest
  have square := Nat.mul_le_mul tail tail
  have monotone : SourceReplayHistoryStack.allowance (historyInput input).length ≤
      SourceReplayHistoryStack.allowance input.length := by
    simp only [SourceReplayHistoryStack.allowance,Nat.mul_assoc]
    omega
  have histories := Nat.mul_le_mul tail monotone
  unfold fuel
  omega

theorem parsed_fields (input : BitString) (d : SourceEncoding.ReductionData)
    (decoded : SourceEncoding.dataCodec.decode input = some d) :
    (result input).get 30 = List.replicate d.dimension true ∧
      (result input).get 31 = List.replicate d.core.length true ∧
      (result input).get 32 = SourceMatrixEncoding.familyBits d.core ∧
      (result input).get 33 = (PNP.Concrete.NativeNormalization.NativeBitCodec.listCodec SourceEncoding.recordCodec).encode d.history ∧
      (result input).get 26 = PNP.Concrete.NativeNormalization.NativeBitCodec.encodeSeq SourceEncoding.recordCodec.encode d.history.reverse ∧
      (result input).get 0 = [] ∧ (result input).get 34 = [true] := by
  have fields := SourceReplayDataFields.decoded_fields input d decoded
  have dim := congrArg SourceReplayDataFields.Fields.dimension fields
  have rows := congrArg SourceReplayDataFields.Fields.rows fields
  have core := congrArg SourceReplayDataFields.Fields.core fields
  have forward := congrArg SourceReplayDataFields.Fields.forward fields
  have reverse := congrArg SourceReplayDataFields.Fields.reverse fields
  have remaining := congrArg SourceReplayDataFields.Fields.remaining fields
  have good := congrArg SourceReplayDataFields.Fields.valid fields
  simp only [result,read_dimension,read_rows,read_core,read_forward,read_reverse,read_input,read_valid]
  change List.replicate (dimension input) true = _ ∧ List.replicate (SourceReplayDataFields.rows input) true = _ ∧
    SourceReplayDataFields.core input = _ ∧ historyInput input = _ ∧ (history input).history = _ ∧
    (history input).input = [] ∧ SourceReplayRecordState.flag (valid input) = [true]
  refine ⟨congrArg (fun n => List.replicate n true) dim,
    congrArg (fun n => List.replicate n true) rows,core,forward,reverse,remaining,?_⟩
  change valid input = true at good
  rw [good]
  rfl

theorem rejected (input : BitString) (bad : SourceEncoding.dataCodec.decode input = none) :
    (result input).get 34 = [] := by
  have checked := SourceReplayDataFields.decode_contract input
  rw [bad] at checked
  rw [result,read_valid]
  change SourceReplayRecordState.flag (valid input) = []
  rw [checked]
  rfl

end PNP.Concrete.ResidualReduction.SourceReplayDataMachine
