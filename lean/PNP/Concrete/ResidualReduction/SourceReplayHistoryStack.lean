import PNP.Concrete.ResidualReduction.SourceReplayHistoryFields

/-! One literal counted-history loop, with a protected reverse stack.
Remaining count and cumulative validity are outside the record workspace.
A failed record stops the loop; no missing record is supplied or skipped. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayHistoryStack
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceReplayHistoryFields

structure Saved where
  remaining : BitString
  valid : BitString
  backup : BitString
def Saved.store (s : Saved) : Store 3 := .cons s.remaining (.cons s.valid (.cons s.backup .nil))
def extras (count : Nat) (good : Bool) : Saved :=
  ⟨List.replicate count true,SourceReplayRecordState.flag good,[]⟩
def full (r : Store 26) (history : BitString) (s : Saved) : Store 30 :=
  Frame.join (SourceReplayRecordStack.stacked r history) s.store
def work (count : Nat) (input history : BitString) (good : Bool) : Store 30 :=
  full (SourceReplayRecordState.initial input) history (extras count good)
def finalState (r : Result) : Store 30 := work 0 r.input r.history r.valid
def lift27 (b : Block 27) : Block 30 := Frame.block 3 b
def lift26 (b : Block 26) : Block 30 := lift27 (SourceReplayRecordStack.lift b)
theorem lift26_exec {b : Block 26} {before after : Store 26} {used : Nat}
    (h : Exec b before used after) (history : BitString) (s : Saved) :
    Exec (lift26 b) (full before history s) used (full after history s) :=
  Frame.execution (Frame.execution h (.cons history .nil)) s.store

def clearWork : Block 30 := lift26 (SourceChartedSuccessorWords.clearAll 26)
theorem clearWork_exec (r : Store 26) (history : BitString) (s : Saved) :
    Exec clearWork (full r history s) 27 (full (SourceReplayRecordState.initial []) history s) :=
  lift26_exec (SourceChartedSuccessorWords.clearAll_exec r) history s
def reset : Block 30 := .seq (.action (.copy 29 0)) <| .seq clearWork <|
  .seq (.action (.copy 0 29)) (.action (.clear 29))
theorem reset_exec (r : SourceMatrixPacket.State) (fields : SourceReplayRecordState.Saved)
    (history : BitString) (s : Saved) :
    Exec reset (full (SourceReplayRecordState.full r fields) history s) 30
      (full (SourceReplayRecordState.initial r.core.core.core.input) history {s with backup := []}) := by
  have saved : Exec (.action (.copy (29 : Fin 30) 0))
      (full (SourceReplayRecordState.full r fields) history s) 1
      (full (SourceReplayRecordState.full r fields) history {s with backup := r.core.core.core.input}) := .action _ _
  have restored : Exec (.action (.copy (0 : Fin 30) 29))
      (full (SourceReplayRecordState.initial []) history {s with backup := r.core.core.core.input}) 1
      (full (SourceReplayRecordState.initial r.core.core.core.input) history {s with backup := r.core.core.core.input}) := .action _ _
  have finished : Exec (.action (.clear (29 : Fin 30)))
      (full (SourceReplayRecordState.initial r.core.core.core.input) history {s with backup := r.core.core.core.input}) 1
      (full (SourceReplayRecordState.initial r.core.core.core.input) history {s with backup := []}) := .action _ _
  exact Exec.seq saved (Exec.seq (clearWork_exec (SourceReplayRecordState.full r fields) history _)
    (Exec.seq restored finished))

theorem record_exec (count : Nat) (input history : BitString) (good : Bool) :
    Exec (lift27 SourceReplayRecordStack.oneBlock) (work count input history good)
      (SourceReplayRecordStack.oneFuel input)
      (full (SourceReplayRecordState.result input)
        (if SourceReplayRecordFields.valid input then
          SourceReplayRecordStack.bytes (SourceReplayRecordState.capture input) ++ history else history)
        (extras count good)) :=
  Frame.execution (SourceReplayRecordStack.one_exec input history) (extras count good).store

private theorem pop_exec (count : Nat) (input history : BitString) :
    Exec (.action (.pop (27 : Fin 30))) (work (count + 1) input history true) 1 (work count input history true) := by
  simp only [work,extras,List.replicate_succ]
  exact .action _ _
def reject : Block 30 := .seq (.action (.clear 27)) (.action (.clear 28))
def check : Block 30 := .branch 24 reject reject .skip
def body : Block 30 := .seq (.action (.pop 27)) <|
  .seq (lift27 SourceReplayRecordStack.oneBlock) <| .seq check reset

theorem body_success (count : Nat) (input history : BitString) (good : SourceReplayRecordFields.valid input = true) :
    Exec body (work (count + 1) input history true) (SourceReplayRecordStack.oneFuel input + 33)
      (work count (SourceReplayRecordFields.rest input)
        (SourceReplayRecordStack.bytes (SourceReplayRecordState.capture input) ++ history) true) := by
  let nextHistory := SourceReplayRecordStack.bytes (SourceReplayRecordState.capture input) ++ history
  have parsed : Exec (lift27 SourceReplayRecordStack.oneBlock) (work count input history true)
      (SourceReplayRecordStack.oneFuel input) (full (SourceReplayRecordState.result input) nextHistory (extras count true)) := by
    simpa only [good,↓reduceIte,nextHistory] using record_exec count input history true
  have read : (full (SourceReplayRecordState.result input) nextHistory (extras count true)).get 24 = [true] := by
    change SourceReplayRecordState.flag (SourceReplayRecordFields.valid input) = [true]
    rw [good]
    rfl
  have checked : Exec check (full (SourceReplayRecordState.result input) nextHistory (extras count true)) 2
      (full (SourceReplayRecordState.result input) nextHistory (extras count true)) :=
    Exec.one read (.skip _)
  have cleaned : Exec reset (full (SourceReplayRecordState.result input) nextHistory (extras count true)) 30
      (work count (SourceReplayRecordFields.rest input) nextHistory true) :=
    reset_exec (SourceReplayRecordState.blank (SourceReplayRecordFields.rest input))
      (SourceReplayRecordState.capture input) nextHistory (extras count true)
  have cost : SourceReplayRecordStack.oneFuel input + 33 = 1 + (SourceReplayRecordStack.oneFuel input + (2 + 30)) := by omega
  simpa only [body,cost,nextHistory] using Exec.seq (pop_exec count input history)
    (Exec.seq parsed (Exec.seq checked cleaned))

theorem body_failure (count : Nat) (input history : BitString) (bad : SourceReplayRecordFields.valid input = false) :
    Exec body (work (count + 1) input history true) (SourceReplayRecordStack.oneFuel input + 34)
      (work 0 (SourceReplayRecordFields.rest input) history false) := by
  have parsed : Exec (lift27 SourceReplayRecordStack.oneBlock) (work count input history true)
      (SourceReplayRecordStack.oneFuel input) (full (SourceReplayRecordState.result input) history (extras count true)) := by
    simpa only [bad,Bool.false_eq_true,↓reduceIte] using record_exec count input history true
  have read : (full (SourceReplayRecordState.result input) history (extras count true)).get 24 = [] := by
    change SourceReplayRecordState.flag (SourceReplayRecordFields.valid input) = []
    rw [bad]
    rfl
  have clearCount : Exec (.action (.clear (27 : Fin 30)))
      (full (SourceReplayRecordState.result input) history (extras count true)) 1
      (full (SourceReplayRecordState.result input) history (extras 0 true)) := .action _ _
  have clearFlag : Exec (.action (.clear (28 : Fin 30)))
      (full (SourceReplayRecordState.result input) history (extras 0 true)) 1
      (full (SourceReplayRecordState.result input) history (extras 0 false)) := .action _ _
  have checked : Exec check (full (SourceReplayRecordState.result input) history (extras count true)) 3
      (full (SourceReplayRecordState.result input) history (extras 0 false)) :=
    Exec.empty read (Exec.seq clearCount clearFlag)
  have cleaned : Exec reset (full (SourceReplayRecordState.result input) history (extras 0 false)) 30
      (work 0 (SourceReplayRecordFields.rest input) history false) :=
    reset_exec (SourceReplayRecordState.blank (SourceReplayRecordFields.rest input))
      (SourceReplayRecordState.capture input) history (extras 0 false)
  have cost : SourceReplayRecordStack.oneFuel input + 34 = 1 + (SourceReplayRecordStack.oneFuel input + (3 + 30)) := by omega
  simpa only [body,cost] using Exec.seq (pop_exec count input history) (Exec.seq parsed (Exec.seq checked cleaned))

def loop : Block 30 := .loop 27 body
def loopFuel : Nat → BitString → Nat
  | 0,_ => 1
  | count + 1,input =>
      if SourceReplayRecordFields.valid input then
        1 + ((SourceReplayRecordStack.oneFuel input + 33) + loopFuel count (SourceReplayRecordFields.rest input))
      else 1 + ((SourceReplayRecordStack.oneFuel input + 34) + 1)
theorem loop_exec (count : Nat) (input history : BitString) :
    Exec loop (work count input history true) (loopFuel count input) (finalState (scan count input history)) := by
  induction count generalizing input history with
  | zero => exact Exec.loopStop rfl
  | succ count ih =>
    have read : (work (count + 1) input history true).get 27 = true :: List.replicate count true := by
      change List.replicate (count + 1) true = _
      rw [List.replicate_succ]
    cases valid : SourceReplayRecordFields.valid input with
    | false =>
      have stopped : Exec loop (work 0 (SourceReplayRecordFields.rest input) history false) 1
          (work 0 (SourceReplayRecordFields.rest input) history false) := Exec.loopStop rfl
      have checked := Exec.loopStep (source := (27 : Fin 30)) read (body_failure count input history valid) stopped
      simpa only [loop,loopFuel,scan,valid,Bool.false_eq_true,↓reduceIte,finalState] using checked
    | true =>
      have checked := Exec.loopStep (source := (27 : Fin 30)) read (body_success count input history valid)
        (ih (SourceReplayRecordFields.rest input)
          (SourceReplayRecordStack.bytes (SourceReplayRecordState.capture input) ++ history))
      simpa only [loop,loopFuel,scan,valid,↓reduceIte] using checked

def allowance (length : Nat) : Nat := 32 * length * length + 153 * length + 387
private theorem allowance_mono {a b : Nat} (bound : a ≤ b) : allowance a ≤ allowance b := by
  have square := Nat.mul_le_mul bound bound
  simp only [allowance,Nat.mul_assoc] at *
  omega
theorem loopFuel_bound (count : Nat) (input : BitString) :
    loopFuel count input ≤ count * allowance input.length + 1 := by
  induction count generalizing input with
  | zero => simp only [loopFuel,Nat.zero_mul,Nat.zero_add,Nat.le_refl]
  | succ count ih =>
    have parser := SourceReplayRecordStack.oneFuel_bound input
    have base : SourceReplayRecordStack.oneFuel input + 35 ≤ allowance input.length := by unfold allowance; omega
    cases valid : SourceReplayRecordFields.valid input with
    | false =>
      simp only [loopFuel,valid,Bool.false_eq_true,↓reduceIte,Nat.add_mul,Nat.one_mul]
      omega
    | true =>
      obtain ⟨_,_,_,_,_,_,_,_,remaining⟩ := SourceReplayRecordFields.input_bounds input
      have continued := ih (SourceReplayRecordFields.rest input)
      have product := Nat.mul_le_mul_left count (allowance_mono remaining)
      simp only [loopFuel,valid,↓reduceIte,Nat.add_mul,Nat.one_mul]
      omega


def headerState (input history : BitString) : Store 30 :=
  full (SourceReplayRecordState.full (SourceReplayFamily.header 0 input) SourceReplayRecordState.emptySaved)
    history (extras 0 false)
theorem header_exec (input history : BitString) :
    Exec (lift26 (SourceReplayRecordState.core MatrixStrictHeader.block)) (work 0 input history false)
      (MatrixStrictHeader.blockFuel input) (headerState input history) :=
  lift26_exec (SourceReplayRecordState.wide_exec (SourceReplayFamily.header_exec 0 input)
    SourceReplayRecordState.emptySaved) history (extras 0 false)

def headerFinish : Block 30 := .seq (.action (.copy 27 1)) <| .seq (.action (.copy 28 4)) reset
theorem headerFinish_exec (input history : BitString) :
    Exec headerFinish (headerState input history) 32
      (work (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest history
        (MatrixStrictHeader.scan input).terminated) := by
  let r := SourceReplayFamily.header 0 input
  let counted := {extras 0 false with remaining := List.replicate (MatrixStrictHeader.scan input).count true}
  have count : r.core.core.core.target = List.replicate (MatrixStrictHeader.scan input).count true := by
    change List.replicate (MatrixStrictHeader.scan input).count true ++ [] = _
    rw [List.append_nil]
  have saved : Exec (.action (.copy (27 : Fin 30) 1)) (headerState input history) 1
      (full (SourceReplayRecordState.full r SourceReplayRecordState.emptySaved) history counted) := by
    have h : Exec (.action (.copy (27 : Fin 30) 1)) (headerState input history) 1
        (full (SourceReplayRecordState.full r SourceReplayRecordState.emptySaved) history
          {extras 0 false with remaining := r.core.core.core.target}) := .action _ _
    rw [count] at h
    exact h
  have valid : Exec (.action (.copy (28 : Fin 30) 4))
      (full (SourceReplayRecordState.full r SourceReplayRecordState.emptySaved) history counted) 1
      (full (SourceReplayRecordState.full r SourceReplayRecordState.emptySaved) history
        (extras (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).terminated)) := .action _ _
  have cleaned : Exec reset
      (full (SourceReplayRecordState.full r SourceReplayRecordState.emptySaved) history
        (extras (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).terminated)) 30
      (work (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest history
        (MatrixStrictHeader.scan input).terminated) :=
    reset_exec r SourceReplayRecordState.emptySaved history
      (extras (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).terminated)
  exact Exec.seq saved (Exec.seq valid cleaned)

def headerSelect : Block 30 := .branch 28 (.action (.clear 27)) (.action (.clear 27)) loop
def prefixBlock : Block 30 := .seq
  (.seq (lift26 (SourceReplayRecordState.core MatrixStrictHeader.block)) headerFinish) headerSelect
def prefixFuel (input : BitString) : Nat :=
  (MatrixStrictHeader.blockFuel input + 32) +
    (1 + (if (MatrixStrictHeader.scan input).terminated then
      loopFuel (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest else 1))
theorem prefix_exec (input history : BitString) :
    Exec prefixBlock (work 0 input history false) (prefixFuel input) (finalState (readHistory input history)) := by
  have first := Exec.seq (header_exec input history) (headerFinish_exec input history)
  cases flag : (MatrixStrictHeader.scan input).terminated with
  | false =>
    rw [flag] at first
    have read : (work (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest history false).get 28 = [] := rfl
    have clear : Exec (.action (.clear (27 : Fin 30)))
        (work (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest history false) 1
        (work 0 (MatrixStrictHeader.scan input).rest history false) := .action _ _
    have branch : Exec headerSelect
        (work (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest history false) 2
        (work 0 (MatrixStrictHeader.scan input).rest history false) := Exec.empty read clear
    have checked := Exec.seq first branch
    simpa only [prefixBlock,headerSelect,prefixFuel,flag,Bool.false_eq_true,↓reduceIte,readHistory,finalState] using checked
  | true =>
    rw [flag] at first
    have read : (work (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest history true).get 28 = [true] := rfl
    have branch : Exec headerSelect
        (work (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest history true)
        (1 + loopFuel (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest)
        (finalState (scan (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest history)) :=
      Exec.one read (loop_exec (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest history)
    have checked := Exec.seq first branch
    simpa only [prefixBlock,headerSelect,prefixFuel,flag,↓reduceIte,readHistory] using checked

theorem prefixFuel_bound (input : BitString) :
    prefixFuel input ≤ input.length * allowance input.length + 4 * input.length + 43 := by
  have header := MatrixStrictHeader.blockFuel_bound input
  have size := MatrixStrictHeader.scan_size input
  have countBound : (MatrixStrictHeader.scan input).count ≤ input.length :=
    Nat.le_trans (Nat.le_add_right _ _) size
  have restBound : (MatrixStrictHeader.scan input).rest.length ≤ input.length :=
    Nat.le_trans (Nat.le_add_left _ _) size
  cases flag : (MatrixStrictHeader.scan input).terminated with
  | false =>
    simp only [prefixFuel,flag,Bool.false_eq_true,↓reduceIte]
    omega
  | true =>
    have traversal := loopFuel_bound (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest
    have product := Nat.mul_le_mul countBound (allowance_mono restBound)
    simp only [prefixFuel,flag,↓reduceIte]
    omega

theorem prefix_parsed_exec (input history : BitString) (records : List SourceChain.StepRecord)
    (suffix : BitString) (parsed : (listCodec SourceEncoding.recordCodec).parse input = some (records,suffix)) :
    Exec prefixBlock (work 0 input history false) (prefixFuel input)
      (work 0 suffix (encodeSeq SourceEncoding.recordCodec.encode records.reverse ++ history) true) := by
  have contract := SourceReplayHistoryFields.prefix_contract input history
  rw [parsed] at contract
  have checked := prefix_exec input history
  rw [contract] at checked
  exact checked
theorem prefix_rejected (input history : BitString)
    (parsed : (listCodec SourceEncoding.recordCodec).parse input = none) :
    (finalState (readHistory input history)).get 28 = [] := by
  have bad := SourceReplayHistoryFields.prefix_contract input history
  rw [parsed] at bad
  change SourceReplayRecordState.flag (readHistory input history).valid = []
  rw [bad]
  rfl


end PNP.Concrete.ResidualReduction.SourceReplayHistoryStack
