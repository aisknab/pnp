import PNP.Concrete.ResidualReduction.SourceReplayRequest

/-! Protected state for the strict outer replay-request parser. Only the
input register starts populated. Status is cumulative: later valid fields
cannot erase an earlier parsing failure. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayParserState
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence

structure Saved where
  mode : BitString
  dimension : BitString
  data : BitString
  witness : BitString
  valid : BitString
def Saved.store (s : Saved) : Store 5 :=
  .cons s.mode (.cons s.dimension (.cons s.data (.cons s.witness (.cons s.valid .nil))))
def emptySaved : Saved := ⟨[],[],[],[],[]⟩
def full (r : Registers) (s : Saved) : Store 14 := Frame.join r.store s.store
def blank (input output : BitString) : Registers := ⟨input,[],[],[],[],[],[],[],output⟩
def work (input output : BitString) (s : Saved) : Store 14 := full (blank input output) s
def initial (input : BitString) : Store 14 := work input [] emptySaved
def core (b : Block 9) : Block 14 := Frame.block 5 b
theorem core_exec {b : Block 9} {before after : Registers} {used : Nat}
    (h : Exec b before.store used after.store) (s : Saved) :
    Exec (core b) (full before s) used (full after s) := Frame.execution h s.store

def reset : Block 14 := .seq (.action (.clear 1)) (.seq (.action (.clear 2))
  (.seq (.action (.clear 3)) (.seq (.action (.clear 4)) (.seq (.action (.clear 5))
  (.seq (.action (.clear 6)) (.seq (.action (.clear 7)) (.action (.clear 8))))))))
theorem reset_exec (r : Registers) (s : Saved) :
    Exec reset (full r s) 8 (work r.input [] s) :=
  Exec.seq (.action _ _) <| Exec.seq (.action _ _) <| Exec.seq (.action _ _) <|
    Exec.seq (.action _ _) <| Exec.seq (.action _ _) <| Exec.seq (.action _ _) <|
      Exec.seq (.action _ _) (.action _ _)

def restrict (s : Saved) (good : Bool) : Saved := {s with valid := if good then s.valid else []}
def guard : Block 14 := .branch 5 (.action (.clear 13)) (.action (.clear 13)) .skip
theorem guard_exec (r : Registers) (s : Saved) (good : Bool)
    (flag : r.mode = if good then [true] else []) :
    Exec guard (full r s) 2 (full r (restrict s good)) := by
  have read : (full r s).get 5 = r.mode := rfl
  cases good with
  | false => exact Exec.empty (read.trans flag) (.action _ _)
  | true => exact Exec.one (read.trans flag) (.skip _)

def saveHeader : Block 14 := .seq (.action (.copy 10 1)) (.seq (.action (.copy 13 4)) reset)
theorem saveHeader_exec (r : Registers) (s : Saved) :
    Exec saveHeader (full r s) 10 (work r.input [] {s with dimension := r.target,valid := r.sign}) := by
  have first : Exec (.action (.copy (10 : Fin 14) 1)) (full r s) 1
      (full r {s with dimension := r.target}) := .action _ _
  have second : Exec (.action (.copy (13 : Fin 14) 4)) (full r {s with dimension := r.target}) 1
      (full r {s with dimension := r.target,valid := r.sign}) := .action _ _
  exact Exec.seq first (Exec.seq second (reset_exec r _))

def dataFinish : Block 14 := .seq (.action (.copy 11 8)) (.seq guard reset)
theorem dataFinish_exec (r : Registers) (s : Saved) (good : Bool)
    (flag : r.mode = if good then [true] else []) :
    Exec dataFinish (full r s) 11 (work r.input [] (restrict {s with data := r.output} good)) := by
  have first : Exec (.action (.copy (11 : Fin 14) 8)) (full r s) 1
      (full r {s with data := r.output}) := .action _ _
  exact Exec.seq first (Exec.seq (guard_exec r {s with data := r.output} good flag)
    (reset_exec r (restrict {s with data := r.output} good)))

def witnessFinish : Block 14 := .seq (.action (.copy 12 8)) (.seq guard reset)
theorem witnessFinish_exec (r : Registers) (s : Saved) (good : Bool)
    (flag : r.mode = if good then [true] else []) :
    Exec witnessFinish (full r s) 11 (work r.input [] (restrict {s with witness := r.output} good)) := by
  have first : Exec (.action (.copy (12 : Fin 14) 8)) (full r s) 1
      (full r {s with witness := r.output}) := .action _ _
  exact Exec.seq first (Exec.seq (guard_exec r {s with witness := r.output} good flag)
    (reset_exec r (restrict {s with witness := r.output} good)))

def endCheck : Block 14 := .branch 0 .skip (.action (.clear 13)) (.action (.clear 13))
def finish : Block 14 := .seq endCheck (.action (.clear 0))
theorem finish_exec (input : BitString) (s : Saved) :
    Exec finish (work input [] s) 3 (work [] [] (restrict s input.isEmpty)) := by
  cases input with
  | nil => exact Exec.seq (Exec.empty rfl (.skip _)) (.action _ _)
  | cons bit rest =>
    cases bit
    · exact Exec.seq (Exec.zero rfl (.action _ _)) (.action _ _)
    · exact Exec.seq (Exec.one rfl (.action _ _)) (.action _ _)

def modeBlock : Block 14 := .branch 0 .skip
  (.seq (.action (.pop 0)) (.action (.push 9 false)))
  (.seq (.action (.pop 0)) (.action (.push 9 true)))
def modeFuel : BitString → Nat | [] => 2 | _ :: _ => 3
def modeSaved (input : BitString) : Saved := {emptySaved with mode := input.take 1}
theorem mode_exec (input : BitString) :
    Exec modeBlock (initial input) (modeFuel input) (work input.tail [] (modeSaved input)) := by
  cases input with
  | nil => exact Exec.empty rfl (.skip _)
  | cons bit rest =>
    cases bit
    · exact Exec.zero rfl (Exec.seq (.action _ _) (.action _ _))
    · exact Exec.one rfl (Exec.seq (.action _ _) (.action _ _))
theorem modeFuel_bound (input : BitString) : modeFuel input ≤ 3 := by cases input <;> simp only [modeFuel] <;> omega

end PNP.Concrete.ResidualReduction.SourceReplayParserState
