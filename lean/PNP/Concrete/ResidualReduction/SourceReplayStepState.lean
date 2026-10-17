import PNP.Concrete.ResidualReduction.SourceReplayTraversal

/-! Protected state for a literal record-to-witness step. The existing
thirty-register frame is reused explicitly: its former history slot holds
the witness; its remaining/valid/backup slots hold direction, cumulative
validity and unread-record cursor. No counted-history meaning is assumed. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayStepState
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence (Registers)

structure Saved where
  point : BitString
  recover : Bool
  valid : Bool
  cursor : BitString

def extras (s : Saved) : SourceReplayHistoryStack.Saved :=
  ⟨[s.recover],SourceReplayRecordState.flag s.valid,s.cursor⟩
def enclose (r : Store 26) (s : Saved) : Store 30 :=
  SourceReplayHistoryStack.full r s.point (extras s)
def framed (r : Store 16) (f : SourceReplayRecordState.Saved) : Store 26 :=
  Frame.join r (Frame.join f.store (.cons [] .nil))
def full (r : Registers) (a : SourceReplayState.Saved) (f : SourceReplayRecordState.Saved)
    (s : Saved) : Store 30 := enclose (framed (SourceReplayState.full r a) f) s
def emptyReplay : SourceReplayState.Saved := ⟨[],[],[],[],[],[],[]⟩
def work (input point : BitString) (recover good : Bool) : Store 30 :=
  enclose (SourceReplayRecordState.initial input) ⟨point,recover,good,[]⟩
def initial (input point : BitString) (recover : Bool) : Store 30 := work input point recover false

def lift26 (b : Block 26) : Block 30 := SourceReplayHistoryStack.lift26 b
theorem lift26_exec {b : Block 26} {before after : Store 26} {used : Nat}
    (h : Exec b before used after) (s : Saved) :
    Exec (lift26 b) (enclose before s) used (enclose after s) :=
  SourceReplayHistoryStack.lift26_exec h s.point (extras s)
def lift16 (b : Block 16) : Block 30 := lift26 (Frame.block 10 b)
theorem lift16_exec {b : Block 16} {before after : Store 16} {used : Nat}
    (h : Exec b before used after) (f : SourceReplayRecordState.Saved) (s : Saved) :
    Exec (lift16 b) (enclose (framed before f) s) used (enclose (framed after f) s) :=
  lift26_exec (Frame.execution h (Frame.join f.store (.cons [] .nil))) s
def core9 (b : Block 9) : Block 30 := lift16 (SourceReplayState.core b)
theorem core9_exec {b : Block 9} {before after : Registers} {used : Nat}
    (h : Exec b before.store used after.store) (a : SourceReplayState.Saved)
    (f : SourceReplayRecordState.Saved) (s : Saved) :
    Exec (core9 b) (full before a f s) used (full after a f s) :=
  lift16_exec (SourceReplayState.core_exec h a) f s

theorem record_view (input : BitString) (f : SourceReplayRecordState.Saved) (s : Saved) :
    enclose (SourceReplayRecordState.work input f) s =
      full (SourceReplayState.blank input []) emptyReplay f s := rfl

def captureBlock : Block 30 := .seq (.action (.copy 29 0)) (.action (.copy 28 24))
theorem capture_exec (r : Registers) (a : SourceReplayState.Saved)
    (f : SourceReplayRecordState.Saved) (s : Saved) (good : Bool)
    (known : f.valid = SourceReplayRecordState.flag good) :
    Exec captureBlock (full r a f s) 2 (full r a f {s with cursor := r.input,valid := good}) := by
  have cursor : Exec (.action (.copy (29 : Fin 30) 0)) (full r a f s) 1
      (full r a f {s with cursor := r.input}) := .action _ _
  have flag : Exec (.action (.copy (28 : Fin 30) 24)) (full r a f {s with cursor := r.input}) 1
      (SourceReplayHistoryStack.full (framed (SourceReplayState.full r a) f) s.point
        {extras s with backup := r.input,valid := f.valid}) := .action _ _
  rw [known] at flag
  exact Exec.seq cursor flag

def guard (index : Fin 30) : Block 30 := .branch index (.action (.clear 28)) (.action (.clear 28)) .skip
theorem guard_exec (index : Fin 30) (r : Registers) (a : SourceReplayState.Saved)
    (f : SourceReplayRecordState.Saved) (s : Saved) (good : Bool)
    (read : (full r a f s).get index = SourceReplayRecordState.flag good) :
    Exec (guard index) (full r a f s) 2 (full r a f {s with valid := s.valid && good}) := by
  cases good with
  | false =>
    have checked : Exec (guard index) (full r a f s) 2 (full r a f {s with valid := false}) :=
      Exec.empty read (.action _ _)
    simpa only [Bool.and_false] using checked
  | true =>
    have checked : Exec (guard index) (full r a f s) 2 (full r a f s) := Exec.one read (.skip _)
    simpa only [Bool.and_true] using checked

def clear9 : Block 30 := lift16 SourceReplayState.clean
theorem clear9_exec (r : Registers) (a : SourceReplayState.Saved)
    (f : SourceReplayRecordState.Saved) (s : Saved) :
    Exec clear9 (full r a f s) 10 (full (SourceReplayState.blank [] []) a f s) :=
  lift16_exec (SourceReplayState.clean_exec r a) f s

def width (recover : Bool) (n : Nat) : Nat := if recover then n else n + 1
def widthSelect : Block 30 := .branch 27 .skip (.action (.push 2 true)) .skip
def witnessSeed : Block 30 := .seq (.action (.copy 0 26)) (.seq (.action (.copy 2 16)) widthSelect)
theorem witnessSeed_exec (cursor : BitString) (n : Nat) (f : SourceReplayRecordState.Saved)
    (s : Saved) (dimension : f.dimension = List.replicate n true) :
    Exec witnessSeed (full (SourceReplayState.blank cursor []) emptyReplay f s) 4
      (full ({SourceReplayState.blank [] [] with input := s.point,remaining := List.replicate (width s.recover n) true})
        emptyReplay f s) := by
  let start := SourceReplayState.blank s.point []
  let counted := {start with remaining := List.replicate n true}
  have point : Exec (.action (.copy (0 : Fin 30) 26))
      (full (SourceReplayState.blank cursor []) emptyReplay f s) 1 (full start emptyReplay f s) := .action _ _
  have count : Exec (.action (.copy (2 : Fin 30) 16)) (full start emptyReplay f s) 1
      (full counted emptyReplay f s) := by
    have checked : Exec (.action (.copy (2 : Fin 30) 16)) (full start emptyReplay f s) 1
        (full {start with remaining := f.dimension} emptyReplay f s) := .action _ _
    rw [dimension] at checked
    exact checked
  have read : (full counted emptyReplay f s).get 27 = [s.recover] := rfl
  have selected : Exec widthSelect (full counted emptyReplay f s) 2
      (full ({SourceReplayState.blank [] [] with input := s.point,remaining := List.replicate (width s.recover n) true})
        emptyReplay f s) := by
    cases direction : s.recover with
    | false =>
      have push : Exec (.action (.push (2 : Fin 30) true)) (full counted emptyReplay f s) 1
          (full {start with remaining := List.replicate (n + 1) true} emptyReplay f s) := by
        simp only [counted,List.replicate_succ]
        exact .action _ _
      rw [direction] at read
      simpa only [widthSelect,width,direction,Bool.false_eq_true,↓reduceIte,start,SourceReplayState.blank] using Exec.zero read push
    | true =>
      rw [direction] at read
      have checked : Exec widthSelect (full counted emptyReplay f s) 2 (full counted emptyReplay f s) :=
        Exec.one read (.skip _)
      simpa only [width,direction,↓reduceIte,counted,start,SourceReplayState.blank] using checked
  exact Exec.seq point (Exec.seq count selected)

def mapped (f : SourceReplayRecordState.Saved) (point : BitString) : SourceReplayState.Saved :=
  ⟨f.weights,f.source,f.pivot,f.tail,point,f.dimension,[]⟩
def mapSetup : Block 30 :=
  .seq (.action (.copy 9 19)) <| .seq (.action (.copy 10 18)) <|
  .seq (.action (.copy 11 20)) <| .seq (.action (.copy 12 21)) <|
  .seq (.action (.copy 13 26)) (.action (.copy 14 16))
theorem mapSetup_exec (f : SourceReplayRecordState.Saved) (s : Saved) :
    Exec mapSetup (full (SourceReplayState.blank [] []) emptyReplay f s) 6
      (full (SourceReplayState.blank [] []) (mapped f s.point) f s) := by
  let a1 := {emptyReplay with weights := f.weights}
  let a2 := {a1 with source := f.source}
  let a3 := {a2 with pivot := f.pivot}
  let a4 := {a3 with tail := f.tail}
  let a5 := {a4 with point := s.point}
  let r := SourceReplayState.blank [] []
  have h1 : Exec (.action (.copy (9 : Fin 30) 19)) (full r emptyReplay f s) 1 (full r a1 f s) := .action _ _
  have h2 : Exec (.action (.copy (10 : Fin 30) 18)) (full r a1 f s) 1 (full r a2 f s) := .action _ _
  have h3 : Exec (.action (.copy (11 : Fin 30) 20)) (full r a2 f s) 1 (full r a3 f s) := .action _ _
  have h4 : Exec (.action (.copy (12 : Fin 30) 21)) (full r a3 f s) 1 (full r a4 f s) := .action _ _
  have h5 : Exec (.action (.copy (13 : Fin 30) 26)) (full r a4 f s) 1 (full r a5 f s) := .action _ _
  have h6 : Exec (.action (.copy (14 : Fin 30) 16)) (full r a5 f s) 1
      (full r (mapped f s.point) f s) := .action _ _
  exact Exec.seq h1 (Exec.seq h2 (Exec.seq h3 (Exec.seq h4 (Exec.seq h5 h6))))

theorem copyPoint_exec (r : Registers) (a : SourceReplayState.Saved)
    (f : SourceReplayRecordState.Saved) (s : Saved) :
    Exec (.action (.copy (26 : Fin 30) 8)) (full r a f s) 1
      (full r a f {s with point := r.output}) := .action _ _

def finishBlock : Block 30 := .seq SourceReplayHistoryStack.clearWork
  (.seq (.action (.copy 0 29)) (.action (.clear 29)))
theorem finish_exec (r : Store 26) (s : Saved) :
    Exec finishBlock (enclose r s) 29
      (enclose (SourceReplayRecordState.initial s.cursor) {s with cursor := []}) := by
  have first := SourceReplayHistoryStack.clearWork_exec r s.point (extras s)
  have restore : Exec (.action (.copy (0 : Fin 30) 29))
      (enclose (SourceReplayRecordState.initial []) s) 1
      (enclose (SourceReplayRecordState.initial s.cursor) s) := .action _ _
  have clear : Exec (.action (.clear (29 : Fin 30)))
      (enclose (SourceReplayRecordState.initial s.cursor) s) 1
      (enclose (SourceReplayRecordState.initial s.cursor) {s with cursor := []}) := .action _ _
  exact Exec.seq first (Exec.seq restore clear)

end PNP.Concrete.ResidualReduction.SourceReplayStepState
