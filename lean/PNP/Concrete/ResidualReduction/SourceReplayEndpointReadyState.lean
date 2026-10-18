import PNP.Concrete.ResidualReduction.SourceReplayEndpointRun

/-! Workspace transition from the literal data loader to guarded replay.
The history count is read from the saved forward stream. Reverse history and
request fields are retained until selection; only obsolete scratch is cleared. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointReadyState
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence (Registers)

def core (r : Registers) : Store 26 :=
  SourceReplayStepState.framed (SourceReplayState.full r SourceReplayStepState.emptyReplay)
    SourceReplayRecordState.emptySaved
def full (r : Registers) (history : BitString) (h : SourceReplayHistoryStack.Saved)
    (d : SourceReplayDataMachine.Saved) (s : SourceReplayEndpointState.Saved) : Store 40 :=
  SourceReplayEndpointState.full (SourceReplayDataMachine.full
    (SourceReplayHistoryStack.full (core r) history h) d) s
def core9 (b : Block 9) : Block 40 :=
  SourceReplayEndpointState.lift35 (SourceReplayDataMachine.lift30
    (SourceReplayHistoryStack.lift26 (Frame.block 10 (SourceReplayState.core b))))
theorem core9_exec {b : Block 9} {before after : Registers} {used : Nat}
    (checked : Exec b before.store used after.store) (history : BitString) (h : SourceReplayHistoryStack.Saved)
    (d : SourceReplayDataMachine.Saved) (s : SourceReplayEndpointState.Saved) :
    Exec (core9 b) (full before history h d s) used (full after history h d s) :=
  SourceReplayEndpointState.lift35_exec (SourceReplayDataMachine.lift30_exec
    (SourceReplayHistoryStack.lift26_exec
      (Frame.execution (SourceReplayState.core_exec checked SourceReplayStepState.emptyReplay)
        (Frame.join SourceReplayRecordState.emptySaved.store (.cons [] .nil))) history h) d) s

theorem copy_exec (before after : Store 40) (destination source : Fin 40) (value : BitString)
    (read : before.get source = value) (write : before.set destination value = after) :
    Exec (.action (.copy destination source)) before 1 after := by
  have checked := Exec.action (.copy destination source) before
  simpa only [Action.update,Action.instruction,Instruction.update,read,write] using checked
theorem push_exec (before after : Store 40) (destination : Fin 40) (bit : Bool)
    (read : before.get destination = []) (write : before.set destination [bit] = after) :
    Exec (.action (.push destination bit)) before 1 after := by
  have checked := Exec.action (.push destination bit) before
  simpa only [Action.update,Action.instruction,Instruction.update,read,write] using checked

theorem read_history (r : Registers) (history : BitString) (h : SourceReplayHistoryStack.Saved)
    (d : SourceReplayDataMachine.Saved) (s : SourceReplayEndpointState.Saved) :
    (full r history h d s).get 26 = history :=
  (Frame.get_core _ s.store 26).trans ((Frame.get_core _ d.store 26).trans
    ((Frame.get_core _ h.store 26).trans (Frame.get_frame (core r) (.cons history .nil) 0)))
theorem read_direction (r : Registers) (history : BitString) (h : SourceReplayHistoryStack.Saved)
    (d : SourceReplayDataMachine.Saved) (s : SourceReplayEndpointState.Saved) :
    (full r history h d s).get 27 = h.remaining :=
  (Frame.get_core _ s.store 27).trans ((Frame.get_core _ d.store 27).trans
    (Frame.get_frame _ h.store 0))
theorem read_forward (r : Registers) (history : BitString) (h : SourceReplayHistoryStack.Saved)
    (d : SourceReplayDataMachine.Saved) (s : SourceReplayEndpointState.Saved) :
    (full r history h d s).get 33 = d.forward :=
  (Frame.get_core _ s.store 33).trans (Frame.get_frame _ d.store 3)
theorem read_mode (r : Registers) (history : BitString) (h : SourceReplayHistoryStack.Saved)
    (d : SourceReplayDataMachine.Saved) (s : SourceReplayEndpointState.Saved) :
    (full r history h d s).get 35 = s.mode := SourceReplayEndpointState.read_mode _ s

def selected (r : Registers) (history : BitString) (s : SourceReplayEndpointState.Saved) : Registers :=
  {r with input := if s.mode.headD false then history else r.input}
def select : Block 40 := .branch 35 .skip .skip (.action (.copy 0 26))
theorem select_exec (r : Registers) (history : BitString) (h : SourceReplayHistoryStack.Saved)
    (d : SourceReplayDataMachine.Saved) (s : SourceReplayEndpointState.Saved) :
    Exec select (full r history h d s) 2 (full (selected r history s) history h d s) := by
  have read := read_mode r history h d s
  have copied : Exec (.action (.copy (0 : Fin 40) 26)) (full r history h d s) 1
      (full {r with input := history} history h d s) :=
    copy_exec _ _ 0 26 history (read_history r history h d s) rfl
  cases mode : s.mode with
  | nil =>
    rw [mode] at read
    simpa only [selected,mode,List.headD_nil,Bool.false_eq_true,↓reduceIte] using
      (show Exec select (full r history h d s) 2 (full r history h d s) from Exec.empty read (.skip _))
  | cons bit rest =>
    rw [mode] at read
    cases bit with
    | false =>
      simpa only [selected,mode,List.headD_cons,Bool.false_eq_true,↓reduceIte] using
        (show Exec select (full r history h d s) 2 (full r history h d s) from Exec.zero read (.skip _))
    | true =>
      simpa only [selected,mode,List.headD_cons,↓reduceIte] using
        (show Exec select (full r history h d s) 2 (full {r with input := history} history h d s) from Exec.one read copied)

def direction : Block 40 := .seq (.action (.clear 27))
  (.branch 35 (.action (.push 27 false)) (.action (.push 27 false)) (.action (.push 27 true)))
theorem direction_exec (r : Registers) (history : BitString) (h : SourceReplayHistoryStack.Saved)
    (d : SourceReplayDataMachine.Saved) (s : SourceReplayEndpointState.Saved) :
    Exec direction (full r history h d s) 3
      (full r history {h with remaining := [s.mode.headD false]} d s) := by
  let empty := {h with remaining := []}
  have cleared : Exec (.action (.clear (27 : Fin 40))) (full r history h d s) 1
      (full r history empty d s) := .action _ _
  have push (bit : Bool) : Exec (.action (.push (27 : Fin 40) bit)) (full r history empty d s) 1
      (full r history {h with remaining := [bit]} d s) :=
    push_exec _ _ 27 bit (read_direction r history empty d s) rfl
  have read := read_mode r history empty d s
  have branch : Exec (.branch 35 (.action (.push 27 false)) (.action (.push 27 false)) (.action (.push 27 true)))
      (full r history empty d s) 2 (full r history {h with remaining := [s.mode.headD false]} d s) := by
    cases mode : s.mode with
    | nil => rw [mode] at read; simpa only [mode,List.headD_nil] using Exec.empty read (push false)
    | cons bit rest =>
      rw [mode] at read
      cases bit with
      | false => simpa only [mode,List.headD_cons] using Exec.zero read (push false)
      | true => simpa only [mode,List.headD_cons] using Exec.one read (push true)
  exact Exec.seq cleared branch

def normalized (s : SourceReplayEndpointState.Saved) : SourceReplayEndpointState.Saved :=
  {s with mode := [s.mode.headD false]}
def normalize : Block 40 := .seq (.action (.clear 35)) (.action (.copy 35 27))
theorem normalize_exec (r : Registers) (history : BitString) (h : SourceReplayHistoryStack.Saved)
    (d : SourceReplayDataMachine.Saved) (s : SourceReplayEndpointState.Saved)
    (direction : h.remaining = [s.mode.headD false]) :
    Exec normalize (full r history h d s) 2 (full r history h d (normalized s)) := by
  let low := SourceReplayDataMachine.full (SourceReplayHistoryStack.full (core r) history h) d
  let cleared := {s with mode := []}
  have first := SourceReplayEndpointState.clear_saved_exec low s 0 cleared rfl
  have read : low.get 27 = [s.mode.headD false] :=
    (Frame.get_core _ d.store 27).trans ((Frame.get_frame _ h.store 0).trans direction)
  have last := SourceReplayEndpointState.copy_saved_exec low cleared 0 27 _ (normalized s) read rfl
  exact Exec.seq first last

def cleanData (d : SourceReplayDataMachine.Saved) : SourceReplayDataMachine.Saved :=
  ⟨d.dimension,[],[],[],[]⟩
def clearExtras : Block 40 := .seq (.action (.clear 28)) <| .seq (.action (.clear 31)) <|
  .seq (.action (.clear 32)) (.seq (.action (.clear 33)) (.action (.clear 34)))
theorem clearExtras_exec (r : Registers) (history : BitString) (h : SourceReplayHistoryStack.Saved)
    (d : SourceReplayDataMachine.Saved) (s : SourceReplayEndpointState.Saved) :
    Exec clearExtras (full r history h d s) 5 (full r history {h with valid := []} (cleanData d) s) := by
  let next := {h with valid := []}
  let d1 := {d with rows := []}
  let d2 := {d1 with core := []}
  let d3 := {d2 with forward := []}
  have a : Exec (.action (.clear (28 : Fin 40))) (full r history h d s) 1 (full r history next d s) := .action _ _
  have b : Exec (.action (.clear (31 : Fin 40))) (full r history next d s) 1 (full r history next d1 s) := .action _ _
  have c : Exec (.action (.clear (32 : Fin 40))) (full r history next d1 s) 1 (full r history next d2 s) := .action _ _
  have e : Exec (.action (.clear (33 : Fin 40))) (full r history next d2 s) 1 (full r history next d3 s) := .action _ _
  have f : Exec (.action (.clear (34 : Fin 40))) (full r history next d3 s) 1 (full r history next (cleanData d) s) := .action _ _
  exact Exec.seq a (Exec.seq b (Exec.seq c (Exec.seq e f)))

def reset : Block 40 := .seq (.action (.copy 29 0)) <| .seq (core9 (SourceChartedSuccessorWords.clearAll 9)) <|
  .seq (.action (.copy 0 29)) (.action (.clear 29))
theorem reset_exec (r : Registers) (history : BitString) (h : SourceReplayHistoryStack.Saved)
    (d : SourceReplayDataMachine.Saved) (s : SourceReplayEndpointState.Saved) :
    Exec reset (full r history h d s) 13
      (full (SourceReplayState.blank r.input []) history {h with backup := []} d s) := by
  let saved := {h with backup := r.input}
  have first : Exec (.action (.copy (29 : Fin 40) 0)) (full r history h d s) 1
      (full r history saved d s) := .action _ _
  have cleaned := core9_exec (before := r) (after := SourceReplayState.blank [] [])
    (SourceChartedSuccessorWords.clearAll_exec r.store) history saved d s
  have read : (full (SourceReplayState.blank [] []) history saved d s).get 29 = r.input :=
    (Frame.get_core _ s.store 29).trans ((Frame.get_core _ d.store 29).trans (Frame.get_frame _ saved.store 2))
  have restored : Exec (.action (.copy (0 : Fin 40) 29))
      (full (SourceReplayState.blank [] []) history saved d s) 1
      (full (SourceReplayState.blank r.input []) history saved d s) := copy_exec _ _ 0 29 r.input read rfl
  have last : Exec (.action (.clear (29 : Fin 40)))
      (full (SourceReplayState.blank r.input []) history saved d s) 1
      (full (SourceReplayState.blank r.input []) history {h with backup := []} d s) := .action _ _
  exact Exec.seq first (Exec.seq cleaned (Exec.seq restored last))

def work (count : Nat) (input point : BitString) (recover : Bool) (s : SourceReplayEndpointState.Saved) : Store 40 :=
  full (SourceReplayState.blank input []) point ⟨[recover],[],[]⟩ ⟨List.replicate count true,[],[],[],[]⟩ s
theorem work_run (count : Nat) (input point : BitString) (p : SourceReplayEndpointRunState.Parameters) (good : Bool) :
    work count input point p.recover (SourceReplayEndpointRunState.saved p good) =
      SourceReplayEndpointRunState.work count input point p false good := by
  simp only [work,full,core,SourceReplayEndpointRunState.work,SourceReplayEndpointRunState.full,
    SourceReplayEndpointRunState.enclose,SourceReplayEndpointRunState.framed,SourceReplayEndpointRunState.middle,
    SourceReplayEndpointState.full,SourceReplayDataMachine.full,SourceReplayLoopMachine.full,
    SourceReplayStepState.full,SourceReplayStepState.enclose,SourceReplayStepState.extras,
    SourceReplayStepState.framed,SourceReplayHistoryStack.full,SourceReplayRecordStack.stacked,
    SourceReplayState.full,SourceReplayState.blank,Registers.store,SourceReplayRecordState.emptySaved,
    SourceReplayRecordState.Saved.store,SourceReplayStepState.emptyReplay,SourceReplayState.Saved.store,
    SourceReplayState.Saved.rest,SourceReplayHistoryStack.Saved.store,SourceReplayDataMachine.Saved.store,
    Frame.join,SourceReplayRecordState.flag,Bool.false_eq_true,↓reduceIte]

end PNP.Concrete.ResidualReduction.SourceReplayEndpointReadyState
