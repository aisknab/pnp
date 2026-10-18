import PNP.Concrete.ResidualReduction.SourceReplayEndpointReadyState

/-! Literal loaded-data to replay-state adapter. Neither the history count,
its direction-selected stream nor the witness is supplied to this machine.
The cumulative validity word is preserved, including on malformed data. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointReady
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence (Registers)
open PNP.Concrete.ResidualReduction.SourceReplayEndpointReadyState

def start (data : BitString) (s : SourceReplayEndpointState.Saved) : Store 40 :=
  full (SourceReplayState.blank (SourceReplayDataFields.history data).input [])
    (SourceReplayDataFields.history data).history
    (SourceReplayHistoryStack.extras 0 (SourceReplayDataFields.history data).valid)
    (SourceReplayDataMachine.saved data) s
theorem loaded_view (data : BitString) (s : SourceReplayEndpointState.Saved) :
    SourceReplayEndpointState.full (SourceReplayDataMachine.result data) s = start data s := rfl
def headerState (data : BitString) (s : SourceReplayEndpointState.Saved) : Store 40 :=
  full (MatrixStrictHeader.result (SourceReplayDataFields.historyInput data) (SourceReplayState.blank [] []))
    (SourceReplayDataFields.history data).history
    (SourceReplayHistoryStack.extras 0 (SourceReplayDataFields.history data).valid)
    (SourceReplayDataMachine.saved data) s
def header : Block 40 := .seq (.action (.copy 0 33)) (core9 MatrixStrictHeader.block)

theorem header_exec (data : BitString) (s : SourceReplayEndpointState.Saved) :
    Exec header (start data s) (1 + MatrixStrictHeader.blockFuel (SourceReplayDataFields.historyInput data))
      (headerState data s) := by
  let history := SourceReplayDataFields.history data
  let h := SourceReplayHistoryStack.extras 0 history.valid
  let d := SourceReplayDataMachine.saved data
  let r := SourceReplayState.blank history.input []
  let forward := SourceReplayDataFields.historyInput data
  have copied : Exec (.action (.copy (0 : Fin 40) 33)) (full r history.history h d s) 1
      (full (SourceReplayState.blank forward []) history.history h d s) :=
    copy_exec _ _ 0 33 forward (read_forward r history.history h d s) rfl
  have parsed := core9_exec (before := SourceReplayState.blank forward [])
    (after := MatrixStrictHeader.result forward (SourceReplayState.blank [] []))
    (MatrixStrictHeader.block_exec forward (SourceReplayState.blank [] [])) history.history h d s
  exact Exec.seq copied parsed

def finish : Block 40 := .seq (.action (.copy 30 1)) <| .seq select <|
  .seq (.action (.copy 26 37)) <| .seq direction <|
  .seq normalize (.seq clearExtras reset)
theorem finish_exec (r : Registers) (history : BitString) (h : SourceReplayHistoryStack.Saved)
    (d : SourceReplayDataMachine.Saved) (s : SourceReplayEndpointState.Saved) (count : Nat)
    (counted : r.target = List.replicate count true) :
    Exec finish (full r history h d s) 27
      (work count (selected r history s).input s.witness (s.mode.headD false) (normalized s)) := by
  let d1 := {d with dimension := List.replicate count true}
  let r1 := selected r history s
  let h1 := {h with remaining := [s.mode.headD false]}
  let h2 := {h1 with valid := []}
  have readCount : (full r history h d s).get 1 = List.replicate count true := counted
  have first : Exec (.action (.copy (30 : Fin 40) 1)) (full r history h d s) 1 (full r history h d1 s) :=
    copy_exec _ _ 30 1 _ readCount rfl
  have choose := select_exec r history h d1 s
  have readPoint : (full r1 history h d1 s).get 37 = s.witness :=
    SourceReplayEndpointState.read_witness _ s
  have point : Exec (.action (.copy (26 : Fin 40) 37)) (full r1 history h d1 s) 1
      (full r1 s.witness h d1 s) := copy_exec _ _ 26 37 _ readPoint rfl
  have mode := direction_exec r1 s.witness h d1 s
  have canonical := normalize_exec r1 s.witness h1 d1 s rfl
  have cleared := clearExtras_exec r1 s.witness h1 d1 (normalized s)
  have cleaned := reset_exec r1 s.witness h2 (cleanData d1) (normalized s)
  exact Exec.seq first (Exec.seq choose (Exec.seq point (Exec.seq mode
    (Exec.seq canonical (Exec.seq cleared cleaned)))))

def result (data : BitString) (s : SourceReplayEndpointState.Saved) : Store 40 :=
  work (SourceReplayEndpointFields.count data) (SourceReplayEndpointFields.stream (s.mode.headD false) data)
    s.witness (s.mode.headD false) (normalized s)
def block : Block 40 := .seq header finish
def fuel (data : BitString) : Nat := MatrixStrictHeader.blockFuel (SourceReplayDataFields.historyInput data) + 28

theorem block_exec (data : BitString) (s : SourceReplayEndpointState.Saved) :
    Exec block (SourceReplayEndpointState.full (SourceReplayDataMachine.result data) s)
      (fuel data) (result data s) := by
  let r := MatrixStrictHeader.result (SourceReplayDataFields.historyInput data) (SourceReplayState.blank [] [])
  let history := SourceReplayDataFields.history data
  have counted : r.target = List.replicate (SourceReplayEndpointFields.count data) true := by
    change List.replicate (SourceReplayEndpointFields.count data) true ++ [] = _
    rw [List.append_nil]
  have last := finish_exec r history.history (SourceReplayHistoryStack.extras 0 history.valid)
    (SourceReplayDataMachine.saved data) s (SourceReplayEndpointFields.count data) counted
  have cost : fuel data = (1 + MatrixStrictHeader.blockFuel (SourceReplayDataFields.historyInput data)) + 27 := by
    unfold fuel
    omega
  rw [loaded_view]
  simpa only [block,cost,result,selected,r,MatrixStrictHeader.result,SourceReplayEndpointFields.stream,history] using
    Exec.seq (header_exec data s) last

theorem fuel_bound (data : BitString) : fuel data ≤ 4 * data.length + 37 := by
  have checked := MatrixStrictHeader.blockFuel_bound (SourceReplayDataFields.historyInput data)
  obtain ⟨_,_,_,_,history,_⟩ := SourceReplayDataFields.bounds data
  unfold fuel
  omega

end PNP.Concrete.ResidualReduction.SourceReplayEndpointReady
