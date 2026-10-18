import PNP.Concrete.ResidualReduction.SourceLinePullbackState

/-! Restartable framed query calls. Every scratch register is cleared before a
query, while the source, cursor and candidate data remain outside the working
prefix. Resetting and copying are actual counted instructions. -/

namespace PNP.Concrete.ResidualReduction.SourceSelectionFrame
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.SourceLinePullback
  (transfers transferStore transfers_exec copy_from_saved copy_to_saved)

def reset (count : Nat) : Block count :=
  transfers ((List.finRange count).map Action.clear)

theorem cleared_get {count : Nat} (indices : List (Fin count)) (r : Store count) (i : Fin count) :
    (transferStore (indices.map Action.clear) r).get i =
      if i ∈ indices then [] else r.get i := by
  induction indices generalizing r with
  | nil => rfl
  | cons j indices ih =>
    simp only [List.map_cons,transferStore,ih,Action.update,Action.instruction,
      Instruction.update,Store.get_set,List.mem_cons]
    by_cases tail : i ∈ indices
    · simp only [tail,or_true,↓reduceIte]
    · simp only [tail,or_false,↓reduceIte]

theorem empty_get {count : Nat} (i : Fin count) : (Store.empty count).get i = [] := by
  induction count with
  | zero => exact Fin.elim0 i
  | succ count ih =>
    exact Store.indexCases (motive := fun k => (Store.empty (count + 1)).get k = [])
      rfl (fun j => ih j) i

theorem reset_store {count : Nat} (r : Store count) :
    transferStore ((List.finRange count).map Action.clear) r = Store.empty count := by
  apply Store.ext
  intro i
  rw [cleared_get,empty_get]
  simp only [List.mem_finRange,↓reduceIte]

theorem reset_exec {count : Nat} (r : Store count) :
    Exec (reset count) r (count + 1) (Store.empty count) := by
  have checked := transfers_exec ((List.finRange count).map Action.clear) r
  simpa only [reset,reset_store,List.length_map,List.length_finRange] using checked

theorem reset_framed {count extra : Nat} (r : Store count) (data : Store extra) :
    Exec (Frame.block extra (reset count)) (Frame.join r data) (count + 1)
      (Frame.join (Store.empty count) data) :=
  Frame.execution (reset_exec r) data

def restart {count extra : Nat} (input : Fin count) (packet : Fin extra) : Block (extra + count) :=
  .seq (Frame.block extra (reset count))
    (.action (.copy (Frame.index extra input) (Frame.frameIndex count packet)))
theorem restart_exec {count extra : Nat} (r : Store count) (data : Store extra)
    (input : Fin count) (packet : Fin extra) :
    Exec (restart input packet) (Frame.join r data) (count + 2)
      (Frame.join ((Store.empty count).set input (data.get packet)) data) := by
  have first := reset_framed r data
  have second := copy_from_saved (Store.empty count) data input packet
  have cost : count + 2 = (count + 1) + 1 := by omega
  simpa only [restart,cost] using Exec.seq first second

def invoke {count extra : Nat} (query : Block count) (input output : Fin count)
    (packet destination : Fin extra) : Block (extra + count) :=
  .seq (restart input packet) <| .seq (Frame.block extra query)
    (.action (.copy (Frame.frameIndex count destination) (Frame.index extra output)))

theorem invoke_exec {count extra : Nat} (query : Block count) (input output : Fin count)
    (packet destination : Fin extra) (r : Store count) (data : Store extra)
    (used : Nat) (after : Store count)
    (checked : Exec query ((Store.empty count).set input (data.get packet)) used after) :
    Exec (invoke query input output packet destination) (Frame.join r data)
      ((count + 2) + (used + 1))
      (Frame.join after (data.set destination (after.get output))) :=
  Exec.seq (restart_exec r data input packet)
    (Exec.seq (Frame.execution checked data) (copy_to_saved after data destination output))

theorem result_saved {count extra : Nat} (after : Store count) (data : Store extra)
    (destination : Fin extra) (output : Fin count) :
    (Frame.join after (data.set destination (after.get output))).get
      (Frame.frameIndex count destination) = after.get output := by
  rw [Frame.get_frame,Store.get_set_same]

theorem other_saved {count extra : Nat} (after : Store count) (data : Store extra)
    (destination i : Fin extra) (output : Fin count) (different : i ≠ destination) :
    (Frame.join after (data.set destination (after.get output))).get
      (Frame.frameIndex count i) = data.get i := by
  rw [Frame.get_frame,Store.get_set]
  simp only [different,↓reduceIte]

end PNP.Concrete.ResidualReduction.SourceSelectionFrame
