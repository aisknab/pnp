import PNP.Concrete.ResidualReduction.SourceCandidateBudget
import PNP.Concrete.ResidualReduction.SourcePlaneMenuBudget

/-! Protected state for the affine-first selector. Registers 46 and 47 retain
the computed line menu and its original record width while either query search
uses the complete 46-register prefix. A present answer is classified by the
literal normal count in register 39, not by stale scratch state. -/

namespace PNP.Concrete.ResidualReduction.SourceSelectorState
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceSelectionInvocation (Data)
open PNP.Concrete.ResidualReduction.SourceCandidateLoad (Held)

structure Saved where
  menu : BitString
  width : BitString
deriving Repr
def Saved.store (s : Saved) : Store 2 := .cons s.menu (.cons s.width .nil)
def full (r : Store 38) (d : Data) (t : Held) (s : Saved) : Store 48 :=
  Frame.join (SourceCandidateLoad.full r d t) s.store
def dataFrame (d : Data) (t : Held) (s : Saved) : Store 10 :=
  Frame.join (Frame.join d.store t.store) s.store
def menuCore (r : Store 14) : Store 38 := Frame.join r (Store.empty 24)
def menuFrame (d : Data) (t : Held) (s : Saved) : Store 34 :=
  Frame.join (Store.empty 24) (dataFrame d t s)

theorem output_get (r : Store 38) (d : Data) (t : Held) (s : Saved) :
    (full r d t s).get 43 = d.output :=
  (Frame.get_core (SourceCandidateLoad.full r d t) s.store (43 : Fin 46)).trans
    (SourceCandidateSearch.output_get r d t)
theorem pending_get (r : Store 38) (d : Data) (t : Held) (s : Saved) :
    (full r d t s).get 44 = t.pending :=
  (Frame.get_core (SourceCandidateLoad.full r d t) s.store (44 : Fin 46)).trans
    (SourceCandidateSearch.pending_get r d t)
theorem menu_get (r : Store 38) (d : Data) (t : Held) (s : Saved) :
    (full r d t s).get 46 = s.menu :=
  Frame.get_frame (SourceCandidateLoad.full r d t) s.store 0
theorem width_get (r : Store 38) (d : Data) (t : Held) (s : Saved) :
    (full r d t s).get 47 = s.width :=
  Frame.get_frame (SourceCandidateLoad.full r d t) s.store 1

private theorem set_saved {extra count : Nat} (core : Store count) (frame : Store extra)
    (i : Fin extra) (word : BitString) :
    (Frame.join core frame).set (Frame.frameIndex count i) word =
      Frame.join core (frame.set i word) := by
  induction core with
  | nil =>
    have position : Frame.frameIndex 0 i = i := by
      apply Fin.ext
      exact Nat.zero_add i.val
    rw [position]
    rfl
  | @cons count first rest ih =>
    have position : Frame.frameIndex (count + 1) i = (Frame.frameIndex count i).succ := by
      apply Fin.ext
      change count + 1 + i.val = count + i.val + 1
      omega
    rw [position]
    exact congrArg (Store.cons first) ih

private theorem clear_saved {count extra : Nat} (r : Store count) (d : Store extra) (i : Fin extra) :
    Exec (.action (.clear (Frame.frameIndex count i))) (Frame.join r d) 1
      (Frame.join r (d.set i [])) := by
  have checked := Exec.action (.clear (Frame.frameIndex count i)) (Frame.join r d)
  simpa only [Action.update,Action.instruction,Instruction.update,set_saved] using checked
private theorem push_saved {count extra : Nat} (r : Store count) (d : Store extra)
    (i : Fin extra) (b : Bool) :
    Exec (.action (.push (Frame.frameIndex count i) b)) (Frame.join r d) 1
      (Frame.join r (d.set i (b :: d.get i))) := by
  have checked := Exec.action (.push (Frame.frameIndex count i) b) (Frame.join r d)
  simpa only [Action.update,Action.instruction,Instruction.update,Frame.get_frame,set_saved] using checked

def countPrefix : BitString → Block 44
  | [] => .action (.clear 39)
  | b :: rest => .seq (countPrefix rest) (.action (.push 39 b))
theorem countPrefix_exec (r : Store 38) (d : Data) (word : BitString) :
    Exec (countPrefix word) (SourceSelectionInvocation.full r d) (word.length + 1)
      (SourceSelectionInvocation.full r {d with count := word}) := by
  induction word with
  | nil => exact clear_saved r d.store 1
  | cons b rest ih =>
    have pushed := push_saved r ({d with count := rest} : Data).store (1 : Fin 6) b
    have position : Frame.frameIndex 38 (1 : Fin 6) = (39 : Fin 44) := rfl
    rw [position] at pushed
    have cost : (b :: rest).length + 1 = (rest.length + 1) + 1 := rfl
    simpa only [countPrefix,cost,SourceSelectionInvocation.full,Data.store,Store.get,Store.set,Store.indexCases]
      using Exec.seq ih pushed

def countWrite (word : BitString) : Block 48 := Frame.block 2 (Frame.block 2 (countPrefix word))
theorem countWrite_exec (r : Store 38) (d : Data) (t : Held) (s : Saved) (word : BitString) :
    Exec (countWrite word) (full r d t s) (word.length + 1)
      (full r {d with count := word} t s) :=
  Frame.execution (Frame.execution (countPrefix_exec r d word) t.store) s.store

def reset : Block 48 :=
  Frame.block 2 (Frame.block 2 (Frame.block 6 (SourceSelectionFrame.reset 38)))
theorem reset_exec (r : Store 38) (d : Data) (t : Held) (s : Saved) :
    Exec reset (full r d t s) 39 (full (Store.empty 38) d t s) :=
  Frame.execution (Frame.execution (SourceSelectionFrame.reset_framed r d.store) t.store) s.store

theorem data_current (base d : Data)
    (dimension : d.dimension = base.dimension) (count : d.count = base.count)
    (family : d.family = base.family) :
    d = SourceCandidateSearch.current base d.normals d.packet d.output := by
  rcases base with ⟨bd,bc,bn,bf,bp,bo⟩
  rcases d with ⟨dd,dc,dn,df,dp,do'⟩
  cases dimension
  cases count
  cases family
  rfl

theorem correct_current {α β : Type} (base d : Data) (encode : α → BitString)
    (payload : β → BitString) (hit : Option (α × β))
    (h : SourceCandidateSearch.Correct base encode payload hit d) :
    d = SourceCandidateSearch.current base d.normals d.packet d.output :=
  data_current base d h.1 h.2.1 h.2.2.1

theorem prefix_working_get (r : Store 38) (d : Data) (t : Held) (i : Fin 38) :
    (SourceCandidateLoad.full r d t).get (Frame.index 8 i) = r.get i :=
  (Frame.get_core (SourceSelectionInvocation.full r d) t.store (Frame.index 6 i)).trans
    (Frame.get_core r d.store i)

def copyPending (i : Fin 38) : Block 48 := .action (.copy 44 (Frame.index 10 i))
theorem copyPending_exec (r : Store 38) (d : Data) (t : Held) (s : Saved) (i : Fin 38) :
    Exec (copyPending i) (full r d t s) 1 (full r d {t with pending := r.get i} s) := by
  have checked := SourceLinePullback.copy_to_saved (SourceSelectionInvocation.full r d) t.store
    0 (Frame.index 6 i)
  have read : (SourceSelectionInvocation.full r d).get (Frame.index 6 i) = r.get i :=
    Frame.get_core r d.store i
  rw [read] at checked
  exact Frame.execution checked s.store

def copyMenu (i : Fin 38) : Block 48 := .action (.copy 46 (Frame.index 10 i))
theorem copyMenu_exec (r : Store 38) (d : Data) (t : Held) (s : Saved) (i : Fin 38) :
    Exec (copyMenu i) (full r d t s) 1 (full r d t {s with menu := r.get i}) := by
  have checked := SourceLinePullback.copy_to_saved (SourceCandidateLoad.full r d t) s.store
    0 (Frame.index 8 i)
  rw [prefix_working_get] at checked
  exact checked

def copyWidth : Block 48 := .action (.copy 45 47)
theorem copyWidth_exec (r : Store 38) (d : Data) (t : Held) (s : Saved) :
    Exec copyWidth (full r d t s) 1 (full r d {t with width := s.width} s) := by
  have changed : (full r d t s).set 45 s.width = full r d {t with width := s.width} s := by
    change (Frame.join (SourceCandidateLoad.full r d t) s.store).set
      (Frame.index 2 (Frame.frameIndex 44 (1 : Fin 2))) s.width = _
    rw [Frame.set_core]
    change Frame.join ((Frame.join (SourceSelectionInvocation.full r d) t.store).set
      (Frame.frameIndex 44 (1 : Fin 2)) s.width) s.store = _
    rw [set_saved]
    rfl
  have checked := Exec.action (.copy (45 : Fin 48) 47) (full r d t s)
  change Exec copyWidth (full r d t s) 1
    ((full r d t s).set 45 ((full r d t s).get 47)) at checked
  rw [width_get,changed] at checked
  exact checked

end PNP.Concrete.ResidualReduction.SourceSelectorState
