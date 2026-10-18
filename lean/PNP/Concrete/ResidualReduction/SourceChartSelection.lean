import PNP.Concrete.ResidualReduction.SourceChartCoordinates

/-! Literal first-one scan, pivot count and coordinate deletion. The bounded
block retains the first pivot in the existing finite-coordinate encoding and
constructs the exact chart tail. An all-zero direction remains explicit failure.
These are source-instruction costs, not yet the complete successor runtime. -/

namespace PNP.Concrete.ResidualReduction.SourceChartSelection
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.SourceChartCoordinates

def skipFalse : Block 9 := .seq (.action (.pop 0)) <|
  .seq (.action (.push 1 true)) (.action (.push 3 false))
def found : Block 9 := .seq (.action (.copy 8 0)) <|
  .seq (.action (.pop 8)) <| .seq (.action (.push 4 true)) (.action (.clear 0))
def scanBody : Block 9 := .branch 0 .skip skipFalse found
def scan : Block 9 := .loop 0 scanBody
def failure : Block 9 := .seq (.action (.clear 3)) (.action (.clear 8))
def finish : Block 9 := .branch 4 failure failure ClauseQuery.reverseLoop
def block : Block 9 := .seq scan finish

def ready (word : BitString) : Registers := ⟨word,[false],[],[],[],[],[],[],[]⟩
def selected (k : Nat) (suffix : BitString) : Registers :=
  ⟨[],natural k,[],[],[true],[],[],[],List.replicate k false ++ suffix⟩
def absent (n : Nat) : Registers := ⟨[],natural n,[],[],[],[],[],[],[]⟩

private theorem repeat_cons (n : Nat) (b : Bool) (tail : BitString) :
    List.replicate n b ++ b :: tail = b :: (List.replicate n b ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,ih]

theorem found_exec (r : Registers) (suffix : BitString) :
    Exec found ({r with input := true :: suffix}).store 4
      ({r with input := [],sign := true :: r.sign,output := suffix}).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

theorem scan_found_exec (r : Registers) (k : Nat) (suffix : BitString) :
    Exec scan ({r with input := List.replicate k false ++ true :: suffix}).store (5 * k + 7)
      ({r with input := [],target := List.replicate k true ++ r.target, excess := List.replicate k false ++ r.excess,sign := true :: r.sign,output := suffix}).store := by
  induction k generalizing r with
  | zero =>
    exact Exec.loopStep (source := (0 : Fin 9)) rfl
      (Exec.one rfl (found_exec r suffix)) (Exec.loopStop rfl)
  | succ k ih =>
    have step : Exec scanBody
        ({r with input := false :: (List.replicate k false ++ true :: suffix)}).store 4
        ({r with input := List.replicate k false ++ true :: suffix, target := true :: r.target,excess := false :: r.excess}).store :=
      Exec.zero rfl (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
    have checked := Exec.loopStep (source := (0 : Fin 9)) rfl step
      (ih {r with target := true :: r.target,excess := false :: r.excess})
    have cost : 5 * (k + 1) + 7 = 1 + (4 + (5 * k + 7)) := by omega
    simpa only [scan,cost,List.replicate_succ,List.cons_append,repeat_cons] using checked

theorem scan_absent_exec (r : Registers) (n : Nat) :
    Exec scan ({r with input := List.replicate n false}).store (5 * n + 1)
      ({r with input := [],target := List.replicate n true ++ r.target, excess := List.replicate n false ++ r.excess}).store := by
  induction n generalizing r with
  | zero => exact Exec.loopStop rfl
  | succ n ih =>
    have step : Exec scanBody ({r with input := false :: List.replicate n false}).store 4
        ({r with input := List.replicate n false, target := true :: r.target,excess := false :: r.excess}).store :=
      Exec.zero rfl (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
    have checked := Exec.loopStep (source := (0 : Fin 9)) rfl step
      (ih {r with target := true :: r.target,excess := false :: r.excess})
    have cost : 5 * (n + 1) + 1 = 1 + (4 + (5 * n + 1)) := by omega
    simpa only [scan,cost,List.replicate_succ,List.cons_append,repeat_cons] using checked

theorem block_found_exec (k : Nat) (suffix : BitString) :
    Exec block (ready (List.replicate k false ++ true :: suffix)).store (9 * k + 9)
      (selected k suffix).store := by
  let before := ready (List.replicate k false ++ true :: suffix)
  let scanned := {before with input := [],target := natural k, excess := List.replicate k false,sign := [true],output := suffix}
  have first : Exec scan before.store (5 * k + 7) scanned.store := by
    simpa only [before,ready,scanned,natural,List.append_nil] using
      scan_found_exec before k suffix
  have rev : Exec ClauseQuery.reverseLoop scanned.store (4 * k + 1)
      (selected k suffix).store := by
    simpa only [scanned,before,ready,selected,List.length_replicate,
      List.reverse_replicate] using ClauseQuery.reverse_exec scanned (List.replicate k false)
  have last : Exec finish scanned.store (1 + (4 * k + 1)) (selected k suffix).store :=
    Exec.one rfl rev
  have cost : 9 * k + 9 = (5 * k + 7) + (1 + (4 * k + 1)) := by omega
  simpa only [block,cost,before] using Exec.seq first last

theorem block_absent_exec (n : Nat) :
    Exec block (ready (List.replicate n false)).store (5 * n + 4) (absent n).store := by
  let before := ready (List.replicate n false)
  let scanned := {before with input := [],target := natural n,excess := List.replicate n false}
  have first : Exec scan before.store (5 * n + 1) scanned.store := by
    simpa only [scanned,before,ready,natural,List.append_nil] using scan_absent_exec before n
  have last : Exec finish scanned.store 3 (absent n).store :=
    Exec.empty rfl (Exec.seq (.action _ _) (.action _ _))
  have cost : 5 * n + 4 = (5 * n + 1) + 3 := by omega
  simpa only [block,cost,before] using Exec.seq first last

theorem word_cases (word : BitString) :
    word = List.replicate word.length false ∨
      ∃ k suffix, word = List.replicate k false ++ true :: suffix := by
  induction word with
  | nil => exact Or.inl rfl
  | cons b tail ih =>
    cases b with
    | true => exact Or.inr ⟨0,tail,rfl⟩
    | false =>
      cases ih with
      | inl h =>
        exact Or.inl (by simpa only [List.length_cons,List.replicate_succ] using congrArg (List.cons false) h)
      | inr h =>
        obtain ⟨k,suffix,h⟩ := h
        exact Or.inr ⟨k + 1,suffix,by
          simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons false) h⟩

theorem block_exec (word : BitString) :
    ∃ ticks, ∃ out : Registers, Exec block (ready word).store ticks out.store ∧ ticks ≤ 9 * word.length + 9 := by
  rcases word_cases word with h | ⟨k,suffix,h⟩
  · refine ⟨5 * word.length + 4,absent word.length,?_,by omega⟩
    simpa only [← h] using block_absent_exec word.length
  · refine ⟨9 * k + 9,selected k suffix,?_,?_⟩
    · rw [h]; exact block_found_exec k suffix
    · rw [h,List.length_append,List.length_replicate,List.length_cons]
      omega

theorem chosen_exec {n : Nat} (v : Point (n + 1))
    (c : Fin (n + 1) × Point n) (h : chooseChart v = some c) :
    Exec block (ready ((SourceEncoding.pointCodec (n + 1)).encode v)).store (9 * c.1.val + 9)
      (⟨[],(finCodec (n + 1)).encode c.1,[],[],[true],[],[],[],
        (SourceEncoding.pointCodec n).encode c.2⟩ : Registers).store := by
  obtain ⟨suffix,whole,tail⟩ := chosen_split v c h
  rw [whole,tail]
  exact block_found_exec c.1.val suffix

theorem absent_exec {n : Nat} (v : Point (n + 1)) (h : chooseChart v = none) :
    Exec block (ready ((SourceEncoding.pointCodec (n + 1)).encode v)).store
      (5 * (n + 1) + 4) (absent (n + 1)).store := by
  rw [absent_bytes v h]
  exact block_absent_exec (n + 1)

end PNP.Concrete.ResidualReduction.SourceChartSelection
