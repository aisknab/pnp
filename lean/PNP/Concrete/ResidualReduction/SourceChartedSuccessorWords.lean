import PNP.Concrete.ResidualReduction.SourceCoefficientGateRaw
import PNP.Concrete.BitRegisterCopyProgram

/-! Literal workspace reset and word concatenation used at successor stage
boundaries. These operations do not compute mathematical results: their output
is exactly the retained bytes, with scratch reset before each component call. -/

namespace PNP.Concrete.ResidualReduction.SourceChartedSuccessorWords
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence

def clearList {count : Nat} : List (Fin count) → Block count
  | [] => .skip
  | i :: rest => .seq (.action (.clear i)) (clearList rest)
def cleared {count : Nat} (s : Store count) : List (Fin count) → Store count
  | [] => s
  | i :: rest => cleared (s.set i []) rest

theorem clear_exec {count : Nat} (s : Store count) (indices : List (Fin count)) :
    Exec (clearList indices) s (indices.length + 1) (cleared s indices) := by
  induction indices generalizing s with
  | nil => exact .skip _
  | cons i rest ih =>
    have cost : (i :: rest).length + 1 = 1 + (rest.length + 1) := by
      simp only [List.length_cons]
      omega
    simpa only [clearList,cleared,cost] using
      Exec.seq (Exec.action (.clear i) s) (ih (s.set i []))

theorem cleared_get {count : Nat} (s : Store count) (indices : List (Fin count)) (i : Fin count) :
    (cleared s indices).get i = if i ∈ indices then [] else s.get i := by
  induction indices generalizing s with
  | nil => rfl
  | cons j rest ih =>
    rw [cleared,ih,Store.get_set]
    simp only [List.mem_cons]
    by_cases ht : i ∈ rest
    · rw [if_pos ht,if_pos (Or.inr ht)]
    · rw [if_neg ht]
      by_cases hi : i = j
      · rw [if_pos hi,if_pos (Or.inl hi)]
      · rw [if_neg hi,if_neg (fun h => h.elim hi ht)]

theorem empty_get (count : Nat) (i : Fin count) : (Store.empty count).get i = [] := by
  induction count with
  | zero => exact Fin.elim0 i
  | succ count ih =>
    exact Store.indexCases (motive := fun i => (Store.empty (count + 1)).get i = []) rfl (fun j => ih j) i

def clearAll (count : Nat) : Block count := clearList (List.finRange count)
theorem cleared_all {count : Nat} (s : Store count) :
    cleared s (List.finRange count) = Store.empty count := by
  apply Store.ext
  intro i
  rw [cleared_get,if_pos (List.mem_finRange i),empty_get]

theorem clearAll_exec {count : Nat} (s : Store count) :
    Exec (clearAll count) s (count + 1) (Store.empty count) := by
  simpa only [clearAll,List.length_finRange,cleared_all] using clear_exec s (List.finRange count)

def prependReady (r : Registers) (word out : BitString) : Registers :=
  {r with input := [],excess := [],mode := word,output := out}
def prepended (r : Registers) (word out : BitString) : Registers :=
  {r with input := [],excess := [],mode := [],output := word ++ out}
def prepare : Block 9 := .seq (.action (.copy 0 8)) <|
  .seq (.action (.copy 3 5)) <| .seq (.action (.clear 8)) (.action (.clear 5))
def reversePrepare : Block 9 := .seq (.action (.copy 3 8)) (.action (.copy 8 0))
def prepend : Block 9 := .seq prepare <| .seq ClauseQuery.reverseLoop <|
  .seq reversePrepare <| .seq ClauseQuery.reverseLoop (.action (.clear 0))

theorem prepend_exec (r : Registers) (word out : BitString) :
    Exec prepend (prependReady r word out).store (8 * word.length + 9)
      (prepended r word out).store := by
  let base := {r with input := out,excess := [],mode := [],output := []}
  let loaded := {base with excess := word}
  let reversed := {base with output := word.reverse}
  let second := {base with excess := word.reverse,output := out}
  let done := {base with output := word ++ out}
  have setup : Exec prepare (prependReady r word out).store 4 loaded.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have reverse : Exec ClauseQuery.reverseLoop loaded.store (4 * word.length + 1) reversed.store := by
    simpa only [loaded,reversed,base,List.append_nil] using ClauseQuery.reverse_exec base word
  have next : Exec reversePrepare reversed.store 2 second.store := Exec.seq (.action _ _) (.action _ _)
  have forward : Exec ClauseQuery.reverseLoop second.store (4 * word.length + 1) done.store := by
    simpa only [second,done,base,List.length_reverse,List.reverse_reverse] using
      ClauseQuery.reverse_exec {base with output := out} word.reverse
  have finish : Exec (.action (.clear (0 : Fin 9))) done.store 1 (prepended r word out).store := .action _ _
  have cost : 8 * word.length + 9 =
      4 + ((4 * word.length + 1) + (2 + ((4 * word.length + 1) + 1))) := by omega
  simpa only [prepend,cost] using Exec.seq setup (Exec.seq reverse (Exec.seq next (Exec.seq forward finish)))

end PNP.Concrete.ResidualReduction.SourceChartedSuccessorWords
