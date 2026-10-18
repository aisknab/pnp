import PNP.Concrete.ResidualReduction.SourceMenuCompare

/-! Literal candidate/prefix/suffix copies for ordered insertion. The prefix
is stored reversed while searching, and is reversed exactly once on output.
Every copying pass is included in the instruction count. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuInsertOutput
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence

def appendReady (r : Registers) (source : Fin 9) : Registers :=
  {r with excess := r.store.get source, output := r.reserved}
def appendPrepare (source : Fin 9) : Block 9 :=
  .seq (.action (.copy 3 source)) (.action (.copy 8 7))
theorem appendPrepare_exec (r : Registers) (source : Fin 9) :
    Exec (appendPrepare source) r.store 2 (appendReady r source).store :=
  Exec.seq (.action _ _) (.action _ _)

def appendFinish : Block 9 := .seq (.action (.copy 7 8)) (.action (.clear 8))
theorem appendFinish_exec (r : Registers) :
    Exec appendFinish r.store 2 ({r with reserved := r.output, output := []}).store :=
  Exec.seq (.action _ _) (.action _ _)

def append (source : Fin 9) : Block 9 := .seq (appendPrepare source) <|
  .seq ClauseQuery.reverseLoop appendFinish
def appendCost (r : Registers) (source : Fin 9) : Nat := 4 * (r.store.get source).length + 5
def appended (r : Registers) (word : BitString) : Registers :=
  {r with excess := [], reserved := word.reverse ++ r.reserved, output := []}
theorem append_exec (r : Registers) (source : Fin 9) :
    Exec (append source) r.store (appendCost r source) (appended r (r.store.get source)).store := by
  have first := appendPrepare_exec r source
  have copied := ClauseQuery.reverse_exec {r with output := r.reserved} (r.store.get source)
  have last := appendFinish_exec
    {r with excess := [], output := (r.store.get source).reverse ++ r.reserved}
  have checked := Exec.seq first (Exec.seq copied last)
  have count : appendCost r source = 2 + ((4 * (r.store.get source).length + 1) + 2) := by
    unfold appendCost
    omega
  simpa only [append, appendReady, appended, count] using checked

def finalPrepare : Block 9 := .seq (.action (.copy 3 7)) (.action (.clear 8))
def finalReady (r : Registers) : Registers := {r with excess := r.reserved, output := []}
theorem finalPrepare_exec (r : Registers) :
    Exec finalPrepare r.store 2 (finalReady r).store := Exec.seq (.action _ _) (.action _ _)

def finish : Block 9 := .seq finalPrepare <|
  .seq ClauseQuery.reverseLoop (.action (.clear 6))
def finalCost (r : Registers) : Nat := 4 * r.reserved.length + 4
def finished (r : Registers) : Registers :=
  {r with excess := [], active := [], output := r.reserved.reverse}
theorem finish_exec (r : Registers) :
    Exec finish r.store (finalCost r) (finished r).store := by
  have first := finalPrepare_exec r
  have copied : Exec ClauseQuery.reverseLoop (finalReady r).store
      (4 * r.reserved.length + 1)
      ({r with excess := [], output := r.reserved.reverse}).store := by
    simpa only [finalReady, List.append_nil] using
      ClauseQuery.reverse_exec {r with output := []} r.reserved
  have last : Exec (.action (.clear (6 : Fin 9)))
      ({r with excess := [], output := r.reserved.reverse}).store 1 (finished r).store := Exec.action _ _
  have checked := Exec.seq first (Exec.seq copied last)
  have count : finalCost r = 2 + ((4 * r.reserved.length + 1) + 1) := by unfold finalCost; omega
  simpa only [finish, count] using checked

def atEnd : Block 9 := .seq (append 4) finish
def endResult (r : Registers) : Registers := finished (appended r r.sign)
def endCost (r : Registers) : Nat := 4 * r.reserved.length + 8 * r.sign.length + 9
theorem end_exec (r : Registers) :
    Exec atEnd r.store (endCost r) (endResult r).store := by
  have first : Exec (append 4) r.store (4 * r.sign.length + 5) (appended r r.sign).store := append_exec r 4
  have last := finish_exec (appended r r.sign)
  have count : endCost r = (4 * r.sign.length + 5) + finalCost (appended r r.sign) := by
    simp only [endCost, finalCost, appended, List.length_append, List.length_reverse]
    omega
  simpa only [atEnd, endResult, count] using Exec.seq first last

def equal : Block 9 := .seq (append 5) (.seq (append 0) finish)
def equalResult (r : Registers) : Registers := finished (appended (appended r r.mode) r.input)
def equalCost (r : Registers) : Nat :=
  4 * r.reserved.length + 8 * r.mode.length + 8 * r.input.length + 14
theorem equal_exec (r : Registers) :
    Exec equal r.store (equalCost r) (equalResult r).store := by
  have first : Exec (append 5) r.store (4 * r.mode.length + 5) (appended r r.mode).store := append_exec r 5
  have second : Exec (append 0) (appended r r.mode).store
      (4 * r.input.length + 5) (appended (appended r r.mode) r.input).store :=
    append_exec (appended r r.mode) 0
  have last := finish_exec (appended (appended r r.mode) r.input)
  have count : equalCost r = (4 * r.mode.length + 5) +
      ((4 * r.input.length + 5) + finalCost (appended (appended r r.mode) r.input)) := by
    simp only [equalCost, finalCost, appended, List.length_append, List.length_reverse]
    omega
  simpa only [equal, equalResult, count] using Exec.seq first (Exec.seq second last)

def before : Block 9 := .seq (append 4) equal
def beforeResult (r : Registers) : Registers := equalResult (appended r r.sign)
def beforeCost (r : Registers) : Nat :=
  4 * r.reserved.length + 8 * r.sign.length + 8 * r.mode.length + 8 * r.input.length + 19
theorem before_exec (r : Registers) :
    Exec before r.store (beforeCost r) (beforeResult r).store := by
  have first : Exec (append 4) r.store (4 * r.sign.length + 5) (appended r r.sign).store := append_exec r 4
  have last := equal_exec (appended r r.sign)
  have count : beforeCost r = (4 * r.sign.length + 5) + equalCost (appended r r.sign) := by
    simp only [beforeCost, equalCost, appended, List.length_append, List.length_reverse]
    omega
  simpa only [before, beforeResult, count] using Exec.seq first last

def advance : Block 9 := .seq (append 5) <|
  .seq (.action (.clear 2)) (.action (.clear 5))
def advanced (r : Registers) : Registers :=
  {appended r r.mode with remaining := [], mode := []}
def advanceCost (r : Registers) : Nat := 4 * r.mode.length + 7
theorem advance_exec (r : Registers) :
    Exec advance r.store (advanceCost r) (advanced r).store := by
  have first : Exec (append 5) r.store (4 * r.mode.length + 5) (appended r r.mode).store := append_exec r 5
  have last : Exec (.seq (.action (.clear (2 : Fin 9))) (.action (.clear 5)))
      (appended r r.mode).store 2 (advanced r).store := Exec.seq (.action _ _) (.action _ _)
  have count : advanceCost r = (4 * r.mode.length + 5) + 2 := by unfold advanceCost; omega
  simpa only [advance, count] using Exec.seq first last

theorem end_output (r : Registers) :
    (endResult r).output = r.reserved.reverse ++ r.sign := by
  simp only [endResult, finished, appended, List.reverse_append, List.reverse_reverse]
theorem equal_output (r : Registers) :
    (equalResult r).output = r.reserved.reverse ++ (r.mode ++ r.input) := by
  simp only [equalResult, finished, appended, List.reverse_append, List.reverse_reverse,
    List.append_assoc]
theorem before_output (r : Registers) :
    (beforeResult r).output = r.reserved.reverse ++ (r.sign ++ (r.mode ++ r.input)) := by
  simp only [beforeResult, equalResult, finished, appended, List.reverse_append, List.reverse_reverse,
    List.append_assoc]

end PNP.Concrete.ResidualReduction.SourceMenuInsertOutput
