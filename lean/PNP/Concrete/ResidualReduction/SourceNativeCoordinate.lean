import PNP.Concrete.ResidualReduction.SourceNativeRowIndex

/-! Checked dense affine-coordinate construction from two unary counters.
Every output bit is produced by a literal instruction. Out-of-range coordinates
clear the success flag and output; they are not silently truncated. The total
source bound includes such malformed inputs as well as every valid coordinate. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeCoordinate
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.SourceUnitDirectionInstructions
open PNP.Concrete.ResidualReduction.MatrixStrictHeader

def initial (input : BitString) (n j : Nat) : Registers :=
  {SourceNativeRowIndex.state input j true with remaining := List.replicate n true}
def afterPrefix (input : BitString) (n j : Nat) : Registers :=
  {SourceNativeRowIndex.state input 0 true with remaining := List.replicate (n - j) true, output := List.replicate j false}
def passed (input : BitString) (n j : Nat) : Registers :=
  {SourceNativeRowIndex.state input 0 true with output := (word n j ++ [false]).reverse}
def failed (input : BitString) : Registers := SourceNativeRowIndex.state input 0 false
def result (input : BitString) (n j : Nat) : Registers :=
  if j < n then passed input n j else failed input

theorem prefix_any (r : Registers) (j n : Nat) :
    Exec prefixLoop
      ({r with target := List.replicate j true,remaining := List.replicate n true}).store
      (4 * j + 1)
      ({r with target := [],remaining := List.replicate (n - j) true, output := List.replicate j false ++ r.output}).store := by
  induction j generalizing r n with
  | zero => exact Exec.loopStop rfl
  | succ j ih =>
    have step : Exec prefixStep
        ({r with target := List.replicate (j + 1) true,remaining := List.replicate n true}).store 3
        ({r with target := List.replicate j true,remaining := List.replicate (n - 1) true, output := false :: r.output}).store := by
      cases n <;> exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
    have checked := Exec.loopStep (source := (1 : Fin 9)) rfl step
      (ih {r with output := false :: r.output} (n - 1))
    have cost : 4 * (j + 1) + 1 = 1 + (3 + (4 * j + 1)) := by omega
    have difference : (n - 1) - j = n - (j + 1) := by omega
    simpa only [prefixLoop,cost,difference,replicate_push] using checked

def pass : Block 9 := .seq middle (.seq suffixLoop (.action (.push 8 false)))
def passFuel (n j : Nat) : Nat := 3 * (n - j - 1) + 4

theorem pass_exec (input : BitString) (n j : Nat) (inRange : j < n) :
    Exec pass (afterPrefix input n j).store (passFuel n j) (passed input n j).store := by
  let tail := n - j - 1
  let r := {SourceNativeRowIndex.state input 0 true with remaining := List.replicate (tail + 1) true,output := List.replicate j false}
  let m := {r with remaining := List.replicate tail true,output := true :: r.output}
  have partition : n - j = tail + 1 := by dsimp only [tail]; omega
  have center : Exec middle r.store 2 m.store := Exec.seq (.action _ _) (.action _ _)
  have rest := suffix_exec m tail
  have last : Exec (.action (.push (8 : Fin 9) false))
      ({m with remaining := [],output := List.replicate tail false ++ m.output}).store 1
      ({SourceNativeRowIndex.state input 0 true with output := false :: (List.replicate tail false ++ true :: List.replicate j false)}).store :=
    .action _ _
  have checked := Exec.seq center (Exec.seq rest last)
  have start : afterPrefix input n j = r := by
    dsimp only [afterPrefix,r]
    rw [partition]
  rw [← start] at checked
  have cost : passFuel n j = 2 + ((3 * tail + 1) + 1) := by unfold passFuel tail; omega
  simpa only [pass,cost,passed,word,tail,List.reverse_append,
    List.reverse_cons,List.reverse_replicate,List.reverse_nil,List.append_nil,List.nil_append,
    List.singleton_append,List.cons_append,List.append_assoc] using checked

def reject : Block 9 := .seq (.action (.clear 8)) (.action (.clear 4))
def dispatch : Block 9 := .branch 2 reject pass pass
def block : Block 9 := .seq prefixLoop dispatch
def fuel (n j : Nat) : Nat := 4 * j + 1 + (if j < n then 1 + passFuel n j else 3)

theorem block_exec (input : BitString) (n j : Nat) :
    Exec block (initial input n j).store (fuel n j) (result input n j).store := by
  have first : Exec prefixLoop (initial input n j).store (4 * j + 1)
      (afterPrefix input n j).store := by
    simpa only [initial,afterPrefix,SourceNativeRowIndex.state,List.replicate_zero,List.append_nil] using
      prefix_any (SourceNativeRowIndex.state input 0 true) j n
  by_cases inRange : j < n
  · have read : (afterPrefix input n j).store.get 2 =
        true :: List.replicate (n - j - 1) true := by
      change List.replicate (n - j) true = _
      rw [show n - j = (n - j - 1) + 1 by omega]
      rfl
    have last : Exec dispatch (afterPrefix input n j).store (1 + passFuel n j)
        (passed input n j).store := Exec.nonempty read (pass_exec input n j inRange)
    simpa only [block,fuel,result,inRange,↓reduceIte] using Exec.seq first last
  · have empty : n - j = 0 := by omega
    have last : Exec dispatch (afterPrefix input n j).store 3 (failed input).store := by
      unfold afterPrefix
      rw [empty]
      exact Exec.empty rfl (Exec.seq (.action _ _) (.action _ _))
    simpa only [block,fuel,result,inRange,↓reduceIte] using Exec.seq first last

theorem fuel_bound (n j : Nat) : fuel n j ≤ 4 * j + 3 * n + 6 := by
  unfold fuel passFuel
  split <;> omega

theorem valid_fuel_bound (n : Nat) (j : Fin n) : fuel n j.val ≤ 4 * n + 2 := by
  have inRange := j.isLt
  simp only [fuel,passFuel,inRange,↓reduceIte]
  omega

theorem coordinate_exec (input : BitString) (n : Nat) (j : Fin n) :
    Exec block (initial input n j.val).store (fuel n j.val)
      ({SourceNativeRowIndex.state input 0 true with output := (SourceNativeEncoding.affineWord (NativeSource.coordinateForm n j)).reverse}).store := by
  have checked := block_exec input n j.val
  simpa only [result,j.isLt,↓reduceIte,passed,SourceNativeEncoding.coordinate_word,unit_bytes] using checked

end PNP.Concrete.ResidualReduction.SourceNativeCoordinate
