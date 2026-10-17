import PNP.Concrete.ResidualReduction.SourceRowCoefficientAlgebra

/-! Counted full-affine coefficient operations used by the row constructor.
Only literal word instructions execute; coefficient addition and equality are
specifications proved about their output, not callbacks in the program. -/

namespace PNP.Concrete.ResidualReduction.SourceRowCoefficientInstructions
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra
open PNP.Concrete.ResidualReduction.SourceMenuBytes
open PNP.Concrete.ResidualReduction.SourceRowCoefficientAlgebra

def zero : Block 9 := .seq (.action (.copy 2 1)) SourceScalarInitialization.zeroLoop

theorem zero_exec (r : Registers) (n : Nat) :
    Exec zero ({r with target := List.replicate (n + 1) true,remaining := [],output := []}).store
      (3 * (n + 1) + 2)
      ({r with target := List.replicate (n + 1) true,remaining := [],output := affineWord (aConst n false)}).store := by
  let base := {r with target := List.replicate (n + 1) true,remaining := [],output := []}
  have load : Exec (.action (.copy (2 : Fin 9) 1)) base.store 1
      ({base with remaining := List.replicate (n + 1) true}).store := .action _ _
  have run := SourceScalarInitialization.zero_exec base (List.replicate (n + 1) true)
  have cost : 3 * (n + 1) + 2 = 1 + (3 * (n + 1) + 1) := by omega
  simpa only [zero,base,cost,List.length_replicate,List.append_nil,zero_word] using Exec.seq load run

def binaryReady (r : Registers) {n : Nat} (a b : Affine n) : Registers :=
  {r with input := affineWord a,target := List.replicate (n + 1) true, remaining := [],excess := [],mode := affineWord b,output := []}
def added (r : Registers) {n : Nat} (a b : Affine n) : Registers :=
  {r with input := [],target := List.replicate (n + 1) true, remaining := [],excess := [],mode := [],output := affineWord (aAdd a b)}
def add : Block 9 := .seq (.action (.copy 2 1)) <| .seq xorLoop ClauseQuery.reverseLoop

theorem add_exec (r : Registers) {n : Nat} (a b : Affine n) :
    Exec add (binaryReady r a b).store (11 * (n + 1) + 3) (added r a b).store := by
  let base := {r with input := [],target := List.replicate (n + 1) true, remaining := [],excess := [],mode := [],output := []}
  let loaded := {binaryReady r a b with remaining := List.replicate (n + 1) true}
  let xored := {base with excess := (affineWord (aAdd a b)).reverse}
  have load : Exec (.action (.copy (2 : Fin 9) 1)) (binaryReady r a b).store 1 loaded.store := .action _ _
  have xor : Exec xorLoop loaded.store (7 * (n + 1) + 1) xored.store := by
    simpa only [loaded,binaryReady,xored,base,affineWord_length,word_add,List.append_nil] using
      xor_exec base (affineWord a) (affineWord b) [] (by rw [affineWord_length,affineWord_length])
  have reverse : Exec ClauseQuery.reverseLoop xored.store (4 * (n + 1) + 1) (added r a b).store := by
    simpa only [xored,base,added,List.length_reverse,affineWord_length,List.reverse_reverse,List.append_nil] using
      ClauseQuery.reverse_exec base (affineWord (aAdd a b)).reverse
  have cost : 11 * (n + 1) + 3 = 1 + ((7 * (n + 1) + 1) + (4 * (n + 1) + 1)) := by omega
  simpa only [add,cost] using Exec.seq load (Exec.seq xor reverse)

def unaryReady (r : Registers) {n : Nat} (f : Affine n) : Registers :=
  {r with input := affineWord f,target := List.replicate (n + 1) true, remaining := [],excess := [],output := []}
def toggled (r : Registers) {n : Nat} (f : Affine n) : Registers :=
  {r with input := [],target := List.replicate (n + 1) true, remaining := [],excess := [],output := affineWord (aAdd f (aConst n true))}
def flipRead : Block 9 := MatrixLinearCombinationInstructions.readInput fun b => .action (.push 3 (!b))
def toggle : Block 9 := .seq (.seq (.action (.copy 2 1)) (.action (.pop 2))) <|
  .seq copyLoop <| .seq flipRead ClauseQuery.reverseLoop

theorem toggle_exec (r : Registers) {n : Nat} (f : Affine n) :
    Exec toggle (unaryReady r f).store (9 * (n + 1) + 2) (toggled r f).store := by
  let base := {r with input := [],target := List.replicate (n + 1) true, remaining := [],excess := [],output := []}
  let loaded := {unaryReady r f with remaining := List.replicate n true}
  let copied := {base with input := [aConstant f],excess := (normalWord f).reverse}
  let flipped := {base with excess := (affineWord (aAdd f (aConst n true))).reverse}
  have load : Exec (.seq (.action (.copy (2 : Fin 9) 1)) (.action (.pop 2)))
      (unaryReady r f).store 2 loaded.store := Exec.seq (.action _ _) (.action _ _)
  have copy : Exec copyLoop loaded.store (5 * n + 1) copied.store := by
    simpa only [loaded,unaryReady,copied,base,word_split,normalWord_length,List.append_nil] using
      copy_exec base (normalWord f) [aConstant f]
  have flip : Exec flipRead copied.store 3 flipped.store := by
    simpa only [flipRead,copied,flipped,base,toggle_word,List.reverse_append,List.reverse_cons,
      List.reverse_nil,List.cons_append,List.nil_append] using
      MatrixLinearCombinationInstructions.readInput_exec
        {base with excess := (normalWord f).reverse} (aConstant f) (fun b => .action (.push 3 (!b)))
        1 _ (.action _ _)
  have reverse : Exec ClauseQuery.reverseLoop flipped.store (4 * (n + 1) + 1) (toggled r f).store := by
    simpa only [flipped,base,toggled,List.length_reverse,affineWord_length,List.reverse_reverse,List.append_nil] using
      ClauseQuery.reverse_exec base (affineWord (aAdd f (aConst n true))).reverse
  have cost : 9 * (n + 1) + 2 = 2 + ((5 * n + 1) + (3 + (4 * (n + 1) + 1))) := by omega
  simpa only [toggle,cost] using Exec.seq load (Exec.seq copy (Exec.seq flip reverse))

private theorem flag_split (flag b rest : Bool) :
    ((flag && !b) && !rest) = (flag && !(b || rest)) := by
  cases flag <;> cases b <;> cases rest <;> rfl

def zeroBody : Block 9 := .seq (.branch 3 .skip (.seq .skip .skip)
  (.seq (.action (.clear 6)) (.action (.push 6 false)))) (.action (.pop 3))
def zeroLoop : Block 9 := .loop 3 zeroBody

theorem zeroBody_exec (r : Registers) (b flag : Bool) :
    Exec zeroBody ({r with excess := b :: r.excess,active := [flag]}).store 4
      ({r with active := [flag && !b]}).store := by
  have branch : Exec (.branch (3 : Fin 9) .skip (.seq .skip .skip)
      (.seq (.action (.clear 6)) (.action (.push 6 false))))
      ({r with excess := b :: r.excess,active := [flag]}).store 3
      ({r with excess := b :: r.excess,active := [flag && !b]}).store := by
    cases b with
    | false => cases flag <;> exact Exec.zero rfl (Exec.seq (.skip _) (.skip _))
    | true => cases flag <;> exact Exec.one rfl (Exec.seq (.action _ _) (.action _ _))
  exact Exec.seq branch (.action _ _)

theorem zeroLoop_exec (r : Registers) (word : BitString) (flag : Bool) :
    Exec zeroLoop ({r with excess := word,active := [flag]}).store (5 * word.length + 1)
      ({r with excess := [],active := [flag && !nonzero word]}).store := by
  induction word generalizing flag with
  | nil =>
    simp only [List.length_nil,nonzero_nil,Bool.not_false,Bool.and_true]
    exact Exec.loopStop rfl
  | cons b word ih =>
    have first := zeroBody_exec {r with excess := word} b flag
    have rest := ih (flag && !b)
    have run := Exec.loopStep (source := (3 : Fin 9)) rfl first rest
    have cost : 5 * (b :: word).length + 1 = 1 + (4 + (5 * word.length + 1)) := by
      simp only [List.length_cons]
      omega
    simpa only [zeroLoop,cost,flag_split,nonzero_cons] using run

def prepareEqual : Block 9 := .seq (.action (.copy 2 1)) <|
  .seq (.action (.clear 6)) (.action (.push 6 true))
def equal : Block 9 := .seq prepareEqual <| .seq xorLoop zeroLoop
def compared (r : Registers) {n : Nat} (a b : Affine n) : Registers :=
  {r with input := [],target := List.replicate (n + 1) true,remaining := [], excess := [],mode := [],active := [aEq a b],output := []}

theorem equal_exec (r : Registers) {n : Nat} (a b : Affine n) :
    Exec equal (binaryReady r a b).store (12 * (n + 1) + 5) (compared r a b).store := by
  let base := {r with input := [],target := List.replicate (n + 1) true, remaining := [],excess := [],mode := [],active := [true],output := []}
  let loaded := {binaryReady r a b with remaining := List.replicate (n + 1) true,active := [true]}
  let xored := {base with excess := (affineWord (aAdd a b)).reverse}
  have load : Exec prepareEqual (binaryReady r a b).store 3 loaded.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have xor : Exec xorLoop loaded.store (7 * (n + 1) + 1) xored.store := by
    simpa only [loaded,binaryReady,xored,base,affineWord_length,word_add,List.append_nil] using
      xor_exec base (affineWord a) (affineWord b) [] (by rw [affineWord_length,affineWord_length])
  have scan : Exec zeroLoop xored.store (5 * (n + 1) + 1) (compared r a b).store := by
    have checked := zeroLoop_exec base (affineWord (aAdd a b)).reverse true
    rw [List.length_reverse,affineWord_length] at checked
    simpa only [xored,base,compared,nonzero_reverse,word_add,← equal_word,Bool.true_and] using checked
  have cost : 12 * (n + 1) + 5 = 3 + ((7 * (n + 1) + 1) + (5 * (n + 1) + 1)) := by omega
  simpa only [equal,cost] using Exec.seq load (Exec.seq xor scan)

end PNP.Concrete.ResidualReduction.SourceRowCoefficientInstructions
