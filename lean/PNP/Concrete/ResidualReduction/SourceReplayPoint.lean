import PNP.Concrete.ResidualReduction.SourceReplayValue

/-! Literal point insertion and conditional shear for replay. The programs
preserve coordinate order, handle the first and last pivot, and charge the
word traversal and reversal. They do not use a semantic point callback. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayPoint
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions

def splice (bit : Bool) : Block 9 := .seq copyLoop
  (.seq (.action (.copy 8 0))
    (.seq (.action (.push 8 bit)) (.seq ClauseQuery.reverseLoop (.action (.clear 0)))))
def spliceFuel (pivot : Nat) : Nat := 9 * pivot + 5

theorem splice_words (r : Registers) (front suffix : BitString) (bit : Bool) :
    Exec (splice bit) ({r with input := front ++ suffix,remaining := List.replicate front.length true,excess := []}).store
      (spliceFuel front.length)
      ({r with input := [],remaining := [],excess := [],output := front ++ bit :: suffix}).store := by
  let copied := {r with input := suffix,remaining := [],excess := front.reverse}
  let staged := {copied with output := bit :: suffix}
  let reversed := {r with input := suffix,remaining := [],excess := [],output := front ++ bit :: suffix}
  have copy : Exec copyLoop
      ({r with input := front ++ suffix,remaining := List.replicate front.length true,excess := []}).store
      (5 * front.length + 1) copied.store := by
    simpa only [copied,List.append_nil] using copy_exec {r with excess := []} front suffix
  have rev : Exec ClauseQuery.reverseLoop staged.store (4 * front.length + 1) reversed.store := by
    simpa only [staged,copied,reversed,List.length_reverse,List.reverse_reverse] using
      ClauseQuery.reverse_exec {r with input := suffix,remaining := [],excess := [],output := bit :: suffix} front.reverse
  have clear : Exec (.action (.clear (0 : Fin 9))) reversed.store 1
      ({r with input := [],remaining := [],excess := [],output := front ++ bit :: suffix}).store := .action _ _
  have cost : spliceFuel front.length = (5 * front.length + 1) + (1 + (1 + ((4 * front.length + 1) + 1))) := by
    unfold spliceFuel
    omega
  have load : Exec (.action (.copy (8 : Fin 9) 0)) copied.store 1 ({copied with output := suffix}).store := .action _ _
  have push : Exec (.action (.push (8 : Fin 9) bit)) ({copied with output := suffix}).store 1 staged.store := .action _ _
  simpa only [splice,cost] using Exec.seq copy (Exec.seq load (Exec.seq push (Exec.seq rev clear)))

theorem splice_point (r : Registers) {n : Nat} (k : Fin (n + 1)) (bit : Bool) (z : Point n) :
    Exec (splice bit)
      ({r with input := (SourceEncoding.pointCodec n).encode z,remaining := List.replicate k.val true,excess := []}).store
      (spliceFuel k.val)
      ({r with input := [],remaining := [],excess := [],output := (SourceEncoding.pointCodec (n + 1)).encode (insert n k (bit,z))}).store := by
  obtain ⟨front,suffix,width,tail,whole⟩ := SourceReplayAlgebra.insert_split k bit z
  have checked := splice_words r front suffix bit
  rw [← tail,← whole,width] at checked
  exact checked

def xorBlock : Block 9 := .seq xorLoop ClauseQuery.reverseLoop
def xorFuel (n : Nat) : Nat := 11 * n + 2

theorem xor_point (r : Registers) {n : Nat} (x y : Point n) :
    Exec xorBlock
      ({r with input := (SourceEncoding.pointCodec n).encode x,mode := (SourceEncoding.pointCodec n).encode y,remaining := List.replicate n true,excess := [],output := []}).store
      (xorFuel n)
      ({r with input := [],mode := [],remaining := [],excess := [],output := (SourceEncoding.pointCodec n).encode (pXor x y)}).store := by
  let word := (SourceEncoding.pointCodec n).encode (pXor x y)
  let middle := {r with input := [],mode := [],remaining := [],excess := word.reverse,output := []}
  have lengths : ((SourceEncoding.pointCodec n).encode x).length =
      ((SourceEncoding.pointCodec n).encode y).length := by rw [SourceEncoding.point_length,SourceEncoding.point_length]
  have first : Exec xorLoop
      ({r with input := (SourceEncoding.pointCodec n).encode x,mode := (SourceEncoding.pointCodec n).encode y,remaining := List.replicate n true,excess := [],output := []}).store
      (7 * n + 1) middle.store := by
    simpa only [middle,word,List.append_nil,SourceEncoding.point_length,← SourceReplayAlgebra.xor_bytes] using
      xor_exec {r with excess := [],output := []} ((SourceEncoding.pointCodec n).encode x)
        ((SourceEncoding.pointCodec n).encode y) [] lengths
  have last : Exec ClauseQuery.reverseLoop middle.store (4 * n + 1)
      ({r with input := [],mode := [],remaining := [],excess := [],output := word}).store := by
    simpa only [middle,word,List.length_reverse,SourceEncoding.point_length,List.reverse_reverse,List.append_nil] using
      ClauseQuery.reverse_exec {r with input := [],mode := [],remaining := [],excess := [],output := []} word.reverse
  have cost : xorFuel n = (7 * n + 1) + (4 * n + 1) := by unfold xorFuel; omega
  simpa only [xorBlock,cost] using Exec.seq first last

def sheared {n : Nat} (bit : Bool) (z v : Point n) : Point n := if bit then pXor z v else z
def clearInputs : Block 9 := .seq (.action (.clear 0)) (.seq (.action (.clear 5)) (.action (.clear 2)))
def shearBlock : Block 9 := .seq (.branch 4 .skip (.action (.copy 8 0)) xorBlock) clearInputs
def shearFuel (n : Nat) (bit : Bool) : Nat := if bit then 11 * n + 6 else 5

theorem shear_point (r : Registers) {n : Nat} (bit : Bool) (z v : Point n) :
    Exec shearBlock
      ({r with input := (SourceEncoding.pointCodec n).encode z,mode := (SourceEncoding.pointCodec n).encode v,remaining := List.replicate n true,excess := [],output := [],sign := [bit]}).store
      (shearFuel n bit)
      ({r with input := [],mode := [],remaining := [],excess := [],output := (SourceEncoding.pointCodec n).encode (sheared bit z v),sign := [bit]}).store := by
  cases bit with
  | false =>
    exact Exec.seq (Exec.zero rfl (.action _ _))
      (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  | true =>
    have run := xor_point {r with sign := [true]} z v
    have clear : Exec clearInputs
        ({r with input := [],mode := [],remaining := [],excess := [],output := (SourceEncoding.pointCodec n).encode (pXor z v),sign := [true]}).store 3
        ({r with input := [],mode := [],remaining := [],excess := [],output := (SourceEncoding.pointCodec n).encode (pXor z v),sign := [true]}).store :=
      Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
    have cost : shearFuel n true = (1 + xorFuel n) + 3 := by simp only [shearFuel,xorFuel,↓reduceIte]; omega
    simpa only [shearBlock,cost,sheared,↓reduceIte] using Exec.seq (Exec.one rfl run) clear

theorem shearFuel_bound (n : Nat) (bit : Bool) : shearFuel n bit ≤ 11 * n + 6 := by
  cases bit <;> simp only [shearFuel,Bool.false_eq_true,↓reduceIte] <;> omega

end PNP.Concrete.ResidualReduction.SourceReplayPoint
