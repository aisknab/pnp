import PNP.Concrete.ResidualReduction.SourceNativeTermsState

/-! Literal affine accumulation after a checked sparse label. Both reversals
and the bitwise XOR are executed, with every scratch register reset afterwards.
The protected suffix, dimension, count and validity survive exactly. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeTermsAdd
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceNativeTermsState

def arrange : Block 14 := .seq (.action (.copy 3 8)) (.action (.clear 8))
def prepare : Block 14 := .seq (.action (.copy 0 8))
  (.seq (.action (.clear 8)) (.seq (.action (.copy 5 10))
    (.seq (.action (.copy 2 9)) (.action (.push 2 true)))))
def block : Block 14 := .seq arrange (.seq (core ClauseQuery.reverseLoop)
  (.seq prepare (.seq (core MatrixInstructions.xorLoop)
    (.seq (core ClauseQuery.reverseLoop) advance))))
def fuel (n : Nat) : Nat := 15 * (n + 1) + 23

def before {n : Nat} (input : BitString) (x : Affine n) : Registers :=
  {SourceNativeRowIndex.state input 0 true with output := (SourceNativeEncoding.affineWord x).reverse}

theorem block_exec {n : Nat} (input : BitString) (x a : Affine n) (count : Nat) :
    Exec block (full (before input x) (data input a (count + 1) true)) (fuel n)
      (state input (aAdd x a) count true) := by
  let xw := SourceNativeEncoding.affineWord x
  let aw := SourceNativeEncoding.affineWord a
  let sum := SourceNativeEncoding.affineWord (aAdd x a)
  let base := SourceNativeRowIndex.state input 0 true
  let saved := data input a (count + 1) true
  let reverseReady := {base with excess := xw.reverse}
  let normal := {base with output := xw}
  let ready := {base with input := xw,mode := aw,remaining := List.replicate (n + 1) true}
  let accumulated := {base with input := [],excess := sum.reverse}
  let out := {base with input := [],output := sum}
  have xLength : xw.length = n + 1 := SourceEncoding.affine_length x
  have aLength : aw.length = n + 1 := SourceEncoding.affine_length a
  have sumLength : sum.length = n + 1 := SourceEncoding.affine_length (aAdd x a)
  have words : List.zipWith Bool.xor xw aw = sum := (SourceNativeEncoding.add_word x a).symm
  have start : Exec arrange (full (before input x) saved) 2 (full reverseReady saved) :=
    Exec.seq (.action _ _) (.action _ _)
  have firstReverse : Exec ClauseQuery.reverseLoop reverseReady.store
      (4 * (n + 1) + 1) normal.store := by
    simpa only [reverseReady,normal,base,SourceNativeRowIndex.state,List.length_reverse,
      xLength,List.reverse_reverse,List.append_nil] using ClauseQuery.reverse_exec base xw.reverse
  have setup : Exec prepare (full normal saved) 5 (full ready saved) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
      (Exec.seq (.action _ _) (.action _ _))))
  have sameLength : xw.length = aw.length := by rw [xLength,aLength]
  have xor : Exec MatrixInstructions.xorLoop ready.store
      (7 * (n + 1) + 1) accumulated.store := by
    simpa only [ready,accumulated,base,SourceNativeRowIndex.state,List.append_nil,xLength,words] using
      MatrixInstructions.xor_exec base xw aw [] sameLength
  have lastReverse : Exec ClauseQuery.reverseLoop accumulated.store
      (4 * (n + 1) + 1) out.store := by
    simpa only [accumulated,out,base,SourceNativeRowIndex.state,List.length_reverse,
      sumLength,List.reverse_reverse,List.append_nil] using
      ClauseQuery.reverse_exec (SourceNativeRowIndex.state [] 0 true) sum.reverse
  have last : Exec advance (full out saved) 13 (state input (aAdd x a) count true) := by
    simpa only [out,saved,base,data,state,SourceNativeRowIndex.state,sum,List.replicate_succ,List.tail_cons] using advance_exec out saved
  have checked := Exec.seq start (Exec.seq (core_exec firstReverse saved)
    (Exec.seq setup (Exec.seq (core_exec xor saved) (Exec.seq (core_exec lastReverse saved) last))))
  have cost : fuel n =
      2 + ((4 * (n + 1) + 1) + (5 + ((7 * (n + 1) + 1) + ((4 * (n + 1) + 1) + 13)))) := by
    unfold fuel
    omega
  simpa only [block,cost,saved] using checked

end PNP.Concrete.ResidualReduction.SourceNativeTermsAdd
