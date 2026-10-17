import PNP.Concrete.ResidualReduction.SourceNativeTermsLoop

/-! Build the initial affine accumulator from the protected unary dimension.
The source term count is copied from the strict header reader; no initial affine
word or list witness is supplied to the machine. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeTermsSeed
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceNativeTermsState

def blank (input : BitString) (n : Nat) : Saved := ⟨List.replicate n true,[],[],input,[]⟩
def prepare : Block 14 := .seq (.action (.copy 11 1))
  (.seq (.action (.clear 1)) (.action (.copy 2 9)))
def finish : Block 14 := .seq (.action (.copy 10 8))
  (.seq (.action (.push 13 true)) (.seq reset restore))
def block (constant : Bool) : Block 14 :=
  .seq prepare (.seq (core SourceUnitDirectionInstructions.suffixLoop)
    (.seq (.action (.push 8 constant)) (.seq SourceNativeTermsAdd.arrange
      (.seq (core ClauseQuery.reverseLoop) finish))))
def fuel (n : Nat) : Nat := 7 * n + 25

theorem finish_exec (r : Registers) (s : Saved) :
    Exec finish (full r s) 13
      (work s.stream {s with accumulator := r.output,active := true :: s.active}) := by
  let done := {s with accumulator := r.output,active := true :: s.active}
  have checked := Exec.seq (.action (.copy (10 : Fin 14) 8) (full r s))
    (Exec.seq (.action (.push (13 : Fin 14) true) (full r {s with accumulator := r.output}))
      (Exec.seq (reset_exec r done) (restore_exec done)))
  simpa only [finish,done] using checked

theorem block_exec (input : BitString) (n count : Nat) (constant : Bool) :
    Exec (block constant) (full (SourceNativeRowIndex.state input count true) (blank input n))
      (fuel n) (state input (aConst n constant) count true) := by
  let base := SourceNativeRowIndex.state input 0 true
  let saved := {blank input n with pending := List.replicate count true}
  let ready := {base with remaining := List.replicate n true}
  let zeros := {base with output := List.replicate n false}
  let reversed := {base with output := constant :: List.replicate n false}
  let reverseReady := {base with excess := constant :: List.replicate n false}
  let normal := {base with output := SourceNativeEncoding.affineWord (aConst n constant)}
  have setup : Exec prepare (full (SourceNativeRowIndex.state input count true) (blank input n)) 3
      (full ready saved) := Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have zeroFill : Exec SourceUnitDirectionInstructions.suffixLoop ready.store
      (3 * n + 1) zeros.store := by
    simpa only [ready,zeros,base,SourceNativeRowIndex.state,List.append_nil] using
      SourceUnitDirectionInstructions.suffix_exec base n
  have constantBit : Exec (.action (.push (8 : Fin 14) constant)) (full zeros saved) 1
      (full reversed saved) := .action _ _
  have arrange : Exec SourceNativeTermsAdd.arrange (full reversed saved) 2
      (full reverseReady saved) := Exec.seq (.action _ _) (.action _ _)
  have reversal : Exec ClauseQuery.reverseLoop reverseReady.store
      (4 * (n + 1) + 1) normal.store := by
    simpa only [reverseReady,normal,base,SourceNativeRowIndex.state,List.length_cons,
      List.length_replicate,List.reverse_cons,List.reverse_replicate,List.append_nil,
      SourceNativeEncoding.constant_word] using
      ClauseQuery.reverse_exec base (constant :: List.replicate n false)
  have last : Exec finish (full normal saved) 13 (state input (aConst n constant) count true) := by
    simpa only [normal,saved,base,blank,data,state,SourceNativeRowIndex.state,↓reduceIte] using
      finish_exec normal saved
  have checked := Exec.seq setup (Exec.seq (core_exec zeroFill saved)
    (Exec.seq constantBit (Exec.seq arrange (Exec.seq (core_exec reversal saved) last))))
  have cost : fuel n = 3 + ((3 * n + 1) + (1 + (2 + ((4 * (n + 1) + 1) + 13)))) := by
    unfold fuel
    omega
  simpa only [block,cost] using checked

end PNP.Concrete.ResidualReduction.SourceNativeTermsSeed
