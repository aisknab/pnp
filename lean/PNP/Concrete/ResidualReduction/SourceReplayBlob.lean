import PNP.Concrete.ResidualReduction.SourceReplayProject
import PNP.Concrete.ResidualReduction.MatrixCountedPayload

/-! A strict length-delimited byte field read by literal instructions.
The unary length and payload come from the input itself. All truncations
are rejected; a failed header cannot be repaired by an empty payload. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayBlob
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec

def bytes (input : BitString) : BitString :=
  (MatrixStrictHeader.scan input).rest.take (MatrixStrictHeader.scan input).count
def rest (input : BitString) : BitString :=
  (MatrixStrictHeader.scan input).rest.drop (MatrixStrictHeader.scan input).count
def valid (input : BitString) : Bool :=
  if (MatrixStrictHeader.scan input).count ≤ (MatrixStrictHeader.scan input).rest.length
  then (MatrixStrictHeader.scan input).terminated else false

theorem parseN_bits (n : Nat) (input : BitString) :
    parseN bitCodec.parse n input =
      if n ≤ input.length then some (input.take n,input.drop n) else none := by
  induction n generalizing input with
  | zero => rfl
  | succ n ih =>
    cases input with
    | nil => simp only [parseN,bitCodec,parseBit,List.length_nil,show ¬ n + 1 ≤ 0 by omega,↓reduceIte]
    | cons b tail =>
      simp only [bitCodec] at ih
      simp only [parseN,bitCodec,parseBit]
      rw [ih]
      cases h : decide (n ≤ tail.length) with
      | false =>
        have hn : ¬ n ≤ tail.length := of_decide_eq_false h
        have hn' : ¬ n + 1 ≤ (b :: tail).length := by simp only [List.length_cons]; omega
        rw [if_neg hn,if_neg hn']
      | true =>
        have hn : n ≤ tail.length := of_decide_eq_true h
        have hn' : n + 1 ≤ (b :: tail).length := by simp only [List.length_cons]; omega
        rw [if_pos hn,if_pos hn']
        rfl

theorem parse_eq (input : BitString) :
    (listCodec bitCodec).parse input =
      if valid input then some (bytes input,rest input) else none := by
  change (match BitString.decodeLength input with
    | none => none
    | some (n,tail) => parseN bitCodec.parse n tail) = _
  rw [MatrixStrictHeader.scan_parse]
  cases flag : (MatrixStrictHeader.scan input).terminated <;>
    by_cases enough : (MatrixStrictHeader.scan input).count ≤ (MatrixStrictHeader.scan input).rest.length <;>
    simp only [flag,Bool.false_eq_true,↓reduceIte,parseN_bits,valid,bytes,rest,enough]

theorem bytes_bound (input : BitString) : (bytes input).length ≤ input.length := by
  have scanned := MatrixStrictHeader.scan_size input
  simp only [bytes,List.length_take]
  have h := Nat.min_le_left (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest.length
  omega
theorem rest_bound (input : BitString) : (rest input).length ≤ input.length := by
  have scanned := MatrixStrictHeader.scan_size input
  simp only [rest,List.length_drop]
  omega

def result (r : Registers) (input : BitString) : Registers :=
  {r with input := rest input,target := [],remaining := [],excess := [],sign := [],mode := if valid input then [true] else [],active := [],output := bytes input}
def header (r : Registers) (input : BitString) : Registers :=
  MatrixStrictHeader.result input {r with target := []}
def prepared (r : Registers) (input : BitString) : Registers :=
  {header r input with target := [],remaining := List.replicate (MatrixStrictHeader.scan input).count true,excess := [],output := [],mode := if (MatrixStrictHeader.scan input).terminated then [true] else [],sign := []}
def copied (r : Registers) (input : BitString) : Registers :=
  MatrixCountedPayload.result (MatrixStrictHeader.scan input).count (MatrixStrictHeader.scan input).rest (prepared r input)

def setup : Block 9 := .seq (.action (.copy 2 1)) (.seq (.action (.clear 1))
  (.seq (.action (.clear 3)) (.seq (.action (.clear 8))
  (.seq (.action (.copy 5 4)) (.action (.clear 4))))))
def block : Block 9 := .seq (.action (.clear 1)) (.seq MatrixStrictHeader.block
  (.seq setup (.seq MatrixCountedPayload.loop ClauseQuery.reverseLoop)))
def fuel (input : BitString) : Nat :=
  MatrixStrictHeader.blockFuel input + 5 * (MatrixStrictHeader.scan input).count + 4 * (bytes input).length + 9

theorem block_exec (r : Registers) (input : BitString) :
    Exec block ({r with input := input}).store (fuel input) (result r input).store := by
  have clear : Exec (.action (.clear (1 : Fin 9))) ({r with input := input}).store 1
      ({r with input := input,target := []}).store := .action _ _
  have scan := MatrixStrictHeader.block_exec input {r with target := []}
  have setupRun : Exec setup (header r input).store 6 (prepared r input).store := by
    dsimp only [header,prepared,MatrixStrictHeader.result]
    simp only [List.append_nil]
    exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
      (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))))
  have copy := MatrixCountedPayload.loop_exec (MatrixStrictHeader.scan input).count
    (MatrixStrictHeader.scan input).rest (prepared r input)
  have reverse : Exec ClauseQuery.reverseLoop (copied r input).store (4 * (bytes input).length + 1)
      (result r input).store := by
    have checked := ClauseQuery.reverse_exec {copied r input with excess := []} (bytes input).reverse
    cases flag : (MatrixStrictHeader.scan input).terminated <;>
      by_cases enough : (MatrixStrictHeader.scan input).count ≤ (MatrixStrictHeader.scan input).rest.length <;>
      simpa only [copied,MatrixCountedPayload.result,prepared,header,MatrixStrictHeader.result,
        result,valid,bytes,rest,flag,enough,Bool.false_eq_true,↓reduceIte,List.append_nil,List.reverse_reverse,List.length_reverse] using checked
  have cost : fuel input = 1 + (MatrixStrictHeader.blockFuel input +
      (6 + ((5 * (MatrixStrictHeader.scan input).count + 1) + (4 * (bytes input).length + 1)))) := by
    unfold fuel
    omega
  simpa only [block,cost,prepared,header,MatrixStrictHeader.result,copied] using
    Exec.seq clear (Exec.seq scan (Exec.seq setupRun (Exec.seq copy reverse)))

theorem fuel_bound (input : BitString) : fuel input ≤ 13 * input.length + 18 := by
  have scan := MatrixStrictHeader.scan_size input
  have header := MatrixStrictHeader.blockFuel_bound input
  have payload := bytes_bound input
  unfold fuel
  omega

end PNP.Concrete.ResidualReduction.SourceReplayBlob
