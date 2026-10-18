import PNP.Concrete.ResidualReduction.SourceNativeEncoding

/-! Literal reader for one native sparse row label. The unary coordinate and
the following polarity bit are consumed from the actual input, producing the
unary index 2*i+b. This reader is total, detects a missing terminator or polarity,
and has a linear source-instruction bound on every input. The enclosing dense
coordinate constructor separately checks that this index is in range. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeRowIndex
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.ResidualReduction.MatrixStrictHeader

structure Parsed where
  index : Nat
  rest : BitString
  valid : Bool

def state (input : BitString) (index : Nat) (valid : Bool) : Registers :=
  ⟨input,List.replicate index true,[],[],if valid then [true] else [],[],[],[],[]⟩
def decoded (count : Nat) : BitString → Parsed
  | [] => ⟨0,[],false⟩
  | bit :: rest => ⟨2 * count + (if bit then 1 else 0),rest,true⟩
def parse (input : BitString) : Parsed :=
  let h := scan input
  if h.terminated then decoded h.count h.rest else ⟨0,h.rest,false⟩

def double : Block 9 := .seq (.action (.copy 2 1))
  (.seq (.action (.copy 6 1)) (.seq MatrixPayloadCounter.addLoop (.action (.clear 1))))
def doubled (input : BitString) (count : Nat) : Registers :=
  {state input 0 true with remaining := List.replicate (2 * count) true}

theorem double_exec (input : BitString) (count : Nat) :
    Exec double (state input count true).store (3 * count + 4) (doubled input count).store := by
  let r := {state input count true with remaining := List.replicate count true}
  have added := MatrixPayloadCounter.addLoop_exec count r
  have twice : count + count = 2 * count := by omega
  simp only [r,replicate_add,twice] at added
  have last : Exec (.action (.clear (1 : Fin 9)))
      ({r with active := [],remaining := List.replicate (2 * count) true}).store 1
      (doubled input count).store := .action _ _
  have checked := Exec.seq (.action (.copy (2 : Fin 9) 1) (state input count true).store)
    (Exec.seq (.action (.copy (6 : Fin 9) 1) r.store) (Exec.seq added last))
  have cost : 3 * count + 4 = 1 + (1 + ((3 * count + 1) + 1)) := by omega
  simpa only [double,cost,r] using checked

def parity : Block 9 := .branch 0
  (.seq (.action (.clear 2)) (.action (.clear 4)))
  (.action (.pop 0))
  (.seq (.action (.pop 0)) (.action (.push 2 true)))
def parityFuel : BitString → Nat
  | false :: _ => 2
  | _ => 3
def parityResult (input : BitString) (count : Nat) : Registers :=
  {state (decoded count input).rest 0 (decoded count input).valid with
    remaining := List.replicate (decoded count input).index true}

theorem parity_exec (input : BitString) (count : Nat) :
    Exec parity (doubled input count).store (parityFuel input) (parityResult input count).store := by
  cases input with
  | nil => exact Exec.empty rfl (Exec.seq (.action _ _) (.action _ _))
  | cons bit rest =>
    cases bit with
    | false => exact Exec.zero rfl (.action _ _)
    | true => exact Exec.one rfl (Exec.seq (.action _ _) (.action _ _))

def finish : Block 9 := .seq (.action (.copy 1 2)) (.action (.clear 2))
def accepted : Block 9 := .seq double (.seq parity finish)
def acceptedFuel (input : BitString) (count : Nat) : Nat := 3 * count + 6 + parityFuel input

theorem accepted_exec (input : BitString) (count : Nat) :
    Exec accepted (state input count true).store (acceptedFuel input count)
      (state (decoded count input).rest (decoded count input).index (decoded count input).valid).store := by
  have last : Exec finish (parityResult input count).store 2
      (state (decoded count input).rest (decoded count input).index (decoded count input).valid).store :=
    Exec.seq (.action _ _) (.action _ _)
  have checked := Exec.seq (double_exec input count) (Exec.seq (parity_exec input count) last)
  have cost : acceptedFuel input count = (3 * count + 4) + (parityFuel input + 2) := by
    unfold acceptedFuel
    omega
  simpa only [accepted,cost] using checked

def dispatch : Block 9 := .branch 4 (.action (.clear 1)) (.action (.clear 1)) accepted
def block : Block 9 := .seq MatrixStrictHeader.block dispatch
def fuel (input : BitString) : Nat :=
  MatrixStrictHeader.blockFuel input +
    (if (scan input).terminated then 1 + acceptedFuel (scan input).rest (scan input).count else 2)

theorem block_exec (input : BitString) :
    Exec block (state input 0 false).store (fuel input)
      (state (parse input).rest (parse input).index (parse input).valid).store := by
  have first : Exec MatrixStrictHeader.block (state input 0 false).store
      (MatrixStrictHeader.blockFuel input)
      (state (scan input).rest (scan input).count (scan input).terminated).store := by
    simpa only [state,MatrixStrictHeader.result,List.replicate_zero,List.append_nil] using
      MatrixStrictHeader.block_exec input (state [] 0 false)
  cases flag : (scan input).terminated with
  | false =>
    have last : Exec dispatch (state (scan input).rest (scan input).count false).store 2
        (state (scan input).rest 0 false).store := Exec.empty rfl (.action _ _)
    rw [flag] at first
    simpa only [block,fuel,parse,flag,Bool.false_eq_true,↓reduceIte] using Exec.seq first last
  | true =>
    have last : Exec dispatch (state (scan input).rest (scan input).count true).store
        (1 + acceptedFuel (scan input).rest (scan input).count)
        (state (decoded (scan input).count (scan input).rest).rest
          (decoded (scan input).count (scan input).rest).index
          (decoded (scan input).count (scan input).rest).valid).store :=
      Exec.one rfl (accepted_exec (scan input).rest (scan input).count)
    rw [flag] at first
    simpa only [block,dispatch,fuel,parse,flag,↓reduceIte] using Exec.seq first last

theorem fuel_bound (input : BitString) : fuel input ≤ 7 * input.length + 19 := by
  have header := MatrixStrictHeader.blockFuel_bound input
  have size := scan_size input
  have parityBound : parityFuel (scan input).rest ≤ 3 := by
    cases (scan input).rest with
    | nil => exact Nat.le_refl 3
    | cons bit rest => cases bit <;> simp only [parityFuel] <;> omega
  unfold fuel acceptedFuel
  split <;> omega


theorem parse_bounds (input : BitString) :
    (parse input).rest.length ≤ input.length ∧
    (parse input).index ≤ 2 * input.length + 1 ∧
    ((parse input).valid = true → (parse input).rest.length < input.length) := by
  have size := scan_size input
  cases flag : (scan input).terminated with
  | false =>
    simp only [parse,flag,Bool.false_eq_true,↓reduceIte]
    exact ⟨by omega,by omega,by intro impossible; cases impossible⟩
  | true =>
    cases rest : (scan input).rest with
    | nil =>
      simp only [parse,flag,↓reduceIte,rest,decoded,List.length_nil]
      exact ⟨by omega,by omega,by intro impossible; cases impossible⟩
    | cons bit tail =>
      rw [rest] at size
      simp only [List.length_cons] at size
      cases bit <;> simp only [parse,flag,Bool.false_eq_true,↓reduceIte,rest,decoded] <;>
        exact ⟨by omega,by omega,by intro _; omega⟩

theorem canonical {c : Nat} (r : NativeEquations.Row c) (suffix : BitString) :
    parse ((NativeSystemCodec.rowCodec c).encode r ++ suffix) =
      ⟨(NativeSource.rowIndex r).val,suffix,true⟩ := by
  change parse ((natural r.1.val ++ [r.2]) ++ suffix) = _
  rw [List.append_assoc]
  simp only [List.singleton_append,parse,scan_canonical,↓reduceIte,decoded,NativeSource.rowIndex]

theorem canonical_exec {c : Nat} (r : NativeEquations.Row c) (suffix : BitString) :
    Exec block (state ((NativeSystemCodec.rowCodec c).encode r ++ suffix) 0 false).store
      (fuel ((NativeSystemCodec.rowCodec c).encode r ++ suffix))
      (state suffix (NativeSource.rowIndex r).val true).store := by
  simpa only [canonical] using block_exec ((NativeSystemCodec.rowCodec c).encode r ++ suffix)

end PNP.Concrete.ResidualReduction.SourceNativeRowIndex
