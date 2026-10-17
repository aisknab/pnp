import PNP.Concrete.ResidualReduction.SourceMenuSerialization
import PNP.Concrete.ResidualReduction.SourceFamilyLoader

/-! Literal loader-to-menu handoff. The family header is rebuilt from the
parser's actual row counter, the sorted menu is constructed from source rows,
and its canonical count and dimension headers are emitted by instructions. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuRaw
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (codec familyBits)
open PNP.Concrete.ResidualReduction.SourceMatrixPacket (State setCore)

def headerState (n count : Nat) (word : BitString) : State :=
  setCore (SourceFamilyLoader.prepared n count word) (SourceMenuRowInput.initial n word [])
def headerBody : Block 16 := .seq (.action (.push 0 true)) (.action (.pop 15))
def headerLoop : Block 16 := .loop 15 headerBody

private theorem replicate_snoc (k : Nat) (word : BitString) :
    List.replicate k true ++ true :: word = List.replicate (k + 1) true ++ word := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons true) ih

theorem headerLoop_exec (n count : Nat) (word : BitString) :
    Exec headerLoop (headerState n count word).store (3 * count + 1)
      (headerState n 0 (List.replicate count true ++ word)).store := by
  induction count generalizing word with
  | zero => exact Exec.loopStop rfl
  | succ count ih =>
    have step : Exec headerBody (headerState n (count + 1) word).store 2
        (headerState n count (true :: word)).store := Exec.seq (.action _ _) (.action _ _)
    have checked := Exec.loopStep (source := (15 : Fin 16)) rfl step (ih (true :: word))
    have cost : 3 * (count + 1) + 1 = 1 + (2 + (3 * count + 1)) := by omega
    simpa only [headerLoop, cost, replicate_snoc] using checked

def saved (n : Nat) : SourceMenuCompare.Saved := ⟨List.replicate n true, [], []⟩
def held : SourceMenuSortStep.Held := ⟨[], []⟩
def extra : Store 2 := .cons [] (.cons [] .nil)
def entered {n : Nat} (F : Family n) : Store 16 :=
  Frame.join (SourceMenuFromFamily.initial F (saved n) held) extra

theorem family_bytes {n : Nat} (F : Family n) :
    (SourceEncoding.familyCodec n).encode F = natural F.length ++ familyBits F := by
  change natural F.length ++ encodeSeq (SourceEncoding.rowCodec n).encode F = _
  rw [SourceMatrixEncoding.familyBits_encode]

theorem entered_store {n : Nat} (F : Family n) :
    (headerState n 0 (natural F.length ++ familyBits F)).store = entered F := by
  unfold entered SourceMenuFromFamily.initial SourceMenuFamily.initial
  rw [family_bytes]
  rfl

def enterPrefix : Block 16 := .seq (.action (.copy 1 9)) (.action (.push 0 false))
def enter : Block 16 := .seq enterPrefix headerLoop
theorem enter_exec {n : Nat} (F : Family n) :
    Exec enter (SourceFamilyLoader.prepared n F.length (familyBits F)).store
      (3 * F.length + 3) (entered F) := by
  have first : Exec enterPrefix (SourceFamilyLoader.prepared n F.length (familyBits F)).store 2
      (headerState n F.length (false :: familyBits F)).store := Exec.seq (.action _ _) (.action _ _)
  have last : Exec headerLoop (headerState n F.length (false :: familyBits F)).store (3 * F.length + 1)
      (headerState n 0 (natural F.length ++ familyBits F)).store := by
    simpa only [natural, List.append_assoc, List.singleton_append] using
      headerLoop_exec n F.length (false :: familyBits F)
  rw [entered_store] at last
  have cost : 3 * F.length + 3 = 2 + (3 * F.length + 1) := by omega
  simpa only [enter, cost] using Exec.seq first last

def outputFrame (s : SourceMenuCompare.Saved) (t : SourceMenuSortStep.Held) : Store 7 :=
  Frame.join (SourceMenuSortStep.frame s t) extra
def finished {n : Nat} (F : Family n) (s : SourceMenuCompare.Saved) (t : SourceMenuSortStep.Held) : Store 16 :=
  Frame.join (SourceMenuSerialization.result (SourceChain.sourceMenu F)).store (outputFrame s t)

theorem serialize_exec {n : Nat} (F : Family n) (s : SourceMenuCompare.Saved) (t : SourceMenuSortStep.Held) :
    Exec (Frame.block 7 SourceMenuSerialization.block)
      (Frame.join (extra := 2) (count := 14) (SourceMenuFromFamily.terminal F s t) extra)
      (SourceMenuSerialization.fuel n (SourceChain.sourceMenu F).length) (finished F s t) :=
  Frame.execution (SourceMenuSerialization.block_exec (SourceChain.sourceMenu F)) (outputFrame s t)
theorem finished_output {n : Nat} (F : Family n) (s : SourceMenuCompare.Saved) (t : SourceMenuSortStep.Held) :
    (finished F s t).get 8 = MatrixInputEncoding.codec.encode ⟨n, SourceChain.sourceMenu F⟩ := rfl

def construct : Block 16 := .seq SourceFamilyLoader.prepare <| .seq enter <|
  .seq (Frame.block 2 SourceMenuFromFamily.block) (Frame.block 7 SourceMenuSerialization.block)
def constructBudget (L : Nat) : Nat := (4 * L + 5) +
  ((3 * L + 3) + (SourceMenuBudget.costPolynomial.eval L + SourceMenuSerialization.costPolynomial.eval L))

theorem construct_exec {n : Nat} (F : Family n) :
    ∃ used after, Exec construct (SourceFamilyLoader.validated n F.length (familyBits F)).store used after ∧
      after.get 8 = MatrixInputEncoding.codec.encode ⟨n, SourceChain.sourceMenu F⟩ ∧
      used ≤ constructBudget (codec.encode ⟨n, F⟩).length := by
  have first := SourceFamilyLoader.prepare_exec n F.length (familyBits F)
  have second := enter_exec F
  obtain ⟨used, last, retained, built, bound⟩ := SourceMenuFromFamily.block_exec F (saved n) held
  have third := Frame.execution built extra
  have fourth := serialize_exec F last retained
  refine ⟨(4 * (familyBits F).length + 5) +
      ((3 * F.length + 3) + (used + SourceMenuSerialization.fuel n (SourceChain.sourceMenu F).length)),
    finished F last retained, Exec.seq first (Exec.seq second (Exec.seq third fourth)), rfl, ?_⟩
  have payload : (familyBits F).length ≤ (codec.encode ⟨n, F⟩).length := by
    rw [SourceMatrixEncoding.familyBits_length, SourceMatrixEncoding.codec_length]
    omega
  have rows := SourceMatrixEncoding.rowCount_bound n F
  have construction := SourceMenuBudget.original_input_bound F
  have serialization := SourceMenuSerialization.original_input_bound F
  unfold constructBudget
  omega

end PNP.Concrete.ResidualReduction.SourceMenuRaw
