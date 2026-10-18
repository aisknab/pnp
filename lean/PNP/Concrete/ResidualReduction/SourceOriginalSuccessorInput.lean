import PNP.Concrete.ResidualReduction.SourceOriginalSuccessorState

/-! Retain the only input before running the complete raw selector, then read
the original headers from those retained bytes. Scratch state from selection
is discarded only after its actual encoded result has been saved. -/

namespace PNP.Concrete.ResidualReduction.SourceOriginalSuccessorInput
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceOriginalSuccessorState

def selected (input choice : BitString) : Saved := {emptySaved with source := input,choice := choice}
def retain : Block 56 := .action (.copy 48 0)

theorem retain_exec (input : BitString) :
    Exec retain (SourceOriginalSuccessorState.initial input) 1
      (full (SourceSelectorInput.rawStart input) (selected input [])) := .action _ _

def select : Block 56 := .seq retain <| .seq (use48 SourceRawSelector.block) <|
  .seq (save .choice 8) reset

theorem select_exec (input : BitString) :
    ∃ ticks, Exec select (SourceOriginalSuccessorState.initial input) ticks
      (work [] [] (selected input (SourceRawSelector.answer input))) ∧
      ticks ≤ SourceRawSelector.sourceBudget input.length + 51 := by
  obtain ⟨used,after,checked,bound,output⟩ := SourceRawSelector.block_exec input
  have query := use48_exec checked (selected input [])
  have store := save_exec Field.choice 8 after (selected input [])
  rw [output] at store
  have clear := reset_exec after (selected input (SourceRawSelector.answer input))
  refine ⟨1 + (used + (1 + 49)),?_,by omega⟩
  simpa only [select,fieldSet,selected] using
    Exec.seq (retain_exec input) (Exec.seq query (Exec.seq store clear))

def saveHeader (field : Field) : Block 56 := .seq (.action (.copy field.slot 1)) <|
  .seq (.action (.clear 1)) (.action (.clear 4))
def header (field : Field) : Block 56 := .seq (core MatrixStrictHeader.block) (saveHeader field)

theorem header_exec (field : Field) (count : Nat) (suffix : BitString) (s : Saved) :
    Exec (header field) (work (natural count ++ suffix) [] s) (4 * count + 12)
      (work suffix [] (fieldSet field s (List.replicate count true))) := by
  let before := SourceScalarState.work (natural count ++ suffix)
  let counted := {SourceScalarState.work suffix with target := List.replicate count true,sign := [true]}
  have scan : Exec MatrixStrictHeader.block before.store (4 * count + 9) counted.store := by
    simpa only [SourceCoefficientGateRaw.header_fuel,MatrixStrictHeader.result,
      MatrixStrictHeader.scan_canonical,if_true,before,counted,SourceScalarState.work,List.append_nil] using
      MatrixStrictHeader.block_exec (natural count ++ suffix) before
  have store : Exec (saveHeader field) (withCore counted s) 3
      (work suffix [] (fieldSet field s (List.replicate count true))) := by
    cases field <;> exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have cost : 4 * count + 12 = (4 * count + 9) + 3 := by omega
  simpa only [header,cost,work,before,SourceScalarState.work] using Exec.seq (core_exec scan s) store

def data {n : Nat} (F : Family n) (choice : BitString) : Saved :=
  ⟨SourceMatrixEncoding.familyBits F,choice,List.replicate n true,
    List.replicate F.length true,[],[],[],[]⟩
def headers : Block 56 := .seq (.action (.copy 0 48)) <|
  .seq (header .dimension) <| .seq (header .rows) <|
  .seq (save .source 0) (.action (.clear 0))
def headersFuel (n rows : Nat) : Nat := 4 * n + 4 * rows + 27

theorem headers_exec {n : Nat} (F : Family n) (choice : BitString) :
    Exec headers (work [] [] (selected (SourceMatrixEncoding.codec.encode ⟨n,F⟩) choice))
      (headersFuel n F.length) (work [] [] (data F choice)) := by
  let s := selected (SourceMatrixEncoding.codec.encode ⟨n,F⟩) choice
  have load : Exec (.action (.copy (0 : Fin 56) 48)) (work [] [] s) 1
      (work (SourceMatrixEncoding.codec.encode ⟨n,F⟩) [] s) := .action _ _
  rw [SourceMatrixEncoding.codec_bits] at load
  have dimension := header_exec Field.dimension n
    (natural F.length ++ SourceMatrixEncoding.familyBits F) s
  have rows := header_exec Field.rows F.length (SourceMatrixEncoding.familyBits F)
    (fieldSet .dimension s (List.replicate n true))
  let d := fieldSet .rows (fieldSet .dimension s (List.replicate n true)) (List.replicate F.length true)
  have capture : Exec (.seq (save .source 0) (.action (.clear (0 : Fin 56))))
      (work (SourceMatrixEncoding.familyBits F) [] d) 2 (work [] [] (data F choice)) :=
    Exec.seq (.action _ _) (.action _ _)
  have cost : headersFuel n F.length = 1 + ((4 * n + 12) + ((4 * F.length + 12) + 2)) := by
    unfold headersFuel
    omega
  simpa only [headers,cost,s,d] using Exec.seq load (Exec.seq dimension (Exec.seq rows capture))

end PNP.Concrete.ResidualReduction.SourceOriginalSuccessorInput
