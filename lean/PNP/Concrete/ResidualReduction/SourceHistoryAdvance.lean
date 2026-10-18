import PNP.Concrete.ResidualReduction.SourceHistoryRecord

/-! Derive the next source packet from the complete returned step. The machine
skips the actual selected weights, pivot header and chart tail; it never receives
a successor family through a separate input or semantic instruction. -/

namespace PNP.Concrete.ResidualReduction.SourceHistoryAdvance
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceHistoryEncoding
open PNP.Concrete.ResidualReduction.SourceHistoryState

def skipHeader : Block 63 := .seq (core MatrixStrictHeader.block) <|
  .seq (.action (.clear 1)) (.action (.clear 4))
theorem skipHeader_exec (count : Nat) (suffix : BitString) (saved : Saved) :
    Exec skipHeader (work (natural count ++ suffix) [] saved) (4 * count + 11)
      (work suffix [] saved) := by
  let before := SourceScalarState.work (natural count ++ suffix)
  let counted := {SourceScalarState.work suffix with target := List.replicate count true,sign := [true]}
  have scan : Exec MatrixStrictHeader.block before.store (4 * count + 9) counted.store := by
    simpa only [SourceCoefficientGateRaw.header_fuel,MatrixStrictHeader.result,
      MatrixStrictHeader.scan_canonical,if_true,before,counted,SourceScalarState.work,List.append_nil] using
      MatrixStrictHeader.block_exec (natural count ++ suffix) before
  have clear : Exec (.seq (.action (.clear (1 : Fin 63))) (.action (.clear 4)))
      (withCore counted saved) 2 (work suffix [] saved) := Exec.seq (.action _ _) (.action _ _)
  have cost : 4 * count + 11 = (4 * count + 9) + 2 := by omega
  simpa only [skipHeader,cost,work,before,SourceScalarState.work] using
    Exec.seq (core_exec scan saved) clear

def held {n : Nat} (F : Family (n + 1)) (h : List SourceChain.StepRecord)
    (s : ConstructedStep n F.length) : Saved :=
  {SourceHistoryRecord.after F h s with dimension := List.replicate n true}
def prepare : Block 63 := .seq (.action (.pop 57)) <|
  .seq (.action (.copy 0 61)) (.action (.copy 2 58))
def finishWord : Block 63 := .seq (.action (.copy 8 0)) <|
  .seq (.action (.clear 0)) (.action (.push 8 false))
def capture : Block 63 := .seq (.action (.copy 56 8)) <|
  .seq (.action (.clear 8)) (.action (.clear 61))
def block : Block 63 := .seq prepare <| .seq (core MatrixInstructions.dropLoop) <|
  .seq skipHeader <| .seq (.action (.copy 2 57)) <| .seq (core MatrixInstructions.dropLoop) <|
  .seq finishWord <| .seq (prepend .dimension) capture
def fuel (n rows pivot : Nat) : Nat := 3 * rows + 11 * n + 4 * pivot + 33

theorem block_exec {n : Nat} (F : Family (n + 1)) (h : List SourceChain.StepRecord)
    (s : ConstructedStep n F.length) (rows : s.output.length = F.length) :
    Exec block (work [] [] (SourceHistoryRecord.after F h s))
      (fuel n F.length s.pivot.val) (work [] [] (data s.output (h ++ [⟨n,F,s⟩]))) := by
  let saved := held F h s
  let weights := (SourceEncoding.pointCodec F.length).encode s.weights
  let tail := (SourceEncoding.pointCodec n).encode s.tail
  let family := (SourceEncoding.familyCodec n).encode s.output
  let suffix := natural s.pivot.val ++ (tail ++ family)
  let base := SourceScalarState.work []
  let loaded := {base with input := weights ++ suffix,remaining := List.replicate F.length true}
  have load : Exec prepare (work [] [] (SourceHistoryRecord.after F h s)) 3
      (withCore loaded saved) := by
    simp only [SourceHistoryRecord.after,data,List.replicate_succ]
    exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have weightsRun : Exec (core MatrixInstructions.dropLoop) (withCore loaded saved)
      (3 * F.length + 1) (work suffix [] saved) := by
    simpa only [weights,SourceEncoding.point_length,loaded,work,base,SourceScalarState.work] using
      core_exec (MatrixInstructions.drop_exec base weights suffix) saved
  have pivotRun := skipHeader_exec s.pivot.val (tail ++ family) saved
  let tailLoaded := {base with input := tail ++ family,remaining := List.replicate n true}
  have tailLoad : Exec (.action (.copy (2 : Fin 63) 57)) (work (tail ++ family) [] saved) 1
      (withCore tailLoaded saved) := .action _ _
  have tailRun : Exec (core MatrixInstructions.dropLoop) (withCore tailLoaded saved)
      (3 * n + 1) (work family [] saved) := by
    simpa only [tail,SourceEncoding.point_length,tailLoaded,work,base,SourceScalarState.work] using
      core_exec (MatrixInstructions.drop_exec base tail family) saved
  have finish : Exec finishWord (work family [] saved) 3 (work [] (false :: family) saved) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have header : Exec (prepend .dimension) (work [] (false :: family) saved) (8 * n + 10)
      (work [] (packet s.output) saved) := by
    simpa only [Field.word,saved,held,List.length_replicate,packet_bits,natural,List.append_assoc,
      List.singleton_append,family] using prepend_exec Field.dimension saved (false :: family)
  have endRun : Exec capture (work [] (packet s.output) saved) 3
      (work [] [] (data s.output (h ++ [⟨n,F,s⟩]))) := by
    simp only [saved,held,SourceHistoryRecord.after,data,rows]
    exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have cost : fuel n F.length s.pivot.val =
      3 + ((3 * F.length + 1) + ((4 * s.pivot.val + 11) +
        (1 + ((3 * n + 1) + (3 + ((8 * n + 10) + 3)))))) := by
    unfold fuel
    omega
  simpa only [block,cost,suffix] using Exec.seq load (Exec.seq weightsRun
    (Exec.seq pivotRun (Exec.seq tailLoad (Exec.seq tailRun (Exec.seq finish (Exec.seq header endRun))))))

end PNP.Concrete.ResidualReduction.SourceHistoryAdvance
