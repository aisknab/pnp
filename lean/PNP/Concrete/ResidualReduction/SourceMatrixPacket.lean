import PNP.Concrete.ResidualReduction.SourceMatrixLoop
import PNP.Concrete.ResidualReduction.MatrixPayloadCounter

/-! Canonical matrix headers are constructed by literal loops after the
source-derived payload. The row count n*n is computed, not supplied. A
protected unary source-family count becomes the matrix dimension. Raw family
packet parsing must establish that count before this prepared phase is used. -/

namespace PNP.Concrete.ResidualReduction.SourceMatrixPacket
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceMatrixSchedule

structure State where
  core : SourceMatrixConstruction.State
  rows : BitString
def State.store (r : State) : Store 16 := Frame.join r.core.store (.cons r.rows .nil)
def lift15 (body : Block 15) : Block 16 := Frame.block 1 body
def lift12 (body : Block 12) : Block 16 := lift15 (SourceMatrixConstruction.lifted body)
def lift9 (body : Block 9) : Block 16 := lift12 (MatrixReconstruction.lift body)

theorem lift15_exec (body : Block 15) (r : State) (fuel : Nat) (after : SourceMatrixConstruction.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lift15 body) r.store fuel ({r with core := after}).store :=
  Frame.execution checked (.cons r.rows .nil)
theorem lift12_exec (body : Block 12) (r : State) (fuel : Nat) (after : MatrixReconstruction.State)
    (checked : Exec body r.core.core.store fuel after.store) :
    Exec (lift12 body) r.store fuel ({r with core := {r.core with core := after}}).store :=
  lift15_exec _ r fuel _ (SourceMatrixConstruction.lifted_exec body r.core fuel after checked)
theorem lift9_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.core.core.core.store fuel after.store) :
    Exec (lift9 body) r.store fuel ({r with core := {r.core with core := {r.core.core with core := after}}}).store :=
  lift12_exec _ r fuel _ (MatrixReconstruction.lift_exec body r.core.core fuel after checked)

def setCore (r : State) (core : Registers) : State :=
  {r with core := {r.core with core := {r.core.core with core := core}}}
def counterReady (r : State) (count : Nat) : State :=
  setCore r {r.core.core.core with remaining := List.replicate count true}
def headerResult (r : State) (count : Nat) : State :=
  setCore r {r.core.core.core with remaining := [], output := natural count ++ r.core.core.core.output}

def prependHeader : Block 16 := .seq (.action (.push 8 false)) (lift9 MatrixSolutionSerialization.unaryLoop)
theorem prependHeader_exec (r : State) (count : Nat) :
    Exec prependHeader (counterReady r count).store (3 * count + 2) (headerResult r count).store := by
  let prepared := counterReady (setCore r {r.core.core.core with output := false :: r.core.core.core.output}) count
  have delimiter : Exec (.action (.push (8 : Fin 16) false)) (counterReady r count).store 1 prepared.store := .action _ _
  have core : Exec MatrixSolutionSerialization.unaryLoop prepared.core.core.core.store (3 * count + 1)
      (headerResult r count).core.core.core.store := by
    simpa only [prepared, counterReady, setCore, headerResult, natural, List.append_assoc,
      List.cons_append, List.nil_append] using
      MatrixSolutionSerialization.unaryLoop_exec {r.core.core.core with output := false :: r.core.core.core.output} count
  have lifted := lift9_exec MatrixSolutionSerialization.unaryLoop prepared (3 * count + 1)
    (headerResult r count).core.core.core core
  have cost : 3 * count + 2 = 1 + (3 * count + 1) := by omega
  simpa only [prependHeader, cost, prepared, counterReady, headerResult, setCore] using Exec.seq delimiter lifted

def inputState {n : Nat} (F : Family n) : State := ⟨SourceMatrixConstruction.inputState F, List.replicate F.length true⟩
def payloadState {n : Nat} (F : Family n) : State :=
  ⟨SourceMatrixConstruction.ready F n 0 0 0 (MatrixInstructions.matrixBits (SourceClosure.affineMaskRows F)),
    List.replicate F.length true⟩

theorem payload_exec {n : Nat} (F : Family n) :
    Exec (lift15 SourceMatrixConstruction.payload) (inputState F).store
      (SourceMatrixConstruction.payloadFuel n F.length) (payloadState F).store :=
  lift15_exec _ (inputState F) _ (payloadState F).core (SourceMatrixConstruction.payload_exec F)

def counted {n : Nat} (F : Family n) (remaining accumulated : Nat) : State :=
  {payloadState F with core := {(payloadState F).core with core := MatrixPayloadCounter.counted n remaining accumulated (payloadState F).core.core}}
def counterSeed : Block 16 := .seq (.action (.copy 1 9)) (.action (.copy 11 9))
theorem counterSeed_exec {n : Nat} (F : Family n) :
    Exec counterSeed (payloadState F).store 2 (counted F n 0).store := Exec.seq (.action _ _) (.action _ _)
theorem count_exec {n : Nat} (F : Family n) :
    Exec (lift12 MatrixPayloadCounter.loop) (counted F n 0).store ((3 * n + 4) * n + 1)
      (counted F 0 (n * n)).store := by
  have checked := lift12_exec MatrixPayloadCounter.loop (counted F n 0) _ (counted F 0 (n * n)).core.core
    (MatrixPayloadCounter.loop_exec n n 0 (payloadState F).core.core)
  simpa only [counted, MatrixPayloadCounter.counted, Nat.add_zero] using checked

def matrixHeaderState {n : Nat} (F : Family n) : State := headerResult (counted F 0 (n * n)) (n * n)
theorem matrixHeader_exec {n : Nat} (F : Family n) :
    Exec prependHeader (counted F 0 (n * n)).store (3 * (n * n) + 2) (matrixHeaderState F).store := by
  simpa only [counterReady, setCore, counted, MatrixPayloadCounter.counted, matrixHeaderState] using
    prependHeader_exec (counted F 0 (n * n)) (n * n)

def result {n : Nat} (F : Family n) : State := headerResult (matrixHeaderState F) F.length
def dimensionHeader : Block 16 := .seq (.action (.copy 2 15)) prependHeader
theorem dimensionHeader_exec {n : Nat} (F : Family n) :
    Exec dimensionHeader (matrixHeaderState F).store (3 * F.length + 3) (result F).store := by
  have copied : Exec (.action (.copy (2 : Fin 16) 15)) (matrixHeaderState F).store 1
      (counterReady (matrixHeaderState F) F.length).store := .action _ _
  have cost : 3 * F.length + 3 = 1 + (3 * F.length + 2) := by omega
  simpa only [dimensionHeader, result, cost] using
    Exec.seq copied (prependHeader_exec (matrixHeaderState F) F.length)

theorem result_output {n : Nat} (F : Family n) : (result F).core.core.core.output = affineMatrixPacket F := by
  change natural F.length ++ (natural (n * n) ++ MatrixInstructions.matrixBits (SourceClosure.affineMaskRows F)) = _
  rw [affineMatrixPacket, MatrixInputEncoding.codec_bits, SourceClosure.affineMaskRows, SourcePlane.planeRows_length]

def headers : Block 16 := .seq counterSeed (.seq (lift12 MatrixPayloadCounter.loop)
  (.seq prependHeader dimensionHeader))
def headerFuel (n rows : Nat) : Nat := (3 * n + 4) * n + 3 * (n * n) + 3 * rows + 8
theorem headers_exec {n : Nat} (F : Family n) :
    Exec headers (payloadState F).store (headerFuel n F.length) (result F).store := by
  have cost : headerFuel n F.length = 2 + (((3 * n + 4) * n + 1) + ((3 * (n * n) + 2) + (3 * F.length + 3))) := by
    unfold headerFuel; omega
  simpa only [headers, cost] using Exec.seq (counterSeed_exec F)
    (Exec.seq (count_exec F) (Exec.seq (matrixHeader_exec F) (dimensionHeader_exec F)))

def block : Block 16 := .seq (lift15 SourceMatrixConstruction.payload) headers
def fuel (n rows : Nat) : Nat := SourceMatrixConstruction.payloadFuel n rows + headerFuel n rows
theorem block_exec {n : Nat} (F : Family n) :
    Exec block (inputState F).store (fuel n F.length) (result F).store :=
  Exec.seq (payload_exec F) (headers_exec F)

end PNP.Concrete.ResidualReduction.SourceMatrixPacket
