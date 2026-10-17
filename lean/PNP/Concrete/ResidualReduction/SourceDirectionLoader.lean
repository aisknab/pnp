import PNP.Concrete.ResidualReduction.SourceDirectionInput
import PNP.Concrete.ResidualReduction.SourceDirectionInstructions
import PNP.Concrete.ResidualReduction.SourceFamilyLoader

/-! Literal input transport for the shared direction calculation. The normal
prefix is counted and copied before the family header is read. The original
dimension and normal bytes remain protected while the family is validated.
Every handoff to the prepared two-kernel calculation is executable code. -/

namespace PNP.Concrete.ResidualReduction.SourceDirectionLoader
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (familyBits familyBits_length)
open PNP.Concrete.ResidualReduction.SourceDirectionInput
open PNP.Concrete.ResidualReduction.SourceDirectionInstructions (State core setCore solver solver_exec small small_exec)

def embed (r : SourceMatrixPacket.State) (dimension normals : BitString) : State :=
  ⟨⟨⟨r.core.core.core, r.core.core.width, r.core.core.history, r.core.core.pending,
    r.core.source, r.core.outer, r.core.inner, r.rows, []⟩, []⟩, dimension, normals⟩
def loader (body : Block 16) : Block 20 := Frame.block 4 body
theorem loader_exec (body : Block 16) (r after : SourceMatrixPacket.State)
    (dimension normals : BitString) (fuel : Nat) (checked : Exec body r.store fuel after.store) :
    Exec (loader body) (embed r dimension normals).store fuel (embed after dimension normals).store :=
  Frame.execution checked (.cons [] (.cons [] (.cons dimension (.cons normals .nil))))

def wrap (c : MatrixReconstruction.State) (dimension normals : BitString) : State :=
  embed (SourceFamilyLoader.wrap c []) dimension normals
def rawStart (input : BitString) : State := wrap (MatrixInputHeaders.start input) [] []
def rawHeaders (input : BitString) : State := wrap (MatrixInputHeaders.result input) [] []
theorem headers_exec (input : BitString) :
    Exec (solver MatrixInputHeaders.block) (rawStart input).store (MatrixInputHeaders.fuel input)
      (rawHeaders input).store := solver_exec _ (rawStart input) _ _ (MatrixInputHeaders.block_exec input)

def normalStart (input : BitString) : State := wrap
  (MatrixInputPayload.start (first input).dimension (first input).rows (first input).payload) [] []
def normalDone (input : BitString) : State := wrap
  (MatrixInputPayload.result (first input).dimension (first input).rows (first input).payload) [] []
theorem normal_seed_exec (input : BitString) (success : (first input).terminated = true) :
    Exec (solver MatrixInputPayload.seed) (rawHeaders input).store 5 (normalStart input).store :=
  solver_exec _ (rawHeaders input) _ _ (MatrixInputPayload.seed_exec input success)
theorem normal_payload_exec (input : BitString) :
    Exec (solver MatrixInputPayload.block) (normalStart input).store
      (MatrixInputPayload.fuel (first input).dimension (first input).rows) (normalDone input).store :=
  solver_exec _ (normalStart input) _ _ (MatrixInputPayload.block_exec _ _ _)

def preserve : Block 20 := .seq (.action (.copy 18 9)) <| .seq (.action (.copy 19 3)) <|
  .seq (.action (.clear 3)) <| .seq (.action (.clear 1)) (.action (.clear 5))
def familySeed (input : BitString) : State := wrap
  ⟨{base 0 [] with input := familyTail input}, List.replicate (first input).dimension true, [], []⟩
    (List.replicate (first input).dimension true) (normalBytes input).reverse
theorem preserve_exec (input : BitString) :
    Exec preserve (normalDone input).store 5 (familySeed input).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
    (Exec.seq (.action _ _) (.action _ _))))

def readHeaderResult (input : BitString) : State := wrap
  ⟨{base (header input).count [] with input := (header input).rest, sign := if (header input).terminated then [true] else []},
    List.replicate (first input).dimension true, [], []⟩
      (List.replicate (first input).dimension true) (normalBytes input).reverse
theorem family_header_exec (input : BitString) :
    Exec (small MatrixStrictHeader.block) (familySeed input).store
      (MatrixStrictHeader.blockFuel (familyTail input)) (readHeaderResult input).store := by
  have checked : Exec MatrixStrictHeader.block (familySeed input).family.core.core.store
      (MatrixStrictHeader.blockFuel (familyTail input)) (readHeaderResult input).family.core.core.store := by
    cases flag : (MatrixStrictHeader.scan (familyTail input)).terminated <;>
      simpa only [familySeed, readHeaderResult, wrap, embed, SourceFamilyLoader.wrap,
      header, MatrixStrictHeader.result, base, List.replicate_zero, List.append_nil,
      flag, Bool.false_eq_true, if_false, if_true] using
      MatrixStrictHeader.block_exec (familyTail input) (base 0 [])
  exact small_exec _ (familySeed input) _ _ checked

theorem readHeader_valid (input : BitString) (success : (header input).terminated = true) :
    readHeaderResult input = embed
      (SourceFamilyLoader.headerState (first input).dimension (header input).count (header input).rest)
      (List.replicate (first input).dimension true) (normalBytes input).reverse := by
  simp only [readHeaderResult, SourceFamilyLoader.headerState, wrap, success, if_true]

def familyStart (input : BitString) : State := embed
  (SourceFamilyLoader.start (first input).dimension (header input).count (header input).rest)
    (List.replicate (first input).dimension true) (normalBytes input).reverse
def familyDone (input : BitString) : State := embed
  (SourceFamilyLoader.result (first input).dimension (header input).count (header input).rest)
    (List.replicate (first input).dimension true) (normalBytes input).reverse
theorem family_seed_exec (input : BitString) (success : (header input).terminated = true) :
    Exec (loader SourceFamilyLoader.seed) (readHeaderResult input).store
      (3 * (first input).dimension + 12) (familyStart input).store := by
  rw [readHeader_valid input success]
  exact loader_exec _ _ _ _ _ _ (SourceFamilyLoader.seed_exec _ _ _)
theorem family_payload_exec (input : BitString) :
    Exec (loader SourceFamilyLoader.block) (familyStart input).store
      (SourceFamilyLoader.fuel (first input).dimension (header input).count) (familyDone input).store :=
  loader_exec _ _ _ _ _ _ (SourceFamilyLoader.block_exec _ _ _)

def validated {n : Nat} (F : Family n) (U : System n) : State := embed
  (SourceFamilyLoader.validated n F.length (familyBits F)) (List.replicate n true) (matrixBits U).reverse
theorem familyDone_canonical {n : Nat} (F : Family n) (U : System n) :
    familyDone (SourceDirectionEncoding.codec.encode ⟨n, U, F⟩) = validated F U := by
  simp only [familyDone, canonical_first, canonical_header, canonical_normalBytes,
    SourceFamilyLoader.result_complete n F.length (familyBits F) (familyBits_length F), validated]

def familyPrepared {n : Nat} (F : Family n) (U : System n) : State := embed
  (SourceFamilyLoader.prepared n F.length (familyBits F)) (List.replicate n true) (matrixBits U).reverse
theorem family_prepare_exec {n : Nat} (F : Family n) (U : System n) :
    Exec (loader SourceFamilyLoader.prepare) (validated F U).store
      (4 * (familyBits F).length + 5) (familyPrepared F U).store :=
  loader_exec _ _ _ _ _ _ (SourceFamilyLoader.prepare_exec n F.length (familyBits F))

def handoff : Block 20 := .seq (.action (.copy 17 0)) <| .seq (.action (.clear 0)) <|
  .seq (.action (.copy 3 19)) <| .seq (.action (.copy 1 18)) <|
    .seq (.action (.push 1 true)) <| .seq (.action (.push 5 true)) (.action (.clear 15))
def normalPrepared {n : Nat} (F : Family n) (U : System n) : State :=
  setCore (SourceDirectionInstructions.framed F U) (MatrixInputPreparation.start n (matrixBits U))
theorem handoff_exec {n : Nat} (F : Family n) (U : System n) :
    Exec handoff (familyPrepared F U).store 7 (normalPrepared F U).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
    (Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))))))
theorem normal_prepare_exec {n : Nat} (F : Family n) (U : System n) :
    Exec (solver MatrixInputPreparation.block) (normalPrepared F U).store
      (4 * (matrixBits U).length + 6) (SourceDirectionInstructions.start F U).store :=
  solver_exec _ (normalPrepared F U) _ _ (MatrixInputPreparation.block_exec n (matrixBits U))

def finish : Block 20 := .seq (loader SourceFamilyLoader.prepare)
  (.seq handoff (solver MatrixInputPreparation.block))
def finishFuel {n : Nat} (F : Family n) (U : System n) : Nat :=
  (4 * (familyBits F).length + 5) + (7 + (4 * (matrixBits U).length + 6))
theorem finish_exec {n : Nat} (F : Family n) (U : System n) :
    Exec finish (validated F U).store (finishFuel F U) (SourceDirectionInstructions.start F U).store :=
  Exec.seq (family_prepare_exec F U) (Exec.seq (handoff_exec F U) (normal_prepare_exec F U))

end PNP.Concrete.ResidualReduction.SourceDirectionLoader
