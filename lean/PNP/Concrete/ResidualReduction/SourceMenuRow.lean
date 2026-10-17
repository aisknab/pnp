import PNP.Concrete.ResidualReduction.SourceMenuRowInput
import PNP.Concrete.NormalizerRegisterFrame

/-! Preserve the source cursor, width and accumulated candidate stream while
the actual row scan and emitter execute. No computed normals or validity
flags are supplied across the source-row boundary. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuRow
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.CoefficientComparison
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChain

structure Saved where
  stream : BitString
  width : BitString
  accumulator : BitString
deriving Repr

def Saved.store (s : Saved) : Store 3 :=
  .cons s.stream (.cons s.width (.cons s.accumulator .nil))
def full (r : Registers) (s : Saved) : Store 12 := Frame.join r.store s.store
def scanFull (r : SourceMenuScan.Registers) (s : Saved) : Store 12 := Frame.join r.store s.store
def snapshot (r : Registers) : Saved := ⟨r.input, r.target, r.reserved⟩

def capture : Block 12 := .seq (.action (.copy 9 0)) <|
  .seq (.action (.copy 10 1)) (.action (.copy 11 7))
theorem capture_exec (r : Registers) (s : Saved) :
    Exec capture (full r s) 3 (full r (snapshot r)) :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def inputRegisters (r : Registers) : Registers :=
  {r with input := r.sign, target := r.output, output := r.reserved}
def loadInputs : Block 9 := .seq (.action (.copy 0 4)) <|
  .seq (.action (.copy 1 8)) (.action (.copy 8 7))
theorem loadInputs_exec (r : Registers) :
    Exec loadInputs r.store 3 (inputRegisters r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def clearScratch : Block 9 := .seq (.action (.clear 2)) <|
  .seq (.action (.clear 3)) (.action (.clear 4))
def scratchCleared (r : Registers) : Registers :=
  {r with remaining := [], excess := [], sign := []}
theorem clearScratch_exec (r : Registers) :
    Exec clearScratch r.store 3 (scratchCleared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def resetFlag (index : Fin 9) : Block 9 :=
  .seq (.action (.clear index)) (.action (.push index false))
def resetFlags : Block 9 := .seq (resetFlag 5) (.seq (resetFlag 6) (resetFlag 7))
def flagsCleared (r : Registers) : Registers :=
  {r with mode := [false], active := [false], reserved := [false]}
theorem resetFlags_exec (r : Registers) :
    Exec resetFlags r.store 6 (flagsCleared r).store :=
  Exec.seq (Exec.seq (.action _ _) (.action _ _))
    (Exec.seq (Exec.seq (.action _ _) (.action _ _)) (Exec.seq (.action _ _) (.action _ _)))

def prepare : Block 9 := .seq loadInputs (.seq clearScratch resetFlags)
theorem prepare_exec (r : Registers) :
    Exec prepare r.store 12 (SourceMenuScan.start r.sign r.output r.reserved).store :=
  Exec.seq (loadInputs_exec r)
    (Exec.seq (clearScratch_exec (inputRegisters r))
      (resetFlags_exec (scratchCleared (inputRegisters r))))

def handoff : Block 12 := .seq capture (Frame.block 3 prepare)
theorem handoff_exec (r : Registers) (s : Saved) :
    Exec handoff (full r s) 15
      (scanFull (SourceMenuScan.start r.sign r.output r.reserved) (snapshot r)) :=
  Exec.seq (capture_exec r s) (Frame.execution (prepare_exec r) (snapshot r).store)

def reload : Block 12 := .seq (.action (.copy 0 9)) <|
  .seq (.action (.copy 1 10)) (.action (.copy 7 8))
def reloaded (r : SourceMenuScan.Registers) (s : Saved) : Registers :=
  ⟨s.stream, s.width, r.leftAccum, r.rightAccum, r.xorAccum,
    [r.leftFlag], [r.rightFlag], r.output, r.output⟩
theorem reload_exec (r : SourceMenuScan.Registers) (s : Saved) :
    Exec reload (scanFull r s) 3 (full (reloaded r s) s) :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def clearFlagsOutput : Block 9 := .seq (.action (.clear 5)) <|
  .seq (.action (.clear 6)) (.action (.clear 8))
def flagsOutputCleared (r : Registers) : Registers :=
  {r with mode := [], active := [], output := []}
theorem clearFlagsOutput_exec (r : Registers) :
    Exec clearFlagsOutput r.store 3 (flagsOutputCleared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
def clearWork : Block 9 := .seq clearScratch clearFlagsOutput
def cleared (r : Registers) : Registers :=
  ⟨r.input, r.target, [], [], [], [], [], r.reserved, []⟩
theorem clearWork_exec (r : Registers) :
    Exec clearWork r.store 6 (cleared r).store :=
  Exec.seq (clearScratch_exec r) (clearFlagsOutput_exec (scratchCleared r))

def restore : Block 12 := .seq reload (Frame.block 3 clearWork)
theorem restore_exec (r : SourceMenuScan.Registers) (s : Saved) :
    Exec restore (scanFull r s) 9 (full (cleared (reloaded r s)) s) :=
  Exec.seq (reload_exec r s) (Frame.execution (clearWork_exec (reloaded r s)) s.store)

def saved (n : Nat) (suffix accumulator : BitString) : Saved :=
  ⟨suffix, List.replicate n true, accumulator⟩
def block : Block 12 := .seq (Frame.block 3 SourceMenuRowInput.block) <|
  .seq handoff <| .seq (Frame.block 3 SourceMenuCandidates.block) restore
def cost {n : Nat} (r : Row n) (accumulator : BitString) : Nat :=
  (18 * n + 11) + (15 +
    (SourceMenuCandidates.cost (normalBits r.left) (normalBits r.right) accumulator + 9))

theorem block_exec {n : Nat} (r : Row n) (suffix accumulator : BitString) (s : Saved) :
    Exec block
      (full (SourceMenuRowInput.initial n
        ((SourceEncoding.rowCodec n).encode r ++ suffix) accumulator) s)
      (cost r accumulator)
      (full (SourceMenuRowInput.initial n suffix
        (matrixBits (rowNormals r).reverse ++ accumulator)) (saved n suffix accumulator)) := by
  have first := Frame.execution (SourceMenuRowInput.block_exec r suffix accumulator) s.store
  have second := handoff_exec (SourceMenuRowInput.result r suffix accumulator) s
  have third := Frame.execution (SourceMenuCandidates.row_exec r accumulator)
    (saved n suffix accumulator).store
  have fourth := restore_exec
    (SourceMenuCandidates.result (normalBits r.left) (normalBits r.right) accumulator)
    (saved n suffix accumulator)
  have output := SourceMenuCandidates.row_output r accumulator
  change (SourceMenuCandidates.result (normalBits r.left) (normalBits r.right) accumulator).output =
    matrixBits (rowNormals r).reverse ++ accumulator at output
  simp only [cleared, reloaded, output, saved] at fourth
  exact Exec.seq first (Exec.seq second (Exec.seq third fourth))

theorem cost_bound {n : Nat} (r : Row n) (accumulator : BitString) :
    cost r accumulator ≤ 43 * n + 49 := by
  have checked := SourceMenuCandidates.row_cost_bound r accumulator
  unfold cost
  omega

end PNP.Concrete.ResidualReduction.SourceMenuRow
