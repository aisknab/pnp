import PNP.Concrete.ResidualReduction.SourceChoiceOutput
import PNP.Concrete.ResidualReduction.SourceMenuRawBridge

/-! Literal preparation of the selector's source fields from the strict
family loader. The raw source is retained before parsing; row and dimension
headers are rebuilt from the parser's actual counters. No menu is supplied
or generated until the selector's own fallback requires it. -/

namespace PNP.Concrete.ResidualReduction.SourceSelectorInput
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (familyBits codec)
open PNP.Concrete.ResidualReduction.SourceSelectionInvocation (Data)
open PNP.Concrete.ResidualReduction.SourceCandidateLoad (Held)
open PNP.Concrete.ResidualReduction.SourceSelectorState
open PNP.Concrete.ResidualReduction.SourceChoiceOutput (core frame zero)

def emptyHeld : Held := ⟨[],[]⟩
def emptySaved : Saved := ⟨[],[]⟩
def data (input : BitString) : Data := ⟨[],[],[],[],input,[]⟩
def loaderCore (r : Store 16) : Store 38 := Frame.join r (Store.empty 22)
def loaderFrame (input : BitString) : Store 32 :=
  Frame.join (Store.empty 22) (dataFrame (data input) emptyHeld emptySaved)
def loaded (r : Store 16) (input : BitString) : Store 48 :=
  full (loaderCore r) (data input) emptyHeld emptySaved
theorem loaded_eq (r : Store 16) (input : BitString) :
    loaded r input = Frame.join r (loaderFrame input) := by
  cases r with
  | cons b0 rest1 =>
    cases rest1 with
    | cons b1 rest2 =>
      cases rest2 with
      | cons b2 rest3 =>
        cases rest3 with
        | cons b3 rest4 =>
          cases rest4 with
          | cons b4 rest5 =>
            cases rest5 with
            | cons b5 rest6 =>
              cases rest6 with
              | cons b6 rest7 =>
                cases rest7 with
                | cons b7 rest8 =>
                  cases rest8 with
                  | cons b8 rest9 =>
                    cases rest9 with
                    | cons b9 rest10 =>
                      cases rest10 with
                      | cons b10 rest11 =>
                        cases rest11 with
                        | cons b11 rest12 =>
                          cases rest12 with
                          | cons b12 rest13 =>
                            cases rest13 with
                            | cons b13 rest14 =>
                              cases rest14 with
                              | cons b14 rest15 =>
                                cases rest15 with
                                | cons b15 rest16 =>
                                  cases rest16
                                  rfl
def rawStart (input : BitString) : Store 48 :=
  Frame.join (SourceFamilyLoader.rawStart input).store (Store.empty 32)
def retain : Block 48 := .action (.copy 42 0)
theorem retain_exec (input : BitString) :
    Exec retain (rawStart input) 1 (loaded (SourceFamilyLoader.rawStart input).store input) := .action _ _

def saveFamily : Block 48 := .action (.copy 41 0)
theorem saveFamily_exec (r : Store 38) (d : Data) (t : Held) (s : Saved) :
    Exec saveFamily (full r d t s) 1 (full r {d with family := r.get 0} t s) :=
  Frame.execution (Frame.execution (SourceLinePullback.copy_to_saved r d.store (3 : Fin 6) 0) t.store) s.store
def saveWidth : Block 48 := .action (.copy 47 1)
theorem saveWidth_exec (r : Store 38) (d : Data) (t : Held) (s : Saved) :
    Exec saveWidth (full r d t s) 1 (full r d t {s with width := r.get 1}) := by
  have checked := SourceLinePullback.copy_to_saved (SourceCandidateLoad.full r d t) s.store
    (1 : Fin 2) (Frame.index 8 (1 : Fin 38))
  rw [prefix_working_get] at checked
  exact checked

def familyData {n : Nat} (F : Family n) (input : BitString) : Data :=
  {data input with family := (SourceEncoding.familyCodec n).encode F}
def widthSaved (n : Nat) : Saved := ⟨[],List.replicate n true⟩
def headerReady (n : Nat) : Registers := {zero with remaining := List.replicate n true,output := [false]}
def headerResult (n : Nat) : Registers := {zero with output := natural n}
def preparedData {n : Nat} (F : Family n) (input : BitString) : Data :=
  ⟨natural n,natural 0,[],(SourceEncoding.familyCodec n).encode F,input,[]⟩

def headerSeed : Block 48 := .seq (.action (.copy 2 47)) (.action (.push 8 false))
theorem headerSeed_exec {n : Nat} (F : Family n) (input : BitString) :
    Exec headerSeed (full (Store.empty 38) (familyData F input) emptyHeld (widthSaved n)) 2
      (full (core (headerReady n)) (familyData F input) emptyHeld (widthSaved n)) :=
  Exec.seq (.action _ _) (.action _ _)

def capture : Block 48 := .seq (.action (.copy 38 8)) <|
  .seq (.action (.push 39 false)) (.action (.push 47 true))
theorem capture_exec {n : Nat} (F : Family n) (input : BitString) :
    Exec capture (full (core (headerResult n)) (familyData F input) emptyHeld (widthSaved n)) 3
      (full (core (headerResult n)) (preparedData F input) emptyHeld (widthSaved (n + 1))) := by
  simp only [widthSaved,List.replicate_succ]
  exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def handoff : Block 48 := .seq saveFamily <| .seq saveWidth <| .seq reset <|
  .seq headerSeed <| .seq (Frame.block 39 MatrixSolutionSerialization.unaryLoop) capture
theorem handoff_exec {n : Nat} (F : Family n) (input : BitString) :
    Exec handoff (loaded (SourceMenuRaw.entered F) input) (3 * n + 47)
      (full (core (headerResult n)) (preparedData F input) emptyHeld (widthSaved (n + 1))) := by
  let r := loaderCore (SourceMenuRaw.entered F)
  have family : r.get 0 = (SourceEncoding.familyCodec n).encode F := rfl
  have width : r.get 1 = List.replicate n true := rfl
  have first := saveFamily_exec r (data input) emptyHeld emptySaved
  rw [family] at first
  have second := saveWidth_exec r (familyData F input) emptyHeld emptySaved
  rw [width] at second
  have cleared := reset_exec r (familyData F input) emptyHeld (widthSaved n)
  have seed := headerSeed_exec F input
  have header : Exec MatrixSolutionSerialization.unaryLoop (headerReady n).store (3 * n + 1)
      (headerResult n).store := by
    simpa only [headerReady,headerResult,zero,natural,List.append_assoc,List.singleton_append] using
      MatrixSolutionSerialization.unaryLoop_exec {zero with output := [false]} n
  have final := capture_exec F input
  have cost : 3 * n + 47 = 1 + (1 + (39 + (2 + ((3 * n + 1) + 3)))) := by omega
  rw [cost]
  exact Exec.seq first (Exec.seq second (Exec.seq cleared
    (Exec.seq seed (Exec.seq (Frame.execution header (frame (familyData F input) emptyHeld (widthSaved n))) final))))

def construct : Block 48 := .seq (Frame.block 32 SourceFamilyLoader.prepare) <|
  .seq (Frame.block 32 SourceMenuRaw.enter) handoff
def constructCost (n m payload : Nat) : Nat := 4 * payload + 3 * m + 3 * n + 55
def constructPolynomial : NatPolynomial := .linear 10 55

theorem construct_exec {n : Nat} (F : Family n) :
    Exec construct (loaded (SourceFamilyLoader.validated n F.length (familyBits F)).store
      (codec.encode ⟨n,F⟩))
      (constructCost n F.length (familyBits F).length)
      (SourceSelectorDispatch.initial F (core (headerResult n)) [] [] [] emptyHeld) := by
  have first := Frame.execution (SourceFamilyLoader.prepare_exec n F.length (familyBits F))
    (loaderFrame (codec.encode ⟨n,F⟩))
  have second := Frame.execution (SourceMenuRaw.enter_exec F) (loaderFrame (codec.encode ⟨n,F⟩))
  have last := handoff_exec F (codec.encode ⟨n,F⟩)
  simp only [← loaded_eq] at first second
  have target : full (core (headerResult n)) (preparedData F (codec.encode ⟨n,F⟩)) emptyHeld (widthSaved (n + 1)) =
      SourceSelectorDispatch.initial F (core (headerResult n)) [] [] [] emptyHeld := rfl
  rw [target] at last
  have cost : constructCost n F.length (familyBits F).length =
      (4 * (familyBits F).length + 5) + ((3 * F.length + 3) + (3 * n + 47)) := by
    unfold constructCost
    omega
  rw [cost]
  exact Exec.seq first (Exec.seq second last)

theorem construct_bound {n : Nat} (F : Family n) :
    constructCost n F.length (familyBits F).length ≤ constructPolynomial.eval (codec.encode ⟨n,F⟩).length := by
  have dimension := SourceMatrixEncoding.dimension_bound n F
  have rows := SourceMatrixEncoding.rowCount_bound n F
  have payload : (familyBits F).length ≤ (codec.encode ⟨n,F⟩).length := by
    rw [SourceMatrixEncoding.codec_bits]
    simp only [List.length_append]
    omega
  simp only [constructCost,constructPolynomial,NatPolynomial.eval_linear]
  omega

end PNP.Concrete.ResidualReduction.SourceSelectorInput
