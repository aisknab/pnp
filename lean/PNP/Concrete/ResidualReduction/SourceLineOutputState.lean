import PNP.Concrete.ResidualReduction.SourceLineOutputEncoding

/-! Reuse the saved direction map and joint vector. Only working registers
are reset; all retained source data remains protected. -/

namespace PNP.Concrete.ResidualReduction.SourceLineOutput
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceLinePullback (copy_from_saved)
open PNP.Concrete.ResidualReduction.SourceWitnessLift (store)

def retain : Block 9 := .action (.copy 7 8)
def retained (r : Registers) : Registers := {r with reserved := r.output}
def load : Block 38 := .seq (Frame.block 29 retain) <|
  .seq (.action (.copy 0 28)) <| .seq (.action (.copy 1 29)) (.action (.copy 3 20))
def loaded (r : Registers) (data : Store 29) : Registers :=
  {r with reserved := r.output, input := data.get 19, target := data.get 20, excess := data.get 11}
theorem load_exec (r : Registers) (data : Store 29) :
    Exec load (store r data) 4 (store (loaded r data) data) := by
  let first := retained r
  let second := {first with input := data.get 19}
  let third := {second with target := data.get 20}
  have saved : Exec (Frame.block 29 retain) (store r data) 1 (store first data) :=
    Frame.execution (Exec.action (.copy (7 : Fin 9) 8) r.store) data
  have mapped : Exec (.action (.copy (0 : Fin 38) 28)) (store first data) 1 (store second data) :=
    copy_from_saved first.store data 0 19
  have counted : Exec (.action (.copy (1 : Fin 38) 29)) (store second data) 1 (store third data) :=
    copy_from_saved second.store data 1 20
  have joint : Exec (.action (.copy (3 : Fin 38) 20)) (store third data) 1 (store (loaded r data) data) :=
    copy_from_saved third.store data 3 11
  exact Exec.seq saved (Exec.seq mapped (Exec.seq counted joint))

def clearFirst : Block 9 := .seq (.action (.clear 2)) (.action (.clear 4))
def clearSecond : Block 9 := .seq (.action (.clear 5)) <| .seq (.action (.clear 6)) (.action (.clear 8))
def clearedFirst (r : Registers) : Registers := {r with remaining := [], sign := []}
def cleared (r : Registers) : Registers := {r with remaining := [], sign := [], mode := [], active := [], output := []}
def clear : Block 9 := .seq clearFirst clearSecond
theorem clear_exec (r : Registers) : Exec clear r.store 5 (cleared r).store := by
  have first : Exec clearFirst r.store 2 (clearedFirst r).store := Exec.seq (.action _ _) (.action _ _)
  have second : Exec clearSecond (clearedFirst r).store 3 (cleared r).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  exact Exec.seq first second
def seed : Block 38 := .seq load (Frame.block 29 clear)
def seeded (r : Registers) (data : Store 29) : Registers := cleared (loaded r data)
theorem seed_exec (r : Registers) (data : Store 29) :
    Exec seed (store r data) 9 (store (seeded r data) data) :=
  Exec.seq (load_exec r data) (Frame.execution (clear_exec (loaded r data)) data)

end PNP.Concrete.ResidualReduction.SourceLineOutput
