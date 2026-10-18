import PNP.Concrete.ResidualReduction.SourceChoiceEncoding

/-! Reorder a complete line witness without inspecting its mathematical
content. Reverse once, extract the fixed-width direction and covector, append
the covector's zero constant, and restore source-weight order. The general
word-level theorem charges every copy and preserves the selected normal. -/

namespace PNP.Concrete.ResidualReduction.SourceChoiceLine
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.MatrixInstructions

def ready (n : Nat) (alpha weights beta direction : BitString) : Registers :=
  ⟨[],alpha,[],weights ++ (beta ++ direction),[],[],List.replicate n true,[],[]⟩
def reversed (n : Nat) (alpha weights beta direction : BitString) : Registers :=
  {ready n alpha weights beta direction with excess := [],output := (weights ++ (beta ++ direction)).reverse}
def directionReady (n : Nat) (alpha weights beta direction : BitString) : Registers :=
  {ready n alpha weights beta direction with input := direction.reverse ++ (beta.reverse ++ weights.reverse), remaining := List.replicate n true,excess := []}
def directionRead (n : Nat) (alpha weights beta direction : BitString) : Registers :=
  {ready n alpha weights beta direction with input := beta.reverse ++ weights.reverse,excess := direction}
def betaReady (n : Nat) (alpha weights beta direction : BitString) : Registers :=
  {directionRead n alpha weights beta direction with remaining := List.replicate n true,excess := [false],sign := direction}
def betaRead (n : Nat) (alpha weights beta direction : BitString) : Registers :=
  {betaReady n alpha weights beta direction with input := weights.reverse,remaining := [],excess := beta ++ [false]}
def weightReady (n : Nat) (alpha weights beta direction : BitString) : Registers :=
  {betaRead n alpha weights beta direction with excess := weights.reverse,mode := beta ++ [false]}
def weightRead (n : Nat) (alpha weights beta direction : BitString) : Registers :=
  {weightReady n alpha weights beta direction with excess := [],output := weights}

def position : Block 9 := .seq (.action (.copy 0 8)) <|
  .seq (.action (.clear 8)) (.action (.copy 2 6))
def saveDirection : Block 9 := .seq (.action (.copy 4 3)) <|
  .seq (.action (.clear 3)) <| .seq (.action (.push 3 false)) (.action (.copy 2 6))
def saveBeta : Block 9 := .seq (.action (.copy 5 3)) (.action (.copy 3 0))
def finish : Block 9 := .seq (.action (.copy 0 4)) <|
  .seq (.action (.copy 4 8)) <| .seq (.action (.clear 6)) (.action (.clear 8))
def block : Block 9 := .seq ClauseQuery.reverseLoop <| .seq position <|
  .seq copyLoop <| .seq saveDirection <| .seq copyLoop <|
    .seq saveBeta <| .seq ClauseQuery.reverseLoop finish
def fuel (n m : Nat) : Nat := 8 * m + 18 * n + 17

theorem reverse_exec (n : Nat) (alpha weights beta direction : BitString) :
    Exec ClauseQuery.reverseLoop (ready n alpha weights beta direction).store
      (4 * (weights ++ (beta ++ direction)).length + 1)
      (reversed n alpha weights beta direction).store := by
  simpa only [ready,reversed,List.append_nil] using
    ClauseQuery.reverse_exec (ready n alpha weights beta direction) (weights ++ (beta ++ direction))

theorem position_exec (n : Nat) (alpha weights beta direction : BitString) :
    Exec position (reversed n alpha weights beta direction).store 3
      (directionReady n alpha weights beta direction).store := by
  simp only [reversed,List.reverse_append,List.append_assoc]
  exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

theorem direction_exec (n : Nat) (alpha weights beta direction : BitString)
    (width : direction.length = n) :
    Exec copyLoop (directionReady n alpha weights beta direction).store (5 * n + 1)
      (directionRead n alpha weights beta direction).store := by
  simpa only [ready,directionReady,directionRead,List.length_reverse,width,
    List.reverse_reverse,List.append_nil] using
    copy_exec {ready n alpha weights beta direction with excess := []} direction.reverse (beta.reverse ++ weights.reverse)

theorem saveDirection_exec (n : Nat) (alpha weights beta direction : BitString) :
    Exec saveDirection (directionRead n alpha weights beta direction).store 4
      (betaReady n alpha weights beta direction).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

theorem beta_exec (n : Nat) (alpha weights beta direction : BitString)
    (width : beta.length = n) :
    Exec copyLoop (betaReady n alpha weights beta direction).store (5 * n + 1)
      (betaRead n alpha weights beta direction).store := by
  simpa only [ready,directionRead,betaReady,betaRead,List.length_reverse,width,List.reverse_reverse] using
    copy_exec (betaReady n alpha weights beta direction) beta.reverse weights.reverse

theorem saveBeta_exec (n : Nat) (alpha weights beta direction : BitString) :
    Exec saveBeta (betaRead n alpha weights beta direction).store 2
      (weightReady n alpha weights beta direction).store :=
  Exec.seq (.action _ _) (.action _ _)

theorem weights_exec (n : Nat) (alpha weights beta direction : BitString) :
    Exec ClauseQuery.reverseLoop (weightReady n alpha weights beta direction).store (4 * weights.length + 1)
      (weightRead n alpha weights beta direction).store := by
  simpa only [ready,directionRead,betaReady,betaRead,weightReady,weightRead,
    List.length_reverse,List.reverse_reverse,List.append_nil] using
    ClauseQuery.reverse_exec (weightReady n alpha weights beta direction) weights.reverse

theorem finish_exec (n : Nat) (alpha weights beta direction : BitString) :
    Exec finish (weightRead n alpha weights beta direction).store 4
      (SourceSelectionPacket.ready alpha (beta ++ [false]) weights direction).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

theorem block_exec (n : Nat) (alpha weights beta direction : BitString)
    (betaWidth : beta.length = n) (directionWidth : direction.length = n) :
    Exec block (ready n alpha weights beta direction).store (fuel n weights.length)
      (SourceSelectionPacket.ready alpha (beta ++ [false]) weights direction).store := by
  have checked := Exec.seq (reverse_exec n alpha weights beta direction)
    (Exec.seq (position_exec n alpha weights beta direction)
      (Exec.seq (direction_exec n alpha weights beta direction directionWidth)
        (Exec.seq (saveDirection_exec n alpha weights beta direction)
          (Exec.seq (beta_exec n alpha weights beta direction betaWidth)
            (Exec.seq (saveBeta_exec n alpha weights beta direction)
              (Exec.seq (weights_exec n alpha weights beta direction)
                (finish_exec n alpha weights beta direction)))))))
  have cost : fuel n weights.length =
      (4 * (weights ++ (beta ++ direction)).length + 1) +
        (3 + ((5 * n + 1) + (4 + ((5 * n + 1) + (2 + ((4 * weights.length + 1) + 4)))))) := by
    simp only [fuel,List.length_append,betaWidth,directionWidth]
    omega
  simpa only [block,cost] using checked

end PNP.Concrete.ResidualReduction.SourceChoiceLine
