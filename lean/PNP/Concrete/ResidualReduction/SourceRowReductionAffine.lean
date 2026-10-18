import PNP.Concrete.ResidualReduction.SourceRowReductionOutput

/-! Affine substitution reads the two saved leading bits and conditionally
adds the computed tail remainder. Every coefficient operation is executed by
the counted word program; no transformed row is supplied as input. -/

namespace PNP.Concrete.ResidualReduction.SourceRowReductionAffine
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra
open PNP.Concrete.ResidualReduction.SourceRowReductionState

def loadLeft : Block 19 := .seq (.action (.copy 0 12)) (.action (.copy 5 11))
def saveLeft : Block 19 := .seq (.action (.copy 11 8)) (.action (.clear 8))
def addLeft : Block 19 := .seq loadLeft <|
  .seq (core SourceRowCoefficientInstructions.add) saveLeft
def loadRight : Block 19 := .seq (.action (.copy 0 12)) (.action (.copy 5 13))
def saveRight : Block 19 := .seq (.action (.copy 13 8)) (.action (.clear 8))
def addRight : Block 19 := .seq loadRight <|
  .seq (core SourceRowCoefficientInstructions.add) saveRight
def addFuel (n : Nat) : Nat := 11 * (n + 1) + 7

theorem addLeft_exec {n : Nat} (A B : BitString) (u f g : Affine n)
    (selected lh rh : Bool) (suffix : BitString) (kind : Bool) :
    Exec addLeft (prepared A B u f g selected lh rh suffix kind) (addFuel n)
      (prepared A B u (aAdd u f) g selected lh rh suffix kind) := by
  let r := work n []
  let s : SourcePlanePartnerBuilder.Saved := ⟨A,B,affineWord f⟩
  let d := rowData u g selected lh rh suffix kind
  have load : Exec loadLeft (full r s d) 2
      (full (SourceRowCoefficientInstructions.binaryReady r u f) s d) :=
    Exec.seq (.action _ _) (.action _ _)
  have add := core_exec (SourceRowCoefficientInstructions.add_exec r u f) s d
  have save : Exec saveLeft (full (SourceRowCoefficientInstructions.added r u f) s d) 2
      (prepared A B u (aAdd u f) g selected lh rh suffix kind) :=
    Exec.seq (.action _ _) (.action _ _)
  have cost : addFuel n = 2 + ((11 * (n + 1) + 3) + 2) := by unfold addFuel; omega
  simpa only [addLeft,cost,r,s,d,prepared] using Exec.seq load (Exec.seq add save)

theorem addRight_exec {n : Nat} (A B : BitString) (u f g : Affine n)
    (selected lh rh : Bool) (suffix : BitString) (kind : Bool) :
    Exec addRight (prepared A B u f g selected lh rh suffix kind) (addFuel n)
      (prepared A B u f (aAdd u g) selected lh rh suffix kind) := by
  let r := work n []
  let s : SourcePlanePartnerBuilder.Saved := ⟨A,B,affineWord f⟩
  let d := rowData u g selected lh rh suffix kind
  have load : Exec loadRight (full r s d) 2
      (full (SourceRowCoefficientInstructions.binaryReady r u g) s d) :=
    Exec.seq (.action _ _) (.action _ _)
  have add := core_exec (SourceRowCoefficientInstructions.add_exec r u g) s d
  have save : Exec saveRight (full (SourceRowCoefficientInstructions.added r u g) s d) 2
      (prepared A B u f (aAdd u g) selected lh rh suffix kind) :=
    Exec.seq (.action _ _) (.action _ _)
  have cost : addFuel n = 2 + ((11 * (n + 1) + 3) + 2) := by unfold addFuel; omega
  simpa only [addRight,cost,r,s,d,prepared] using Exec.seq load (Exec.seq add save)

def left : Block 19 := .branch 15 .skip .skip addLeft
def right : Block 19 := .branch 16 .skip .skip addRight
def flagFuel (n : Nat) : Bool → Nat
  | false => 2
  | true => addFuel n + 1

theorem left_exec {n : Nat} (A B : BitString) (u f g : Affine n)
    (selected lh rh : Bool) (suffix : BitString) (kind : Bool) :
    Exec left (prepared A B u f g selected lh rh suffix kind) (flagFuel n lh)
      (prepared A B u (aAdd (aScale lh u) f) g selected lh rh suffix kind) := by
  cases lh with
  | false =>
    simpa only [flagFuel,scale_false,add_zero_left] using
      (show Exec left (prepared A B u f g selected false rh suffix kind) 2
        (prepared A B u f g selected false rh suffix kind) from Exec.zero rfl (.skip _))
  | true =>
    have run : Exec left (prepared A B u f g selected true rh suffix kind) (1 + addFuel n)
        (prepared A B u (aAdd u f) g selected true rh suffix kind) :=
      Exec.one rfl (addLeft_exec A B u f g selected true rh suffix kind)
    simpa only [flagFuel,scale_true,Nat.add_comm] using run

theorem right_exec {n : Nat} (A B : BitString) (u f g : Affine n)
    (selected lh rh : Bool) (suffix : BitString) (kind : Bool) :
    Exec right (prepared A B u f g selected lh rh suffix kind) (flagFuel n rh)
      (prepared A B u f (aAdd (aScale rh u) g) selected lh rh suffix kind) := by
  cases rh with
  | false =>
    simpa only [flagFuel,scale_false,add_zero_left] using
      (show Exec right (prepared A B u f g selected lh false suffix kind) 2
        (prepared A B u f g selected lh false suffix kind) from Exec.zero rfl (.skip _))
  | true =>
    have run : Exec right (prepared A B u f g selected lh true suffix kind) (1 + addFuel n)
        (prepared A B u f (aAdd u g) selected lh true suffix kind) :=
      Exec.one rfl (addRight_exec A B u f g selected lh true suffix kind)
    simpa only [flagFuel,scale_true,Nat.add_comm] using run

def block : Block 19 := .seq left (.seq right SourceRowReductionOutput.finish)
def fuel (n : Nat) (lh rh : Bool) : Nat :=
  flagFuel n lh + (flagFuel n rh + SourceRowReductionOutput.finishFuel n)

theorem block_exec {n : Nat} (A B : BitString) (u f g : Affine n)
    (selected lh rh : Bool) (suffix : BitString) (kind : Bool) :
    Exec block (prepared A B u f g selected lh rh suffix kind) (fuel n lh rh)
      (SourceRowReductionOutput.terminal A B u suffix kind
        ((codec n).encode (some ⟨selected,aAdd (aScale lh u) f,aAdd (aScale rh u) g⟩))) :=
  Exec.seq (left_exec A B u f g selected lh rh suffix kind)
    (Exec.seq (right_exec A B u (aAdd (aScale lh u) f) g selected lh rh suffix kind)
      (SourceRowReductionOutput.finish_exec A B u (aAdd (aScale lh u) f)
        (aAdd (aScale rh u) g) selected lh rh suffix kind))

theorem fuel_bound (n : Nat) (lh rh : Bool) : fuel n lh rh ≤ 40 * (n + 1) + 41 := by
  cases lh <;> cases rh
  all_goals simp only [fuel,flagFuel,addFuel,SourceRowReductionOutput.finishFuel,SourceRowReductionOutput.fuel]
  all_goals omega

end PNP.Concrete.ResidualReduction.SourceRowReductionAffine
