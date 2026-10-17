import PNP.Concrete.ResidualReduction.SourceRowReductionAssemble

/-! The complete four-way plane row transformation. Both leading coefficient
bits are read from the loaded row. Swapping and the both-active sum-plus-one
query are constructed by instructions before the ordered partner lookup. -/

namespace PNP.Concrete.ResidualReduction.SourceRowReductionPlane
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceRowReductionState

def swap : Block 19 := .seq (.action (.copy 0 11)) <|
  .seq (.action (.copy 11 13)) <| .seq (.action (.copy 13 0)) (.action (.clear 0))
theorem swap_exec {n : Nat} (A B : BitString) (u f g : Affine n)
    (selected lh rh : Bool) (suffix : BitString) (kind : Bool) :
    Exec swap (prepared A B u f g selected lh rh suffix kind) 4
      (prepared A B u g f selected lh rh suffix kind) :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def loadBoth : Block 19 := .seq (.action (.copy 4 11)) <|
  .seq (.action (.copy 0 11)) (.action (.copy 5 13))
def saveBoth : Block 19 := .seq (.action (.copy 13 4)) <|
  .seq (.action (.clear 4)) <| .seq (.action (.copy 0 8)) (.action (.clear 8))
def saveQuery : Block 19 := .seq (.action (.copy 11 8)) (.action (.clear 8))
def both : Block 19 := .seq loadBoth <| .seq (core SourceRowCoefficientInstructions.add) <|
  .seq saveBoth <| .seq (core SourceRowCoefficientInstructions.toggle) saveQuery
def bothFuel (n : Nat) : Nat := 20 * (n + 1) + 14

theorem both_exec {n : Nat} (A B : BitString) (u f g : Affine n)
    (selected lh rh : Bool) (suffix : BitString) (kind : Bool) :
    Exec both (prepared A B u f g selected lh rh suffix kind) (bothFuel n)
      (prepared A B u (aAdd (aAdd f g) (aConst n true)) f selected lh rh suffix kind) := by
  let base := work n []
  let held := {base with sign := affineWord f}
  let s : SourcePlanePartnerBuilder.Saved := ⟨A,B,affineWord f⟩
  let d := rowData u g selected lh rh suffix kind
  let next := rowData u f selected lh rh suffix kind
  have load : Exec loadBoth (full base s d) 3
      (full (SourceRowCoefficientInstructions.binaryReady held f g) s d) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have add := core_exec (SourceRowCoefficientInstructions.add_exec held f g) s d
  have save : Exec saveBoth (full (SourceRowCoefficientInstructions.added held f g) s d) 4
      (full (SourceRowCoefficientInstructions.unaryReady base (aAdd f g)) s next) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have toggle := core_exec (SourceRowCoefficientInstructions.toggle_exec base (aAdd f g)) s next
  have query : Exec saveQuery (full (SourceRowCoefficientInstructions.toggled base (aAdd f g)) s next) 2
      (prepared A B u (aAdd (aAdd f g) (aConst n true)) f selected lh rh suffix kind) :=
    Exec.seq (.action _ _) (.action _ _)
  have cost : bothFuel n = 3 + ((11 * (n + 1) + 3) + (4 + ((9 * (n + 1) + 2) + 2))) := by
    unfold bothFuel
    omega
  simpa only [both,cost,base,s,d,prepared] using
    Exec.seq load (Exec.seq add (Exec.seq save (Exec.seq toggle query)))

def leftZero : Block 19 := .branch 16 .skip
  SourceRowReductionOutput.finish SourceRowReductionAssemble.block
def leftOne : Block 19 := .branch 16 .skip
  (.seq swap SourceRowReductionAssemble.block) (.seq both SourceRowReductionAssemble.block)
def block : Block 19 := .branch 15 .skip leftZero leftOne
def fuel {n : Nat} (a b f g : Affine n) : Bool → Bool → Nat
  | false,false => 1 + (1 + SourceRowReductionOutput.finishFuel n)
  | false,true => 1 + (1 + SourceRowReductionAssemble.fuel a b f)
  | true,false => 1 + (1 + (4 + SourceRowReductionAssemble.fuel a b g))
  | true,true => 1 + (1 + (bothFuel n +
      SourceRowReductionAssemble.fuel a b (aAdd (aAdd f g) (aConst n true))))

theorem block_exec {n : Nat} (a b u f g : Affine n)
    (selected lh rh : Bool) (suffix : BitString) :
    Exec block (prepared (affineWord a) (affineWord b) u f g selected lh rh suffix true)
      (fuel a b f g lh rh)
      (SourceRowReductionOutput.terminal (affineWord a) (affineWord b) u suffix true
        ((codec n).encode (planeRow a b u ⟨selected,(lh,f),(rh,g)⟩))) := by
  cases lh <;> cases rh
  · exact Exec.zero rfl (Exec.zero rfl
      (SourceRowReductionOutput.finish_exec (affineWord a) (affineWord b) u f g
        selected false false suffix true))
  · exact Exec.zero rfl (Exec.one rfl
      (SourceRowReductionAssemble.block_exec a b u f g selected false true suffix true))
  · exact Exec.one rfl (Exec.zero rfl
      (Exec.seq (swap_exec (affineWord a) (affineWord b) u f g selected true false suffix true)
        (SourceRowReductionAssemble.block_exec a b u g f selected true false suffix true)))
  · exact Exec.one rfl (Exec.one rfl
      (Exec.seq (both_exec (affineWord a) (affineWord b) u f g selected true true suffix true)
        (SourceRowReductionAssemble.block_exec a b u (aAdd (aAdd f g) (aConst n true)) f
          selected true true suffix true)))

theorem fuel_bound {n : Nat} (a b f g : Affine n) (lh rh : Bool) :
    fuel a b f g lh rh ≤ 287 * (n + 1) + 197 := by
  have first := SourceRowReductionAssemble.fuel_bound a b f
  have second := SourceRowReductionAssemble.fuel_bound a b g
  have combined := SourceRowReductionAssemble.fuel_bound a b (aAdd (aAdd f g) (aConst n true))
  cases lh <;> cases rh
  all_goals simp only [fuel,bothFuel,SourceRowReductionOutput.finishFuel,SourceRowReductionOutput.fuel]
  all_goals omega

end PNP.Concrete.ResidualReduction.SourceRowReductionPlane
