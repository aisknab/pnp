import PNP.Concrete.ResidualReduction.SourceRowReductionOutput

/-! Assemble the plane branch from its internally generated first-match partner.
A missing partner remains an explicit failure. A successful lookup is consumed
as a word, combined with the actual right coefficient and remainder, and emitted
as one canonical row. The partner is never supplied to the public block. -/

namespace PNP.Concrete.ResidualReduction.SourceRowReductionAssemble
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceRowReductionState

def stashed {n : Nat} (A B : BitString) (u f g p : Affine n)
    (selected lh rh : Bool) (suffix : BitString) (kind : Bool) : Store 19 :=
  full {work n [] with sign := affineWord p} ⟨A,B,affineWord f⟩ (rowData u g selected lh rh suffix kind)
inductive Operand where
  | remainder | partner
def operandIndex : Operand → Fin 19
  | .remainder => 12
  | .partner => 4
def operandValue {n : Nat} (u p : Affine n) : Operand → Affine n
  | .remainder => u
  | .partner => p
def loadAdd (op : Operand) : Block 19 :=
  .seq (.action (.copy 0 13)) (.action (.copy 5 (operandIndex op)))
def saveAdd : Block 19 := .seq (.action (.copy 13 8)) (.action (.clear 8))
def add (op : Operand) : Block 19 :=
  .seq (loadAdd op) (.seq (core SourceRowCoefficientInstructions.add) saveAdd)
def addFuel (n : Nat) : Nat := 11 * (n + 1) + 7

theorem add_exec {n : Nat} (A B : BitString) (u f g p : Affine n)
    (selected lh rh : Bool) (suffix : BitString) (kind : Bool) (op : Operand) :
    Exec (add op) (stashed A B u f g p selected lh rh suffix kind) (addFuel n)
      (stashed A B u f (aAdd g (operandValue u p op)) p selected lh rh suffix kind) := by
  let r := {work n [] with sign := affineWord p}
  let s : SourcePlanePartnerBuilder.Saved := ⟨A,B,affineWord f⟩
  let d := rowData u g selected lh rh suffix kind
  let v := operandValue u p op
  have load : Exec (loadAdd op) (full r s d) 2
      (full (SourceRowCoefficientInstructions.binaryReady r g v) s d) := by
    cases op <;> exact Exec.seq (.action _ _) (.action _ _)
  have calculation := core_exec (SourceRowCoefficientInstructions.add_exec r g v) s d
  have save : Exec saveAdd (full (SourceRowCoefficientInstructions.added r g v) s d) 2
      (stashed A B u f (aAdd g v) p selected lh rh suffix kind) :=
    Exec.seq (.action _ _) (.action _ _)
  have cost : addFuel n = 2 + ((11 * (n + 1) + 3) + 2) := by unfold addFuel; omega
  simpa only [add,cost,r,s,d,v,stashed] using Exec.seq load (Exec.seq calculation save)

def storePartner : Block 19 := .seq (.action (.pop 8)) <|
  .seq (.action (.copy 4 8)) (.action (.clear 8))
theorem storePartner_exec {n : Nat} (A B : BitString) (u f g p : Affine n)
    (selected lh rh : Bool) (suffix : BitString) (kind : Bool) :
    Exec storePartner
      (SourceRowReductionOutput.buffered A B u f g selected lh rh suffix kind
        ((SourcePlanePartnerInstructions.codec n).encode (some p))) 3
      (stashed A B u f g p selected lh rh suffix kind) :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def success : Block 19 := .seq storePartner <| .seq (add .remainder) <|
  .seq (add .partner) <| .seq (.action (.clear 4)) SourceRowReductionOutput.finish
def successFuel (n : Nat) : Nat := 40 * (n + 1) + 43

theorem success_exec {n : Nat} (A B : BitString) (u f g p : Affine n)
    (selected lh rh : Bool) (suffix : BitString) (kind : Bool) :
    Exec success
      (SourceRowReductionOutput.buffered A B u f g selected lh rh suffix kind
        ((SourcePlanePartnerInstructions.codec n).encode (some p))) (successFuel n)
      (SourceRowReductionOutput.terminal A B u suffix kind
        ((codec n).encode (some ⟨selected,f,aAdd (aAdd g u) p⟩))) := by
  have store := storePartner_exec A B u f g p selected lh rh suffix kind
  have first := add_exec A B u f g p selected lh rh suffix kind .remainder
  have second := add_exec A B u f (aAdd g u) p selected lh rh suffix kind .partner
  have clear : Exec (.action (.clear (4 : Fin 19)))
      (stashed A B u f (aAdd (aAdd g u) p) p selected lh rh suffix kind) 1
      (prepared A B u f (aAdd (aAdd g u) p) selected lh rh suffix kind) := .action _ _
  have finish := SourceRowReductionOutput.finish_exec A B u f (aAdd (aAdd g u) p)
    selected lh rh suffix kind
  have cost : successFuel n = 3 + (addFuel n + (addFuel n + (1 + SourceRowReductionOutput.finishFuel n))) := by
    unfold successFuel addFuel SourceRowReductionOutput.finishFuel SourceRowReductionOutput.fuel
    omega
  simpa only [success,cost,operandValue] using
    Exec.seq store (Exec.seq first (Exec.seq second (Exec.seq clear finish)))

def assembled {n : Nat} (selected : Bool) (u f g : Affine n)
    (p : Option (Affine n)) : Option (Row n) :=
  p.map fun v => ⟨selected,f,aAdd (aAdd g u) v⟩
def complete : Block 19 := .branch 8 .skip cleanup success
def completeFuel (n : Nat) : Option (Affine n) → Nat
  | none => 13
  | some _ => 1 + successFuel n

theorem complete_exec {n : Nat} (A B : BitString) (u f g : Affine n)
    (selected lh rh : Bool) (suffix : BitString) (kind : Bool) (p : Option (Affine n)) :
    Exec complete
      (SourceRowReductionOutput.buffered A B u f g selected lh rh suffix kind
        ((SourcePlanePartnerInstructions.codec n).encode p)) (completeFuel n p)
      (SourceRowReductionOutput.terminal A B u suffix kind ((codec n).encode (assembled selected u f g p))) := by
  cases p with
  | none =>
    exact Exec.zero rfl (SourceRowReductionOutput.cleanup_buffered A B u f g selected lh rh suffix kind [false])
  | some p => exact Exec.one rfl (success_exec A B u f g p selected lh rh suffix kind)

def clearFlags : Block 19 := .seq (.action (.clear 6)) (.action (.clear 7))
theorem clearFlags_exec {n : Nat} (a b u f g : Affine n)
    (selected lh rh : Bool) (suffix : BitString) (kind : Bool) (p : Option (Affine n)) :
    Exec clearFlags
      (Frame.join (SourcePlanePartnerInstructions.encodedResult a b f p)
        (rowData u g selected lh rh suffix kind).store) 2
      (SourceRowReductionOutput.buffered (affineWord a) (affineWord b) u f g
        selected lh rh suffix kind ((SourcePlanePartnerInstructions.codec n).encode p)) :=
  Exec.seq (.action _ _) (.action _ _)

def block : Block 19 := .seq (partner SourcePlanePartnerInstructions.block) (.seq clearFlags complete)
def fuel {n : Nat} (a b f : Affine n) : Nat :=
  SourcePlanePartnerInstructions.fuel a b f + (2 + completeFuel n (planePartner a b f))

theorem block_exec {n : Nat} (a b u f g : Affine n)
    (selected lh rh : Bool) (suffix : BitString) (kind : Bool) :
    Exec block (prepared (affineWord a) (affineWord b) u f g selected lh rh suffix kind)
      (fuel a b f)
      (SourceRowReductionOutput.terminal (affineWord a) (affineWord b) u suffix kind
        ((codec n).encode (FactoredContraction.assemble selected a b u f g))) :=
  Exec.seq (partner_exec (SourcePlanePartnerInstructions.block_exec a b f)
    (rowData u g selected lh rh suffix kind))
    (Exec.seq (clearFlags_exec a b u f g selected lh rh suffix kind (planePartner a b f))
      (complete_exec (affineWord a) (affineWord b) u f g selected lh rh suffix kind (planePartner a b f)))

theorem completeFuel_bound {n : Nat} (p : Option (Affine n)) :
    completeFuel n p ≤ 40 * (n + 1) + 44 := by
  cases p <;> simp only [completeFuel,successFuel] <;> omega
theorem fuel_bound {n : Nat} (a b f : Affine n) : fuel a b f ≤ 267 * (n + 1) + 181 := by
  have lookup := SourcePlanePartnerInstructions.fuel_bound a b f
  have finish := completeFuel_bound (planePartner a b f)
  unfold fuel
  omega

end PNP.Concrete.ResidualReduction.SourceRowReductionAssemble
