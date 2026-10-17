import PNP.Concrete.ResidualReduction.SourcePlanePartnerSpecification

/-! Construct each of the complete partner lookup's coefficient candidates
from the original normal pair. The zero word is allocated by instructions,
and sums and constant toggles use counted scans. Original operands remain
protected while the current candidate is compared in full, including constants. -/

namespace PNP.Concrete.ResidualReduction.SourcePlanePartnerBuilder
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourcePlanePartnerSpecification

structure Saved where
  left : BitString
  right : BitString
  query : BitString

def Saved.store (s : Saved) : Store 3 := .cons s.left (.cons s.right (.cons s.query .nil))
def full (r : Registers) (s : Saved) : Store 12 := Frame.join r.store s.store
def data {n : Nat} (a b f : Affine n) : Saved := ⟨affineWord a,affineWord b,affineWord f⟩
def work (n : Nat) (flag : Bool) (out : BitString) : Registers :=
  ⟨[],List.replicate (n + 1) true,[],[],[],[],[flag],affineWord (aConst n false),out⟩
def state {n : Nat} (a b f : Affine n) (flag : Bool) (out : BitString) : Store 12 :=
  full (work n flag out) (data a b f)
def core (b : Block 9) : Block 12 := Frame.block 3 b

theorem core_exec {b : Block 9} {before after : Registers} {ticks : Nat}
    (h : Exec b before.store ticks after.store) (s : Saved) :
    Exec (core b) (full before s) ticks (full after s) := Frame.execution h s.store

def initialCore (n : Nat) : Registers := ⟨[],List.replicate (n + 1) true,[],[],[],[],[],[],[]⟩
def initial {n : Nat} (a b f : Affine n) : Store 12 := full (initialCore n) (data a b f)
def recordZero : Block 12 := .seq (.action (.copy 7 8)) <|
  .seq (.action (.clear 8)) <| .seq (.action (.clear 6)) (.action (.push 6 false))
def setup : Block 12 := .seq (core SourceRowCoefficientInstructions.zero) recordZero

theorem initialize_exec {n : Nat} (a b f : Affine n) :
    Exec setup (initial a b f) (3 * (n + 1) + 6) (state a b f false []) := by
  have alloc : Exec SourceRowCoefficientInstructions.zero (initialCore n).store (3 * (n + 1) + 2)
      ({initialCore n with output := affineWord (aConst n false)}).store :=
    SourceRowCoefficientInstructions.zero_exec (initialCore n) n
  have save : Exec recordZero
      (full {initialCore n with output := affineWord (aConst n false)} (data a b f)) 4
      (state a b f false []) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have cost : 3 * (n + 1) + 6 = (3 * (n + 1) + 2) + 4 := by omega
  simpa only [setup,initial,cost] using Exec.seq (core_exec alloc (data a b f)) save

def prepareSum : Block 12 := .seq (.action (.copy 0 9)) (.action (.copy 5 10))
def sum : Block 12 := .seq prepareSum (core SourceRowCoefficientInstructions.add)

theorem sum_exec {n : Nat} (a b f : Affine n) (flag : Bool) :
    Exec sum (state a b f flag []) (11 * (n + 1) + 5)
      (state a b f flag (affineWord (aAdd a b))) := by
  have load : Exec prepareSum (state a b f flag []) 2
      (full (SourceRowCoefficientInstructions.binaryReady (work n flag []) a b) (data a b f)) :=
    Exec.seq (.action _ _) (.action _ _)
  have run := core_exec (SourceRowCoefficientInstructions.add_exec (work n flag []) a b) (data a b f)
  have cost : 11 * (n + 1) + 5 = 2 + (11 * (n + 1) + 3) := by omega
  simpa only [sum,cost,SourceRowCoefficientInstructions.added,state,work] using Exec.seq load run

def prepareFlip : Block 12 := .seq (.action (.copy 0 8)) (.action (.clear 8))
def flip : Block 12 := .seq prepareFlip (core SourceRowCoefficientInstructions.toggle)

theorem flip_exec {n : Nat} (a b f : Affine n) (flag : Bool) (z : Affine n) :
    Exec flip (state a b f flag (affineWord z)) (9 * (n + 1) + 4)
      (state a b f flag (affineWord (aAdd z (aConst n true)))) := by
  have load : Exec prepareFlip (state a b f flag (affineWord z)) 2
      (full (SourceRowCoefficientInstructions.unaryReady (work n flag []) z) (data a b f)) :=
    Exec.seq (.action _ _) (.action _ _)
  have run := core_exec (SourceRowCoefficientInstructions.toggle_exec (work n flag []) z) (data a b f)
  have cost : 9 * (n + 1) + 4 = 2 + (9 * (n + 1) + 2) := by omega
  simpa only [flip,cost,SourceRowCoefficientInstructions.toggled,state,work] using Exec.seq load run

def generate : Candidate → Block 12
  | .zero => .action (.copy 8 7)
  | .left => .action (.copy 8 9)
  | .right => .action (.copy 8 10)
  | .leftOne => .seq (.action (.copy 8 9)) flip
  | .rightOne => .seq (.action (.copy 8 10)) flip
  | .sum => sum
  | .sumOne => .seq sum flip
def generateFuel (n : Nat) : Candidate → Nat
  | .zero | .left | .right => 1
  | .leftOne | .rightOne => 1 + (9 * (n + 1) + 4)
  | .sum => 11 * (n + 1) + 5
  | .sumOne => (11 * (n + 1) + 5) + (9 * (n + 1) + 4)

theorem generate_exec {n : Nat} (a b f : Affine n) (flag : Bool) (c : Candidate) :
    Exec (generate c) (state a b f flag []) (generateFuel n c)
      (state a b f flag (affineWord (value a b c))) := by
  cases c with
  | zero => exact .action _ _
  | left => exact .action _ _
  | right => exact .action _ _
  | leftOne => exact Exec.seq (.action _ _) (flip_exec a b f flag a)
  | rightOne => exact Exec.seq (.action _ _) (flip_exec a b f flag b)
  | sum => exact sum_exec a b f flag
  | sumOne => exact Exec.seq (sum_exec a b f flag) (flip_exec a b f flag (aAdd a b))

theorem generateFuel_bound (n : Nat) (c : Candidate) : generateFuel n c ≤ 20 * (n + 1) + 9 := by
  cases c <;> simp only [generateFuel] <;> omega

def prepareCompare : Block 12 := .seq (.action (.copy 0 11)) <|
  .seq (.action (.copy 5 8)) (.action (.clear 8))
def compare : Block 12 := .seq prepareCompare (core SourceRowCoefficientInstructions.equal)
def compareFuel (n : Nat) : Nat := 12 * (n + 1) + 8

theorem compare_exec {n : Nat} (a b f : Affine n) (flag : Bool) (z : Affine n) :
    Exec compare (state a b f flag (affineWord z)) (compareFuel n)
      (state a b f (aEq f z) []) := by
  have load : Exec prepareCompare (state a b f flag (affineWord z)) 3
      (full (SourceRowCoefficientInstructions.binaryReady (work n flag []) f z) (data a b f)) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have run := core_exec (SourceRowCoefficientInstructions.equal_exec (work n flag []) f z) (data a b f)
  have cost : compareFuel n = 3 + (12 * (n + 1) + 5) := by
    unfold compareFuel
    omega
  simpa only [compare,cost,SourceRowCoefficientInstructions.compared,state,work] using Exec.seq load run

def choose : Partner → Block 12
  | .zero => .action (.copy 8 7)
  | .left => .action (.copy 8 9)
  | .right => .action (.copy 8 10)

theorem choose_exec {n : Nat} (a b f : Affine n) (flag : Bool) (p : Partner) :
    Exec (choose p) (state a b f flag []) 1 (state a b f flag (affineWord (output a b p))) := by
  cases p <;> exact .action _ _

end PNP.Concrete.ResidualReduction.SourcePlanePartnerBuilder
