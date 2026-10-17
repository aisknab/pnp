import PNP.Concrete.ResidualReduction.SourceQuadraticEquality
import PNP.Concrete.ResidualReduction.SourceTailPolynomial

/-! Protected state and the exact two gates of checked contraction.
The saved words hold an actually computed head result and the input tail,
not a certificate that either comparison succeeds. -/

namespace PNP.Concrete.ResidualReduction.SourceCoefficientGateState
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceScalarState (work data zero)

def checks {n : Nat} (h : Affine n) (q : Quadratic n) (t : TailForm n) : Bool :=
  aEq h (aConst n true) && qEq q t.polynomial

theorem checks_true_iff {n : Nat} (h : Affine n) (q : Quadratic n) (t : TailForm n) :
    checks h q t = true ↔ h = aConst n true ∧ q = t.polynomial := by
  rw [checks,Bool.and_eq_true,aEq_true_iff,qEq_true_iff]

theorem contract_eq {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (v : Point n) (t : TailForm n) :
    contract F k v t = if checks (scalar (chartRows F k v)).1
      (scalar (chartRows F k v)).2 t then t.reduce (chartRows F k v) else none := by
  cases head : aEq (scalar (chartRows F k v)).1 (aConst n true) <;>
    cases tail : qEq (scalar (chartRows F k v)).2 t.polynomial <;>
    simp only [contract,checks,head,tail,Bool.false_and,Bool.true_and,Bool.false_eq_true,↓reduceIte]

structure Saved where
  head : BitString
  expected : BitString
def Saved.store (s : Saved) : Store 2 := .cons s.head (.cons s.expected .nil)
def noSaved : Saved := ⟨[],[]⟩
def full (r : Registers) (p : SourceQuadraticProduct.Saved)
    (d : SourceScalarState.Data) (s : Saved) : Store 18 :=
  Frame.join (SourceScalarState.full r p d) s.store
def scalar (b : Block 16) : Block 18 := Frame.block 2 b
def core (b : Block 9) : Block 18 := scalar (Frame.block 7 b)

theorem scalar_exec {b : Block 16} {before after : Store 16} {ticks : Nat}
    (h : Exec b before ticks after) (s : Saved) :
    Exec (scalar b) (Frame.join before s.store) ticks (Frame.join after s.store) :=
  Frame.execution h s.store
theorem core_exec {b : Block 9} {r out : Registers} {ticks : Nat}
    (h : Exec b r.store ticks out.store) (p : SourceQuadraticProduct.Saved)
    (d : SourceScalarState.Data) (s : Saved) :
    Exec (core b) (full r p d s) ticks (full out p d s) :=
  scalar_exec (SourceScalarState.core_exec h p d) s

def state {n : Nat} (input : BitString) (q : Quadratic n) (s : Saved) : Store 18 :=
  full (work input) SourceScalarState.emptySaved (data input q) s
def prepared (n : Nat) (input : BitString) : Store 18 := state input (zero n) noSaved
def finished {n : Nat} (h : Affine n) (q : Quadratic n) (t : TailForm n)
    (suffix : BitString) : Store 18 :=
  full {work suffix with output := [checks h q t]} SourceScalarState.emptySaved
    (data suffix t.polynomial) ⟨[aEq h (aConst n true)],SourceQuadraticEncoding.word q⟩

theorem output_get {n : Nat} (h : Affine n) (q : Quadratic n) (t : TailForm n) (suffix : BitString) :
    (finished h q t suffix).get 8 = [checks h q t] := rfl
theorem suffix_get {n : Nat} (h : Affine n) (q : Quadratic n) (t : TailForm n) (suffix : BitString) :
    (finished h q t suffix).get 0 = suffix := rfl

end PNP.Concrete.ResidualReduction.SourceCoefficientGateState
