import PNP.Concrete.ResidualReduction.SourceComputedTailEncoding
import PNP.Concrete.ResidualReduction.SourcePlaneRemainderInstructions

/-! Protected storage for the computed-tail constructor. Original pivot and
derived normals survive scalar arithmetic in a separate frame. No coefficient
object is synthesized by a semantic callback in this register layout. -/

namespace PNP.Concrete.ResidualReduction.SourceComputedTailState
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceScalarState (work data emptySaved Data)

structure Extra where
  pivot : BitString
  left : BitString
  right : BitString

def Extra.store (x : Extra) : Store 3 := .cons x.pivot (.cons x.left (.cons x.right .nil))
def extras {n : Nat} (k : Fin (n + 1)) (left right : BitString) : Extra :=
  ⟨List.replicate k.val true,left,right⟩
def full (r : Registers) (p : SourceQuadraticProduct.Saved) (s : Data) (x : Extra) : Store 19 :=
  Frame.join (SourceScalarState.full r p s) x.store
def core (b : Block 9) : Block 19 := Frame.block 3 (Frame.block 7 b)
def scalar (b : Block 16) : Block 19 := Frame.block 3 b
def product (b : Block 11) : Block 19 := Frame.block 3 (Frame.block 5 b)

theorem core_exec {b : Block 9} {r out : Registers} {ticks : Nat}
    (h : Exec b r.store ticks out.store) (p : SourceQuadraticProduct.Saved) (s : Data) (x : Extra) :
    Exec (core b) (full r p s x) ticks (full out p s x) :=
  Frame.execution (SourceScalarState.core_exec h p s) x.store
theorem scalar_exec {b : Block 16} {before after : Store 16} {ticks : Nat}
    (h : Exec b before ticks after) (x : Extra) :
    Exec (scalar b) (Frame.join before x.store) ticks (Frame.join after x.store) :=
  Frame.execution h x.store
theorem product_exec {b : Block 11} {r out : Registers}
    {p after : SourceQuadraticProduct.Saved} {ticks : Nat}
    (h : Exec b (SourceQuadraticProduct.full r p) ticks (SourceQuadraticProduct.full out after))
    (s : Data) (x : Extra) :
    Exec (product b) (full r p s x) ticks (full out after s x) :=
  Frame.execution (SourceScalarState.product_exec h s) x.store

def state {n : Nat} (input : BitString) (q : Quadratic n) (x : Extra) : Store 19 :=
  full (work input) emptySaved (data input q) x
def initial {n : Nat} (input : BitString) (k : Fin (n + 1)) : Store 19 :=
  Frame.join (SourceScalarState.initial n input) (extras k [] []).store

theorem output_get (r : Registers) (p : SourceQuadraticProduct.Saved) (s : Data) (x : Extra) :
    (full r p s x).get 8 = r.output := rfl
theorem pivot_get (r : Registers) (p : SourceQuadraticProduct.Saved) (s : Data) (x : Extra) :
    (full r p s x).get 16 = x.pivot := rfl
theorem left_get (r : Registers) (p : SourceQuadraticProduct.Saved) (s : Data) (x : Extra) :
    (full r p s x).get 17 = x.left := rfl
theorem right_get (r : Registers) (p : SourceQuadraticProduct.Saved) (s : Data) (x : Extra) :
    (full r p s x).get 18 = x.right := rfl

end PNP.Concrete.ResidualReduction.SourceComputedTailState
