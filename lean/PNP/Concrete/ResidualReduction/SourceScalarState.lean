import PNP.Concrete.ResidualReduction.SourceQuadraticProduct
import PNP.Concrete.ResidualReduction.SourceChartFamily
import PNP.Concrete.ResidualReduction.SourceScalarTail

/-! Exact selected-scalar accumulation and its protected register layout.
The accumulator denotes the actual existing quadratic, not supplied semantic
values. Product scratch and family metadata are separate protected frames. -/

namespace PNP.Concrete.ResidualReduction.SourceScalarState
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceClosure

def zero (n : Nat) : Quadratic n := qOfAffine (aConst n false)

theorem add_assoc {n : Nat} (p q r : Quadratic n) :
    qAdd (qAdd p q) r = qAdd p (qAdd q r) := by
  apply quadratic_eval_ext
  intro x
  simp only [qAdd_eval,Bool.xor_assoc]
theorem add_zero_left {n : Nat} (q : Quadratic n) : qAdd (zero n) q = q := by
  apply quadratic_eval_ext
  intro x
  simp only [zero,qAdd_eval,qOfAffine_eval,aConst_eval,Bool.false_xor]
theorem add_zero_right {n : Nat} (q : Quadratic n) : qAdd q (zero n) = q := by
  apply quadratic_eval_ext
  intro x
  simp only [zero,qAdd_eval,qOfAffine_eval,aConst_eval,Bool.xor_false]

def step {n : Nat} (q : Quadratic n) (r : Row n) : Quadratic n :=
  if r.selected then qAdd q (qProduct r.left r.right) else q

theorem step_scalar {n : Nat} (q : Quadratic n) (r : Row n) (F : Family n) :
    qAdd (step q r) (scalar F) = qAdd q (scalar (r :: F)) := by
  rcases r with ⟨selected,f,g⟩
  cases selected with
  | false => rfl
  | true => exact add_assoc q (qProduct f g) (scalar F)

structure Data where
  stream : BitString
  dimension : BitString
  width : BitString
  quadratic : BitString
  accumulator : BitString

def Data.store (s : Data) : Store 5 :=
  .cons s.stream <| .cons s.dimension <| .cons s.width <|
    .cons s.quadratic (.cons s.accumulator .nil)
def emptyData : Data := ⟨[],[],[],[],[]⟩
def emptySaved : SourceQuadraticProduct.Saved := ⟨[],[]⟩
def extra (p : SourceQuadraticProduct.Saved) (s : Data) : Store 7 :=
  Frame.join p.store s.store
def full (r : Registers) (p : SourceQuadraticProduct.Saved) (s : Data) : Store 16 :=
  Frame.join (SourceQuadraticProduct.full r p) s.store

theorem core_exec {b : Block 9} {r out : Registers} {ticks : Nat}
    (h : Exec b r.store ticks out.store) (p : SourceQuadraticProduct.Saved) (s : Data) :
    Exec (Frame.block 7 b) (full r p s) ticks (full out p s) := by
  change Exec (Frame.block 7 b) (Frame.join r.store (extra p s)) ticks
    (Frame.join out.store (extra p s))
  exact Frame.execution h (extra p s)

theorem product_exec {b : Block 11} {r out : Registers}
    {p after : SourceQuadraticProduct.Saved} {ticks : Nat}
    (h : Exec b (SourceQuadraticProduct.full r p) ticks (SourceQuadraticProduct.full out after))
    (s : Data) : Exec (Frame.block 5 b) (full r p s) ticks (full out after s) :=
  Frame.execution h s.store

def work (input : BitString) : Registers := ⟨input,[],[],[],[],[],[],[],[]⟩
def data {n : Nat} (input : BitString) (q : Quadratic n) : Data :=
  ⟨input,List.replicate n true,List.replicate (n + 1) true,
    List.replicate (quadraticBits n) true,SourceQuadraticEncoding.word q⟩
def state {n : Nat} (input : BitString) (q : Quadratic n) : Store 16 :=
  full (work input) emptySaved (data input q)
def initial (n : Nat) (input : BitString) : Store 16 :=
  full {work input with target := List.replicate n true} emptySaved emptyData

theorem output_get (r : Registers) (p : SourceQuadraticProduct.Saved) (s : Data) :
    (full r p s).get 8 = r.output := rfl
theorem input_get (r : Registers) (p : SourceQuadraticProduct.Saved) (s : Data) :
    (full r p s).get 0 = r.input := rfl

end PNP.Concrete.ResidualReduction.SourceScalarState
