import Std

namespace PNP.SignedTernary.Field

inductive F3 where
  | z | o | t
  deriving DecidableEq, Repr

def add : F3 → F3 → F3
  | .z, b => b
  | .o, .z => .o
  | .o, .o => .t
  | .o, .t => .z
  | .t, .z => .t
  | .t, .o => .z
  | .t, .t => .o

def mul : F3 → F3 → F3
  | .z, _ => .z
  | .o, b => b
  | .t, .z => .z
  | .t, .o => .t
  | .t, .t => .o

def neg : F3 → F3
  | .z => .z
  | .o => .t
  | .t => .o

theorem add_zero (a : F3) : add a .z = a := by cases a <;> rfl

theorem zero_add (a : F3) : add .z a = a := rfl

theorem add_comm (a b : F3) : add a b = add b a := by cases a <;> cases b <;> rfl

theorem add_assoc (a b c : F3) : add (add a b) c = add a (add b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem add_shuffle (a b c d : F3) :
    add (add a b) (add c d) = add (add a c) (add b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem mul_zero (a : F3) : mul a .z = .z := by cases a <;> rfl

theorem zero_mul (a : F3) : mul .z a = .z := rfl

theorem mul_one (a : F3) : mul a .o = a := by cases a <;> rfl

theorem one_mul (a : F3) : mul .o a = a := rfl

theorem mul_comm (a b : F3) : mul a b = mul b a := by cases a <;> cases b <;> rfl

theorem mul_assoc (a b c : F3) : mul (mul a b) c = mul a (mul b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem mul_add (a b c : F3) : mul a (add b c) = add (mul a b) (mul a c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem add_mul (a b c : F3) : mul (add a b) c = add (mul a c) (mul b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem neg_add (a b : F3) : neg (add a b) = add (neg a) (neg b) := by
  cases a <;> cases b <;> rfl

end PNP.SignedTernary.Field

namespace PNP.SignedTernary.Field

@[reducible] def Point : Nat → Type
  | 0 => Unit
  | n + 1 => F3 × Point n

end PNP.SignedTernary.Field
