import PNP.ThreeUse.Group

/-!
# Physical matrix realization

The coordinate product and inverse agree with ordinary multiplication of three-by-three Boolean matrices over the binary field.
-/

set_option autoImplicit false

namespace PNP.ThreeUse

abbrev Physical := Fin 3 → Fin 3 → Bool
/-- Diagonal 1 and the three independent entries at (0,1),(1,2),(0,2). -/
def matrix (x : G) (i j : Fin 3) : Bool :=
  if i = j then true else
  if i.val = 0 ∧ j.val = 1 then x.a else
  if i.val = 1 ∧ j.val = 2 then x.b else
  if i.val = 0 ∧ j.val = 2 then x.c else false

def matmul (x y : Physical) (i j : Fin 3) : Bool :=
  ((x i 0 && y 0 j) ^^ (x i 1 && y 1 j)) ^^ (x i 2 && y 2 j)

theorem matrix_mul (x y : G) : matrix (gmul x y) = matmul (matrix x) (matrix y) := by
  funext i j; cases x; cases y; decide +revert

theorem matrix_inv (x : G) : matmul (matrix x) (matrix (ginv x)) = matrix one ∧
    matmul (matrix (ginv x)) (matrix x) = matrix one := by
  rw [←matrix_mul, ←matrix_mul]; have e : gmul (ginv x) x = one := by cases x; decide +revert
  rw [(inv_cancel x x).mpr rfl, e]; exact ⟨rfl, rfl⟩

theorem matrix_inj (x y : G) : matrix x = matrix y ↔ x = y := by
  constructor
  · intro h
    have a := congrFun (congrFun h 0) 1; have b := congrFun (congrFun h 1) 2
    have c := congrFun (congrFun h 0) 2
    change x.a = y.a at a; change x.b = y.b at b; change x.c = y.c at c
    cases x; cases y; cases a; cases b; cases c; rfl
  · intro e; rw [e]
end PNP.ThreeUse
