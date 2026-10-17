import PNP.Concrete.ResidualReduction.SourceMenuBytes

/-! One literal, constant-size finite program scans both coefficient words.
It constructs their reversals and XOR and records all three nonzero tests.
The words have arbitrary equal length; no normal, menu or test result is given
to the program. Register 8 is preserved for the enclosing candidate stream. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuScan
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.SourceMenuBytes

structure Registers where
  left : BitString
  right : BitString
  leftAccum : BitString
  rightAccum : BitString
  xorAccum : BitString
  leftFlag : Bool
  rightFlag : Bool
  xorFlag : Bool
  output : BitString
deriving Repr

def Registers.store (r : Registers) : Store 9 :=
  .cons r.left (.cons r.right (.cons r.leftAccum (.cons r.rightAccum
    (.cons r.xorAccum (.cons [r.leftFlag] (.cons [r.rightFlag]
      (.cons [r.xorFlag] (.cons r.output .nil))))))))

def markFuel (bit : Bool) : Nat := if bit then 2 else 1
def mark (index : Fin 9) (bit : Bool) : Block 9 :=
  if bit then .seq (.action (.clear index)) (.action (.push index true)) else .skip

theorem markLeft_exec (r : Registers) (bit : Bool) :
    Exec (mark 5 bit) r.store (markFuel bit) ({r with leftFlag := r.leftFlag || bit}).store := by
  cases bit <;> simp only [mark, markFuel, Bool.or_false, Bool.or_true, ↓reduceIte]
  · exact Exec.skip _
  · exact Exec.seq (.action _ _) (.action _ _)

theorem markRight_exec (r : Registers) (bit : Bool) :
    Exec (mark 6 bit) r.store (markFuel bit) ({r with rightFlag := r.rightFlag || bit}).store := by
  cases bit <;> simp only [mark, markFuel, Bool.or_false, Bool.or_true, ↓reduceIte]
  · exact Exec.skip _
  · exact Exec.seq (.action _ _) (.action _ _)

theorem markXor_exec (r : Registers) (bit : Bool) :
    Exec (mark 7 bit) r.store (markFuel bit) ({r with xorFlag := r.xorFlag || bit}).store := by
  cases bit <;> simp only [mark, markFuel, Bool.or_false, Bool.or_true, ↓reduceIte]
  · exact Exec.skip _
  · exact Exec.seq (.action _ _) (.action _ _)

def appendPair (a b : Bool) : Block 9 :=
  .seq (.action (.push 2 a)) (.seq (.action (.push 3 b)) (.action (.push 4 (Bool.xor a b))))
def appended (r : Registers) (a b : Bool) : Registers :=
  {r with
    leftAccum := a :: r.leftAccum, rightAccum := b :: r.rightAccum,
    xorAccum := Bool.xor a b :: r.xorAccum}

theorem appendPair_exec (r : Registers) (a b : Bool) :
    Exec (appendPair a b) r.store 3 (appended r a b).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def marked (r : Registers) (a b : Bool) : Registers :=
  {r with
    leftFlag := r.leftFlag || a, rightFlag := r.rightFlag || b,
    xorFlag := r.xorFlag || Bool.xor a b}
def markPair (a b : Bool) : Block 9 :=
  .seq (mark 5 a) (.seq (mark 6 b) (mark 7 (Bool.xor a b)))

theorem markPair_exec (r : Registers) (a b : Bool) :
    Exec (markPair a b) r.store (markFuel a + (markFuel b + markFuel (Bool.xor a b)))
      (marked r a b).store :=
  Exec.seq (markLeft_exec r a)
    (Exec.seq (markRight_exec {r with leftFlag := r.leftFlag || a} b)
      (markXor_exec {r with leftFlag := r.leftFlag || a, rightFlag := r.rightFlag || b}
        (Bool.xor a b)))

def popPair : Block 9 := .seq (.action (.pop 0)) (.action (.pop 1))
def pair (a b : Bool) : Block 9 := .seq (appendPair a b) (.seq (markPair a b) popPair)
def pairFuel (a b : Bool) : Nat := 3 + ((markFuel a + (markFuel b + markFuel (Bool.xor a b))) + 2)
def pairResult (r : Registers) (a b : Bool) : Registers := marked (appended r a b) a b

theorem pair_exec (r : Registers) (a b : Bool) :
    Exec (pair a b) ({r with left := a :: r.left, right := b :: r.right}).store
      (pairFuel a b) (pairResult r a b).store := by
  let start := {r with left := a :: r.left, right := b :: r.right}
  have first := appendPair_exec start a b
  have second := markPair_exec (appended start a b) a b
  have last : Exec popPair (marked (appended start a b) a b).store 2
      (pairResult r a b).store := Exec.seq (.action _ _) (.action _ _)
  exact Exec.seq first (Exec.seq second last)

def body : Block 9 := .branch 0 .skip
  (.branch 1 .skip (pair false false) (pair false true))
  (.branch 1 .skip (pair true false) (pair true true))
def loop : Block 9 := .loop 0 body

theorem body_exec (r : Registers) (a b : Bool) :
    Exec body ({r with left := a :: r.left, right := b :: r.right}).store
      (2 + pairFuel a b) (pairResult r a b).store := by
  cases a <;> cases b
  · exact Exec.zero rfl (Exec.zero rfl (pair_exec r false false))
  · exact Exec.zero rfl (Exec.one rfl (pair_exec r false true))
  · exact Exec.one rfl (Exec.zero rfl (pair_exec r true false))
  · exact Exec.one rfl (Exec.one rfl (pair_exec r true true))

def fuel : BitString → BitString → Nat
  | a :: xs, b :: ys => 1 + ((2 + pairFuel a b) + fuel xs ys)
  | _, _ => 1

def result (r : Registers) (xs ys : BitString) : Registers :=
  {r with
    left := [], right := [],
    leftAccum := xs.reverse ++ r.leftAccum, rightAccum := ys.reverse ++ r.rightAccum,
    xorAccum := (List.zipWith Bool.xor xs ys).reverse ++ r.xorAccum,
    leftFlag := r.leftFlag || nonzero xs, rightFlag := r.rightFlag || nonzero ys,
    xorFlag := r.xorFlag || nonzero (List.zipWith Bool.xor xs ys)}

theorem result_cons (r : Registers) (a b : Bool) (xs ys : BitString) :
    result (pairResult {r with left := xs, right := ys} a b) xs ys =
      result r (a :: xs) (b :: ys) := by
  simp only [result, pairResult, marked, appended, nonzero_cons, List.zipWith_cons_cons,
    List.reverse_cons, List.append_assoc, List.singleton_append, Bool.or_assoc]

theorem loop_exec (r : Registers) (xs ys : BitString) (sameLength : xs.length = ys.length) :
    Exec loop ({r with left := xs, right := ys}).store (fuel xs ys)
      (result r xs ys).store := by
  induction xs generalizing r ys with
  | nil =>
    have empty : ys = [] := by
      cases ys with
      | nil => rfl
      | cons b ys => exact False.elim (Nat.noConfusion sameLength)
    subst ys
    simpa only [loop, fuel, result, nonzero_nil, Bool.or_false, List.reverse_nil, List.nil_append,
      List.zipWith_nil_left] using
      (Exec.loopStop (body := body) (source := (0 : Fin 9))
        (store := ({r with left := [], right := []}).store) rfl)
  | cons a xs ih =>
    cases ys with
    | nil => exact False.elim (Nat.noConfusion sameLength)
    | cons b ys =>
      have lengths : xs.length = ys.length := by
        simpa only [List.length_cons, Nat.succ.injEq] using sameLength
      have first := body_exec {r with left := xs, right := ys} a b
      have rest := ih (pairResult {r with left := xs, right := ys} a b) ys lengths
      have done := Exec.loopStep (source := (0 : Fin 9)) rfl first rest
      simpa only [loop, fuel, result_cons] using done

theorem pairFuel_bound (a b : Bool) : pairFuel a b ≤ 10 := by
  cases a <;> cases b <;> decide

theorem fuel_bound (xs ys : BitString) : fuel xs ys ≤ 13 * xs.length + 1 := by
  induction xs generalizing ys with
  | nil => exact Nat.le_refl 1
  | cons a xs ih =>
    cases ys with
    | nil => change 1 ≤ 13 * (xs.length + 1) + 1; omega
    | cons b ys =>
      have bodyBound := pairFuel_bound a b
      have rest := ih ys
      simp only [fuel, List.length_cons]
      omega

def start (xs ys output : BitString) : Registers :=
  ⟨xs, ys, [], [], [], false, false, false, output⟩

theorem result_output (r : Registers) (xs ys : BitString) :
    (result r xs ys).store.get 8 = r.output := rfl

end PNP.Concrete.ResidualReduction.SourceMenuScan
