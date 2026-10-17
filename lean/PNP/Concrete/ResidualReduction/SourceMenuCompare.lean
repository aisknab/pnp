import PNP.Concrete.ResidualReduction.SourceMenuOrderAlgebra

/-! Two literal binary comparisons with the source cursor and record width
protected. Their Boolean results select exact equality, insertion before the
current record, or continued traversal. No numeric ranks are constructed. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuCompare
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.CoefficientComparison
open PNP.Concrete.ResidualReduction.SourceMenuOrder

structure Saved where
  tail : BitString
  width : BitString
  firstFlag : BitString
deriving Repr
def Saved.store (s : Saved) : Store 3 :=
  .cons s.tail (.cons s.width (.cons s.firstFlag .nil))
def full (r : Registers) (s : Saved) : Store 12 := Frame.join r.store s.store
def comparisonFrame (r : Registers) (s : Saved) : Store 9 :=
  .cons r.excess (.cons r.sign (.cons r.mode (.cons r.active (.cons r.reserved
    (.cons r.output s.store)))))
def comparisonState (r : Registers) (xs ys : BitString) (flag : Bool) : Registers :=
  {r with input := xs, target := ys, remaining := [flag]}

theorem comparison_exec (r : Registers) (s : Saved) (xs ys : BitString) (flag : Bool) :
    Exec (Frame.block 9 CoefficientComparison.comparison)
      (full (comparisonState r xs ys flag) s) (CoefficientComparison.fuel xs ys)
      (full (comparisonState r [] [] (wordLower xs ys)) s) :=
  Frame.execution (CoefficientComparison.comparison_exec xs ys flag) (comparisonFrame r s)

def capture : Block 12 := .seq (.action (.copy 9 0)) (.action (.copy 10 1))
def captured (r : Registers) (s : Saved) : Saved := {s with tail := r.input, width := r.target}
theorem capture_exec (r : Registers) (s : Saved) :
    Exec capture (full r s) 2 (full r (captured r s)) := Exec.seq (.action _ _) (.action _ _)

def prepare : Block 9 := .seq (.action (.copy 0 4)) <|
  .seq (.action (.copy 1 5)) <| .seq (.action (.clear 2)) (.action (.push 2 false))
theorem prepare_exec (r : Registers) :
    Exec prepare r.store 4 (comparisonState r r.sign r.mode false).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def second : Block 12 := .seq (.action (.copy 11 2)) <|
  .seq (.action (.copy 0 5)) (.action (.copy 1 4))
def savedFlag (s : Saved) (flag : Bool) : Saved := {s with firstFlag := [flag]}
theorem second_exec (r : Registers) (s : Saved) (flag : Bool) :
    Exec second (full (comparisonState r [] [] flag) s) 3
      (full (comparisonState r r.mode r.sign flag) (savedFlag s flag)) :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def restore : Block 12 := .seq (.action (.copy 0 9)) (.action (.copy 1 10))
def restored (r : Registers) (s : Saved) : Registers := {r with input := s.tail, target := s.width}
theorem restore_exec (r : Registers) (s : Saved) :
    Exec restore (full r s) 2 (full (restored r s) s) := Exec.seq (.action _ _) (.action _ _)

def block : Block 12 := .seq capture <| .seq (Frame.block 3 prepare) <|
  .seq (Frame.block 9 CoefficientComparison.comparison) <| .seq second <|
  .seq (Frame.block 9 CoefficientComparison.comparison) restore
def cost (r : Registers) : Nat := 2 + (4 + (CoefficientComparison.fuel r.sign r.mode +
  (3 + (CoefficientComparison.fuel r.mode r.sign + 2))))
def resultCore (r : Registers) : Registers := {r with remaining := [wordLower r.mode r.sign]}
def resultSaved (r : Registers) : Saved := ⟨r.input, r.target, [wordLower r.sign r.mode]⟩

theorem block_exec (r : Registers) (s : Saved) :
    Exec block (full r s) (cost r) (full (resultCore r) (resultSaved r)) := by
  have first := capture_exec r s
  have prepared := Frame.execution (prepare_exec r) (captured r s).store
  have left := comparison_exec r (captured r s) r.sign r.mode false
  have swapped := second_exec r (captured r s) (wordLower r.sign r.mode)
  have right := comparison_exec r (savedFlag (captured r s) (wordLower r.sign r.mode))
    r.mode r.sign (wordLower r.sign r.mode)
  have last := restore_exec (comparisonState r [] [] (wordLower r.mode r.sign))
    (savedFlag (captured r s) (wordLower r.sign r.mode))
  exact Exec.seq first (Exec.seq prepared (Exec.seq left (Exec.seq swapped (Exec.seq right last))))

theorem cost_bound (r : Registers) :
    cost r ≤ 14 * (r.sign.length + r.mode.length) + 19 := by
  have left := CoefficientComparison.fuel_bound r.sign r.mode
  have right := CoefficientComparison.fuel_bound r.mode r.sign
  unfold cost
  omega

theorem result_first (r : Registers) : (full (resultCore r) (resultSaved r)).get 11 =
    [wordLower r.sign r.mode] := rfl
theorem result_second (r : Registers) : (full (resultCore r) (resultSaved r)).get 2 =
    [wordLower r.mode r.sign] := rfl
theorem result_cursor (r : Registers) : (full (resultCore r) (resultSaved r)).get 0 = r.input := rfl
theorem result_width (r : Registers) : (full (resultCore r) (resultSaved r)).get 1 = r.target := rfl

end PNP.Concrete.ResidualReduction.SourceMenuCompare
