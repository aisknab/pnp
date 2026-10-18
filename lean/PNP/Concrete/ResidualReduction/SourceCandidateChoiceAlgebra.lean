import PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude

/-! Exact reduction of the existing nine-candidate search to eight corner bits.
The order, first successful support pair, and rejected-candidate count are
preserved for arbitrary matrix dimensions and repeated seed indices. -/

namespace PNP.Concrete.ResidualReduction.SourceCandidateChoice
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.ConstrainedBilinear

inductive Axis where
  | first | second | both
  deriving DecidableEq, Repr
abbrev Choice := Axis × Axis
structure Corners where
  firstFirst : Bool
  firstSecond : Bool
  secondFirst : Bool
  secondSecond : Bool
  deriving DecidableEq, Repr

def axisValue : Axis → Bool → Bool → Bool
  | .first, a, _ => a
  | .second, _, b => b
  | .both, a, b => Bool.xor a b
def value (r : Corners) (c : Choice) : Bool :=
  axisValue c.1 (axisValue c.2 r.firstFirst r.firstSecond)
    (axisValue c.2 r.secondFirst r.secondSecond)
def accepts (A C : Corners) (choice : Choice) : Bool :=
  BilinearSelection.good (value A choice) (value C choice)
def choices : List Choice :=
  [(.first, .first), (.first, .second), (.first, .both),
   (.second, .first), (.second, .second), (.second, .both),
   (.both, .first), (.both, .second), (.both, .both)]
def choose (A C : Corners) : Option Choice := (BilinearSelection.scan (accepts A C) choices).1
def candidateChecks (A C : Corners) : Nat := (BilinearSelection.scan (accepts A C) choices).2

def support {T : Type} (first second : T) : Axis → List T
  | .first => [first]
  | .second => [second]
  | .both => [first, second]
def decode {I J : Type} (i k : I) (j l : J) (choice : Choice) : List I × List J :=
  (support i k choice.1, support j l choice.2)
def corners {I J : Type} (M : I → J → Bool) (i k : I) (j l : J) : Corners :=
  ⟨M i j, M i l, M k j, M k l⟩

theorem value_exact {I J : Type} (M : I → J → Bool) (i k : I) (j l : J) (choice : Choice) :
    value (corners M i k j l) choice =
      BilinearSelection.eval M (decode i k j l choice).1 (decode i k j l choice).2 := by
  rcases choice with ⟨row, column⟩
  cases row <;> cases column <;>
    simp only [value, axisValue, corners, decode, support,
      BilinearSelection.eval, BilinearSelection.rowEval, Bool.xor_false]

theorem accepts_exact {I J : Type} (A C : I → J → Bool) (i k : I) (j l : J) (choice : Choice) :
    accepts (corners A i k j l) (corners C i k j l) choice =
      BilinearSelection.accepts A C (decode i k j l choice) := by
  rw [accepts, value_exact, value_exact]
  rfl

theorem candidates_decode {I J : Type} (i k : I) (j l : J) :
    choices.map (decode i k j l) = BilinearSelection.candidates i k j l := rfl

theorem scan_map {I J : Type} (p : J → Bool) (f : I → J) (xs : List I) :
    BilinearSelection.scan p (xs.map f) =
      ((BilinearSelection.scan (fun x => p (f x)) xs).1.map f,
        (BilinearSelection.scan (fun x => p (f x)) xs).2) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : p (f x) <;>
      simp only [List.map_cons, BilinearSelection.scan, h, Bool.false_eq_true, if_false, if_true, ih,
        Option.map_some]

theorem candidate_scan_exact {I J : Type} (A C : I → J → Bool) (i k : I) (j l : J) :
    BilinearSelection.scan (BilinearSelection.accepts A C) (BilinearSelection.candidates i k j l) =
      ((choose (corners A i k j l) (corners C i k j l)).map (decode i k j l),
        candidateChecks (corners A i k j l) (corners C i k j l)) := by
  rw [← candidates_decode, scan_map]
  have predicate : (fun choice => BilinearSelection.accepts A C (decode i k j l choice)) =
      accepts (corners A i k j l) (corners C i k j l) := by
    funext choice
    exact (accepts_exact A C i k j l choice).symm
  rw [predicate]
  rfl

theorem choose_exact {I J : Type} (A C : I → J → Bool) (i k : I) (j l : J) :
    (BilinearSelection.scan (BilinearSelection.accepts A C) (BilinearSelection.candidates i k j l)).1 =
      (choose (corners A i k j l) (corners C i k j l)).map (decode i k j l) :=
  congrArg Prod.fst (candidate_scan_exact A C i k j l)
theorem checks_bound (A C : Corners) : candidateChecks A C ≤ 9 :=
  BilinearSelection.scan_steps_le (accepts A C) choices

def axisBits : Axis → BitString
  | .first => [true, false]
  | .second => [false, true]
  | .both => [true, true]
def outputBits : Option Choice → BitString
  | none => [false]
  | some c => true :: (axisBits c.1 ++ axisBits c.2)
theorem axisBits_length (a : Axis) : (axisBits a).length = 2 := by cases a <;> rfl
theorem output_length (choice : Option Choice) :
    (outputBits choice).length = if choice.isSome then 5 else 1 := by
  cases choice with
  | none => rfl
  | some c => simp only [outputBits, List.length_cons, List.length_append, axisBits_length, Option.isSome_some, if_true]
theorem output_length_bound (choice : Option Choice) : (outputBits choice).length ≤ 5 := by
  rw [output_length]
  cases choice <;>
    simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, if_false, if_true] <;> omega

end PNP.Concrete.ResidualReduction.SourceCandidateChoice
