import PNP.Concrete.ResidualReduction.SourceRowCoefficientInstructions

/-! The row reducer's exact ordered partner list. The seven cases are the
complete existing algorithm, not a growing prefix. Duplicates remain in order
because the first matching coefficient row determines the returned partner. -/

namespace PNP.Concrete.ResidualReduction.SourcePlanePartnerSpecification
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction

inductive Candidate where
  | zero | left | right | leftOne | rightOne | sum | sumOne
inductive Partner where
  | zero | left | right
abbrev Entry := Candidate × Partner

def value {n : Nat} (a b : Affine n) : Candidate → Affine n
  | .zero => aConst n false
  | .left => a
  | .right => b
  | .leftOne => aAdd a (aConst n true)
  | .rightOne => aAdd b (aConst n true)
  | .sum => aAdd a b
  | .sumOne => aAdd (aAdd a b) (aConst n true)
def output {n : Nat} (a b : Affine n) : Partner → Affine n
  | .zero => aConst n false
  | .left => a
  | .right => b
def entries : List Entry :=
  [(.zero,.zero),(.left,.right),(.leftOne,.zero),(.right,.left),
    (.rightOne,.zero),(.sum,.zero),(.sumOne,.left)]
def pair {n : Nat} (a b : Affine n) (entry : Entry) : Affine n × Affine n :=
  (value a b entry.1,output a b entry.2)
def lookup {n : Nat} (a b f : Affine n) : List Entry → Option (Affine n)
  | [] => none
  | entry :: rest =>
    if aEq f (value a b entry.1) then some (output a b entry.2) else lookup a b f rest

theorem lookup_eq {n : Nat} (a b f : Affine n) (es : List Entry) :
    lookup a b f es =
      ((es.map (pair a b)).find? (fun p => aEq f p.1)).map Prod.snd := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [lookup,List.map_cons,List.find?_cons]
    cases h : aEq f (value a b e.1) <;>
      simp only [h,Bool.false_eq_true,↓reduceIte,Option.map,pair,ih]

theorem entries_eq {n : Nat} (a b : Affine n) :
    entries.map (pair a b) = planePairs a b := rfl

theorem lookup_existing {n : Nat} (a b f : Affine n) :
    lookup a b f entries = planePartner a b f := by
  rw [lookup_eq,entries_eq]
  rfl

end PNP.Concrete.ResidualReduction.SourcePlanePartnerSpecification
