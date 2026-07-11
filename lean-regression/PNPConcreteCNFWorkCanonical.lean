/-
Copyright (c) 2026 PNP Labs.

Targeted finite differential regression for canonical CNF inputs.

This checks 620 small formulae against 15 assignments, or 9,300 pairs.  The
formula family covers declared widths zero through three, both literal signs,
indices zero through three, every single clause of length at most two, and
every ordered pair of clauses of length at most one (including empty
clauses).  The assignment family contains every bit string of length at most
three.  A timeout is a failure even when the semantic checker returns false.

This is bounded implementation evidence only.  It is not the universal
machine-correctness or polynomial-halting theorem.
-/

import PNP.Concrete.CNFWorkMachine

namespace PNP.Concrete.CNFWorkCanonicalRegression

def listsExact (items : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 =>
      (listsExact items n).flatMap
        (fun tail => items.map (fun item => item :: tail))

def listsThrough (items : List α) (n : Nat) : List (List α) :=
  (List.range (n + 1)).flatMap (listsExact items)

def literals : List CNFLiteral :=
  [false, true].flatMap (fun positive =>
    (List.range 4).map (fun variableIndex =>
      { positive := positive, variableIndex := variableIndex }))

def clauses : List (List CNFLiteral) := listsThrough literals 2

def smallClauses : List (List CNFLiteral) := listsThrough literals 1

def clauseLists : List (List (List CNFLiteral)) :=
  listsThrough clauses 1 ++ listsExact smallClauses 2

def formulas : List CNFFormula :=
  (List.range 4).flatMap (fun variableCount =>
    clauseLists.map (fun clauses =>
      { variableCount := variableCount, clauses := clauses }))

def assignments : List BitString := listsThrough [false, true] 3

def mismatch (formula : CNFFormula) (assignment : BitString) : Bool :=
  let input := encodeCNF formula
  let certificate := encodeAssignmentCertificate assignment
  let expected := checkEncodedCertificate input certificate
  let actual := cnfWorkDecide input certificate
  match expected, actual with
  | true, .accept => false
  | false, .reject => false
  | _, _ => true

def findAssignmentMismatch (formula : CNFFormula) :
    List BitString → Option (CNFFormula × BitString)
  | [] => none
  | assignment :: rest =>
      if mismatch formula assignment then some (formula, assignment)
      else findAssignmentMismatch formula rest

def findMismatch : List CNFFormula → Option (CNFFormula × BitString)
  | [] => none
  | formula :: rest =>
      match findAssignmentMismatch formula assignments with
      | some pair => some pair
      | none => findMismatch rest

#guard literals.length == 8
#guard clauses.length == 73
#guard smallClauses.length == 9
#guard clauseLists.length == 155
#guard formulas.length == 620
#guard assignments.length == 15
#guard formulas.length * assignments.length == 9300
#guard findMismatch formulas == none

end PNP.Concrete.CNFWorkCanonicalRegression
