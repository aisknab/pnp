/-
Copyright (c) 2026 PNP Labs.

Extended finite differential executable for canonical CNF inputs.

This checks 2,668 small formulae against all 15 assignments of length at most
three, or 40,020 pairs.  It extends the guarded 9,300-pair regression with
every one-clause word of length at most three while retaining the two-small-
clause family.  A timeout is a failure.

This is bounded implementation evidence only.  It is not the universal
machine-correctness or polynomial-halting theorem.  It is an executable
`main`, rather than a default `#guard`, so the extended sweep remains opt-in.
-/

import PNP.Concrete.CNFWorkMachine

namespace PNP.Concrete.CNFWorkCanonicalExtendedRegression

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

def clauses : List (List CNFLiteral) := listsThrough literals 3

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
  match expected, cnfWorkDecide input certificate with
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

#guard formulas.length == 2668
#guard assignments.length == 15
#guard formulas.length * assignments.length == 40020

def main : IO Unit := do
  match findMismatch formulas with
  | none =>
      IO.println "green: 2668 formulae, 15 assignments, 40020 pairs"
  | some pair => throw (IO.userError s!"CNF work-machine mismatch: {repr pair}")

end PNP.Concrete.CNFWorkCanonicalExtendedRegression

def main := PNP.Concrete.CNFWorkCanonicalExtendedRegression.main
