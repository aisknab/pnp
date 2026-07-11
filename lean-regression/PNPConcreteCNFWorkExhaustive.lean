/-
Copyright (c) 2026 PNP Labs.

Bounded differential regression for the executable CNF work machine.

This checks every ordered pair of bit strings of length at most eight:
511 formula strings times 511 certificate strings, or 261,121 pairs.  It is
finite implementation evidence only; it is not the universal machine-
correctness theorem and is intentionally kept out of the default CI path.
-/

import PNP.Concrete.CNFWorkMachine

namespace PNP.Concrete.CNFWorkRegression

def exactBits : Nat → List BitString
  | 0 => [[]]
  | n + 1 =>
      (exactBits n).map (fun bits => false :: bits) ++
        (exactBits n).map (fun bits => true :: bits)

def bitsThrough : Nat → List BitString
  | 0 => [[]]
  | n + 1 => bitsThrough n ++ exactBits (n + 1)

def mismatch (input certificate : BitString) : Bool :=
  let expected := checkEncodedCertificate input certificate
  let actual := cnfWorkDecide input certificate == WorkVerdict.accept
  expected != actual

def findCertificateMismatch (input : BitString) :
    List BitString → Option (BitString × BitString)
  | [] => none
  | certificate :: rest =>
      if mismatch input certificate then some (input, certificate)
      else findCertificateMismatch input rest

def findMismatch (certificates : List BitString) :
    List BitString → Option (BitString × BitString)
  | [] => none
  | input :: rest =>
      match findCertificateMismatch input certificates with
      | some pair => some pair
      | none => findMismatch certificates rest

def samples : List BitString := bitsThrough 8

#guard samples.length == 511
#guard findMismatch samples samples == none

end PNP.Concrete.CNFWorkRegression
