/-
Copyright (c) 2026 PNP Labs.

Finite edge regression for the exact-six-step work-machine compiler.

The cases cover left, stay, and right movement; implicit blank work symbols
at both finite-tape boundaries; one and two explicit neighbours; unequal
written components; and adjacent components unknown to the selected rule.

This is bounded implementation evidence only.  It is not the universal
compiler-simulation theorem.
-/

import PNP.Concrete.WorkMachine

namespace PNP.Concrete.WorkCompilerEdgeRegression

def source : Nat := 2
def target : Nat := 3

def ruleFor (read write : WorkSymbol) (move : HeadMove) : WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := write
    move := move }

def machineFor (rule : WorkRule) : WorkMachine :=
  { rules := [rule]
    startState := source
    acceptState := 0
    rejectState := 1 }

def exactSixMatches (left : List WorkSymbol) (head : WorkSymbol)
    (right : List WorkSymbol) (write : WorkSymbol) (move : HeadMove) : Bool :=
  let config : WorkConfiguration :=
    { state := source, tape := { left := left, head := head, right := right } }
  let rule := ruleFor head write move
  run (compileWorkMachine (machineFor rule)) 6 (encodeWorkConfiguration config) ==
    encodeWorkConfiguration (applyWorkRule rule config)

def cases : List (String × Bool) :=
  [ ("left/implicit-blank",
      exactSixMatches [] .zeroOne [] .blankOne .left)
  , ("left/one-neighbour",
      exactSixMatches [.oneZero] .zeroOne [] .blankOne .left)
  , ("left/two-neighbours",
      exactSixMatches [.oneZero, .zeroBlank] .zeroOne [.oneOne]
        .blankOne .left)
  , ("stay/empty-sides",
      exactSixMatches [] .zeroOne [] .blankOne .stay)
  , ("stay/nonempty-sides",
      exactSixMatches [.oneZero] .zeroOne [.oneOne] .blankOne .stay)
  , ("right/implicit-blank",
      exactSixMatches [] .zeroOne [] .blankOne .right)
  , ("right/one-neighbour",
      exactSixMatches [] .zeroOne [.oneZero] .blankOne .right)
  , ("right/two-neighbours",
      exactSixMatches [.zeroBlank] .zeroOne [.oneZero, .oneOne]
        .blankOne .right)
  , ("right/unequal-written-components",
      exactSixMatches [.oneOne] .oneZero [.blankZero] .zeroOne .right)
  , ("left/unknown-adjacent-component",
      exactSixMatches [.blankZero] .oneZero [.oneOne] .zeroOne .left) ]

#guard cases.length == 10
#guard cases.all Prod.snd

end PNP.Concrete.WorkCompilerEdgeRegression
