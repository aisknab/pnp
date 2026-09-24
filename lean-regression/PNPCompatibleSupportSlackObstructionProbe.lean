import PNP

set_option autoImplicit false

namespace PNP.Regression.CompatibleSupportSlackObstruction
open PNP.DirectWire PNP.DirectWire.CompatibleSupportSlackObstruction

private def expected (input : Valuation 4) (output : Fin 10) : Bool :=
  let a := input 0
  let b := input 1
  let ab := a && b
  let q := boolNand ab (input 2)
  let z := boolNand q (input 3)
  match output.val with
  | 0 => ab
  | 1 => q
  | 2 => z
  | 3 => boolNand a z
  | 4 => a && z
  | 5 => boolNand (a && z) b
  | 6 => !z
  | 7 => boolNand a (!z)
  | 8 => a && !z
  | _ => boolNand (a && !z) b

#eval show IO Unit from do
  if original.toImplementation.gateCount != 11 || support.gateCount != 9 ||
      smaller.toImplementation.gateCount != 8 then
    throw (IO.userError "the physical sizes no longer match the proved example")
  if support.boundary = [.input 0, .input 1, .gate 3] then pure ()
  else throw (IO.userError "the cut omitted or changed an incoming port")
  if support.interface = [1, 4, 5, 6, 7, 8, 9, 10] then pure ()
  else throw (IO.userError "the cut omitted or changed an outgoing port")
  for value in allFin 16 do
    for output in allFin 10 do
      if original.semantics (valuation value) output != expected (valuation value) output then
        throw (IO.userError "the literal source differs from the independently written formula")
  if equivalentBool offered comparison != true then
    throw (IO.userError "the smaller word does not preserve the complete independent cut")
  if (ArbitrarySupportSplice.compile original records offered).isNone != true then
    throw (IO.userError "the cyclic saving was accepted as an acyclic substitution")
  if (ArbitrarySupportSplice.compile original records comparison).isSome != true then
    throw (IO.userError "the identity replacement control did not compile")
  let wrong := { offered with outputs := OutputWord.ofFn (fun _ => .constant false) }
  if equivalentBool wrong comparison != false then
    throw (IO.userError "a wrong-interface negative control was accepted")
  -- The source's hidden first gate is deliberately not an ordinary output.
  if (allFin 16).all (fun value =>
      originalProgram.eval (valuation value) 0 ==
        boolNand (freeValue 0 (valuation value)) (freeValue 1 (valuation value))) != true then
    throw (IO.userError "the excluded first-gate control does not have free NAND semantics")
  IO.println "compatible-support-slack-obstruction-regressions-passed"

end PNP.Regression.CompatibleSupportSlackObstruction
