import PNP.Concrete.ResidualReduction.SourceCoefficientGateRaw
import Lean

/-! Hostile exact-gate regressions: both failures, every coefficient position,
nonzero off-diagonal terms with zero affine part, input-only startup, protected
scratch, suffix consumption and instruction-budget exhaustion. These examples
test the general execution theorems; they do not confer finite-instance proof
credit or assert a complete physical-runtime theorem. -/

namespace PNP.Concrete.ResidualReduction.SourceCoefficientGateRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceScalarState (zero)
open PNP.Concrete.ResidualReduction.SourceCoefficientGateState (checks finished)

private def x : Affine 2 := (true,(false,false))
private def y : Affine 2 := (false,(true,false))
private def z : Affine 2 := aConst 2 false
private def one : Affine 2 := aConst 2 true
private def suffix : BitString := [true,false,true,true,false]

example : qEq (qProduct x y) (qOfAffine z) = false := rfl
example : SourceClosure.affinePart (qProduct x y) = z := rfl
example : checks one (qProduct x y) (.affine z) = false := rfl
example : checks one (qProduct x y) (.plane x y z) = true := rfl
example : checks one (qProduct x y) (.plane x y one) = false := rfl
example : checks x (qOfAffine z) (.affine z) = false := rfl
example : checks z (qProduct x y) (.affine z) = false := rfl
example : checks one (qProduct x x) (.affine x) = true := rfl
example : checks one (qOfAffine z) (.plane x x x) = true := rfl
example : checks (n := 0) true false (.affine false) = true := rfl
example : checks (n := 0) false false (.affine false) = false := rfl
example : checks (n := 0) true true (.affine false) = false := rfl
example : checks (n := 0) true true (.plane true true false) = true := rfl
example : SourceCoefficientGateRaw.packet (n := 0) (true,false) (.affine false) =
    [false,true,false,false,false] := rfl
example {n : Nat} (q : Quadratic (n + 1)) (t : TailForm n) (rest : BitString) :
    Exec SourceCoefficientGateRaw.block (SourceCoefficientGateRaw.initial
      (SourceCoefficientGateRaw.packet q t ++ rest)) (SourceCoefficientGateRaw.fuel t)
      (finished q.1 q.2 t rest) := SourceCoefficientGateRaw.block_exec q t rest
example {n : Nat} (q : Quadratic (n + 1)) (t : TailForm n) (rest : BitString) :
    BitRegister.run (SourceCoefficientGateRaw.block.program 0 8) (SourceCoefficientGateRaw.fuel t + 1)
      ⟨.running 0,SourceCoefficientGateRaw.initial (SourceCoefficientGateRaw.packet q t ++ rest)⟩ =
      ⟨.accepted,finished q.1 q.2 t rest⟩ := SourceCoefficientGateRaw.program_run q t rest
example {n : Nat} (q : Quadratic (n + 1)) (t : TailForm n) :
    SourceCoefficientGateRaw.fuel t + 1 ≤ 82 * (SourceCoefficientGateRaw.packet q t).length + 169 :=
  SourceCoefficientGateRaw.fuel_encoded_bound q t
example {n : Nat} (q : Quadratic (n + 1)) (t : TailForm n) (rest : BitString) :
    (finished q.1 q.2 t rest).get 8 = [true] ↔ q.1 = aConst n true ∧ q.2 = t.polynomial :=
  SourceCoefficientGateRaw.output_true_iff q t rest
example {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1)) (v : Point n) (t : TailForm n) :
    contract F k v t = if checks (scalar (chartRows F k v)).1
      (scalar (chartRows F k v)).2 t then t.reduce (chartRows F k v) else none :=
  SourceCoefficientGateState.contract_eq F k v t

private def expectStore {k : Nat} (count : IO.Ref Nat)
    (actual : BitRegister.Configuration k) (expected : Store k) (label : String) : IO Unit := do
  if actual.control != .accepted then throw (IO.userError (label ++ ": instruction budget exhausted"))
  for i in List.finRange k do
    if actual.store.get i != expected.get i then throw (IO.userError (label ++ ": exact state differs"))
  count.modify (· + 1)

private def checkRaw {n : Nat} (count : IO.Ref Nat) (h : Affine n) (q : Quadratic n)
    (t : TailForm n) (rest : BitString) (wanted : Bool) : IO Unit := do
  if checks h q t != wanted then throw (IO.userError "Gate fixture expectation is wrong")
  let input := SourceCoefficientGateRaw.packet (h,q) t ++ rest
  let start := SourceCoefficientGateRaw.initial input
  if start.get 0 != input then throw (IO.userError "Gate: input stream missing")
  for i in List.finRange 18 do
    if i.val != 0 then
      if start.get i != [] then throw (IO.userError "Gate: hidden prepared input")
  let ticks := SourceCoefficientGateRaw.fuel t
  if ticks + 1 > 82 * (SourceCoefficientGateRaw.packet (h,q) t).length + 169 then
    throw (IO.userError "Gate: encoded instruction bound")
  let actual := BitRegister.run (SourceCoefficientGateRaw.block.program 0 8) (ticks + 1) ⟨.running 0,start⟩
  if actual.store.get 8 != [wanted] then throw (IO.userError "Gate: wrong independent acceptance result")
  expectStore count actual (finished h q t rest) "Input-only exact gates"

private def affines : (n : Nat) → List (Affine n)
  | 0 => [false,true]
  | n + 1 => (affines n).flatMap fun a => [(false,a),(true,a)]
private def quadratics : (n : Nat) → List (Quadratic n)
  | 0 => [false,true]
  | n + 1 => (affines n).flatMap fun a => (quadratics n).map fun q => (a,q)
private def affineBasis : (n : Nat) → List (Affine n)
  | 0 => [true]
  | n + 1 => (true,aConst n false) :: (affineBasis n).map fun a => (false,a)
private def quadraticBasis : (n : Nat) → List (Quadratic n)
  | 0 => [true]
  | n + 1 => ((affineBasis n).map fun a => (a,zero n)) ++
    ((quadraticBasis n).map fun q => (aConst n false,q))

private def checkEqual {n : Nat} (count : IO.Ref Nat) (p q : Quadratic n) : IO Unit := do
  let r : NormalizerBlocks.Occurrence.Registers :=
    ⟨[true],[false],[true],[false],[true,false],[true],[false],suffix,[false]⟩
  let actual := BitRegister.run (SourceQuadraticEquality.block.program 0 8)
    (SourceQuadraticEquality.fuel n + 1) ⟨.running 0,(SourceQuadraticEquality.ready r p q).store⟩
  expectStore count actual (SourceQuadraticEquality.finished r p q).store "All quadratic coefficients"

private def checkShort {n : Nat} (count : IO.Ref Nat) (q : Quadratic (n + 1)) (t : TailForm n) : IO Unit := do
  let actual := BitRegister.run (SourceCoefficientGateRaw.block.program 0 8) (SourceCoefficientGateRaw.fuel t)
    ⟨.running 0,SourceCoefficientGateRaw.initial (SourceCoefficientGateRaw.packet q t ++ suffix)⟩
  if actual.control == .accepted then throw (IO.userError "Gate: accepted before the final instruction")
  count.modify (· + 1)

private def checkTail {n : Nat} (count : IO.Ref Nat) (t : TailForm n) : IO Unit := do
  for rest in [[],suffix] do
    checkRaw count (aConst n true) t.polynomial t rest true
    checkRaw count (aConst n false) t.polynomial t rest false
    for b in quadraticBasis n do
      checkRaw count (aConst n true) (qAdd t.polynomial b) t rest false
  for b in affineBasis n do
    checkRaw count (aAdd (aConst n true) b) t.polynomial t suffix false

#eval (show IO Unit from do
  let count ← IO.mkRef 0
  for n in [0,1,2] do
    for p in quadratics n do
      for q in quadratics n do checkEqual count p q
  for n in [0,1] do
    for u in affines n do
      checkTail count (.affine u)
      for a in affines n do
        for b in affines n do
          checkRaw count (aConst n true) (TailForm.plane a b u).polynomial (.plane a b u) suffix true
  for u in affines 2 do checkTail count (.affine u)
  for t in [TailForm.plane x y z,.plane x y one,.plane x x x,.plane one y x,.plane z z one] do
    checkTail count t
  for n in [3,5,9] do
    checkTail count (.affine (aConst n true))
    checkTail count (.plane (aConst n true) (aConst n false) (aConst n true))
  checkRaw count z (qProduct x y) (.affine z) suffix false
  for t in [TailForm.affine x,.plane x y z] do
    checkShort count (one,t.polynomial) t
    checkShort count (z,t.polynomial) t
  IO.println s!"EXACT_COEFFICIENT_GATE_REGRESSIONS_GREEN: {← count.get} executions")

run_cmd do
  for name in [
    ``SourceQuadraticEquality.equal_zero,
    ``SourceQuadraticEquality.equal_word,
    ``SourceQuadraticEquality.block_exec,
    ``SourceQuadraticEquality.fuel_encoded,
    ``SourceTailPolynomialAffine.product_one,
    ``SourceTailPolynomialAffine.one_word,
    ``SourceTailPolynomialAffine.one_exec,
    ``SourceTailPolynomialAffine.load_exec,
    ``SourceTailPolynomialAffine.block_exec,
    ``SourceTailPolynomialAffine.fuel_exact,
    ``SourceTailPolynomial.plane_exec,
    ``SourceTailPolynomial.block_exec,
    ``SourceTailPolynomial.affine_fuel,
    ``SourceTailPolynomial.plane_fuel,
    ``SourceTailPolynomial.fuel_bound,
    ``SourceCoefficientGateState.checks_true_iff,
    ``SourceCoefficientGateState.contract_eq,
    ``SourceCoefficientGateState.scalar_exec,
    ``SourceCoefficientGateState.core_exec,
    ``SourceCoefficientGateState.output_get,
    ``SourceCoefficientGateState.suffix_get,
    ``SourceCoefficientGateHead.block_exec,
    ``SourceCoefficientGateTail.load_exec,
    ``SourceCoefficientGateTail.mask_exec,
    ``SourceCoefficientGateTail.compare_exec,
    ``SourceCoefficientGateTail.block_exec,
    ``SourceCoefficientGateTail.fuel_bound,
    ``SourceCoefficientGateRaw.packet_bytes,
    ``SourceCoefficientGateRaw.header_fuel,
    ``SourceCoefficientGateRaw.dimension_exec,
    ``SourceCoefficientGateRaw.setup_exec,
    ``SourceCoefficientGateRaw.block_exec,
    ``SourceCoefficientGateRaw.program_run,
    ``SourceCoefficientGateRaw.packet_length,
    ``SourceCoefficientGateRaw.fuel_bound,
    ``SourceCoefficientGateRaw.fuel_encoded_bound,
    ``SourceCoefficientGateRaw.output_true_iff] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo "EXACT_COEFFICIENT_GATE_AXIOMS_GREEN: 37 theorems"

#print axioms PNP.Concrete.ResidualReduction.SourceQuadraticEquality.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceTailPolynomial.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceCoefficientGateState.contract_eq
#print axioms PNP.Concrete.ResidualReduction.SourceCoefficientGateRaw.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceCoefficientGateRaw.program_run
#print axioms PNP.Concrete.ResidualReduction.SourceCoefficientGateRaw.fuel_encoded_bound

end PNP.Concrete.ResidualReduction.SourceCoefficientGateRegression
