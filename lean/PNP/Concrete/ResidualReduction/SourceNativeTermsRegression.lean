import PNP.Concrete.ResidualReduction.SourceNativeTermsInput
import Lean

/-! Focused complete-list conversion regressions. General kernel contracts
cover arbitrary counts and streams. Executions independently compare canonical
native sparse-form bytes, duplicate cancellation, protected fields, malformed
headers/labels and partially consumed failures. Prior suites are not rerun. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeTermsRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceNativeTermsState

example (input : BitString) (n : Nat) : (SourceNativeTermsInput.initial input n).get 0 = input := rfl
example (input : BitString) (n : Nat) :
    (SourceNativeTermsInput.initial input n).get 9 = List.replicate n true := rfl
example (input : BitString) (n : Nat) : (SourceNativeTermsInput.initial input n).get 10 = [] := rfl
example (input : BitString) (n : Nat) : (SourceNativeTermsInput.initial input n).get 11 = [] := rfl
example (input : BitString) (n : Nat) : (SourceNativeTermsInput.initial input n).get 12 = [] := rfl
example (input : BitString) (n : Nat) : (SourceNativeTermsInput.initial input n).get 13 = [] := rfl
example (input : BitString) (n : Nat) (constant : Bool) :
    Exec (SourceNativeTermsInput.block constant) (SourceNativeTermsInput.initial input n)
      (SourceNativeTermsInput.fuel input n) (SourceNativeTermsInput.result input n constant) :=
  SourceNativeTermsInput.block_exec input n constant
example (input : BitString) (n : Nat) :
    SourceNativeTermsInput.fuel input n ≤
      input.length * (15 * input.length + 18 * n + 72) + 4 * input.length + 7 * n + 40 :=
  SourceNativeTermsInput.fuel_bound input n
example (input : BitString) (n limit : Nat) (size : input.length ≤ limit) (dimension : n ≤ 2 * limit) :
    SourceNativeTermsInput.fuel input n ≤ 51 * (limit * limit) + 90 * limit + 40 :=
  SourceNativeTermsInput.polynomial_bound input n limit size dimension
example {c : Nat} (xs : NativeCoefficients.Coefficients c) (suffix : BitString) (constant : Bool) :
    (SourceNativeTermsInput.result ((NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix)
      (2 * c) constant).get 8 = SourceNativeEncoding.termsWord xs constant :=
  SourceNativeTermsInput.canonical_output xs suffix constant
example {c : Nat} (xs : NativeCoefficients.Coefficients c) (suffix : BitString) (constant : Bool) :
    (SourceNativeTermsInput.result ((NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix)
      (2 * c) constant).get 4 = [true] :=
  SourceNativeTermsInput.canonical_flag xs suffix constant
example {c : Nat} (xs : NativeCoefficients.Coefficients c) (suffix : BitString) (a : Affine (2 * c)) :
    SourceNativeTermsSpec.scan xs.length (encodeSeq (NativeSystemCodec.rowCodec c).encode xs ++ suffix) a =
      ⟨suffix,SourceNativeEncoding.accumulate xs a,true⟩ :=
  SourceNativeTermsSpec.scan_canonical xs suffix a
example : SourceNativeEncoding.termsWord ([(0,false),(0,false)] : NativeCoefficients.Coefficients 1) true =
    [false,false,true] := by decide
example {c : Nat} (xs : NativeCoefficients.Coefficients c) (suffix : BitString) (constant : Bool) :
    (SourceNativeTermsInput.result ((NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix)
      (2 * c) constant).get 0 = suffix := by
  rw [SourceNativeTermsInput.canonical_result]
  rfl
example : (SourceNativeTermsInput.result (natural 2 ++ [false,false]) 2 false).get 4 = [] := by decide

private def check (counter : IO.Ref Nat) (p : Program 14) (start expected : Store 14)
    (ticks : Nat) (label : String) : IO Unit := do
  let actual := BitRegister.run p (ticks + 1) ⟨.running 0,start⟩
  if actual.control != .accepted then throw (IO.userError (label ++ ": did not halt at its source bound"))
  for i in List.finRange 14 do
    if actual.store.get i != expected.get i then
      throw (IO.userError (label ++ ": complete state differs"))
  counter.modify (· + 1)

private def checkWhole (counter : IO.Ref Nat) (input : BitString) (n : Nat) (constant : Bool)
    (expected : Store 14) : IO Unit := do
  let start := SourceNativeTermsInput.initial input n
  for i in List.finRange 14 do
    let allowed := if i.val == 0 then input else if i.val == 9 then List.replicate n true else []
    if start.get i != allowed then throw (IO.userError "Sparse-list converter has hidden initial data")
  let ticks := SourceNativeTermsInput.fuel input n
  if ticks > input.length * (15 * input.length + 18 * n + 72) + 4 * input.length + 7 * n + 40 then
    throw (IO.userError "Sparse-list source budget differs")
  if n <= 2 * input.length && ticks > 51 * (input.length * input.length) + 90 * input.length + 40 then
    throw (IO.userError "Sparse-list encoded-size polynomial bound differs")
  check counter (SourceNativeTermsInput.block constant |>.program 0 8) start expected ticks "Complete sparse list"

#eval (show IO Unit from do
  let counter ← IO.mkRef 0
  for n in [0,1,3,7] do
    for left in [false,true] do
      for right in [false,true] do
        for pending in [0,2] do
          let input := [true,false,true]
          let x := aConst n left
          let a := aConst n right
          check counter (SourceNativeTermsAdd.block.program 0 8)
            (full (SourceNativeTermsAdd.before input x) (data input a (pending + 1) true))
            (state input (aAdd x a) pending true) (SourceNativeTermsAdd.fuel n) "Affine accumulation"
  IO.println "TERMS_PHASE: literal accumulation and protected state passed"
  for c in [0,1,3,5] do
    let rows : NativeCoefficients.Coefficients c :=
      (List.finRange c).flatMap (fun i => [(i,false),(i,true)])
    let candidates : List (NativeCoefficients.Coefficients c) :=
      if rows.isEmpty then [[]] else [[],rows,rows.reverse,rows ++ rows,rows ++ rows ++ rows]
    for xs in candidates do
      for constant in [false,true] do
        for suffix in [[],[true,false,true]] do
          let input := (NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix
          let sum := aAdd (NativeSource.sparseForm xs) (aConst (2 * c) constant)
          let expected := SourceNativeTermsInput.emitted ⟨suffix,sum,true⟩
          if expected.get 8 != SourceNativeEncoding.termsWord xs constant ||
              expected.get 0 != suffix || expected.get 4 != [true] then
            throw (IO.userError "Independent native sparse-form fixture differs")
          checkWhole counter input (2 * c) constant expected
  IO.println "TERMS_PHASE: complete lists, repeats, order and suffix preservation passed"
  for n in [0,2,6] do
    let invalid : List BitString :=
      [[],[true],List.replicate 9 true,natural 1,natural 2,natural 1 ++ [false],
       natural 1 ++ List.replicate 5 true,natural 1 ++ natural (n + 1) ++ [false],
       natural 2 ++ [false,false],natural 2 ++ [false,false,true],
       natural 3 ++ [false,false,false,true,false]]
    for input in invalid do
      for constant in [false,true] do
        let expected := SourceNativeTermsInput.result input n constant
        if expected.get 4 != [] || expected.get 8 != [] || expected.get 11 != [] || expected.get 13 != [] then
          throw (IO.userError "Malformed sparse list retained success or partial output")
        checkWhole counter input n constant expected
  IO.println s!"TERMS_REGRESSIONS_GREEN: {← counter.get} executions")

run_cmd do
  let names := [
    ``SourceNativeTermsSpec.label_result,
    ``SourceNativeTermsSpec.readCore_input,
    ``SourceNativeTermsSpec.readCore_some,
    ``SourceNativeTermsSpec.readCore_none,
    ``SourceNativeTermsSpec.remaining_bound,
    ``SourceNativeTermsSpec.selected_canonical,
    ``SourceNativeTermsSpec.remaining_canonical,
    ``SourceNativeTermsSpec.scan_input_bound,
    ``SourceNativeTermsSpec.scan_canonical,
    ``SourceNativeTermsState.core_exec,
    ``SourceNativeTermsState.label_exec,
    ``SourceNativeTermsState.reset_exec,
    ``SourceNativeTermsState.restore_exec,
    ``SourceNativeTermsState.retain_exec,
    ``SourceNativeTermsState.reject_exec,
    ``SourceNativeTermsState.advance_exec,
    ``SourceNativeTermsAdd.block_exec,
    ``SourceNativeTerm.block_exec,
    ``SourceNativeTerm.fuel_bound,
    ``SourceNativeTermsLoop.block_exec,
    ``SourceNativeTermsLoop.fuel_bound_at,
    ``SourceNativeTermsLoop.fuel_bound,
    ``SourceNativeTermsLoop.canonical_exec,
    ``SourceNativeTermsSeed.finish_exec,
    ``SourceNativeTermsSeed.block_exec,
    ``SourceNativeTermsInput.headers_exec,
    ``SourceNativeTermsInput.emit_exec,
    ``SourceNativeTermsInput.accepted_exec,
    ``SourceNativeTermsInput.block_exec,
    ``SourceNativeTermsInput.fuel_bound,
    ``SourceNativeTermsInput.polynomial_bound,
    ``SourceNativeTermsInput.canonical_result,
    ``SourceNativeTermsInput.canonical_exec,
    ``SourceNativeTermsInput.canonical_output,
    ``SourceNativeTermsInput.canonical_flag]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"TERMS_AXIOMS_GREEN: {names.length} theorems"

#print axioms PNP.Concrete.ResidualReduction.SourceNativeTermsSpec.scan_canonical
#print axioms PNP.Concrete.ResidualReduction.SourceNativeTerm.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceNativeTermsLoop.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceNativeTermsInput.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceNativeTermsInput.polynomial_bound
#print axioms PNP.Concrete.ResidualReduction.SourceNativeTermsInput.canonical_output

end PNP.Concrete.ResidualReduction.SourceNativeTermsRegression
