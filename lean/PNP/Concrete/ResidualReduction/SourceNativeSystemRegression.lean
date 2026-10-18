import PNP.Concrete.ResidualReduction.SourceNativeSystemGroup
import Lean

/-! Focused native row-group integration checks. General execution and bounds
cover every stream and arbitrary row counts. Concrete executions independently
derive expected row bytes from the native source, exercise both protected
buffers, and reject malformed groups without reviving invalid input. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeSystemRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceNativeSystemState

example (input : BitString) :
    Exec SourceNativeSystemHeader.block (initial input)
      (SourceNativeSystemHeader.fuel input) (SourceNativeSystemHeader.result input) :=
  SourceNativeSystemHeader.block_exec input
example (input : BitString) : SourceNativeSystemHeader.fuel input ≤ 21 * input.length + 62 :=
  SourceNativeSystemHeader.fuel_bound input
example (input : BitString) (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved)
    (dimension : s.dimension = List.replicate n true) :
    Exec (SourceNativeSystemRow.block kind) (work input [] s)
      (SourceNativeSystemRow.fuel input n kind s)
      (work (SourceNativeSystemRow.result input n kind s).stream [] (SourceNativeSystemRow.result input n kind s)) :=
  SourceNativeSystemRow.block_exec input n kind s dimension
example (count n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved)
    (pending : s.pending = List.replicate count true)
    (dimension : s.dimension = List.replicate n true) :
    Exec (SourceNativeSystemLoop.block kind) (work s.stream [] s)
      (SourceNativeSystemLoop.fuel count n kind s)
      (work (SourceNativeSystemLoop.result count n kind s).stream [] (SourceNativeSystemLoop.result count n kind s)) :=
  SourceNativeSystemLoop.block_exec count n kind s pending dimension
example (input : BitString) (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved)
    (dimension : s.dimension = List.replicate n true) :
    Exec (SourceNativeSystemGroup.block kind) (work input [] s)
      (SourceNativeSystemGroup.fuel input n kind s)
      (work (SourceNativeSystemGroup.result input n kind s).stream [] (SourceNativeSystemGroup.result input n kind s)) :=
  SourceNativeSystemGroup.block_exec input n kind s dimension
example (input : BitString) (n limit : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved)
    (size : input.length ≤ limit) (dimension : n ≤ 2 * limit)
    (constant : s.constant.length ≤ n + 1) :
    SourceNativeSystemGroup.fuel input n kind s ≤
      limit * (51 * (limit * limit) + 151 * limit + 179) + 4 * limit + 29 :=
  SourceNativeSystemGroup.polynomial_bound input n limit kind s size dimension constant
example (input : BitString) (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) :
    (SourceNativeSystemGroup.result input n kind s).pending = [] :=
  SourceNativeSystemGroup.pending_empty input n kind s
example (input : BitString) (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) :
    (SourceNativeSystemGroup.result input n kind s).stream.length ≤ input.length :=
  SourceNativeSystemGroup.stream_bound input n kind s
example {c : Nat} (entry : NativeEquations.Row c × NativeCoefficients.Coefficients c)
    (suffix : BitString) (s : Saved) (valid : s.active = [true]) :
    SourceNativeSystemRow.result ((NativeSystemCodec.entryCodec c).encode entry ++ suffix) (2 * c) .product s =
      SourceNativeSystemRows.result .product {s with stream := suffix,left := SourceNativeEncoding.affineWord (NativeSource.coordinateForm (2 * c) (NativeSource.rowIndex entry.1)),payload := SourceNativeEncoding.termsWord entry.2 true} :=
  SourceNativeSystemRow.canonical_product_result entry suffix s valid

private def fixture (n : Nat) : Saved :=
  ⟨List.replicate n true,[true,false],List.replicate 3 true,List.replicate 2 true,
    [true,false,true],[false,true],[],SourceNativeEncoding.affineWord (aConst n true),[true],[]⟩

private def check (counter : IO.Ref Nat) (p : Program 24) (start expected : Store 24)
    (ticks : Nat) (label : String) : IO Unit := do
  let actual := BitRegister.run p (ticks + 1) ⟨.running 0,start⟩
  if actual.control != .accepted then throw (IO.userError (label ++ ": did not halt at its bound"))
  for i in List.finRange 24 do
    if actual.store.get i != expected.get i then
      throw (IO.userError (label ++ ": complete state differs at register " ++ toString i.val))
  counter.modify (· + 1)

private def checkGroup (counter : IO.Ref Nat) (input : BitString) (n : Nat)
    (kind : SourceNativeSystemRow.Kind) (s expected : Saved) : IO Unit := do
  let ticks := SourceNativeSystemGroup.fuel input n kind s
  let limit := input.length + n + 1
  if ticks > limit * (51 * (limit * limit) + 151 * limit + 179) + 4 * limit + 29 then
    throw (IO.userError "Group encoded-size work bound differs")
  check counter ((SourceNativeSystemGroup.block kind).program 0 8) (work input [] s)
    (work expected.stream [] expected) ticks "Native row group"

private def expectedLinear {c : Nat} (xs : List (NativeCoefficients.Coefficients c))
    (suffix : BitString) (s : Saved) : Saved :=
  {s with stream := suffix,pending := [],total := List.replicate xs.length true ++ s.total,rows := (encodeSeq SourceNativeEncoding.zeroRow xs).reverse ++ s.rows,payload := (match xs.getLast? with | none => s.payload | some last => SourceNativeEncoding.termsWord last false)}

private def expectedProducts {c : Nat}
    (xs : List (NativeEquations.Row c × NativeCoefficients.Coefficients c))
    (suffix : BitString) (s : Saved) : Saved :=
  {s with stream := suffix,pending := [],total := List.replicate xs.length true ++ s.total,products := (encodeSeq SourceNativeEncoding.productRow xs).reverse ++ s.products,left := (match xs.getLast? with | none => s.left | some last => SourceNativeEncoding.affineWord (NativeSource.coordinateForm (2 * c) (NativeSource.rowIndex last.1))),payload := (match xs.getLast? with | none => s.payload | some last => SourceNativeEncoding.termsWord last.2 true)}

#eval (show IO Unit from do
  let counter ← IO.mkRef 0
  for c in [0,1,3,7] do
    for suffix in [[],[true,false,true]] do
      let input := natural c ++ suffix
      let start := initial input
      for i in List.finRange 24 do
        if start.get i != (if i.val == 0 then input else []) then
          throw (IO.userError "System reader has hidden initial data")
      check counter (SourceNativeSystemHeader.block.program 0 8) start
        (work suffix [] (SourceNativeSystemHeader.data suffix c))
        (SourceNativeSystemHeader.fuel input) "Actual dimension header"
  for input in [[],[true],List.replicate 8 true] do
    check counter (SourceNativeSystemHeader.block.program 0 8) (initial input)
      (work [] [] emptySaved) (SourceNativeSystemHeader.fuel input) "Malformed dimension"
  IO.println "NATIVE_SYSTEM_PHASE: actual input dimensions and fail-closed headers passed"
  for c in [0,1,3] do
    let terms : NativeCoefficients.Coefficients c :=
      (List.finRange c).flatMap (fun i => [(i,false),(i,true)])
    let collections : List (List (NativeCoefficients.Coefficients c)) :=
      [[],[[]],[terms],[terms,terms ++ terms,[],terms.reverse],[terms,terms,terms,terms,terms]]
    let base := fixture (2 * c)
    for xs in collections do
      for suffix in [[],[true,false,true]] do
        let input := (listCodec (NativeSystemCodec.coefficientsCodec c)).encode xs ++ suffix
        checkGroup counter input (2 * c) .zero base (expectedLinear xs suffix base)
    for xs in [[],terms,terms ++ terms] do
      let suffix := [true,false,true]
      let input := (NativeSystemCodec.coefficientsCodec c).encode xs ++ suffix
      let expected := {base with stream := suffix,payload := SourceNativeEncoding.termsWord xs true,rows := (SourceNativeEncoding.oneRow xs).reverse ++ base.rows,total := true :: base.total}
      check counter ((SourceNativeSystemRow.block .one).program 0 8) (work input [] base)
        (work suffix [] expected) (SourceNativeSystemRow.fuel input (2 * c) .one base) "Initial one row"
    let entries := terms.map (fun r => (r,terms ++ terms ++ [r]))
    let groups := [[],entries,entries.reverse,entries ++ entries]
    for xs in groups do
      for suffix in [[],[false,true,false]] do
        let input := (listCodec (NativeSystemCodec.entryCodec c)).encode xs ++ suffix
        checkGroup counter input (2 * c) .product base (expectedProducts xs suffix base)
  IO.println "NATIVE_SYSTEM_PHASE: arbitrary groups, independent row bytes, order and protected buffers passed"
  for n in [0,2,6] do
    let base := fixture n
    for kind in [SourceNativeSystemRow.Kind.zero,.product] do
      let bad : List BitString := [[],[true],List.replicate 5 true,natural 1,
        natural 1 ++ [true],natural 1 ++ natural (n + 2) ++ [false]]
      for input in bad do
        let expected := SourceNativeSystemGroup.result input n kind base
        if expected.active != [] || expected.pending != [] ||
            expected.rows != base.rows || expected.products != base.products || expected.total != base.total then
          throw (IO.userError "Malformed group appended a row or retained validity")
        checkGroup counter input n kind base expected
    let interruptedInput := natural 2 ++ natural 0
    let r := SourceNativeSystemGroup.result interruptedInput n .zero base
    let first := false :: (SourceNativeEncoding.affineWord (aConst n false) ++ base.constant)
    if r.active != [] || r.pending != [] || r.total != true :: base.total ||
        r.rows != first.reverse ++ base.rows || r.products != base.products then
      throw (IO.userError "Partial group did not stop at its first malformed row")
    checkGroup counter interruptedInput n .zero base r
    let inactive := {base with active := []}
    let input := natural 2 ++ natural 0 ++ natural 0
    let expected := {inactive with stream := [],pending := [],payload := SourceNativeEncoding.affineWord (aConst n false)}
    checkGroup counter input n .zero inactive expected
  IO.println s!"NATIVE_SYSTEM_REGRESSIONS_GREEN: {← counter.get} executions")

run_cmd do
  let names := [
    ``SourceNativeSystemState.core_exec,
    ``SourceNativeSystemState.use14_exec,
    ``SourceNativeSystemState.use10_exec,
    ``SourceNativeSystemState.field_get,
    ``SourceNativeSystemState.working_get,
    ``SourceNativeSystemState.field_set,
    ``SourceNativeSystemState.push_exec,
    ``SourceNativeSystemState.clear_exec,
    ``SourceNativeSystemState.pop_exec,
    ``SourceNativeSystemState.save_exec,
    ``SourceNativeSystemState.load_exec,
    ``SourceNativeSystemState.reset_exec,
    ``SourceNativeSystemState.restore_exec,
    ``SourceNativeSystemState.clean_exec,
    ``SourceNativeSystemState.reject_exec,
    ``SourceNativeSystemHeader.headers_exec,
    ``SourceNativeSystemHeader.accepted_exec,
    ``SourceNativeSystemHeader.block_exec,
    ``SourceNativeSystemHeader.fuel_bound,
    ``SourceNativeSystemHeader.dimension_bound,
    ``SourceNativeSystemHeader.canonical_exec,
    ``SourceNativeSystemCapture.recorded_stream,
    ``SourceNativeSystemCapture.captured_stream,
    ``SourceNativeSystemCapture.captured_dimension,
    ``SourceNativeSystemCapture.block_exec,
    ``SourceNativeSystemCapture.fuel_bound,
    ``SourceNativeSystemTerms.prepare_exec,
    ``SourceNativeSystemTerms.block_exec,
    ``SourceNativeSystemTerms.dimension_preserved,
    ``SourceNativeSystemTerms.parsed_input_bound,
    ``SourceNativeSystemTerms.parsed_output_bound,
    ``SourceNativeSystemTerms.stream_bound,
    ``SourceNativeSystemTerms.payload_bound,
    ``SourceNativeSystemTerms.fuel_bound,
    ``SourceNativeSystemTerms.polynomial_bound,
    ``SourceNativeSystemTerms.canonical_result,
    ``SourceNativeSystemTerms.canonical_exec,
    ``SourceNativeSystemLabel.reverse_exec,
    ``SourceNativeSystemLabel.block_exec,
    ``SourceNativeSystemLabel.readCore_empty_output,
    ``SourceNativeSystemLabel.readCore_output_bound,
    ``SourceNativeSystemLabel.dimension_preserved,
    ``SourceNativeSystemLabel.stream_eq,
    ``SourceNativeSystemLabel.stream_bound,
    ``SourceNativeSystemLabel.left_bound,
    ``SourceNativeSystemLabel.invalid_result,
    ``SourceNativeSystemLabel.selected_result,
    ``SourceNativeSystemLabel.fuel_bound,
    ``SourceNativeSystemLabel.polynomial_bound,
    ``SourceNativeSystemLabel.canonical_result,
    ``SourceNativeSystemLabel.canonical_exec,
    ``SourceNativeSystemRows.finish_exec,
    ``SourceNativeSystemRows.block_exec,
    ``SourceNativeSystemRows.stream_preserved,
    ``SourceNativeSystemRows.dimension_preserved,
    ``SourceNativeSystemRows.pending_preserved,
    ``SourceNativeSystemRows.active_preserved,
    ``SourceNativeSystemRows.total_length,
    ``SourceNativeSystemRows.buffer_eq,
    ``SourceNativeSystemRows.word_length,
    ``SourceNativeSystemRows.fuel_bound,
    ``SourceNativeSystemRow.commit_exec,
    ``SourceNativeSystemRow.source_exec,
    ``SourceNativeSystemRow.block_exec,
    ``SourceNativeSystemRow.terms_constant,
    ``SourceNativeSystemRow.terms_left,
    ``SourceNativeSystemRow.label_constant,
    ``SourceNativeSystemRow.sourced_dimension,
    ``SourceNativeSystemRow.sourced_constant,
    ``SourceNativeSystemRow.sourced_stream_bound,
    ``SourceNativeSystemRow.sourced_left_bound,
    ``SourceNativeSystemRow.sourced_right_bound,
    ``SourceNativeSystemRow.dimension_preserved,
    ``SourceNativeSystemRow.constant_preserved,
    ``SourceNativeSystemRow.stream_bound,
    ``SourceNativeSystemRow.sourceFuel_bound,
    ``SourceNativeSystemRow.polynomial_bound,
    ``SourceNativeSystemRow.canonical_linear_result,
    ``SourceNativeSystemRow.canonical_product_result,
    ``SourceNativeSystemRow.canonical_linear_exec,
    ``SourceNativeSystemRow.canonical_product_exec,
    ``SourceNativeSystemLoop.capture_pending,
    ``SourceNativeSystemLoop.sourced_pending,
    ``SourceNativeSystemLoop.row_pending,
    ``SourceNativeSystemLoop.step_exec,
    ``SourceNativeSystemLoop.after_dimension,
    ``SourceNativeSystemLoop.after_constant,
    ``SourceNativeSystemLoop.after_stream_bound,
    ``SourceNativeSystemLoop.block_exec,
    ``SourceNativeSystemLoop.dimension_preserved,
    ``SourceNativeSystemLoop.constant_preserved,
    ``SourceNativeSystemLoop.stream_bound,
    ``SourceNativeSystemLoop.pending_empty,
    ``SourceNativeSystemLoop.fuel_bound,
    ``SourceNativeSystemGroup.prepare_exec,
    ``SourceNativeSystemGroup.block_exec,
    ``SourceNativeSystemGroup.dimension_preserved,
    ``SourceNativeSystemGroup.constant_preserved,
    ``SourceNativeSystemGroup.stream_bound,
    ``SourceNativeSystemGroup.pending_empty,
    ``SourceNativeSystemGroup.polynomial_bound]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"NATIVE_SYSTEM_AXIOMS_GREEN: {names.length} theorems"

#print axioms PNP.Concrete.ResidualReduction.SourceNativeSystemHeader.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceNativeSystemRow.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceNativeSystemRow.canonical_product_result
#print axioms PNP.Concrete.ResidualReduction.SourceNativeSystemLoop.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceNativeSystemGroup.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceNativeSystemGroup.polynomial_bound

end PNP.Concrete.ResidualReduction.SourceNativeSystemRegression
