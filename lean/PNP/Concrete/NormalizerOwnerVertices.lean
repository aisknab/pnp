/-
Copyright (c) 2026 PNP Labs.

Reuse the fixed first-owner scanner for source-order variable positions.
Singleton entries may carry either tag: polarity does not participate in
index comparison. The contract covers arbitrary lists, duplicates and misses;
the scanner and its already-proved polynomial runtime are unchanged.
-/
import PNP.Concrete.NormalizerOwnerFrame
import PNP.Concrete.NormalizerVertexCanonical

namespace PNP.Concrete.NormalizerBlocks.TableOwner
open BitRegister Occurrence

def vertexOwnerFrom (index : Nat) (vertices : List CNFLiteral) (target : Nat) : Option Nat :=
  ownerFrom index (vertices.map (fun v => some v.variableIndex)) target

def vertexOwner (vertices : List CNFLiteral) (target : Nat) : Option Nat :=
  vertexOwnerFrom 0 vertices target

theorem tokenScan_tagged_entry (positive : Bool) (value target index : Nat)
    (rest : List CNFToken) (remaining excess sign : BitString) :
    (tokenScan (encodeClauseTokens [⟨positive,value⟩] ++ rest)
      (waiting target remaining excess sign (List.replicate index true))).output =
      if value == target then answer (some index)
      else (tokenScan rest (waiting target (List.replicate (target - value) true)
        (List.replicate (value - target) true) [positive]
        (List.replicate (index + 1) true))).output := by
  simp only [encodeClauseTokens, encodeLiteralListTokens, List.append_nil,
    List.cons_append, List.nil_append, List.append_assoc]
  change (tokenScan (encodeLiteralTokens ⟨positive,value⟩ ++ (.finish :: rest))
    (waiting target remaining excess sign (List.replicate index true))).output = _
  rw [tokenScan_literal]
  by_cases same : value = target
  · subst value
    have equal : (target == target) = true := by
      change decide (target = target) = true
      exact decide_eq_true rfl
    simp only [equal, ite_true, Nat.sub_self, counting, List.replicate_zero,
      tokenScan, tokenResult, foundState, answer]
  · have different : (value == target) = false := beq_eq_false_iff_ne.mpr same
    simp only [different, Bool.false_eq_true, ite_false]
    cases left : target - value with
    | zero =>
        cases right : value - target with
        | zero => exact False.elim (same (Nat.le_antisymm
            (Nat.le_of_sub_eq_zero right) (Nat.le_of_sub_eq_zero left)))
        | succ extra =>
            simp only [counting, List.replicate_zero, List.replicate_succ,
              tokenScan, tokenResult, waiting, afterEntry]
    | succ remainingCount =>
        have right : value - target = 0 := by
          apply Nat.sub_eq_zero_of_le
          apply Nat.le_of_lt
          apply Nat.lt_of_sub_pos
          rw [left]
          exact Nat.zero_lt_succ _
        simp only [right, counting, List.replicate_zero, List.replicate_succ,
          tokenScan, tokenResult, waiting, afterEntry]

theorem tokenScan_vertices_correct (vertices : List CNFLiteral) (target index : Nat)
    (remaining excess sign : BitString) :
    (tokenScan (encodeClauseListTokens (vertices.map (fun v => [v])) ++ [.finish])
      (waiting target remaining excess sign (List.replicate index true))).output =
        answer (vertexOwnerFrom index vertices target) := by
  induction vertices generalizing index remaining excess sign with
  | nil => rfl
  | cons vertex vertices ih =>
      cases vertex with
      | mk positive value =>
          simp only [List.map_cons, encodeClauseListTokens, List.append_assoc]
          rw [tokenScan_tagged_entry]
          cases found : (value == target)
          · simpa only [vertexOwnerFrom, List.map_cons, ownerFrom, found,
              Bool.false_eq_true, ite_false] using
              ih (index + 1) (List.replicate (target-value) true)
                (List.replicate (value-target) true) [positive]
          · simp only [vertexOwnerFrom, List.map_cons, ownerFrom, found, ite_true]

theorem prepared_vertices (target : Nat) (vertices : List CNFLiteral) :
    (queryResult (prepared (List.replicate target true)
      (SearchVertices.encodeVertices vertices))).state.output =
        answer (vertexOwner vertices target) := by
  let values := encodeClauseListTokens (vertices.map (fun v => [v])) ++ [.finish]
  let start := prepared (List.replicate target true) (SearchVertices.encodeVertices vertices)
  obtain ⟨fuel, canonical⟩ := tokenScan_exec values (waiting target [] [] [] [])
  have actual := query_exec start
  have same := NANDFrontend.accepted_store_unique (loop.program 0 8)
    _ _ ⟨.running 0, start.store⟩
    (queryResult start).state.store (tokenScan values (waiting target [] [] [] [])).store
    (actual.program_run 0 8) (canonical.program_run 0 8)
  exact (congrArg (fun store : Store 9 => store.get 8) same).trans
    (tokenScan_vertices_correct vertices target 0 [] [] [])

def encodeVertexQuery (target : Nat) (vertices : List CNFLiteral) : BitString :=
  List.replicate target true ++ false :: SearchVertices.encodeVertices vertices

theorem vertices_block_exec (target : Nat) (vertices : List CNFLiteral) :
    ∃ fuel, Exec block (initialRegisters (encodeVertexQuery target vertices)).store fuel
      (tokenScan (encodeClauseListTokens (vertices.map (fun v => [v])) ++ [.finish])
        (waiting target [] [] [] [])).store := by
  let values := encodeClauseListTokens (vertices.map (fun v => [v])) ++ [.finish]
  let input := encodeVertexQuery target vertices
  obtain ⟨fuel, scanned⟩ := tokenScan_exec values (waiting target [] [] [] [])
  have start : Exec initializeBlock (initialRegisters input).store 2 (seeded input).store :=
    Exec.seq (.action _ _) (.action _ _)
  have header : Exec headerLoop (seeded input).store (4 * target + 5)
      (Registers.store ⟨encodeTokenPairs values, List.replicate target true,
        [], [], [], [], [], [], [false]⟩) := by
    simpa only [seeded, input, encodeVertexQuery, SearchVertices.encodeVertices, values,
      List.replicate_zero, Nat.zero_add] using
      Occurrence.header_canonical target 0 (encodeTokenPairs values) [] [] [] [] [] [false]
  have activate : Exec (.action (.push 6 true))
      (Registers.store ⟨encodeTokenPairs values, List.replicate target true,
        [], [], [], [], [], [], [false]⟩) 1
      ({waiting target [] [] [] [] with input := encodeTokenPairs values}).store := .action _ _
  exact ⟨2 + ((4 * target + 5) + (1 + fuel)),
    Exec.seq start (Exec.seq header (Exec.seq activate scanned))⟩

theorem vertices_polynomial_canonical (target : Nat) (vertices : List CNFLiteral) :
    polynomial.output (encodeVertexQuery target vertices) =
      answer (vertexOwner vertices target) := by
  obtain ⟨fuel, checked⟩ := vertices_block_exec target vertices
  have canonical : BitRegister.run program (fuel + 1)
      (BitRegister.initial program (encodeVertexQuery target vertices)) =
        ⟨.accepted, (tokenScan
          (encodeClauseListTokens (vertices.map (fun v => [v])) ++ [.finish])
          (waiting target [] [] [] [])).store⟩ := by
    rw [initial_registers]
    exact checked.program_run 0 8
  have stores := NANDFrontend.accepted_store_unique program
    (sourceSteps (encodeVertexQuery target vertices) + 1) (fuel + 1)
    (BitRegister.initial program (encodeVertexQuery target vertices))
    (result (encodeVertexQuery target vertices)).state.store
    (tokenScan (encodeClauseListTokens (vertices.map (fun v => [v])) ++ [.finish])
      (waiting target [] [] [] [])).store
    (closed_run (encodeVertexQuery target vertices)) canonical
  rw [polynomial_output]
  exact (congrArg (fun store : Store 9 => store.get 8) stores).trans
    (tokenScan_vertices_correct vertices target 0 [] [] [])

private theorem output_projection (input : BitString) :
    polynomial.output input =
      machineOutput (CompilerIO.rawMachine program)
        ((CompilerIO.runtimePolynomial 9 sourceFuel).eval input.length) input := rfl

theorem vertices_machine_canonical (target : Nat) (vertices : List CNFLiteral) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 9 sourceFuel).eval
        (encodeVertexQuery target vertices).length)
      (encodeVertexQuery target vertices) = answer (vertexOwner vertices target) :=
  (output_projection (encodeVertexQuery target vertices)).symm.trans
    (vertices_polynomial_canonical target vertices)

end PNP.Concrete.NormalizerBlocks.TableOwner
