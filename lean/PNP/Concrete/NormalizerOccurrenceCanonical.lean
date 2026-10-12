/-
Copyright (c) 2026 PNP Labs.

End-to-end correctness of the concrete occurrence query on every canonical
target/clause encoding. The input header is read by the machine itself.
No semantic incidence predicate, successful run, or correctness certificate
is supplied to the executable polynomial-time query.
-/

import PNP.Concrete.NormalizerOccurrenceSemantics
import PNP.Concrete.NANDFrontendCanonical

namespace PNP.Concrete.NormalizerBlocks.Occurrence

open BitRegister

theorem header_canonical (count initialTarget : Nat) (suffix : BitString)
    (remaining excess sign mode reserved output : BitString) :
    Exec headerLoop
      (Registers.store ⟨List.replicate count true ++ false :: suffix, List.replicate initialTarget true,
        remaining, excess, sign, mode, [true], reserved, output⟩)
      (4 * count + 5)
      (Registers.store ⟨suffix, List.replicate (initialTarget + count) true,
        remaining, excess, sign, mode, [], reserved, output⟩) := by
  induction count generalizing initialTarget with
  | zero =>
      simp only [List.replicate_zero, List.nil_append, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
      exact Exec.loopStep (source := (6 : Fin 9)) (body := headerBody)
        (before := Registers.store ⟨false :: suffix, List.replicate initialTarget true,
          remaining, excess, sign, mode, [true], reserved, output⟩)
        rfl (header_false_exec
          ⟨[], List.replicate initialTarget true, remaining, excess, sign, mode, [true], reserved, output⟩ suffix)
        (Exec.loopStop rfl)
  | succ count ih =>
      have next := ih (initialTarget + 1)
      have sum : initialTarget + 1 + count = initialTarget + (count + 1) := by omega
      rw [sum] at next
      have step := Exec.loopStep (source := (6 : Fin 9)) (body := headerBody)
        (before := Registers.store ⟨true :: (List.replicate count true ++ false :: suffix),
          List.replicate initialTarget true, remaining, excess, sign, mode, [true], reserved, output⟩)
        rfl (header_true_exec
          ⟨[], List.replicate initialTarget true, remaining, excess, sign, mode, [true], reserved, output⟩
          (List.replicate count true ++ false :: suffix))
        (by simpa only [headerLoop, List.replicate_succ] using next)
      have cost : 4 * (count + 1) + 5 = 1 + (3 + (4 * count + 5)) := by omega
      simpa only [headerLoop, List.replicate_succ, List.cons_append, cost] using step

theorem canonical_block_exec (target : Nat) (clause : List CNFLiteral) :
    ∃ fuel, Exec block (initialRegisters (encodeQuery target clause)).store fuel
      (tokenScan (encodeLiteralListTokens clause ++ [.finish]) (waiting target [] [] [] [])).store := by
  let values := encodeLiteralListTokens clause ++ [.finish]
  let input := encodeQuery target clause
  obtain ⟨fuel, scanned⟩ := tokenScan_exec values (waiting target [] [] [] [])
  have start : Exec initializeBlock (initialRegisters input).store 2 (seeded input).store :=
    Exec.seq (.action _ _) (.action _ _)
  have header : Exec headerLoop (seeded input).store (4 * target + 5)
      (Registers.store ⟨encodeTokenPairs values, List.replicate target true,
        [], [], [], [], [], [], [false]⟩) := by
    simpa only [seeded, input, encodeQuery, values, List.replicate_zero, Nat.zero_add] using
      header_canonical target 0 (encodeTokenPairs values) [] [] [] [] [] [false]
  have activate : Exec (.action (.push 6 true))
      (Registers.store ⟨encodeTokenPairs values, List.replicate target true,
        [], [], [], [], [], [], [false]⟩) 1
      ({waiting target [] [] [] [] with input := encodeTokenPairs values}).store := .action _ _
  exact ⟨2 + ((4 * target + 5) + (1 + fuel)),
    Exec.seq start (Exec.seq header (Exec.seq activate scanned))⟩

theorem polynomial_canonical (target : Nat) (clause : List CNFLiteral) :
    polynomial.output (encodeQuery target clause) =
      answer (clause.find? (fun literal => literal.variableIndex == target)) := by
  obtain ⟨fuel, checked⟩ := canonical_block_exec target clause
  have canonical : BitRegister.run program (fuel + 1)
      (BitRegister.initial program (encodeQuery target clause)) =
        ⟨.accepted, (tokenScan (encodeLiteralListTokens clause ++ [.finish])
          (waiting target [] [] [] [])).store⟩ := by
    rw [initial_registers]
    exact checked.program_run 0 8
  have stores := NANDFrontend.accepted_store_unique program
    (sourceSteps (encodeQuery target clause) + 1) (fuel + 1)
    (BitRegister.initial program (encodeQuery target clause))
    (result (encodeQuery target clause)).state.store
    (tokenScan (encodeLiteralListTokens clause ++ [.finish]) (waiting target [] [] [] [])).store
    (closed_run (encodeQuery target clause)) canonical
  rw [polynomial_output]
  exact (congrArg (fun store : Store 9 => store.get 8) stores).trans
    (tokenScan_clause_correct clause target [] [] [] [])

private theorem output_projection (input : BitString) :
    polynomial.output input =
      machineOutput (CompilerIO.rawMachine program)
        ((CompilerIO.runtimePolynomial 9 sourceFuel).eval input.length) input := rfl

theorem machine_canonical (target : Nat) (clause : List CNFLiteral) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 9 sourceFuel).eval (encodeQuery target clause).length)
      (encodeQuery target clause) =
        answer (clause.find? (fun literal => literal.variableIndex == target)) :=
  (output_projection (encodeQuery target clause)).symm.trans (polynomial_canonical target clause)

theorem polynomial_canonical_length (target : Nat) (clause : List CNFLiteral) :
    (polynomial.output (encodeQuery target clause)).length ≤ 2 := by
  rw [polynomial_canonical]
  cases clause.find? (fun literal => literal.variableIndex == target) <;>
    simp only [answer, List.length_cons, List.length_nil] <;> decide

end PNP.Concrete.NormalizerBlocks.Occurrence
