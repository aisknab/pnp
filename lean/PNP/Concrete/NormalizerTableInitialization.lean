/-
Copyright (c) 2026 PNP Labs.

Finite empty-table emission. The table size is consumed as a finite unary
word; each iteration emits one empty entry. The later closed wrapper reads
that word from the input and supplies the complete tape-runtime bound.
-/

import PNP.Concrete.NormalizerTableCanonical

namespace PNP.Concrete.NormalizerBlocks.TableInit

open BitRegister Occurrence

def emptyData : Nat → BitString
  | 0 => []
  | count + 1 => emptyData count ++ [false, true, true, false]

def step : Block 9 :=
  .seq (.action (.pop 1))
    (.seq (ClauseQuery.emit false true) (ClauseQuery.emit true false))

def loop : Block 9 := .loop 1 step

def built (word : BitString) (r : Registers) : Registers :=
  {r with target := [], excess := emptyData word.length ++ r.excess}

theorem loop_exec (word : BitString) (r : Registers) :
    Exec loop ({r with target := word}).store (6 * word.length + 1) (built word r).store := by
  induction word generalizing r with
  | nil => exact Exec.loopStop rfl
  | cons bit rest ih =>
      have body : Exec step ({r with target := bit :: rest}).store 5
          ({r with target := rest, excess := false :: true :: true :: false :: r.excess}).store :=
        Exec.seq (.action _ _) (Exec.seq (Exec.seq (.action _ _) (.action _ _))
          (Exec.seq (.action _ _) (.action _ _)))
      have tail := ih {r with excess := false :: true :: true :: false :: r.excess}
      have checked := Exec.loopStep (source := (1 : Fin 9)) (body := step)
        (before := ({r with target := bit :: rest}).store) rfl body tail
      have cost : 6 * (bit :: rest).length + 1 = 1 + (5 + (6 * rest.length + 1)) := by
        simp only [List.length_cons]
        omega
      rw [cost]
      simpa only [loop, built, List.length_cons, emptyData,
        List.append_assoc, List.cons_append, List.nil_append] using checked

theorem emptyData_length (count : Nat) : (emptyData count).length = 4 * count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [emptyData, List.length_append, List.length_cons, List.length_nil, ih]
      omega

theorem emptyData_encoding (count : Nat) :
    (encodeTokenPairs (encodeClauseListTokens (MatchingTable.clauses (List.replicate count none)))).reverse =
      emptyData count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [List.replicate_succ, MatchingTable.clauses, List.map_cons,
        MatchingTable.entryClause, encodeClauseListTokens, encodeClauseTokens, encodeLiteralListTokens,
        NANDFrontend.encodeTokenPairs_append, encodeTokenPairs, CNFToken.bits, List.nil_append,
        List.reverse_append, List.reverse_cons, List.reverse_nil, List.cons_append, emptyData,
        List.append_assoc] using
        congrArg (fun bits : BitString => bits ++ [false, true, true, false]) ih

theorem built_input (word : BitString) (r : Registers) : (built word r).input = r.input := rfl
theorem built_target (word : BitString) (r : Registers) : (built word r).target = [] := rfl

end PNP.Concrete.NormalizerBlocks.TableInit
