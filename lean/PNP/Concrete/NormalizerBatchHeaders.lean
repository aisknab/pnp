/-
Copyright (c) 2026 PNP Labs.

Raw header progress and scratch-frame facts needed by the uniform update
driver. A live read consumes at least one bit of nonempty input. This is
independent of canonical well-formedness and prevents malformed update loops.
-/

import PNP.Concrete.NormalizerTableGrowth

namespace PNP.Concrete.NormalizerBlocks

open Occurrence

theorem Occurrence.header_excess (input : BitString) (r : Registers) :
    (headerResult input r).state.excess = r.excess := by
  induction input generalizing r with
  | nil =>
      cases active : r.active <;> simp only [headerResult, active]
  | cons bit rest ih =>
      cases active : r.active with
      | nil => cases bit <;> simp only [headerResult, active]
      | cons head tail =>
          cases bit
          · simp only [headerResult, active]
          · simpa only [headerResult, active] using ih {r with target := true :: r.target}

theorem Occurrence.header_input_strict (input : BitString) (r : Registers)
    (live : r.active ≠ []) (nonempty : input ≠ []) :
    (headerResult input r).state.input.length < input.length := by
  cases input with
  | nil => exact False.elim (nonempty rfl)
  | cons bit rest =>
      cases active : r.active with
      | nil => exact False.elim (live active)
      | cons head tail =>
          cases bit
          · simp only [headerResult, active, List.length_cons]
            omega
          · have bound := header_input_bound rest {r with target := true :: r.target}
            simpa only [headerResult, active, List.length_cons] using Nat.lt_succ_of_le bound

theorem TableWrite.prepared_excess (input : BitString) : (TableWrite.prepared input).excess = [] := by
  have first := Occurrence.header_excess input (TableWrite.seeded input)
  have second := Occurrence.header_excess (TableWrite.readIndex input).state.input
    (ClauseQuery.saved (TableWrite.readIndex input).state)
  exact second.trans first

theorem TableWrite.prepared_input_strict (input : BitString) (nonempty : input ≠ []) :
    (TableWrite.prepared input).input.length < input.length := by
  have first : (TableWrite.readIndex input).state.input.length < input.length :=
    Occurrence.header_input_strict input (TableWrite.seeded input) (by intro bad; cases bad) nonempty
  have second : (TableWrite.readValue input).state.input.length ≤ (TableWrite.readIndex input).state.input.length :=
    Occurrence.header_input_bound (TableWrite.readIndex input).state.input
      (ClauseQuery.saved (TableWrite.readIndex input).state)
  exact Nat.lt_of_le_of_lt second first

end PNP.Concrete.NormalizerBlocks
