import PNP.NANDGuardedSpineSupportMinimum

set_option autoImplicit false
set_option Elab.async false

/-! For every fixed window limit, a source-derived nonminimum circuit is
quiet under the complete arbitrary-support search. This excludes a fixed
circuit-independent limit as a global-minimum certificate, not other routes. -/

namespace PNP.DirectWire.GuardedSpineBoundedQuiet
open GuardedSpineFamily (candidate shorter)
open BoundedWindowSchedule (BoundedQuiet scan windowsFrom)

private theorem fully_selected_count {gates : Nat} (selected : Fin gates → Bool)
    (every : ∀ node, selected node = true) :
    (terminalSelectedGateIndices selected).length = gates := by
  induction gates with
  | zero => rfl
  | succ gates ih =>
      have prior := ih (fun node => selected node.castSucc) (fun node => every node.castSucc)
      simp only [terminalSelectedGateIndices,every (Fin.last gates),if_true,
        List.length_append,List.length_map,List.length_cons,List.length_nil]
      omega

theorem proper_of_small_support {width : Nat} (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 width))
    (small : (extractTerminalSupport (candidate n) records).gateCount < n + 2) :
    ∃ node, terminalGateSelected records node = false := by
  by_cases proper : ∃ node, terminalGateSelected records node = false
  · exact proper
  · exfalso
    have every : ∀ node, terminalGateSelected records node = true := by
      intro node
      cases selected : terminalGateSelected records node with
      | false => exact False.elim (proper ⟨node,selected⟩)
      | true => rfl
    have count := fully_selected_count (terminalGateSelected records) every
    rw [extractTerminalSupport_gateCount] at small
    change (terminalSelectedGateIndices (terminalGateSelected records)).length < n + 2 at small
    omega

/-- All record widths and all supports within the cap, not only intervals or
the canonical schedule representation. No causal premise is used for minimality. -/
theorem bounded_quiet (n limit : Nat) (below : limit < n + 2) :
    BoundedQuiet (candidate n) limit := by
  intro width records bounded offered valid
  have proper := proper_of_small_support n records (Nat.lt_of_le_of_lt bounded below)
  have lower := GuardedSpineSupportMinimum.proper_minimum n records proper
    offered.gateCount offered.candidate.program offered.candidate.directWireWord valid.2.1
  have smaller := valid.1
  omega

/-- The actual complete scheduled search returns no replacement. This is
proved symbolically; the exponentially large finite search is not executed. -/
theorem scan_none (n limit : Nat) (below : limit < n + 2) :
    scan (candidate n) (windowsFrom (n + 2) limit 0) = none :=
  (BoundedWindowSchedule.scan_schedule_none_iff (candidate n) limit).mpr
    (bounded_quiet n limit below)

/-- Uniform strict gain and positive residual coexist with arbitrary-support
bounded quietness for every fixed limit. -/
theorem quiet_with_strict_gain (limit : Nat) :
    BoundedQuiet (candidate (limit + 2)) limit ∧
      StrictEquivalentGain (candidate (limit + 2)).toImplementation (shorter limit).toImplementation ∧
      0 < residualSlack (candidate (limit + 2)).toImplementation :=
  ⟨bounded_quiet (limit + 2) limit (by omega),
    GuardedSpineFamily.strict_gain limit,GuardedSpineFamily.residual_positive limit⟩

theorem quiet_nonminimum_exists (limit : Nat) :
    ∃ source : Candidate (limit + 3) (limit + 4) 1,
      BoundedQuiet source limit ∧ 0 < residualSlack source.toImplementation := by
  exact ⟨candidate (limit + 2),(quiet_with_strict_gain limit).1,
    (quiet_with_strict_gain limit).2.2⟩

/-- No fixed circuit-independent support cap turns this exact local silence
condition into global zero slack. Growing windows or other routes are not excluded. -/
theorem no_uniform_zero_slack_limit :
    ¬ ∃ limit : Nat, ∀ (inputs gates outputs : Nat) (source : Candidate inputs gates outputs),
      BoundedQuiet source limit → residualSlack source.toImplementation = 0 := by
  rintro ⟨limit,complete⟩
  obtain ⟨source,quiet,positive⟩ := quiet_nonminimum_exists limit
  have zero := complete (limit + 3) (limit + 4) 1 source quiet
  omega

end PNP.DirectWire.GuardedSpineBoundedQuiet
