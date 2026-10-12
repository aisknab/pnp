/-
Copyright (c) 2026 PNP Labs.

Whole-list semantics for a bounded source row domain. The loop enumerates
every ordinal exactly once; source proofs identify its emitted packets.
-/
import PNP.Concrete.NormalizerSystemRowsList

namespace PNP.Concrete.NormalizerBlocks.SystemRows
open BitRegister Occurrence

theorem packetsFrom_finRange (packets : Nat → List BitString) (count start : Nat) :
    packetsFrom packets count start =
      (List.finRange count).flatMap (fun i => packets (start+i.val)) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      rw [packetsFrom,List.finRange_succ,List.flatMap_cons,List.flatMap_map,ih]
      change packets start ++ (List.finRange count).flatMap (fun i => packets (start+1+i.val)) =
        packets (start+0) ++ (List.finRange count).flatMap (fun i => packets (start+(i.val+1)))
      rw [Nat.add_zero]
      have point : (fun i : Fin count => packets (start+1+i.val)) =
          (fun i : Fin count => packets (start+(i.val+1))) := by
        funext i
        have index : start+1+i.val = start+(i.val+1) := by omega
        rw [index]
      simp only [point,Nat.add_zero]

theorem list_packets_from (iteration : Iteration) (ctx : Coefficient.Context)
    (packets : Nat → List BitString) (r : State) (encoded : ctx.Encoded r.core)
    (step : ∀ s index, ctx.Encoded s.core → s.counter = List.replicate index true →
      index < r.rows.length → Produced s (iteration.result s) (packets index)) :
    (listResult iteration r).registers.output =
      encodePackets (packetsFrom packets r.rows.length 0) := by
  have counter : (begun r).counter = List.replicate 0 true := rfl
  have within : 0+r.rows.length ≤ r.rows.length := by omega
  have all := scan_produced iteration ctx packets r.rows.length step
    r.rows (begun r) 0 encoded counter within
  exact list_packets iteration r _ all

theorem list_packets_finRange (iteration : Iteration) (ctx : Coefficient.Context)
    (packets : Nat → List BitString) (r : State) (encoded : ctx.Encoded r.core)
    (step : ∀ s index, ctx.Encoded s.core → s.counter = List.replicate index true →
      index < r.rows.length → Produced s (iteration.result s) (packets index)) :
    (listResult iteration r).registers.output =
      encodePackets ((List.finRange r.rows.length).flatMap (fun i => packets i.val)) := by
  rw [list_packets_from iteration ctx packets r encoded step,packetsFrom_finRange]
  simp only [Nat.zero_add]

end PNP.Concrete.NormalizerBlocks.SystemRows
