import PNP
import Lean.Util.CollectAxioms
import Lean.Elab.Command

namespace PNP.ThreeUse.Audit
open PNP.Concrete

example (bits : BitString) :
    CNFSAT bits ↔ finiteFeasible (targetRows bits) :=
  strict_finite bits

example (bits : BitString) :
    CNFSAT bits ↔ Encoding.ThreeUseSAT (Encoding.compile bits) :=
  Encoding.strict_restricted bits

example (bits : BitString) :
    CNFSAT bits ↔ ∃ w : BitString, w.length ≤ 144 * (bits.length + 1) ∧
      Encoding.verify (Encoding.compile bits) w = true :=
  Encoding.source_short_witness bits

example (bits : BitString) :
    (Encoding.compile bits).length ≤ 8000 * ((bits.length + 1) * (bits.length + 1)) :=
  Encoding.byte_bound bits

open Lean Elab Command

-- Select by the defining module, not just the public name prefix: internal
-- helper theorems and generated declarations belong to the audit as well.
run_cmd do
  let env ← getEnv
  let mut checked : NameSet := {}
  for (n, _) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    if env.header.moduleNames[i]!.toString.startsWith "PNP.ThreeUse." then
      checked := checked.insert n
      for ax in ← collectAxioms n do
        unless ax == ``propext || ax == ``Quot.sound do
          throwError "Unexpected axiom {ax} in three-use word-system declaration {n}"
  for n in [``matrix_mul, ``matrix_inv, ``gate_factor, ``macro_sound, ``macro_complete,
            ``split_lift, ``split_project, ``third_uses, ``original_replay, ``target_simple,
            ``strict_finite_three, ``Encoding.decode_iff, ``Encoding.reject_trailing,
            ``Encoding.slot_iff, ``Encoding.pack_restricted, ``Encoding.strict_restricted,
            ``Encoding.emitted_exact, ``Encoding.byte_bound, ``Encoding.source_encoded,
            ``Encoding.witness_spec, ``Encoding.witness_replay, ``Encoding.source_short_witness] do
    unless checked.contains n do throwError "Root did not bring in {n}"
  logInfo "THREE_USE_ROOT_AXIOMS_OK"

end PNP.ThreeUse.Audit
