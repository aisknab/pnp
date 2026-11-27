import PNP
import Lean.Util.CollectAxioms
import Lean.Elab.Command

namespace PNP.ClauseSquare.Audit

open PNP.Concrete

example (bits : BitString) :
    CNFSAT bits ↔ ∃ a : Nat, NumberedKernel (compile bits) a :=
  strict_all_numbered bits

example (bits w : BitString) :
    (∃ F, decodeEncodedCNF bits = some F ∧ F.Satisfied w) ↔
      ∃ a : Nat, NumberedKernel (compile bits) a ∧
        SignedTernary.CNF.readWord (compile bits).n (numberedHead (compile bits).n a) = w :=
  strict_same_mask_word bits w

example (b : Raw) (x : Head b.n) : MaskWitness b x ↔
    ∃ z : Nat, z ≠ 0 ∧ z < 2^b.d ∧ action b x z = 0 := Iff.rfl

example (bits : BitString) :
    CNFSAT bits ↔ Framed.accept (Framed.emit bits) = true :=
  Framed.strict_iff_target bits

example (bits : BitString) :
    (Framed.emit bits).length ≤ (bits.length+1)^3 + 2*bits.length + 3 :=
  Framed.emit_length bits

open Lean Elab Command

-- Scan by defining module, including private names and compiler auxiliaries.
run_cmd do
  let env ← getEnv
  let mut checked : NameSet := {}
  for (n, _) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    if env.header.moduleNames[i]!.toString.startsWith "PNP.ClauseSquare." then
      checked := checked.insert n
      for ax in ← collectAxioms n do
        unless ax == ``propext || ax == ``Quot.sound do
          throwError "Unexpected axiom {ax} in affine square declaration {n}"
  for n in [``strict_all_numbered, ``strict_same_mask_word, ``only_nonzero_witness,
            ``prefix_exact, ``reject_singleton, ``chosen_bit, ``action_zero,
            ``exact_dimension, ``raw_column_bound, ``EncodedCost.accepted_length,
            ``EncodedCost.payload_bit, ``EncodedCost.exact_payload_length,
            ``EncodedCost.payload_polynomial, ``Framed.strict_iff_target,
            ``Framed.strict_same_word, ``Framed.decode_emit, ``Framed.decode_trailing,
            ``Framed.product_row, ``Framed.emit_length, ``Framed.target_characterization] do
    unless checked.contains n do throwError "Root did not bring in {n}"
  logInfo "CLAUSE_SQUARE_ROOT_AXIOMS_OK"

end PNP.ClauseSquare.Audit
