import PNP
import Lean

/-! Root-context checks for the signed ternary matrix representation of strict CNFSAT.
Signed input and output must share one word. Neither polynomial running time nor
deterministic CNFSAT membership follows from the output-length bound. -/

namespace PNP.SignedTernary.Audit

open PNP.Concrete PNP.SignedTernary.Field PNP.SignedTernary.Linear
open PNP.SignedTernary.Codec PNP.SignedTernary.Encoding

example (raw : BitString) : MatrixSAT (encodeCNFMatrix raw) ↔ CNFSAT raw :=
  matrixSAT_encodeCNFMatrix_iff raw

example (bits : BitString) : MatrixSAT bits ↔
    ∃ A : Square, unpack bits = some A ∧
      ∃ x : Vec A.1, Signed x ∧ Signed (applyRows A.2 x) := Iff.rfl

example (raw : BitString) :
    unpack (encodeCNFMatrix raw) = some ⟨dimension raw, encodedMatrix raw⟩ :=
  canonical_unpack raw

example (raw : BitString) :
    (encodeCNFMatrix raw).length ≤
      (13*raw.length+30)+1+2*((13*raw.length+30)*(13*raw.length+30)) :=
  canonical_quadratic_bound raw

open Lean Elab Command

-- Check by defining module, so private names and compiler-generated
-- auxiliaries do not escape via a different declaration-name prefix.
run_cmd do
  let env ← getEnv
  -- Generated equations are attributed on first import. The new research
  -- modules must not take ownership of these existing concrete CNF facts.
  for n in [`PNP.Concrete.assignmentAt.eq_1, `PNP.Concrete.checkClause.eq_1,
            `PNP.Concrete.checkClause.eq_2, `PNP.Concrete.encodeCNFTokens.eq_1] do
    let some i := env.getModuleIdxFor? n | throwError "Missing existing equation {n}"
    unless env.header.moduleNames[i]!.toString.startsWith "PNP.Concrete." do
      throwError "The signed matrix import reassigned existing concrete equation {n}"
  let mut checked : NameSet := {}
  for (n, _) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    if env.header.moduleNames[i]!.toString.startsWith "PNP.SignedTernary." then
      checked := checked.insert n
      for a in ← collectAxioms n do
        unless a == ``propext || a == ``Quot.sound do
          throwError "Unexpected axiom {a} in signed matrix declaration {n}"
  for n in [``matrixSAT_encodeCNFMatrix_iff, ``canonical_unpack, ``canonical_quadratic_bound,
            ``physicalMatrix_entry, ``physicalMatrix_apply, ``basis_samples_alone_fail,
            ``PNP.SignedTernary.Network.marked_norm, ``PNP.SignedTernary.CNF.raw_iff_CNFSAT] do
    unless checked.contains n do throwError "Root did not bring in {n}"
  logInfo "SIGNED_TERNARY_MATRIX_ROOT_AXIOMS_OK"

end PNP.SignedTernary.Audit
