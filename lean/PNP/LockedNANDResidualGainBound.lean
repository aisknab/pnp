/-
Copyright (c) 2026 PNP Labs.

The universal gain-chain bound specialized to the answer-independent locked
NAND candidate.  The existing global semantic theorem supplies residual slack
at most four; this module does not supply a gain generator, route completeness,
ZeroSlack, exact minimization, or a polynomial runtime for the chain checker.
-/

import PNP.ResidualGainChain
import PNP.LockedNANDGlobalSemanticThreshold

namespace PNP
namespace DirectWire
namespace LockedNANDGlobalCandidates

open LockedNANDTrace

/-- The complete locked candidate with its static gate index existentially
    packaged as an implementation. -/
def fullCandidateImplementation {inputs : Nat} (circuit : Circuit inputs) :
    Implementation (carrierWidth inputs circuit.gateCount)
      (lockedBaselineCount circuit.program + 1) :=
  (fullCandidate circuit).toImplementation

/-- The packaged complete locked candidate inherits the manuscript's
    four-gate residual band. -/
theorem fullCandidateImplementation_residualSlack_le_four
    {inputs : Nat} (circuit : Circuit inputs) :
    residualSlack (fullCandidateImplementation circuit) ≤ 4 :=
  fullCandidate_residualSlack_le_four circuit

/-- Every proof-bearing strict-gain chain from a locked candidate has at most
    four steps. -/
theorem fullCandidate_strictGainChain_length_le_four
    {inputs : Nat} (circuit : Circuit inputs)
    {chain : List
      (Implementation (carrierWidth inputs circuit.gateCount)
        (lockedBaselineCount circuit.program + 1))}
    (valid : StrictGainChain (fullCandidateImplementation circuit) chain) :
    chain.length ≤ 4 :=
  Nat.le_trans valid.length_le_residualSlack
    (fullCandidateImplementation_residualSlack_le_four circuit)

/-- The executable chain checker accepts at most four gains from every locked
    candidate. -/
theorem fullCandidate_strictGainChainBool_length_le_four
    {inputs : Nat} (circuit : Circuit inputs)
    {chain : List
      (Implementation (carrierWidth inputs circuit.gateCount)
        (lockedBaselineCount circuit.program + 1))}
    (checked :
      strictGainChainBool (fullCandidateImplementation circuit) chain = true) :
    chain.length ≤ 4 :=
  Nat.le_trans (strictGainChainBool_length_le_residualSlack checked)
    (fullCandidateImplementation_residualSlack_le_four circuit)

end LockedNANDGlobalCandidates
end DirectWire
end PNP
