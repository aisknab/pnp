# Uniform bounded verifier tableaux

`PNP.Concrete.CookLevinVerifierTableau` lifts the fixed-certificate semantic
trace to an arbitrary proof-bearing verifier in the concrete NP model.

For one source input, the layer:

- recursively compiles the verifier's complete finite decision pipeline to
  one raw finite machine;
- preserves the verifier's `inputOnly` or canonical `paired` input convention;
- bounds every encoded input using the explicit certificate polynomial;
- evaluates the compiled raw time polynomial at that maximum size to obtain
  one answer-independent fuel budget shared by all bounded certificates;
- proves the per-certificate raw budget is below the shared budget;
- pads only after a proved designated halt, preserving the exact verifier
  verdict rather than treating timeout as rejection; and
- proves `VerifierTableauProblem.language_iff_exists_acceptingTableau`, which
  is the exact equivalence between concrete verifier membership and an
  existential bounded certificate with a valid accepting semantic tableau.

The complete 41-declaration kernel audit has empty axiom closure.  The shared
dimensions and variable layout are explicit, but this layer does not encode a
configuration, transition window, or certificate as Boolean clauses.  It does
not emit CNF, prove an output/runtime polynomial for an emitter, define a
polynomial reduction, prove CNFSAT NP-complete or in P, or establish P = NP.
The concrete publication gate remains false.
