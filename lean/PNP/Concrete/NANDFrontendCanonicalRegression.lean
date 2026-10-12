import PNP.Concrete.NANDFrontendCanonical

namespace PNP.Concrete.NANDFrontend

example (circuit : LockedNAND.RawCircuit) :
    polynomial.output (LockedNAND.encodeCircuit circuit) = circuitData circuit := polynomial_canonical circuit
example (circuit : LockedNAND.RawCircuit) :
    polynomial.output (LockedNAND.encodeCircuit circuit) =
      recordData circuit.inputCount (formula circuit) := polynomial_canonical circuit
example (circuit : LockedNAND.RawCircuit) :
    ∃ fuel store, BitRegister.run program fuel (BitRegister.initial program (LockedNAND.encodeCircuit circuit)) =
        ⟨.accepted, store⟩ ∧ store.get 8 = circuitData circuit := circuit_canonical_execution circuit

#print axioms circuit_header_encoding
#print axioms accepted_store_unique
#print axioms circuit_canonical_execution
#print axioms polynomial_canonical

end PNP.Concrete.NANDFrontend
