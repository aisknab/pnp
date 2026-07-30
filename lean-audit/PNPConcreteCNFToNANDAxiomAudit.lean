import PNP.Concrete.CNFToNAND

/-! Reused exact CNF, NAND, codec, polynomial, and locked-threshold
interfaces. -/

#print axioms PNP.Concrete.CNFFormula
#print axioms PNP.Concrete.CNFFormula.Satisfied
#print axioms PNP.Concrete.CNFFormula.Satisfiable
#print axioms PNP.Concrete.CNFSAT
#print axioms PNP.Concrete.encodeCNF
#print axioms PNP.Concrete.decodeEncodedCNF
#print axioms PNP.Concrete.decodeEncodedCNF_canonical
#print axioms PNP.Concrete.checkCNF_eq_true_iff
#print axioms PNP.Concrete.LockedNAND.RawCircuit
#print axioms PNP.Concrete.LockedNAND.encodeCircuit
#print axioms PNP.Concrete.LockedNAND.decodeValidCircuit
#print axioms PNP.Concrete.LockedNAND.EncodedNANDSAT
#print axioms PNP.Concrete.LockedNAND.EncodedLockedNANDThreshold
#print axioms PNP.Concrete.LockedNAND.buildLockedNANDInstance
#print axioms PNP.Concrete.LockedNAND.buildLockedNANDInstance_correct
#print axioms PNP.Concrete.NatPolynomial

/-! Complete transcript for the new public semantic compiler package. -/

#print axioms PNP.Concrete.CNFToNAND.literalCount
#print axioms PNP.Concrete.CNFToNAND.validNegativeLiteralCount
#print axioms PNP.Concrete.CNFToNAND.encodeCNF_of_decodeEncodedCNF
#print axioms PNP.Concrete.CNFToNAND.compiledFormulaCircuit
#print axioms PNP.Concrete.CNFToNAND.compileFormula
#print axioms PNP.Concrete.CNFToNAND.compileFormula_inputCount
#print axioms PNP.Concrete.CNFToNAND.compileFormula_output_is_gate
#print axioms PNP.Concrete.CNFToNAND.compileFormula_wellFormed
#print axioms PNP.Concrete.CNFToNAND.decodeValidCircuit_encode_compileFormula
#print axioms PNP.Concrete.CNFToNAND.compiledFormulaCircuit_eval_eq_true_iff
#print axioms PNP.Concrete.CNFToNAND.compiledFormulaCircuit_satisfiable_iff
#print axioms PNP.Concrete.CNFToNAND.compileFormula_satisfiable_iff
#print axioms PNP.Concrete.CNFToNAND.formula_satisfiable_iff_encoded_compileFormula
#print axioms PNP.Concrete.CNFToNAND.compileFormula_gateCount_exact
#print axioms PNP.Concrete.CNFToNAND.compileFormula_gateCount_le
#print axioms PNP.Concrete.CNFToNAND.cnfToNANDOutputSizePolynomial
#print axioms PNP.Concrete.CNFToNAND.cnfToNANDOutputSizePolynomial_eval
#print axioms PNP.Concrete.CNFToNAND.compileEncodedCNFToNAND
#print axioms PNP.Concrete.CNFToNAND.compileEncodedCNFToNAND_of_decoded
#print axioms PNP.Concrete.CNFToNAND.compileEncodedCNFToNAND_of_malformed
#print axioms PNP.Concrete.CNFToNAND.compileEncodedCNFToNAND_size_le
#print axioms PNP.Concrete.CNFToNAND.empty_not_encodedNANDSAT
#print axioms PNP.Concrete.CNFToNAND.compileEncodedCNFToNAND_correct
#print axioms PNP.Concrete.CNFToNAND.buildLockedNANDFromCNF
#print axioms PNP.Concrete.CNFToNAND.buildLockedNANDFromCNF_correct
