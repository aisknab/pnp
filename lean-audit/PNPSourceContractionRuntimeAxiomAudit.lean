import PNP

/-! Assumption transcript for the polynomial source-construction and witness-replay
endpoints. The explicit root already imports the independent kernel contracts
and physical component regressions; this audit does not rerun those suites. -/

#print axioms PNP.Concrete.ResidualReduction.SourceReductionRuntime.recover_certificate
#print axioms PNP.Concrete.ResidualReduction.SourceReductionRuntime.recover_certificate_runtime
#print axioms PNP.Concrete.ResidualReduction.SourceReductionRuntime.recovery_output
#print axioms PNP.Concrete.ResidualReduction.SourceReductionRuntime.replay_halts
#print axioms PNP.Concrete.ResidualReduction.SourceReductionRuntime.replay_output
#print axioms PNP.Concrete.ResidualReduction.SourceReductionRuntime.replay_output_size
#print axioms PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_halts
#print axioms PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_output
#print axioms PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_output_size
#print axioms PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_satisfiability
#print axioms PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_system_output
#print axioms PNP.Concrete.ResidualReduction.SourceReductionRuntime.unresolved_remains_unknown
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointBudget.native_project_run
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointGenerated.project_recover_model
