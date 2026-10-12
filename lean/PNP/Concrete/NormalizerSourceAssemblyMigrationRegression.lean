import PNP.Concrete.NormalizerSourceAssemblyMigration
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example : (TableOwner.answer (some 0)).tail = [] := rfl
example : (TableOwner.answer (some 0)).headD false = true ∧
    (TableOwner.answer none).headD false = false := ⟨rfl,rfl⟩
example (r : CutDriver.State) :
    (SourceAssembly.migrated (SourceAssembly.extended r)).recovery = SourceAssembly.recovery r :=
  SourceAssembly.migrated_source_recovery r
#print axioms SourceAssembly.migrate_exec
#print axioms SourceAssembly.migrated_data
#print axioms SourceAssembly.migrated_frame
#print axioms SourceAssembly.migrated_output
#print axioms SourceAssembly.migrated_bounded
#print axioms SourceAssembly.migrated_source_data
#print axioms SourceAssembly.migrated_source_rows
#print axioms SourceAssembly.migrated_source_recovery
end PNP.Concrete.NormalizerBlocks
