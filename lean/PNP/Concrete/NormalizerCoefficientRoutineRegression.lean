import PNP.Concrete.NormalizerCoefficientRoutine
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (a b : Coefficient.Routine) (r : Coefficient.State) :
    (Coefficient.Routine.seq a b).result r = b.result (a.result r) := rfl
example (a b : Coefficient.Routine) :
    (Coefficient.Routine.choose 8 a b).block = .branch 8 a.block a.block b.block := rfl
example (tag : Bool) : (Coefficient.emitAnswerRoutine tag).block = Coefficient.emitAnswer tag := rfl
#print axioms Coefficient.Routine.result_bounded
#print axioms Coefficient.Routine.seq
#print axioms Coefficient.Routine.choose
#print axioms Coefficient.Routine.seq_data
#print axioms Coefficient.Routine.choose_data
#print axioms Coefficient.queryRoutine
#print axioms Coefficient.ordinalRoutine
#print axioms Coefficient.emitIndexRoutine
#print axioms Coefficient.emitAnswerRoutine
end PNP.Concrete.NormalizerBlocks
