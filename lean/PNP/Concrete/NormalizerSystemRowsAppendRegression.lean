import PNP.Concrete.NormalizerSystemRowsAppend
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : SystemRows.State) :
    (SystemRows.appended r).buffer = r.registers.output.reverse ++ r.buffer := rfl
example (routine : Coefficient.Routine) (r : SystemRows.State) (n : Nat)
    (fixed : r.shared.Bounded n) (index : r.counter.length ≤ n) :
    SystemRows.emitFuel routine r ≤ 4*n + 5*routine.bound.eval n + 24 :=
  SystemRows.emitFuel_bound routine r n fixed index
example (routine : Coefficient.Routine) (r : SystemRows.State) (n : Nat)
    (fixed : r.shared.Bounded n) (index : r.counter.length ≤ n) :
    (SystemRows.emitted routine r).buffer.length ≤ n + routine.bound.eval n + r.buffer.length :=
  SystemRows.emitted_buffer_length routine r n fixed index
#print axioms SystemRows.prepareAppend_exec
#print axioms SystemRows.saveAppend_exec
#print axioms SystemRows.append_exec
#print axioms SystemRows.appended_shared
#print axioms SystemRows.emit_exec
#print axioms SystemRows.emitted_shared
#print axioms SystemRows.emitFuel_bound
#print axioms SystemRows.emitted_buffer_length
end PNP.Concrete.NormalizerBlocks
