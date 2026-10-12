import PNP.Concrete.NormalizerRecoveryCall
namespace PNP.Concrete.NormalizerBlocks
example (r : Recovery.State) : (Recovery.started r).counter = [] := rfl
example (r : Recovery.State) : (Recovery.started r).buffer = [] := rfl
example (r : Recovery.State) : (Recovery.finished r).core.output = r.buffer.reverse := rfl
#print axioms Recovery.scan_buffer
#print axioms Recovery.start_exec
#print axioms Recovery.front_exec
#print axioms Recovery.finish_exec
#print axioms Recovery.call_exec
#print axioms Recovery.called_data
#print axioms Recovery.called_output_length
#print axioms Recovery.called_canonical
#print axioms Recovery.callSteps_bound
end PNP.Concrete.NormalizerBlocks
