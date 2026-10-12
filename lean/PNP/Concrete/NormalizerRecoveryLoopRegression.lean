import PNP.Concrete.NormalizerRecoveryLoop
namespace PNP.Concrete.NormalizerBlocks
example (r : Recovery.State) : (Recovery.scan [] r).fuel = 1 := rfl
example (r : Recovery.State) : (Recovery.advanced r).counter = true::r.counter := rfl
example (r : Recovery.State) : (Recovery.advanced r).remaining = r.remaining.tail := rfl
#print axioms Recovery.appendBit_exec
#print axioms Recovery.body_exec
#print axioms Recovery.body_fields
#print axioms Recovery.body_buffer
#print axioms Recovery.bodyFuel_bound
#print axioms Recovery.scan_exec
#print axioms Recovery.scan_fields
#print axioms Recovery.scan_counter
#print axioms Recovery.scan_buffer_length
#print axioms Recovery.scan_fuel_bound
#print axioms Recovery.whole_exec
#print axioms Recovery.whole_fuel_bound
end PNP.Concrete.NormalizerBlocks
