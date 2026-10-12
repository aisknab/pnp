import PNP.Concrete.NormalizerSeenScan
namespace PNP.Concrete.NormalizerBlocks
def seenScanFixture (trace : List TraceData.Row) : SeenTrace.State :=
  ⟨{ParentQuery.initial [] with pending := TraceData.encode trace}, [], []⟩
example : (SeenTrace.whole (seenScanFixture [])).state.buffer = [] := by decide
example : (SeenTrace.whole (seenScanFixture [(⟨true, 0⟩, some ⟨false, 7⟩), (⟨false, 2⟩, none)])).state.buffer = (SeenTrace.bytes [none, some 2]).reverse := by decide
example : (SeenTrace.whole (seenScanFixture [(⟨false, 2⟩, none), (⟨false, 1⟩, none)])).state.core.pending = [] := by decide
#print axioms SeenTrace.scan_exec
#print axioms SeenTrace.scan_fuel_bound
#print axioms SeenTrace.scan_stopped
#print axioms SeenTrace.scan_preserves
#print axioms SeenTrace.whole_exec
#print axioms SeenTrace.whole_fuel_bound
#print axioms SeenTrace.whole_stopped
end PNP.Concrete.NormalizerBlocks
