import PNP.Concrete.NormalizerPathScan
namespace PNP.Concrete.NormalizerBlocks
def pathScanFixture (trace : List TraceData.Row) : TracePath.State :=
  ⟨{ParentQuery.initial [] with pending := TraceData.encode trace, targetIndex := [true], targetTag := [false], output := [false]}, [], []⟩
example : (TracePath.whole (pathScanFixture [(⟨false, 1⟩, some ⟨true, 0⟩), (⟨true, 0⟩, none)])).state.core.output = [true] := by decide
example : (TracePath.whole (pathScanFixture [(⟨false, 1⟩, some ⟨true, 0⟩)])).state.core.output = [false] := by decide
example : (TracePath.whole (pathScanFixture [(⟨true, 0⟩, none), (⟨false, 1⟩, some ⟨true, 0⟩)])).state.core.output = [false] := by decide
example : (TracePath.whole (pathScanFixture [(⟨false, 1⟩, some ⟨false, 1⟩)])).state.core.pending = [] := by decide
#print axioms TracePath.body_shorter
#print axioms TracePath.scan_exec
#print axioms TracePath.scan_fuel_bound
#print axioms TracePath.scan_stopped
#print axioms TracePath.scan_preserves
#print axioms TracePath.whole_exec
#print axioms TracePath.whole_fuel_bound
#print axioms TracePath.whole_stopped
end PNP.Concrete.NormalizerBlocks
