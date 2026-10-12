import PNP.Concrete.NormalizerCacheLiteralScan
namespace PNP.Concrete.NormalizerBlocks
example (r : CacheLiteral.State) :
    (CacheLiteral.skipped [] r).core.pending = r.core.pending := rfl
example (r : CacheLiteral.State) (word : BitString) :
    (CacheLiteral.skipped word r).remaining = [] := (CacheLiteral.skipped_fields word r).2.1
example (r : CacheLiteral.State) (leading : List CNFLiteral) (suffix : BitString)
    (h : r.core.pending = CompactClause.bits leading ++ suffix) :
    (CacheLiteral.skipped (List.replicate leading.length true) r).core.pending = suffix :=
  CacheLiteral.skipped_canonical leading r suffix h
example (r : CacheLiteral.State) :
    Exec CacheLiteral.select r.store (CacheLiteral.selectFuel r) (CacheLiteral.selected r).store :=
  CacheLiteral.select_exec r
#print axioms CacheLiteral.skip_exec
#print axioms CacheLiteral.read_pending_bound
#print axioms CacheLiteral.skipped_fields
#print axioms CacheLiteral.skipped_pending_bound
#print axioms CacheLiteral.skipFuel_bound
#print axioms CacheLiteral.skipped_canonical
#print axioms CacheLiteral.select_exec
#print axioms CacheLiteral.selected_fields
#print axioms CacheLiteral.selectFuel_bound
#print axioms CacheLiteral.selected_index_bound
#print axioms CacheLiteral.selected_canonical
end PNP.Concrete.NormalizerBlocks
