/-
Copyright (c) 2026 PNP Labs.

Canonical semantics of one encoded update. The header and writer executions
are matched to the previously proved machines, and the pending suffix is
retained exactly for the next iteration.
-/

import PNP.Concrete.NormalizerBatchLoop

namespace PNP.Concrete.NormalizerBlocks.TableBatch

open BitRegister

theorem registers_eq_of_store {left right : Occurrence.Registers} (same : left.store = right.store) :
    left = right := by
  cases left
  cases right
  simp only [Occurrence.Registers.store, Store.cons.injEq] at same
  rcases same with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, _⟩
  rfl

def encodePair (index value : Nat) (rest : BitString) : BitString :=
  List.replicate index true ++ false :: (List.replicate value true ++ false :: rest)

def decoded (index value : Nat) (rest : BitString) : Occurrence.Registers :=
  ⟨rest, List.replicate value true, List.replicate index true, [], [], [], [true],
    List.replicate index true, []⟩

theorem headers_canonical (index value : Nat) (rest : BitString) :
    TableWrite.prepared (encodePair index value rest) = decoded index value rest := by
  let input := encodePair index value rest
  let afterIndex : Occurrence.Registers :=
    ⟨List.replicate value true ++ false :: rest, List.replicate index true, [], [], [], [], [], [], []⟩
  let afterValue : Occurrence.Registers :=
    ⟨rest, List.replicate value true, [], [], [], [], [], List.replicate index true, []⟩
  have start : Exec (.action (.push 6 true)) (Occurrence.initialRegisters input).store 1
      (TableWrite.seeded input).store := .action _ _
  have first : Exec Occurrence.headerLoop (TableWrite.seeded input).store (4 * index + 5) afterIndex.store := by
    simpa only [TableWrite.seeded, input, encodePair, afterIndex, List.replicate_zero, Nat.zero_add] using
      Occurrence.header_canonical index 0 (List.replicate value true ++ false :: rest) [] [] [] [] [] []
  have second : Exec Occurrence.headerLoop (ClauseQuery.saved afterIndex).store (4 * value + 5) afterValue.store := by
    simpa only [ClauseQuery.saved, afterIndex, afterValue, List.replicate_zero, Nat.zero_add] using
      Occurrence.header_canonical value 0 rest [] [] [] [] (List.replicate index true) []
  have setup : Exec TableWrite.prepare afterValue.store 2 (decoded index value rest).store :=
    TableWrite.prepare_exec afterValue
  have canonical : Exec TableWrite.headers (Occurrence.initialRegisters input).store
      (1 + ((4 * index + 5) + (3 + ((4 * value + 5) + 2)))) (decoded index value rest).store :=
    Exec.seq start (Exec.seq first (Exec.seq (ClauseQuery.save_exec afterIndex) (Exec.seq second setup)))
  have actual := TableWrite.headers_exec input
  exact registers_eq_of_store (NANDFrontend.accepted_store_unique (TableWrite.headers.program 0 8)
    _ _ ⟨.running 0, (Occurrence.initialRegisters input).store⟩
    (TableWrite.prepared input).store (decoded index value rest).store
    (actual.program_run 0 8) (canonical.program_run 0 8))

theorem scan_pack_canonical (entries : MatchingTable.Entries) (index value : Nat) :
    (TableWrite.packed (TableWrite.queryResult
      {TableWrite.writeInitial index value with input := MatchingTable.encode entries}).state).output =
        MatchingTable.encode (MatchingTable.write entries index value) := by
  let values := encodeClauseListTokens (MatchingTable.clauses entries) ++ [.finish]
  let start : Occurrence.Registers :=
    {TableWrite.writeInitial index value with input := MatchingTable.encode entries}
  obtain ⟨fuel, selected⟩ := TableWrite.tokenScan_exec values (TableWrite.writeInitial index value)
  have actual := Exec.seq (TableWrite.query_exec start)
    (TableWrite.pack_exec (TableWrite.queryResult start).state)
  have canonical := Exec.seq selected
    (TableWrite.pack_exec (TableWrite.tokenScan values (TableWrite.writeInitial index value)))
  have same := NANDFrontend.accepted_store_unique ((Block.seq TableWrite.loop TableWrite.pack).program 0 8)
    _ _ ⟨.running 0, start.store⟩
    (TableWrite.packed (TableWrite.queryResult start).state).store
    (TableWrite.packed (TableWrite.tokenScan values (TableWrite.writeInitial index value))).store
    (actual.program_run 0 8) (canonical.program_run 0 8)
  exact (congrArg (fun store : Store 9 => store.get 8) same).trans
    (TableWrite.packed_canonical entries index value)

theorem body_canonical (r : State) (entries : MatchingTable.Entries) (index value : Nat) (rest : BitString)
    (pending : r.pending = encodePair index value rest) (table : r.table = MatchingTable.encode entries) :
    (result r).pending = rest ∧ (result r).table = MatchingTable.encode (MatchingTable.write entries index value) := by
  have stage : (staged r).core =
      {TableWrite.writeInitial index value with input := MatchingTable.encode entries} := by
    simp only [staged, ready, parsed, pending, table, headers_canonical, decoded,
      TableWrite.writeInitial, TableWrite.tableState]
  constructor
  · change (TableWrite.prepared r.pending).input = rest
    rw [pending, headers_canonical]
    rfl
  · change (TableWrite.packed (TableWrite.queryResult (staged r).core).state).output = _
    rw [stage]
    exact scan_pack_canonical entries index value

end PNP.Concrete.NormalizerBlocks.TableBatch
