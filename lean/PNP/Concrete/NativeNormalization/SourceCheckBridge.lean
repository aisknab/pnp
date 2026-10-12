import PNP.Concrete.NormalizerSourceCheckPolynomial
import PNP.Concrete.NativeNormalization.MeasuredCandidate
import PNP.Concrete.NormalizerSourceCandidatePolynomial
import PNP.Concrete.NormalizerSourceCachePolynomial
import PNP.Concrete.NormalizerModeCachePolynomial
import PNP.Concrete.NativeNormalization.MeasuredSourceCache
import PNP.Concrete.NormalizerOwnerCachePolynomial
import PNP.Concrete.NormalizerCutPolynomial
import PNP.Concrete.NativeNormalization.MeasuredCut
import PNP.Concrete.NormalizerMatchingPolynomial
import PNP.Concrete.NativeNormalization.MeasuredMatchingLoop
import PNP.Concrete.NativeNormalization.MeasuredPrepared
import PNP.Concrete.NormalizerCompactSemantics
import PNP.Concrete.NormalizerPreparedPolynomial


namespace PNP.Concrete.NativeNormalization.ExplorationSourceBridge

open PNP.Concrete PNP.Concrete.NormalizerBlocks MatchingCache Matching

def erased (T : Table c n) : MatchingTable.Entries := T.entries.map (fun cell => cell.map Fin.val)

theorem erased_matches (entry : Option (Fin n)) (value : Fin n) :
    (entry.map Fin.val == some value.val) = (entry == some value) := by
  cases entry with
  | none => rfl
  | some previous =>
      by_cases same : previous = value
      · subst previous
        have left : ((some value.val : Option Nat) == some value.val) = true := beq_iff_eq.mpr rfl
        have right : ((some value : Option (Fin n)) == some value) = true := beq_iff_eq.mpr rfl
        exact left.trans right.symm
      · have different : previous.val ≠ value.val := fun eq => same (Fin.ext eq)
        have left : ((some previous.val : Option Nat) == some value.val) = false :=
          beq_eq_false_iff_ne.mpr (fun eq => different (Option.some.inj eq))
        have right : ((some previous : Option (Fin n)) == some value) = false :=
          beq_eq_false_iff_ne.mpr (fun eq => same (Option.some.inj eq))
        exact left.trans right.symm

theorem read_source (T : Table c n) (index : Fin c) :
    MatchingTable.read (erased T) index.val = (MeasuredMatching.readMatching T index).value.map Fin.val := by
  have bound : index.val < (erased T).length := by
    simp only [erased, List.length_map, T.length_eq]
    exact index.isLt
  rw [MeasuredMatching.readMatching_value, MatchingTable.read, List.getElem?_eq_getElem bound]
  simp only [Option.getD_some, erased, List.getElem_map, Table.get]


theorem incidence_source (F : CNFFormula) (index : Fin F.clauses.length) (value : Fin F.variableCount) :
    ((F.clauses[index.val]?.getD []).find? (fun literal => literal.variableIndex == value.val)).isSome =
      (MeasuredMatching.incidence F index value).value := by
  simp only [MeasuredMatching.incidence, MeasuredReach.find_value, MeasuredMatching.readClause,
    MeasuredMatching.lookup_value]


def encodeVertex : Vertex c n → CNFLiteral
  | .inl index => ⟨true, index.val⟩
  | .inr value => ⟨false, value.val⟩

theorem root_value (T : Table c n) (vertex : Vertex c n) :
    RootKinds.value (encodeVertex vertex) (erased T) = (MeasuredMatching.seed T vertex).value := by
  cases vertex with
  | inl index =>
      change (MatchingTable.read (erased T) index.val).isNone =
        (MeasuredMatching.readMatching T index).value.isNone
      rw [read_source]
      cases (MeasuredMatching.readMatching T index).value <;> rfl
  | inr value => rfl

theorem edge_value (F : CNFFormula) (T : Table F.clauses.length F.variableCount)
    (first second : Vertex F.clauses.length F.variableCount) :
    EdgeKinds.value (encodeVertex first) (encodeVertex second) F.clauses (erased T) =
      (MeasuredMatching.edge F T first second).value := by
  cases first with
  | inl index =>
      cases second with
      | inl other => rfl
      | inr value =>
          change ForwardEdge.value value.val index.val F.clauses (erased T) =
            (MeasuredMatching.edge F T (.inl index) (.inr value)).value
          rw [ForwardEdge.value, read_source, erased_matches, incidence_source]
          rfl
  | inr value =>
      cases second with
      | inl index =>
          change (MatchingTable.read (erased T) index.val == some value.val) =
            (MeasuredMatching.edge F T (.inr value) (.inl index)).value
          rw [read_source, erased_matches]
          rfl
      | inr other => rfl

def encodeRow (entry : Vertex c n × Option (Vertex c n)) : TraceData.Row :=
  (encodeVertex entry.1, entry.2.map encodeVertex)

theorem find_rows (F : CNFFormula) (T : Table F.clauses.length F.variableCount)
    (target : Vertex F.clauses.length F.variableCount)
    (trace : Trace (Vertex F.clauses.length F.variableCount)) :
    ((trace.map encodeRow).find? (fun entry => EdgeKinds.value entry.1 (encodeVertex target) F.clauses (erased T))) =
      (trace.find? (fun entry => (MeasuredMatching.edge F T entry.1 target).value)).map encodeRow := by
  induction trace with
  | nil => rfl
  | cons entry rest ih =>
      change ((encodeRow entry :: rest.map encodeRow).find?
        (fun entry => EdgeKinds.value entry.1 (encodeVertex target) F.clauses (erased T))) = _
      rw [List.find?_cons, List.find?_cons]
      have edgeRead : EdgeKinds.value (encodeRow entry).1 (encodeVertex target) F.clauses (erased T) =
          (MeasuredMatching.edge F T entry.1 target).value := edge_value F T entry.1 target
      rw [edgeRead]
      cases (MeasuredMatching.edge F T entry.1 target).value
      · exact ih
      · rfl

theorem parent_value (F : CNFFormula) (T : Table F.clauses.length F.variableCount)
    (target : Vertex F.clauses.length F.variableCount)
    (trace : Trace (Vertex F.clauses.length F.variableCount)) :
    ParentQuery.value (encodeVertex target) F.clauses (erased T) (trace.map encodeRow) =
      (MeasuredReach.parent (MeasuredMatching.seed T) (MeasuredMatching.edge F T) trace target).value.map
        (Option.map encodeVertex) := by
  rw [ParentQuery.value, root_value]
  cases root : (MeasuredMatching.seed T target).value
  · simp only [root, Bool.false_eq_true, ite_false, MeasuredReach.parent, MeasuredReach.find_value, find_rows]
    cases trace.find? (fun entry => (MeasuredMatching.edge F T entry.1 target).value) <;> rfl
  · simp only [root, ite_true, MeasuredReach.parent, Option.map_some, Option.map_none]

theorem encodeVertex_injective : Function.Injective (@encodeVertex c n) := by
  intro first second eq
  cases first with
  | inl index =>
      cases second with
      | inl other => exact congrArg Sum.inl (Fin.ext (congrArg CNFLiteral.variableIndex eq))
      | inr other =>
          have impossible : true = false := congrArg CNFLiteral.positive eq
          cases impossible
  | inr index =>
      cases second with
      | inl other =>
          have impossible : false = true := congrArg CNFLiteral.positive eq
          cases impossible
      | inr other => exact congrArg Sum.inr (Fin.ext (congrArg CNFLiteral.variableIndex eq))

theorem same_true_iff (first second : CNFLiteral) : TraceMember.same first second = true ↔ first = second := by
  constructor
  · intro h
    have fields : (first.variableIndex == second.variableIndex) = true ∧
        (first.positive == second.positive) = true := by
      cases indexTest : first.variableIndex == second.variableIndex with
      | false =>
          have impossible : false = true := by simpa only [TraceMember.same, indexTest, Bool.false_and] using h
          cases impossible
      | true =>
          cases tagTest : first.positive == second.positive with
          | false =>
              have impossible : false = true := by simpa only [TraceMember.same, indexTest, tagTest, Bool.true_and] using h
              cases impossible
          | true => exact ⟨rfl, rfl⟩
    have index : first.variableIndex = second.variableIndex := beq_iff_eq.mp fields.1
    have tag : first.positive = second.positive := beq_iff_eq.mp fields.2
    cases first
    cases second
    cases index
    cases tag
    rfl
  · intro eq
    subst second
    have index : (first.variableIndex == first.variableIndex) = true := beq_iff_eq.mpr rfl
    have tag : (first.positive == first.positive) = true := beq_iff_eq.mpr rfl
    rw [TraceMember.same, index, tag]
    rfl

theorem member_value (target : Vertex c n) (trace : Trace (Vertex c n)) :
    TraceMember.value (encodeVertex target) (trace.map encodeRow) =
      (MeasuredReach.nodeMember trace target).value := by
  induction trace with
  | nil => rfl
  | cons entry rest ih =>
      by_cases occurs : target = entry.1
      · have found : TraceMember.same (encodeVertex entry.1) (encodeVertex target) = true :=
          (same_true_iff _ _).mpr (congrArg encodeVertex occurs.symm)
        have source : (MeasuredReach.nodeMember (entry :: rest) target).value = true := by
          simp only [MeasuredReach.nodeMember, occurs, ite_true]
        rw [source]
        simp only [TraceMember.value, List.map_cons, List.any_cons, encodeRow, found, Bool.true_or]
      · have missing : TraceMember.same (encodeVertex entry.1) (encodeVertex target) = false := by
          cases checked : TraceMember.same (encodeVertex entry.1) (encodeVertex target) with
          | false => rfl
          | true => exact False.elim (occurs (encodeVertex_injective ((same_true_iff _ _).mp checked)).symm)
        simpa only [TraceMember.value, List.map_cons, List.any_cons, encodeRow,
          missing, Bool.false_or, MeasuredReach.nodeMember, occurs, ite_false] using ih

theorem eligible_value (F : CNFFormula) (T : Table F.clauses.length F.variableCount)
    (target : Vertex F.clauses.length F.variableCount)
    (trace : Trace (Vertex F.clauses.length F.variableCount)) :
    Eligibility.value (encodeVertex target) F.clauses (erased T) (trace.map encodeRow) =
      (MeasuredReach.eligible (MeasuredMatching.seed T) (MeasuredMatching.edge F T) trace target).value.map
        (Option.map encodeVertex) := by
  rw [Eligibility.value, member_value]
  cases seen : (MeasuredReach.nodeMember trace target).value
  · simpa only [seen, Bool.false_eq_true, ite_false, MeasuredReach.eligible] using parent_value F T target trace
  · simp only [seen, ite_true, MeasuredReach.eligible, Option.map_none]

def encodeFound (found : (Vertex c n × Option (Vertex c n)) × List (Vertex c n)) : Extraction.Found :=
  (encodeRow found.1, found.2.map encodeVertex)

theorem extract_value (F : CNFFormula) (T : Table F.clauses.length F.variableCount)
    (trace : Trace (Vertex F.clauses.length F.variableCount))
    (unseen : List (Vertex F.clauses.length F.variableCount)) :
    Extraction.value F.clauses (erased T) (trace.map encodeRow) (unseen.map encodeVertex) =
      (MeasuredReach.extract (MeasuredReach.eligible (MeasuredMatching.seed T) (MeasuredMatching.edge F T) trace)
        unseen).value.map encodeFound := by
  induction unseen with
  | nil => rfl
  | cons vertex rest ih =>
      simp only [List.map_cons, Extraction.value, eligible_value, MeasuredReach.extract]
      cases found : (MeasuredReach.eligible (MeasuredMatching.seed T) (MeasuredMatching.edge F T) trace vertex).value with
      | none =>
          simp only [Option.map_none]
          rw [ih]
          cases (MeasuredReach.extract (MeasuredReach.eligible (MeasuredMatching.seed T) (MeasuredMatching.edge F T) trace) rest).value <;> rfl
      | some parent =>
          simp only [Option.map_some]
          rfl

theorem explore_value (F : CNFFormula) (T : Table F.clauses.length F.variableCount)
    (fuel : Nat) (unseen : List (Vertex F.clauses.length F.variableCount))
    (trace : Trace (Vertex F.clauses.length F.variableCount)) :
    Exploration.value F.clauses (erased T) fuel (unseen.map encodeVertex) (trace.map encodeRow) =
      ((MeasuredReach.explore (MeasuredMatching.seed T) (MeasuredMatching.edge F T) fuel unseen trace).value).map encodeRow := by
  induction fuel generalizing unseen trace with
  | zero => rfl
  | succ fuel ih =>
      cases selected : (MeasuredReach.extract
          (MeasuredReach.eligible (MeasuredMatching.seed T) (MeasuredMatching.edge F T) trace) unseen).value with
      | none =>
          simp only [Exploration.value, extract_value, MeasuredReach.explore, selected, Option.map_none]
      | some found =>
          obtain ⟨⟨vertex, parent⟩, rest⟩ := found
          simpa only [Exploration.value, extract_value, MeasuredReach.explore, selected,
            Option.map_some, encodeFound, encodeRow, List.map_cons] using ih rest ((vertex, parent) :: trace)

theorem vertices_value (clauses variables : Nat) :
    SearchVertices.vertices clauses variables =
      (MeasuredCollections.vertices clauses variables).value.map encodeVertex := by
  rw [MeasuredCollections.vertices_value]
  simp only [SearchVertices.vertices, SearchVertices.rangeData_finRange, Matching.vertices,
    List.map_append, List.map_map, Function.comp_def, encodeVertex, Nat.zero_add]

theorem scan_value (F : CNFFormula) (T : Table F.clauses.length F.variableCount) :
    Exploration.value F.clauses (erased T) (F.clauses.length + F.variableCount)
      (SearchVertices.vertices F.clauses.length F.variableCount) [] =
      (MeasuredSearch.scan F T).value.map encodeRow := by
  rw [vertices_value]
  exact explore_value F T (F.clauses.length + F.variableCount)
    (MeasuredCollections.vertices F.clauses.length F.variableCount).value []

theorem polynomial_source (F : CNFFormula) (T : Table F.clauses.length F.variableCount) :
    Exploration.polynomial.output (Exploration.encode F.variableCount F.clauses (erased T)) =
      TraceData.encode ((MeasuredSearch.scan F T).value.map encodeRow) := by
  rw [Exploration.polynomial_canonical, scan_value]

theorem machine_source (F : CNFFormula) (T : Table F.clauses.length F.variableCount) :
    machineOutput (BitRegister.CompilerIO.rawMachine Exploration.program)
      ((BitRegister.CompilerIO.runtimePolynomial 28 Exploration.sourceFuel).eval
        (Exploration.encode F.variableCount F.clauses (erased T)).length)
      (Exploration.encode F.variableCount F.clauses (erased T)) =
      TraceData.encode ((MeasuredSearch.scan F T).value.map encodeRow) := by
  rw [Exploration.machine_canonical, scan_value]


end PNP.Concrete.NativeNormalization.ExplorationSourceBridge


namespace PNP.Concrete.NativeNormalization.OwnerSearchBridge

open PNP.Concrete PNP.Concrete.NormalizerBlocks MatchingCache

def erased (T : Table c n) : MatchingTable.Entries :=
  T.entries.map (fun cell => cell.map Fin.val)

theorem entries_ofFn (T : Table c n) : T.entries = List.ofFn T.get := by
  apply List.ext_getElem
  · rw [T.length_eq, List.length_ofFn]
  · intro index leftBound rightBound
    simp only [List.getElem_ofFn, Table.get]

theorem erased_ofFn (T : Table c n) :
    erased T = List.ofFn (fun i => (T.get i).map Fin.val) := by
  rw [erased, entries_ofFn, List.map_ofFn]
  rfl

theorem erased_matches (entry : Option (Fin n)) (value : Fin n) :
    (entry.map Fin.val == some value.val) = (entry == some value) := by
  cases entry with
  | none => rfl
  | some previous =>
      by_cases same : previous = value
      · subst previous
        have left : ((some value.val : Option Nat) == some value.val) = true := beq_iff_eq.mpr rfl
        have right : ((some value : Option (Fin n)) == some value) = true := beq_iff_eq.mpr rfl
        exact left.trans right.symm
      · have different : previous.val ≠ value.val := fun eq => same (Fin.ext eq)
        have left : ((some previous.val : Option Nat) == some value.val) = false :=
          beq_eq_false_iff_ne.mpr (fun eq => different (Option.some.inj eq))
        have right : ((some previous : Option (Fin n)) == some value) = false :=
          beq_eq_false_iff_ne.mpr (fun eq => same (Option.some.inj eq))
        exact left.trans right.symm

theorem owner_source (T : Table c n) (value : Fin n) :
    TableOwner.owner (erased T) value.val = (MeasuredSearch.owner T value).value.map Fin.val := by
  rw [erased_ofFn, TableOwner.owner_ofFn, MeasuredSearch.owner_value]
  simp only [Matching.owner, erased_matches]

theorem owner_output (T : Table c n) (value : Fin n) :
    TableOwner.polynomial.output (TableOwner.encodeQuery value.val (erased T)) =
      TableOwner.answer ((MeasuredSearch.owner T value).value.map Fin.val) := by
  rw [TableOwner.polynomial_canonical, owner_source]

theorem owner_machine_output (T : Table c n) (value : Fin n) :
    machineOutput (BitRegister.CompilerIO.rawMachine TableOwner.program)
      ((BitRegister.CompilerIO.runtimePolynomial 9 TableOwner.sourceFuel).eval
        (TableOwner.encodeQuery value.val (erased T)).length)
      (TableOwner.encodeQuery value.val (erased T)) =
        TableOwner.answer ((MeasuredSearch.owner T value).value.map Fin.val) := by
  rw [TableOwner.machine_canonical, owner_source]


end PNP.Concrete.NativeNormalization.OwnerSearchBridge

namespace PNP.Concrete.NativeNormalization.CandidateSearchBridge

open PNP.Concrete PNP.Concrete.NormalizerBlocks Matching MatchingCache

def nodeEntry : Vertex c n → Option Nat
  | .inl _ => none
  | .inr value => some value.val

def seenEntries (tr : Trace (Vertex c n)) : MatchingTable.Entries :=
  tr.map (fun pair => nodeEntry pair.1)

theorem nodeEntry_matches (node : Vertex c n) (value : Fin n) :
    (nodeEntry node == some value.val) = decide (Sum.inr value = node) := by
  cases node with
  | inl clause => rfl
  | inr previous =>
      by_cases same : previous = value
      · subst previous
        have left : ((some value.val : Option Nat) == some value.val) = true := beq_iff_eq.mpr rfl
        have right : decide ((Sum.inr value : Vertex c n) = Sum.inr value) = true := decide_eq_true rfl
        exact left.trans right.symm
      · have different : previous.val ≠ value.val := fun eq => same (Fin.ext eq)
        have left : ((some previous.val : Option Nat) == some value.val) = false :=
          beq_eq_false_iff_ne.mpr (fun eq => different (Option.some.inj eq))
        have right : decide ((Sum.inr value : Vertex c n) = Sum.inr previous) = false :=
          decide_eq_false (fun eq => same (Sum.inr.inj eq).symm)
        exact left.trans right.symm

theorem seen_source (tr : Trace (Vertex c n)) (value : Fin n) :
    (TableOwner.owner (seenEntries tr) value.val).isSome =
      (MeasuredReach.nodeMember tr (.inr value)).value := by
  rw [TableOwner.owner_isSome]
  induction tr with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨node, parent⟩
      change ((nodeEntry node == some value.val) ||
        (seenEntries rest).any (fun entry => entry == some value.val)) = _
      rw [nodeEntry_matches]
      by_cases same : (Sum.inr value : Vertex c n) = node
      · simp only [MeasuredReach.nodeMember, same, ite_true, decide_true, Bool.true_or]
      · simpa only [MeasuredReach.nodeMember, same, ite_false, decide_false, Bool.false_or] using ih

theorem eligible_source (T : Table c n) (tr : Trace (Vertex c n)) (value : Fin n) :
    Candidate.eligible (OwnerSearchBridge.erased T) (seenEntries tr) value.val =
      (MeasuredSearch.candidateCheck T tr value).value := by
  rw [Candidate.eligible, OwnerSearchBridge.owner_source, seen_source]
  have mapped :
      ((MeasuredSearch.owner T value).value.map Fin.val).isNone =
        (MeasuredSearch.owner T value).value.isNone := by
    cases (MeasuredSearch.owner T value).value <;> rfl
  rw [mapped]
  rfl

theorem candidate_source (T : Table c n) (tr : Trace (Vertex c n)) :
    Candidate.selectFrom (OwnerSearchBridge.erased T) (seenEntries tr) n 0 =
      (MeasuredSearch.candidate T tr).value.map Fin.val := by
  rw [Candidate.select_finRange]
  simp only [MeasuredSearch.candidate, MeasuredReach.find_value,
    MeasuredCollections.range_value, eligible_source]

theorem candidate_output (T : Table c n) (tr : Trace (Vertex c n)) :
    CandidatePacket.polynomial.output
      (CandidatePacket.encode n (OwnerSearchBridge.erased T) (seenEntries tr)) =
        TableOwner.answer ((MeasuredSearch.candidate T tr).value.map Fin.val) := by
  rw [CandidatePacket.polynomial_canonical, candidate_source]

theorem candidate_machine_output (T : Table c n) (tr : Trace (Vertex c n)) :
    machineOutput (BitRegister.CompilerIO.rawMachine CandidatePacket.program)
      ((BitRegister.CompilerIO.runtimePolynomial 13 CandidatePacket.sourceFuel).eval
        (CandidatePacket.encode n (OwnerSearchBridge.erased T) (seenEntries tr)).length)
      (CandidatePacket.encode n (OwnerSearchBridge.erased T) (seenEntries tr)) =
        TableOwner.answer ((MeasuredSearch.candidate T tr).value.map Fin.val) := by
  rw [CandidatePacket.machine_canonical, candidate_source]


end PNP.Concrete.NativeNormalization.CandidateSearchBridge


namespace PNP.Concrete.NativeNormalization.PathSourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks MatchingCache Matching

def encodeVertex : Vertex c n → CNFLiteral
  | .inl index => ⟨true, index.val⟩
  | .inr value => ⟨false, value.val⟩

def encodeRow (entry : Vertex c n × Option (Vertex c n)) : TraceData.Row :=
  (encodeVertex entry.1, entry.2.map encodeVertex)

theorem encodeVertex_injective : Function.Injective (@encodeVertex c n) := by
  intro first second eq
  cases first with
  | inl index =>
      cases second with
      | inl other => exact congrArg Sum.inl (Fin.ext (congrArg CNFLiteral.variableIndex eq))
      | inr other =>
          have impossible : true = false := congrArg CNFLiteral.positive eq
          cases impossible
  | inr index =>
      cases second with
      | inl other =>
          have impossible : false = true := congrArg CNFLiteral.positive eq
          cases impossible
      | inr other => exact congrArg Sum.inr (Fin.ext (congrArg CNFLiteral.variableIndex eq))


theorem path_value (trace : Trace (Vertex c n)) (target : Vertex c n) :
    TracePath.value (trace.map encodeRow) (encodeVertex target) =
      (MeasuredSearch.path trace target).value.map (List.map encodeVertex) := by
  induction trace generalizing target with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨vertex, parent⟩
      by_cases occurs : target = vertex
      · subst vertex
        have found : TraceMember.same (encodeVertex target) (encodeVertex target) = true :=
          (TraceMember.same_true_iff _ _).2 rfl
        cases parent with
        | none =>
            simp only [List.map_cons, encodeRow, Option.map_none, TracePath.value, found, ite_true,
              MeasuredSearch.path, Option.map_some, List.map_nil]
        | some parent =>
            simp only [List.map_cons, encodeRow, Option.map_some, TracePath.value, found, ite_true, MeasuredSearch.path]
            rw [ih parent]
            cases (MeasuredSearch.path rest parent).value <;> rfl
      · have missing : TraceMember.same (encodeVertex vertex) (encodeVertex target) = false := by
          cases checked : TraceMember.same (encodeVertex vertex) (encodeVertex target) with
          | false => rfl
          | true => exact False.elim (occurs (encodeVertex_injective ((TraceMember.same_true_iff _ _).1 checked)).symm)
        simpa only [List.map_cons, encodeRow, TracePath.value, missing, Bool.false_eq_true, ite_false,
          MeasuredSearch.path, occurs] using ih target

theorem polynomial_source (trace : Trace (Vertex c n)) (target : Vertex c n) :
    TracePath.polynomial.output (TracePath.encode (encodeVertex target) (trace.map encodeRow)) =
      PathData.answer ((MeasuredSearch.path trace target).value.map (List.map encodeVertex)) := by
  rw [TracePath.polynomial_canonical, path_value]

theorem machine_source (trace : Trace (Vertex c n)) (target : Vertex c n) :
    machineOutput (BitRegister.CompilerIO.rawMachine TracePath.program)
      ((BitRegister.CompilerIO.runtimePolynomial 23 TracePath.sourceFuel).eval
        (TracePath.encode (encodeVertex target) (trace.map encodeRow)).length)
      (TracePath.encode (encodeVertex target) (trace.map encodeRow)) =
      PathData.answer ((MeasuredSearch.path trace target).value.map (List.map encodeVertex)) := by
  rw [TracePath.machine_canonical, path_value]

end PNP.Concrete.NativeNormalization.PathSourceBridge

namespace PNP.Concrete.NativeNormalization.CompleteSearchSourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks MatchingCache Matching
open ExplorationSourceBridge

theorem seen_encoding (trace : Trace (Vertex c n)) :
    SeenTrace.value (trace.map encodeRow) = CandidateSearchBridge.seenEntries trace := by
  simp only [SeenTrace.value, CandidateSearchBridge.seenEntries, List.map_map, Function.comp_def]
  have same : (fun entry : Vertex c n × Option (Vertex c n) => SeenTrace.entry (encodeRow entry).1) =
      (fun entry => CandidateSearchBridge.nodeEntry entry.1) := by
    funext entry
    rcases entry with ⟨vertex, parent⟩
    cases vertex <;> rfl
  rw [same]

def encodeOutput : SearchOutput c n → Search.Output
  | .terminal trace => .terminal (trace.map encodeRow)
  | .augment index path => .augment index.val (path.map encodeVertex)

theorem value_source (F : CNFFormula) (T : Table F.clauses.length F.variableCount) :
    Search.value F.variableCount F.clauses (erased T) = encodeOutput (MeasuredSearch.search F T).value := by
  have scanned : Search.traceValue F.variableCount F.clauses (erased T) =
      (MeasuredSearch.scan F T).value.map encodeRow := scan_value F T
  unfold Search.value
  rw [scanned]
  dsimp only
  rw [seen_encoding]
  have picked : Candidate.selectFrom (erased T)
      (CandidateSearchBridge.seenEntries (MeasuredSearch.scan F T).value) F.variableCount 0 =
      (MeasuredSearch.candidate T (MeasuredSearch.scan F T).value).value.map Fin.val :=
    CandidateSearchBridge.candidate_source T (MeasuredSearch.scan F T).value
  rw [picked]
  cases chosen : (MeasuredSearch.candidate T (MeasuredSearch.scan F T).value).value with
  | none => simp only [Option.map_none, MeasuredSearch.search, chosen, encodeOutput]
  | some index =>
      simp only [Option.map_some, MeasuredSearch.search, chosen, encodeOutput]
      have route := PathSourceBridge.path_value (MeasuredSearch.scan F T).value (.inr index)
      change TracePath.value ((MeasuredSearch.scan F T).value.map encodeRow) ⟨false, index.val⟩ =
        (MeasuredSearch.path (MeasuredSearch.scan F T).value (.inr index)).value.map (List.map encodeVertex) at route
      rw [route]
      cases (MeasuredSearch.path (MeasuredSearch.scan F T).value (.inr index)).value <;> rfl

theorem polynomial_source (F : CNFFormula) (T : Table F.clauses.length F.variableCount) :
    Search.polynomial.output (Exploration.encode F.variableCount F.clauses (erased T)) =
      Search.answer (encodeOutput (MeasuredSearch.search F T).value) := by
  rw [Search.polynomial_canonical, value_source]

theorem machine_source (F : CNFFormula) (T : Table F.clauses.length F.variableCount) :
    machineOutput (BitRegister.CompilerIO.rawMachine Search.program)
      ((BitRegister.CompilerIO.runtimePolynomial 29 Search.sourceFuel).eval
        (Exploration.encode F.variableCount F.clauses (erased T)).length)
      (Exploration.encode F.variableCount F.clauses (erased T)) =
      Search.answer (encodeOutput (MeasuredSearch.search F T).value) := by
  rw [Search.machine_canonical, value_source]


end PNP.Concrete.NativeNormalization.CompleteSearchSourceBridge

namespace PNP.Concrete.NativeNormalization.MatchingTableBridge

open PNP.Concrete PNP.Concrete.NormalizerBlocks MatchingCache

def erased (T : Table c n) : MatchingTable.Entries :=
  T.entries.map (fun cell => cell.map Fin.val)

theorem erased_length (T : Table c n) : (erased T).length = c := by
  rw [erased, List.length_map, T.length_eq]

theorem read_erased (T : Table c n) (j : Fin c) :
    MatchingTable.read (erased T) j.val = (T.get j).map Fin.val := by
  have valid : j.val < T.entries.length := by rw [T.length_eq]; exact j.isLt
  simp only [MatchingTable.read, erased, List.getElem?_map,
    List.getElem?_eq_getElem valid, Option.map_some, Option.getD_some, Table.get]

theorem read_source (T : Table c n) (j : Fin c) :
    ClauseQuery.polynomial.output (ClauseQuery.encodeQuery 0 j.val (MatchingTable.clauses (erased T))) =
      Occurrence.encodeQuery 0 (MatchingTable.entryClause ((MeasuredMatching.readMatching T j).value.map Fin.val)) := by
  rw [MatchingTable.read_query, read_erased, MeasuredMatching.readMatching_value]

def eraseUpdates (xs : List (Fin c × Fin n)) : List (Nat × Nat) :=
  xs.map (fun pair => (pair.1.val, pair.2.val))

theorem writeAll_reads (xs : List (Fin c × Fin n)) (entries : MatchingTable.Entries)
    (length : entries.length = c) (m : Fin c → Option (Fin n))
    (agree : ∀ j, MatchingTable.read entries j.val = (m j).map Fin.val) (j : Fin c) :
    MatchingTable.read (MatchingTable.writeAll entries (eraseUpdates xs)) j.val =
      (Matching.augment xs m j).map Fin.val := by
  induction xs generalizing entries m with
  | nil => exact agree j
  | cons pair rest ih =>
      rcases pair with ⟨i,v⟩
      change MatchingTable.read (MatchingTable.writeAll (MatchingTable.write entries i.val v.val)
        (eraseUpdates rest)) j.val = (Matching.augment rest (Matching.put m i v) j).map Fin.val
      apply ih
      · rw [MatchingTable.write_length, length]
      · intro k
        have valid : k.val < entries.length := by rw [length]; exact k.isLt
        rw [MatchingTable.read_write entries i.val v.val k.val valid]
        by_cases eq : k = i
        · subst k
          simp only [Matching.put, ite_true, Option.map_some]
        · have different : k.val ≠ i.val := fun same => eq (Fin.ext same)
          simp only [Matching.put, if_neg eq, if_neg different, agree k]

theorem updated_reads (T : Table c n) (xs : List (Fin c × Fin n)) (j : Fin c) :
    MatchingTable.read (erased (MeasuredAugment.update T xs).value) j.val =
      (Matching.augment xs T.get j).map Fin.val := by
  rw [read_erased, MeasuredAugment.update_value, Table.get_ofFunction]

theorem writeAll_source (T : Table c n) (xs : List (Fin c × Fin n)) :
    MatchingTable.writeAll (erased T) (eraseUpdates xs) =
      erased (MeasuredAugment.update T xs).value := by
  apply List.ext_getElem
  · rw [MatchingTable.writeAll_length, erased_length, erased_length]
  · intro index leftBound rightBound
    have valid : index < c := by simpa only [erased_length] using rightBound
    have left := writeAll_reads xs (erased T) (erased_length T) T.get (read_erased T) ⟨index,valid⟩
    have right := updated_reads T xs ⟨index,valid⟩
    have eq := left.trans right.symm
    simpa only [MatchingTable.read, List.getElem?_eq_getElem leftBound,
      List.getElem?_eq_getElem rightBound, Option.getD_some] using eq

theorem single_write_source (T : Table c n) (i : Fin c) (v : Fin n) :
    TableWrite.polynomial.output (TableWrite.encodeWrite i.val v.val (erased T)) =
      MatchingTable.encode (erased (MeasuredAugment.update T [(i,v)]).value) := by
  rw [TableWrite.polynomial_canonical]
  exact congrArg MatchingTable.encode (writeAll_source T [(i,v)])

theorem single_write_machine_source (T : Table c n) (i : Fin c) (v : Fin n) :
    machineOutput (BitRegister.CompilerIO.rawMachine TableWrite.program)
      ((BitRegister.CompilerIO.runtimePolynomial 9 TableWrite.sourceFuel).eval
        (TableWrite.encodeWrite i.val v.val (erased T)).length)
      (TableWrite.encodeWrite i.val v.val (erased T)) =
        MatchingTable.encode (erased (MeasuredAugment.update T [(i,v)]).value) := by
  rw [TableWrite.machine_canonical]
  exact congrArg MatchingTable.encode (writeAll_source T [(i,v)])

theorem batch_source (T : Table c n) (xs : List (Fin c × Fin n)) :
    BatchPacket.polynomial.output (BatchPacket.encode (erased T) (eraseUpdates xs)) =
      MatchingTable.encode (erased (MeasuredAugment.update T xs).value) := by
  rw [BatchPacket.polynomial_canonical, writeAll_source]

theorem batch_machine_source (T : Table c n) (xs : List (Fin c × Fin n)) :
    machineOutput (BitRegister.CompilerIO.rawMachine BatchPacket.program)
      ((BitRegister.CompilerIO.runtimePolynomial 11 BatchPacket.sourceFuel).eval
        (BatchPacket.encode (erased T) (eraseUpdates xs)).length)
      (BatchPacket.encode (erased T) (eraseUpdates xs)) =
        MatchingTable.encode (erased (MeasuredAugment.update T xs).value) := by
  rw [BatchPacket.machine_canonical, writeAll_source]


end PNP.Concrete.NativeNormalization.MatchingTableBridge

namespace PNP.Concrete.NativeNormalization.AugmentationSourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks Matching MatchingCache
open MatchingTableBridge

def encodeVertex : Vertex c n → CNFLiteral
  | .inl index => ⟨true, index.val⟩
  | .inr value => ⟨false, value.val⟩

theorem value_source : (xs : List (Vertex c n)) →
    PathPairs.value (xs.map encodeVertex) = eraseUpdates (MeasuredAugment.decodePairs xs).value
  | [] => rfl
  | [node] => by cases node <;> rfl
  | .inl index :: second :: rest => rfl
  | .inr value :: .inr other :: rest => rfl
  | .inr value :: .inl index :: rest => by
      change (index.val, value.val) :: PathPairs.value (rest.map encodeVertex) =
        (index.val, value.val) :: eraseUpdates (MeasuredAugment.decodePairs rest).value
      rw [value_source rest]

theorem pair_polynomial_source (xs : List (Vertex c n)) :
    PathPairs.polynomial.output (PathData.encode (xs.map encodeVertex)) =
      TableBatch.encodeUpdates (eraseUpdates (MeasuredAugment.decodePairs xs).value) := by
  rw [PathPairs.polynomial_canonical, value_source]

theorem pair_machine_source (xs : List (Vertex c n)) :
    machineOutput (BitRegister.CompilerIO.rawMachine PathPairs.program)
      ((BitRegister.CompilerIO.runtimePolynomial 12 PathPairs.sourceFuel).eval
        (PathData.encode (xs.map encodeVertex)).length)
      (PathData.encode (xs.map encodeVertex)) =
      TableBatch.encodeUpdates (eraseUpdates (MeasuredAugment.decodePairs xs).value) := by
  rw [PathPairs.machine_canonical, value_source]

theorem augmentation_source (T : Table c n) (xs : List (Vertex c n)) :
    Augmentation.polynomial.output (Augmentation.encode (erased T) (xs.map encodeVertex)) =
      MatchingTable.encode (erased (MeasuredAugment.update T (MeasuredAugment.decodePairs xs).value).value) := by
  rw [Augmentation.polynomial_canonical, value_source, writeAll_source]

theorem augmentation_machine_source (T : Table c n) (xs : List (Vertex c n)) :
    machineOutput (BitRegister.CompilerIO.rawMachine Augmentation.program)
      ((BitRegister.CompilerIO.runtimePolynomial 13 Augmentation.sourceFuel).eval
        (Augmentation.encode (erased T) (xs.map encodeVertex)).length)
      (Augmentation.encode (erased T) (xs.map encodeVertex)) =
      MatchingTable.encode (erased (MeasuredAugment.update T (MeasuredAugment.decodePairs xs).value).value) := by
  rw [Augmentation.machine_canonical, value_source, writeAll_source]

end PNP.Concrete.NativeNormalization.AugmentationSourceBridge


namespace PNP.Concrete.NativeNormalization.FullMatchingSourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks MatchingCache Matching
open MatchingTableBridge

theorem finish_source (F : CNFFormula) (fuel : Nat) (T : Table F.clauses.length F.variableCount) :
    MatchingLoop.finish F.variableCount F.clauses fuel (erased T) =
      erased (MeasuredMatchingLoop.finish F fuel T).value := by
  induction fuel generalizing T with
  | zero => rfl
  | succ fuel ih =>
      have queried := CompleteSearchSourceBridge.value_source F T
      change Search.value F.variableCount F.clauses (erased T) =
        CompleteSearchSourceBridge.encodeOutput (MeasuredSearch.search F T).value at queried
      rw [MatchingLoop.finish, queried]
      cases search : (MeasuredSearch.search F T).value with
      | terminal trace =>
          simp only [CompleteSearchSourceBridge.encodeOutput, MeasuredMatchingLoop.finish, search]
      | augment index route =>
          simp only [CompleteSearchSourceBridge.encodeOutput, MeasuredMatchingLoop.finish, search]
          change MatchingLoop.finish F.variableCount F.clauses fuel
            (MatchingTable.writeAll (erased T) (PathPairs.value (route.map AugmentationSourceBridge.encodeVertex))) =
              erased (MeasuredMatchingLoop.finish F fuel
                (MeasuredAugment.update T (MeasuredAugment.decodePairs route).value).value).value
          rw [AugmentationSourceBridge.value_source, writeAll_source]
          exact ih _

theorem empty_source (c n : Nat) :
    erased (MeasuredAugment.emptyTable c n).value = List.replicate c none := by
  rw [MeasuredAugment.emptyTable_value]
  simp only [erased, Table.ofFunction, List.map_ofFn, Function.comp_def, Option.map_none]
  apply List.ext_getElem
  · rw [List.length_ofFn, List.length_replicate]
  · intro index leftBound rightBound
    simp only [List.getElem_ofFn, List.getElem_replicate]

theorem fullTable_source (F : CNFFormula) :
    MatchingLoop.fullTable F.variableCount F.clauses = erased (MeasuredMatchingLoop.fullTable F).value := by
  unfold MatchingLoop.fullTable
  rw [← empty_source F.clauses.length F.variableCount]
  exact finish_source F (F.clauses.length + 1) (MeasuredAugment.emptyTable F.clauses.length F.variableCount).value

theorem result_source (F : CNFFormula) :
    (MatchingDriver.result (MatchingDriver.encode F.variableCount F.clauses)).registers.output =
      MatchingTable.encode (erased (MeasuredMatchingLoop.fullTable F).value) := by
  rw [MatchingDriver.result_canonical, fullTable_source]

theorem program_source (F : CNFFormula) :
    (BitRegister.run MatchingDriver.program
      (MatchingDriver.sourceSteps (MatchingDriver.encode F.variableCount F.clauses) + 1)
      (BitRegister.initial MatchingDriver.program (MatchingDriver.encode F.variableCount F.clauses))).store.get 8 =
        MatchingTable.encode (erased (MeasuredMatchingLoop.fullTable F).value) := by
  rw [MatchingDriver.program_canonical, fullTable_source]

theorem source_table_bytes (F : CNFFormula) :
    (MatchingTable.encode (erased (MeasuredMatchingLoop.fullTable F).value)).length ≤
      MatchingLoop.tableBytes F.clauses.length (F.clauses.length + F.variableCount) := by
  rw [← fullTable_source]
  exact MatchingLoop.fullTable_bytes F.variableCount F.clauses

theorem polynomial_source (F : CNFFormula) :
    MatchingDriver.polynomial.output (MatchingDriver.encode F.variableCount F.clauses) =
      MatchingTable.encode (erased (MeasuredMatchingLoop.fullTable F).value) := by
  rw [MatchingDriver.polynomial_canonical, fullTable_source]

theorem machine_source (F : CNFFormula) :
    machineOutput (BitRegister.CompilerIO.rawMachine MatchingDriver.program)
      ((BitRegister.CompilerIO.runtimePolynomial 33 MatchingDriver.sourceFuel).eval
        (MatchingDriver.encode F.variableCount F.clauses).length)
      (MatchingDriver.encode F.variableCount F.clauses) =
        MatchingTable.encode (erased (MeasuredMatchingLoop.fullTable F).value) := by
  rw [MatchingDriver.machine_canonical, fullTable_source]

end PNP.Concrete.NativeNormalization.FullMatchingSourceBridge


namespace PNP.Concrete.NativeNormalization.CutTraceSourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks

theorem trace_value_source (F : CNFFormula) :
    Search.traceValue F.variableCount F.clauses (MatchingLoop.fullTable F.variableCount F.clauses) =
      (MeasuredSearch.scan F (MeasuredMatchingLoop.fullTable F).value).value.map ExplorationSourceBridge.encodeRow := by
  rw [FullMatchingSourceBridge.fullTable_source]
  exact ExplorationSourceBridge.scan_value F (MeasuredMatchingLoop.fullTable F).value

theorem result_source (F : CNFFormula) :
    (CutTrace.result (MatchingDriver.encode F.variableCount F.clauses)).registers.output =
      TraceData.encode ((MeasuredSearch.scan F (MeasuredMatchingLoop.fullTable F).value).value.map
        ExplorationSourceBridge.encodeRow) := by
  rw [CutTrace.result_canonical, trace_value_source]

theorem polynomial_source (F : CNFFormula) :
    CutTrace.polynomial.output (MatchingDriver.encode F.variableCount F.clauses) =
      TraceData.encode ((MeasuredSearch.scan F (MeasuredMatchingLoop.fullTable F).value).value.map
        ExplorationSourceBridge.encodeRow) := by
  rw [CutTrace.polynomial_canonical, trace_value_source]

theorem machine_source (F : CNFFormula) :
    machineOutput (BitRegister.CompilerIO.rawMachine CutTrace.program)
      ((BitRegister.CompilerIO.runtimePolynomial 33 CutTrace.sourceFuel).eval
        (MatchingDriver.encode F.variableCount F.clauses).length)
      (MatchingDriver.encode F.variableCount F.clauses) =
        TraceData.encode ((MeasuredSearch.scan F (MeasuredMatchingLoop.fullTable F).value).value.map
          ExplorationSourceBridge.encodeRow) := by
  rw [CutTrace.machine_canonical, trace_value_source]

theorem cut_trace_projection (F : CNFFormula) :
    (MeasuredCut.prepare F).value.nodeData =
      (MeasuredSearch.scan F (MeasuredMatchingLoop.fullTable F).value).value := rfl

theorem cut_matching_projection (F : CNFFormula) :
    (MeasuredCut.prepare F).value.matchingData = (MeasuredMatchingLoop.fullTable F).value.entries := rfl

theorem cut_trace_source (F : CNFFormula) :
    (CutTrace.result (MatchingDriver.encode F.variableCount F.clauses)).registers.output =
      TraceData.encode ((MeasuredCut.prepare F).value.nodeData.map ExplorationSourceBridge.encodeRow) := by
  rw [cut_trace_projection]
  exact result_source F

theorem cut_matching_source (F : CNFFormula) :
    (CutTrace.result (MatchingDriver.encode F.variableCount F.clauses)).table =
      MatchingTable.encode ((MeasuredCut.prepare F).value.matchingData.map (fun cell => cell.map Fin.val)) := by
  rw [cut_matching_projection, CutTrace.result_matching, FullMatchingSourceBridge.fullTable_source]
  rfl

end PNP.Concrete.NativeNormalization.CutTraceSourceBridge


namespace PNP.Concrete.NativeNormalization.CutSelectionSourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks Matching
open ExplorationSourceBridge

theorem selected_clauses (trace : Trace (Vertex c n)) :
    CutSelection.selected true (trace.map encodeRow) c 0 =
      ((MeasuredCut.selectRange c (fun i => MeasuredReach.nodeMember trace (.inl i))).value).map
        (fun i => encodeVertex (.inl i : Vertex c n)) := by
  have predicates : (fun i : Fin c => TraceMember.value ⟨true,i.val⟩ (trace.map encodeRow)) =
      (fun i : Fin c => (MeasuredReach.nodeMember trace (.inl i)).value) := by
    funext i
    exact member_value (.inl i) trace
  rw [CutSelection.selected_finRange, MeasuredCut.selectRange_value]
  simp only [Nat.zero_add]
  rw [predicates]
  rfl

theorem selected_variables (trace : Trace (Vertex c n)) :
    CutSelection.selected false (trace.map encodeRow) n 0 =
      ((MeasuredCut.selectRange n (fun i => MeasuredReach.nodeMember trace (.inr i))).value).map
        (fun i => encodeVertex (.inr i : Vertex c n)) := by
  have predicates : (fun i : Fin n => TraceMember.value ⟨false,i.val⟩ (trace.map encodeRow)) =
      (fun i : Fin n => (MeasuredReach.nodeMember trace (.inr i)).value) := by
    funext i
    exact member_value (.inr i) trace
  rw [CutSelection.selected_finRange, MeasuredCut.selectRange_value]
  simp only [Nat.zero_add]
  rw [predicates]
  rfl

theorem polynomial_clauses (trace : Trace (Vertex c n)) :
    (CutSelection.polynomial true).output (CutSelection.encode c (trace.map encodeRow)) =
      SearchVertices.encodeVertices
        (((MeasuredCut.selectRange c (fun i => MeasuredReach.nodeMember trace (.inl i))).value).map
          (fun i => encodeVertex (.inl i : Vertex c n))) := by
  rw [CutSelection.polynomial_canonical, selected_clauses]

theorem polynomial_variables (trace : Trace (Vertex c n)) :
    (CutSelection.polynomial false).output (CutSelection.encode n (trace.map encodeRow)) =
      SearchVertices.encodeVertices
        (((MeasuredCut.selectRange n (fun i => MeasuredReach.nodeMember trace (.inr i))).value).map
          (fun i => encodeVertex (.inr i : Vertex c n))) := by
  rw [CutSelection.polynomial_canonical, selected_variables]

theorem machine_clauses (trace : Trace (Vertex c n)) :
    machineOutput (BitRegister.CompilerIO.rawMachine (CutSelection.program true))
      ((BitRegister.CompilerIO.runtimePolynomial 24 CutSelection.sourceFuel).eval
        (CutSelection.encode c (trace.map encodeRow)).length)
      (CutSelection.encode c (trace.map encodeRow)) =
      SearchVertices.encodeVertices
        (((MeasuredCut.selectRange c (fun i => MeasuredReach.nodeMember trace (.inl i))).value).map
          (fun i => encodeVertex (.inl i : Vertex c n))) := by
  rw [CutSelection.machine_output, polynomial_clauses]

theorem machine_variables (trace : Trace (Vertex c n)) :
    machineOutput (BitRegister.CompilerIO.rawMachine (CutSelection.program false))
      ((BitRegister.CompilerIO.runtimePolynomial 24 CutSelection.sourceFuel).eval
        (CutSelection.encode n (trace.map encodeRow)).length)
      (CutSelection.encode n (trace.map encodeRow)) =
      SearchVertices.encodeVertices
        (((MeasuredCut.selectRange n (fun i => MeasuredReach.nodeMember trace (.inr i))).value).map
          (fun i => encodeVertex (.inr i : Vertex c n))) := by
  rw [CutSelection.machine_output, polynomial_variables]

theorem cut_trace_projection (F : CNFFormula) :
    (MeasuredCut.prepare F).value.nodeData =
      (MeasuredSearch.scan F (MeasuredMatchingLoop.fullTable F).value).value := rfl

theorem cut_clause_projection (F : CNFFormula) :
    (MeasuredCut.prepare F).value.clauseData =
      (MeasuredCut.selectRange F.clauses.length
        (fun i => MeasuredReach.nodeMember
          (MeasuredSearch.scan F (MeasuredMatchingLoop.fullTable F).value).value (.inl i))).value := rfl

theorem cut_variable_projection (F : CNFFormula) :
    (MeasuredCut.prepare F).value.variableData =
      (MeasuredCut.selectRange F.variableCount
        (fun i => MeasuredReach.nodeMember
          (MeasuredSearch.scan F (MeasuredMatchingLoop.fullTable F).value).value (.inr i))).value := rfl

theorem cut_clauses_source (F : CNFFormula) :
    (CutSelection.polynomial true).output
      (CutSelection.encode F.clauses.length ((MeasuredCut.prepare F).value.nodeData.map encodeRow)) =
      SearchVertices.encodeVertices
        ((MeasuredCut.prepare F).value.clauseData.map
          (fun i => encodeVertex (.inl i : Vertex F.clauses.length F.variableCount))) := by
  rw [cut_trace_projection, cut_clause_projection]
  exact polynomial_clauses _

theorem cut_variables_source (F : CNFFormula) :
    (CutSelection.polynomial false).output
      (CutSelection.encode F.variableCount ((MeasuredCut.prepare F).value.nodeData.map encodeRow)) =
      SearchVertices.encodeVertices
        ((MeasuredCut.prepare F).value.variableData.map
          (fun i => encodeVertex (.inr i : Vertex F.clauses.length F.variableCount))) := by
  rw [cut_trace_projection, cut_variable_projection]
  exact polynomial_variables _

theorem cut_clauses_machine (F : CNFFormula) :
    machineOutput (BitRegister.CompilerIO.rawMachine (CutSelection.program true))
      ((BitRegister.CompilerIO.runtimePolynomial 24 CutSelection.sourceFuel).eval
        (CutSelection.encode F.clauses.length
          ((MeasuredCut.prepare F).value.nodeData.map encodeRow)).length)
      (CutSelection.encode F.clauses.length ((MeasuredCut.prepare F).value.nodeData.map encodeRow)) =
      SearchVertices.encodeVertices
        ((MeasuredCut.prepare F).value.clauseData.map
          (fun i => encodeVertex (.inl i : Vertex F.clauses.length F.variableCount))) := by
  rw [CutSelection.machine_output, cut_clauses_source]

theorem cut_variables_machine (F : CNFFormula) :
    machineOutput (BitRegister.CompilerIO.rawMachine (CutSelection.program false))
      ((BitRegister.CompilerIO.runtimePolynomial 24 CutSelection.sourceFuel).eval
        (CutSelection.encode F.variableCount
          ((MeasuredCut.prepare F).value.nodeData.map encodeRow)).length)
      (CutSelection.encode F.variableCount ((MeasuredCut.prepare F).value.nodeData.map encodeRow)) =
      SearchVertices.encodeVertices
        ((MeasuredCut.prepare F).value.variableData.map
          (fun i => encodeVertex (.inr i : Vertex F.clauses.length F.variableCount))) := by
  rw [CutSelection.machine_output, cut_variables_source]

end PNP.Concrete.NativeNormalization.CutSelectionSourceBridge



namespace PNP.Concrete.NativeNormalization.FullCutSourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks Matching
open ExplorationSourceBridge

def sourcePacket (F : CNFFormula) : BitString :=
  CutDriver.packet
    (MatchingTable.encode ((MeasuredCut.prepare F).value.matchingData.map (fun cell => cell.map Fin.val)))
    (TraceData.encode ((MeasuredCut.prepare F).value.nodeData.map encodeRow))
    (SearchVertices.encodeVertices ((MeasuredCut.prepare F).value.clauseData.map
      (fun i => encodeVertex (.inl i : Vertex F.clauses.length F.variableCount))))
    (SearchVertices.encodeVertices ((MeasuredCut.prepare F).value.variableData.map
      (fun v => encodeVertex (.inr v : Vertex F.clauses.length F.variableCount))))

theorem canonicalPacket_source (F : CNFFormula) :
    CutDriver.canonicalPacket F.variableCount F.clauses = sourcePacket F := by
  dsimp only [CutDriver.canonicalPacket, sourcePacket]
  rw [CutTraceSourceBridge.trace_value_source, FullMatchingSourceBridge.fullTable_source,
    CutSelectionSourceBridge.selected_clauses, CutSelectionSourceBridge.selected_variables,
    CutTraceSourceBridge.cut_matching_projection, CutSelectionSourceBridge.cut_trace_projection,
    CutSelectionSourceBridge.cut_clause_projection, CutSelectionSourceBridge.cut_variable_projection]
  rfl

theorem result_source (F : CNFFormula) :
    (CutDriver.result (MatchingDriver.encode F.variableCount F.clauses)).registers.output = sourcePacket F := by
  rw [CutDriver.result_canonical, canonicalPacket_source]

theorem polynomial_source (F : CNFFormula) :
    CutDriver.polynomial.output (MatchingDriver.encode F.variableCount F.clauses) = sourcePacket F := by
  rw [CutDriver.polynomial_canonical, canonicalPacket_source]

theorem machine_source (F : CNFFormula) :
    machineOutput (BitRegister.CompilerIO.rawMachine CutDriver.program)
      ((BitRegister.CompilerIO.runtimePolynomial 36 CutDriver.sourceFuel).eval
        (MatchingDriver.encode F.variableCount F.clauses).length)
      (MatchingDriver.encode F.variableCount F.clauses) = sourcePacket F := by
  rw [CutDriver.machine_canonical, canonicalPacket_source]

theorem program_source (F : CNFFormula) :
    (BitRegister.run CutDriver.program
      (CutDriver.sourceSteps (MatchingDriver.encode F.variableCount F.clauses) + 1)
      (BitRegister.initial CutDriver.program (MatchingDriver.encode F.variableCount F.clauses))).store.get 8 =
      sourcePacket F := by
  rw [CutDriver.closed_run, CutDriver.State.get_output, result_source]

theorem matching_source (F : CNFFormula) :
    (CutDriver.result (MatchingDriver.encode F.variableCount F.clauses)).core.table =
      MatchingTable.encode ((MeasuredCut.prepare F).value.matchingData.map (fun cell => cell.map Fin.val)) := by
  rw [(CutDriver.result_data F.variableCount F.clauses).matchingRead,
    CutTraceSourceBridge.cut_matching_projection, FullMatchingSourceBridge.fullTable_source]
  rfl

theorem trace_source (F : CNFFormula) :
    (CutDriver.result (MatchingDriver.encode F.variableCount F.clauses)).trace =
      TraceData.encode ((MeasuredCut.prepare F).value.nodeData.map encodeRow) := by
  rw [(CutDriver.result_data F.variableCount F.clauses).traceRead,
    CutTraceSourceBridge.trace_value_source, CutSelectionSourceBridge.cut_trace_projection]

theorem clauses_source (F : CNFFormula) :
    (CutDriver.result (MatchingDriver.encode F.variableCount F.clauses)).clauses =
      SearchVertices.encodeVertices ((MeasuredCut.prepare F).value.clauseData.map
        (fun i => encodeVertex (.inl i : Vertex F.clauses.length F.variableCount))) := by
  rw [(CutDriver.result_data F.variableCount F.clauses).clausesRead,
    CutTraceSourceBridge.trace_value_source, CutSelectionSourceBridge.selected_clauses,
    CutSelectionSourceBridge.cut_clause_projection]

theorem variables_source (F : CNFFormula) :
    (CutDriver.result (MatchingDriver.encode F.variableCount F.clauses)).variables =
      SearchVertices.encodeVertices ((MeasuredCut.prepare F).value.variableData.map
        (fun v => encodeVertex (.inr v : Vertex F.clauses.length F.variableCount))) := by
  rw [(CutDriver.result_data F.variableCount F.clauses).variablesRead,
    CutTraceSourceBridge.trace_value_source, CutSelectionSourceBridge.selected_variables,
    CutSelectionSourceBridge.cut_variable_projection]

theorem original_width (F : CNFFormula) :
    (CutDriver.result (MatchingDriver.encode F.variableCount F.clauses)).core.width =
      List.replicate F.variableCount true :=
  (CutDriver.result_data F.variableCount F.clauses).widthRead

end PNP.Concrete.NativeNormalization.FullCutSourceBridge



namespace PNP.Concrete.NativeNormalization.CompactClauseSourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks

def selectedVertices {width : Nat} (variables : List (Fin width)) : List CNFLiteral :=
  variables.map (fun v => ⟨false,v.val⟩)

theorem fin_beq_self {width : Nat} (target : Fin width) : (target == target) = true := by
  change decide (target = target) = true
  exact decide_eq_true rfl

theorem fin_beq_ne {width : Nat} (first target : Fin width) (different : first ≠ target) :
    (first == target) = false := by
  change decide (first = target) = false
  exact decide_eq_false different

theorem owner_position {width : Nat} (variables : List (Fin width))
    (target : Fin width) (offset : Nat) :
    TableOwner.vertexOwnerFrom offset (selectedVertices variables) target.val =
      if (MeasuredSelection.contains target variables).value then
        some (offset + (MeasuredSelection.position target variables).value) else none := by
  induction variables generalizing offset with
  | nil => rfl
  | cons first variables ih =>
      by_cases same : first = target
      · subst first
        have equalNat : (target.val == target.val) = true := by
          change decide (target.val = target.val) = true
          exact decide_eq_true rfl
        have equalFin : (target == target) = true := fin_beq_self target
        simp only [selectedVertices, List.map_cons, TableOwner.vertexOwnerFrom,
          TableOwner.ownerFrom, equalNat, ite_true, MeasuredSelection.contains,
          MeasuredSelection.position, equalFin, Nat.add_zero]
      · have different : (first.val == target.val) = false :=
          beq_eq_false_iff_ne.mpr (fun h => same (Fin.ext h))
        have differentFin : (first == target) = false := fin_beq_ne first target same
        have reversed : target ≠ first := Ne.symm same
        change (if first.val == target.val then some offset
          else TableOwner.vertexOwnerFrom (offset + 1) (selectedVertices variables) target.val) = _
        rw [different]
        simp only [Bool.false_eq_true, ite_false]
        rw [ih]
        simp only [MeasuredSelection.contains, reversed, ite_false,
          MeasuredSelection.position, differentFin, Bool.false_eq_true]
        cases present : (MeasuredSelection.contains target variables).value
        · simp only [ Bool.false_eq_true, ite_false]
        · simp only [ ite_true]
          apply congrArg some
          omega

theorem owner_outside {width : Nat} (variables : List (Fin width))
    (target offset : Nat) (outside : ¬ target < width) :
    TableOwner.vertexOwnerFrom offset (selectedVertices variables) target = none := by
  induction variables generalizing offset with
  | nil => rfl
  | cons first variables ih =>
      have different : (first.val == target) = false := by
        apply beq_eq_false_iff_ne.mpr
        intro equal
        exact outside (equal ▸ first.isLt)
      change (if first.val == target then some offset
        else TableOwner.vertexOwnerFrom (offset + 1) (selectedVertices variables) target) = none
      rw [different]
      simp only [Bool.false_eq_true, ite_false]
      exact ih (offset + 1)

theorem literal_source {F : CNFFormula} (cut : NativeContext.CutData F) (literal : CNFLiteral) :
    CompactClause.compactLiteral (selectedVertices cut.variableData) literal =
      (MeasuredPrepared.compactLiteral cut literal).value := by
  by_cases valid : literal.variableIndex < F.variableCount
  · have owner := owner_position cut.variableData ⟨literal.variableIndex,valid⟩ 0
    change TableOwner.vertexOwnerFrom 0 (selectedVertices cut.variableData) literal.variableIndex = _ at owner
    simp only [Nat.zero_add] at owner
    unfold CompactClause.compactLiteral TableOwner.vertexOwner
    rw [owner]
    simp only [MeasuredPrepared.compactLiteral, dif_pos valid]
    cases present : (MeasuredSelection.contains
      (⟨literal.variableIndex,valid⟩ : Fin F.variableCount) cut.variableData).value <;>
      simp only [ Bool.false_eq_true, ite_false, ite_true, Option.map_none, Option.map_some]
  · have owner := owner_outside cut.variableData literal.variableIndex 0 valid
    unfold CompactClause.compactLiteral TableOwner.vertexOwner
    rw [owner]
    simp only [MeasuredPrepared.compactLiteral, dif_neg valid, Option.map_none]

theorem clause_source {F : CNFFormula} (cut : NativeContext.CutData F) (literals : List CNFLiteral) :
    CompactClause.value (selectedVertices cut.variableData) literals =
      (MeasuredPrepared.compactClause cut literals).value := by
  rw [MeasuredPrepared.compactClause, MeasuredSelection.filterMap_value]
  unfold CompactClause.value
  apply congrArg (fun f : CNFLiteral → Option CNFLiteral => literals.filterMap f)
  funext literal
  exact literal_source cut literal

theorem whole_source {F : CNFFormula} (cut : NativeContext.CutData F)
    (literals : List CNFLiteral) (r : CompactClause.State)
    (pending : r.pending = CompactClause.bits literals ++ [true,false])
    (variables : r.variables = SearchVertices.encodeVertices (selectedVertices cut.variableData)) :
    (CompactClause.whole r).state.buffer =
      (CompactClause.bits (MeasuredPrepared.compactClause cut literals).value).reverse ++ r.buffer := by
  rw [CompactClause.whole_buffer (selectedVertices cut.variableData) literals r pending variables,
    clause_source]

theorem loop_execution (r : CompactClause.State) :
    NormalizerBlocks.Exec CompactClause.loop r.store
      (CompactClause.whole r).fuel (CompactClause.whole r).state.store :=
  CompactClause.whole_exec r

theorem loop_polynomial (r : CompactClause.State) (bound : Nat)
    (bounded : r.store.Bounded bound) :
    (CompactClause.whole r).fuel ≤ (71 * bound + 119) * (bound + 1) + 1 := by
  rw [← CompactClause.callBound_eval]
  exact CompactClause.whole_fuel_bounded r bound bounded


end PNP.Concrete.NativeNormalization.CompactClauseSourceBridge

namespace PNP.Concrete.NativeNormalization.PreparedStateSourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks Matching
open ExplorationSourceBridge

theorem dense_source {F : CNFFormula} (cut : NativeContext.CutData F) :
    DenseClauses.value F.clauses (CompactClauseSourceBridge.selectedVertices cut.variableData)
      (cut.clauseData.map (fun i => (⟨true,i.val⟩ : CNFLiteral))) =
      (MeasuredPrepared.denseClauses cut).value := by
  simp only [DenseClauses.value, List.map_map, MeasuredPrepared.denseClauses,
    MeasuredCollections.map_value]
  apply congrArg (fun f : Fin F.clauses.length → List CNFLiteral => cut.clauseData.map f)
  funext index
  change CompactClause.value (CompactClauseSourceBridge.selectedVertices cut.variableData)
    (F.clauses[index.val]?.getD []) = (MeasuredPrepared.readAndCompact cut index).value
  rw [CompactClauseSourceBridge.clause_source]
  simp only [MeasuredPrepared.readAndCompact, MeasuredMatching.readClause, MeasuredMatching.lookup_value]

theorem literals_projection (F : CNFFormula) :
    (MeasuredPrepared.prepare F).value.literals =
      (MeasuredPrepared.denseClauses (MeasuredCut.prepare F).value).value := rfl

theorem denseValue_source (F : CNFFormula) :
    PreparedDriver.denseValue F.variableCount F.clauses = (MeasuredPrepared.prepare F).value.literals := by
  dsimp only [PreparedDriver.denseValue]
  rw [CutTraceSourceBridge.trace_value_source, CutSelectionSourceBridge.selected_variables,
    CutSelectionSourceBridge.selected_clauses, ← CutSelectionSourceBridge.cut_variable_projection,
    ← CutSelectionSourceBridge.cut_clause_projection, literals_projection]
  exact dense_source (MeasuredCut.prepare F).value

theorem result_source (F : CNFFormula) :
    (PreparedDriver.result (MatchingDriver.encode F.variableCount F.clauses)).registers.output =
      GraphQuery.clauseData (MeasuredPrepared.prepare F).value.literals := by
  rw [PreparedDriver.result_canonical, denseValue_source]

theorem polynomial_source (F : CNFFormula) :
    PreparedDriver.polynomial.output (MatchingDriver.encode F.variableCount F.clauses) =
      GraphQuery.clauseData (MeasuredPrepared.prepare F).value.literals := by
  rw [PreparedDriver.polynomial_canonical, denseValue_source]

theorem machine_source (F : CNFFormula) :
    machineOutput (BitRegister.CompilerIO.rawMachine PreparedDriver.program)
      ((BitRegister.CompilerIO.runtimePolynomial 36 PreparedDriver.sourceFuel).eval
        (MatchingDriver.encode F.variableCount F.clauses).length)
      (MatchingDriver.encode F.variableCount F.clauses) =
        GraphQuery.clauseData (MeasuredPrepared.prepare F).value.literals := by
  rw [PreparedDriver.machine_canonical, denseValue_source]

theorem matching_source (F : CNFFormula) :
    (PreparedDriver.result (MatchingDriver.encode F.variableCount F.clauses)).core.table =
      MatchingTable.encode ((MeasuredPrepared.prepare F).value.matchingData.map (fun cell => cell.map Fin.val)) := by
  change _ = MatchingTable.encode ((MeasuredCut.prepare F).value.matchingData.map (fun cell => cell.map Fin.val))
  rw [(PreparedDriver.result_data F.variableCount F.clauses).matchingRead,
    CutTraceSourceBridge.cut_matching_projection, FullMatchingSourceBridge.fullTable_source]
  rfl

theorem trace_source (F : CNFFormula) :
    (PreparedDriver.result (MatchingDriver.encode F.variableCount F.clauses)).trace =
      TraceData.encode ((MeasuredPrepared.prepare F).value.nodeData.map encodeRow) := by
  change _ = TraceData.encode ((MeasuredCut.prepare F).value.nodeData.map encodeRow)
  rw [(PreparedDriver.result_data F.variableCount F.clauses).traceRead,
    CutTraceSourceBridge.trace_value_source, CutSelectionSourceBridge.cut_trace_projection]

theorem clauses_source (F : CNFFormula) :
    (PreparedDriver.result (MatchingDriver.encode F.variableCount F.clauses)).clauses =
      SearchVertices.encodeVertices ((MeasuredPrepared.prepare F).value.clauseData.map
        (fun i => encodeVertex (.inl i : Vertex F.clauses.length F.variableCount))) := by
  change _ = SearchVertices.encodeVertices ((MeasuredCut.prepare F).value.clauseData.map
    (fun i => encodeVertex (.inl i : Vertex F.clauses.length F.variableCount)))
  rw [(PreparedDriver.result_data F.variableCount F.clauses).clausesRead,
    CutTraceSourceBridge.trace_value_source, CutSelectionSourceBridge.selected_clauses,
    CutSelectionSourceBridge.cut_clause_projection]

theorem variables_source (F : CNFFormula) :
    (PreparedDriver.result (MatchingDriver.encode F.variableCount F.clauses)).variables =
      SearchVertices.encodeVertices ((MeasuredPrepared.prepare F).value.variableData.map
        (fun v => encodeVertex (.inr v : Vertex F.clauses.length F.variableCount))) := by
  change _ = SearchVertices.encodeVertices ((MeasuredCut.prepare F).value.variableData.map
    (fun v => encodeVertex (.inr v : Vertex F.clauses.length F.variableCount)))
  rw [(PreparedDriver.result_data F.variableCount F.clauses).variablesRead,
    CutTraceSourceBridge.trace_value_source, CutSelectionSourceBridge.selected_variables,
    CutSelectionSourceBridge.cut_variable_projection]

structure MatchesPrepared (F : CNFFormula) (r : CutDriver.State) : Prop where
  widthRead : r.core.width = List.replicate F.variableCount true
  formulaRead : r.core.formula = GraphQuery.clauseData F.clauses
  matchingRead : r.core.table = MatchingTable.encode
    ((MeasuredPrepared.prepare F).value.matchingData.map (fun cell => cell.map Fin.val))
  traceRead : r.trace = TraceData.encode ((MeasuredPrepared.prepare F).value.nodeData.map encodeRow)
  clausesRead : r.clauses = SearchVertices.encodeVertices
    ((MeasuredPrepared.prepare F).value.clauseData.map
      (fun i => encodeVertex (.inl i : Vertex F.clauses.length F.variableCount)))
  variablesRead : r.variables = SearchVertices.encodeVertices
    ((MeasuredPrepared.prepare F).value.variableData.map
      (fun v => encodeVertex (.inr v : Vertex F.clauses.length F.variableCount)))
  literalsRead : r.registers.output = GraphQuery.clauseData (MeasuredPrepared.prepare F).value.literals

theorem prepared_state_source (F : CNFFormula) :
    MatchesPrepared F (PreparedDriver.result (MatchingDriver.encode F.variableCount F.clauses)) :=
  ⟨(PreparedDriver.result_data F.variableCount F.clauses).widthRead,
    (PreparedDriver.result_data F.variableCount F.clauses).formulaRead,
    matching_source F,trace_source F,clauses_source F,variables_source F,result_source F⟩

theorem program_source (F : CNFFormula) :
    (BitRegister.run PreparedDriver.program
      (PreparedDriver.sourceSteps (MatchingDriver.encode F.variableCount F.clauses) + 1)
      (BitRegister.initial PreparedDriver.program (MatchingDriver.encode F.variableCount F.clauses))).store.get 8 =
      GraphQuery.clauseData (MeasuredPrepared.prepare F).value.literals := by
  rw [PreparedDriver.closed_run, CutDriver.State.get_output, result_source]

theorem polynomial_all_raw_inputs (input : BitString) :
    boundedDecide (BitRegister.CompilerIO.rawMachine PreparedDriver.program)
      ((BitRegister.CompilerIO.runtimePolynomial 36 PreparedDriver.sourceFuel).eval input.length) input = .accept :=
  PreparedDriver.polynomial_accepts input

theorem bounded_all_raw_states (input : BitString) :
    (PreparedDriver.result input).store.Bounded (PreparedDriver.resultSize.eval input.length) :=
  PreparedDriver.result_bounded input

end PNP.Concrete.NativeNormalization.PreparedStateSourceBridge


namespace PNP.Concrete.NativeNormalization.OwnerCacheSourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks

def clauseVertices {F : CNFFormula} (cut : NativeContext.CutData F) : List CNFLiteral :=
  cut.clauseData.map (fun index => ⟨true,index.val⟩)
def variableVertices {F : CNFFormula} (cut : NativeContext.CutData F) : List CNFLiteral :=
  cut.variableData.map (fun index => ⟨false,index.val⟩)
def matchingEntries {F : CNFFormula} (cut : NativeContext.CutData F) : MatchingTable.Entries :=
  cut.matchingData.map (fun cell => cell.map Fin.val)
def ownerEntries {F : CNFFormula} (cut : NativeContext.CutData F) : MatchingTable.Entries :=
  List.ofFn (fun v : Fin (CNFCore.variables F).length => some (MeasuredChoice.partner cut v).value.val)

theorem clause_position {width : Nat} (indices : List (Fin width)) (target : Fin width) :
    TableOwner.vertexOwner (indices.map (fun i => (⟨true,i.val⟩ : CNFLiteral))) target.val =
      if (MeasuredSelection.contains target indices).value then
        some (MeasuredSelection.position target indices).value else none := by
  have checked := CompactClauseSourceBridge.owner_position indices target 0
  simpa only [TableOwner.vertexOwner, TableOwner.vertexOwnerFrom,
    CompactClauseSourceBridge.selectedVertices, List.map_map, Function.comp_def, Nat.zero_add] using checked

theorem partner_source {F : CNFFormula} (cut : NativeContext.CutData F)
    (v : Fin (CNFCore.variables F).length) :
    CacheOwner.value (matchingEntries cut) (clauseVertices cut)
      (MeasuredAccess.atVariable cut v).value.val =
      some (MeasuredChoice.partner cut v).value.val := by
  have owner := OwnerSearchBridge.owner_source (MeasuredAccess.table cut) (MeasuredAccess.atVariable cut v).value
  change TableOwner.owner (matchingEntries cut) (MeasuredAccess.atVariable cut v).value.val = _ at owner
  rw [CacheOwner.value, owner]
  unfold MeasuredChoice.partner
  dsimp only
  split
  · rename_i absent
    exact False.elim (CNFCore.core_owner_exists F v ((MeasuredChoice.ownerLookup_value cut v).symm.trans absent))
  · rename_i index found
    have member : index ∈ cut.clauseData := by
      rw [cut.clause_eq]
      apply (CNFCore.positions_mem F index).mpr
      exact CNFCore.core_owner_kept F v index ((MeasuredChoice.ownerLookup_value cut v).symm.trans found)
    have present : (MeasuredSelection.contains index cut.clauseData).value = true :=
      (MeasuredSelection.contains_value index cut.clauseData).trans (decide_eq_true member)
    simp only [found, Option.map_some, Option.bind_some]
    change TableOwner.vertexOwner (cut.clauseData.map (fun i => (⟨true,i.val⟩ : CNFLiteral))) index.val = _
    rw [clause_position, present]
    rfl

theorem variableData_ofFn {F : CNFFormula} (cut : NativeContext.CutData F) :
    cut.variableData =
      List.ofFn (fun v : Fin (CNFCore.variables F).length => (MeasuredAccess.atVariable cut v).value) := by
  apply List.ext_getElem
  · rw [List.length_ofFn]
    exact congrArg List.length cut.variable_eq
  · intro index before after
    simp only [List.getElem_ofFn, MeasuredAccess.atVariable, MeasuredAccess.get_value]

theorem values_source {F : CNFFormula} (cut : NativeContext.CutData F) :
    CacheOwner.values (matchingEntries cut) (clauseVertices cut) (variableVertices cut) =
      ownerEntries cut := by
  unfold CacheOwner.values variableVertices ownerEntries
  rw [variableData_ofFn]
  simp only [List.map_ofFn, Function.comp_def]
  apply congrArg List.ofFn
  funext v
  exact partner_source cut v

theorem ownerValues_source (F : CNFFormula) :
    OwnerCacheDriver.ownerValues F.variableCount F.clauses = ownerEntries (MeasuredCut.prepare F).value := by
  dsimp only [OwnerCacheDriver.ownerValues]
  rw [CutTraceSourceBridge.trace_value_source, FullMatchingSourceBridge.fullTable_source,
    CutSelectionSourceBridge.selected_clauses, CutSelectionSourceBridge.selected_variables,
    ← CutSelectionSourceBridge.cut_clause_projection, ← CutSelectionSourceBridge.cut_variable_projection]
  exact values_source (MeasuredCut.prepare F).value

theorem result_source (F : CNFFormula) :
    (OwnerCacheDriver.result (MatchingDriver.encode F.variableCount F.clauses)).registers.output =
      MatchingTable.encode (ownerEntries (MeasuredCut.prepare F).value) := by
  rw [OwnerCacheDriver.result_canonical, ownerValues_source]

theorem polynomial_source (F : CNFFormula) :
    OwnerCacheDriver.polynomial.output (MatchingDriver.encode F.variableCount F.clauses) =
      MatchingTable.encode (ownerEntries (MeasuredCut.prepare F).value) := by
  rw [OwnerCacheDriver.polynomial_canonical, ownerValues_source]

theorem machine_source (F : CNFFormula) :
    machineOutput (BitRegister.CompilerIO.rawMachine OwnerCacheDriver.program)
      ((BitRegister.CompilerIO.runtimePolynomial 36 OwnerCacheDriver.sourceFuel).eval
        (MatchingDriver.encode F.variableCount F.clauses).length)
      (MatchingDriver.encode F.variableCount F.clauses) =
        MatchingTable.encode (ownerEntries (MeasuredCut.prepare F).value) := by
  rw [OwnerCacheDriver.machine_canonical, ownerValues_source]

theorem retained_literals_source (F : CNFFormula) :
    OwnerCacheDriver.literals (OwnerCacheDriver.result (MatchingDriver.encode F.variableCount F.clauses)) =
      GraphQuery.clauseData (MeasuredPrepared.prepare F).value.literals := by
  rw [OwnerCacheDriver.result_literals_canonical, PreparedStateSourceBridge.denseValue_source]

theorem polynomial_all_raw_inputs (input : BitString) :
    boundedDecide (BitRegister.CompilerIO.rawMachine OwnerCacheDriver.program)
      ((BitRegister.CompilerIO.runtimePolynomial 36 OwnerCacheDriver.sourceFuel).eval input.length) input = .accept :=
  OwnerCacheDriver.polynomial_accepts input


def cachedOwners {n c : Nat} {selection : NativeBasis.Selection n c}
    (ops : MeasuredOperations.Operations selection) : MatchingTable.Entries :=
  (MeasuredCache.build ops).value.ownerData.map (fun index => some index.val)

theorem cache_ownerData_source {F : CNFFormula} (context : NativeContext.Prepared F)
    (three : NativeSource.ThreeCore F) :
    ownerEntries context.toCutData = cachedOwners (MeasuredOperations.source context three) := by
  unfold cachedOwners
  rw [(MeasuredCache.build (MeasuredOperations.source context three)).value.owner_eq, List.map_ofFn]
  unfold ownerEntries
  apply congrArg List.ofFn
  funext v
  rw [MeasuredChoice.partner_value]
  rfl

theorem transport_cachedOwners {n c n' c' : Nat} (hn : n = n') (hc : c = c')
    {selection : NativeBasis.Selection n c} (ops : MeasuredOperations.Operations selection) :
    cachedOwners (MeasuredOperations.transport hn hc ops) = cachedOwners ops := by
  cases hn
  cases hc
  rfl

theorem sourceCache_ownerData (F : CNFFormula) (three : NativeSource.ThreeCore F) :
    (MeasuredSourceCache.build F three).value.data.ownerData.map (fun index => some index.val) =
      ownerEntries (MeasuredCut.prepare F).value := by
  change cachedOwners (MeasuredOperations.transport _ _
    (MeasuredOperations.source (MeasuredPrepared.prepare F).value three)) = _
  rw [transport_cachedOwners]
  exact (cache_ownerData_source (MeasuredPrepared.prepare F).value three).symm

theorem machine_source_cache (F : CNFFormula) (three : NativeSource.ThreeCore F) :
    machineOutput (BitRegister.CompilerIO.rawMachine OwnerCacheDriver.program)
      ((BitRegister.CompilerIO.runtimePolynomial 36 OwnerCacheDriver.sourceFuel).eval
        (MatchingDriver.encode F.variableCount F.clauses).length)
      (MatchingDriver.encode F.variableCount F.clauses) =
        MatchingTable.encode ((MeasuredSourceCache.build F three).value.data.ownerData.map
          (fun index => some index.val)) := by
  rw [machine_source, sourceCache_ownerData]

end PNP.Concrete.NativeNormalization.OwnerCacheSourceBridge



namespace PNP.Concrete.NativeNormalization.ModeCacheSourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks
open NativeBasis NativeSource OwnerCacheSourceBridge

theorem matching_read {F : CNFFormula} (C : NativeContext.CutData F) (i : Fin F.clauses.length) :
    MatchingTable.read (matchingEntries C) i.val = (MeasuredAccess.matchAt C i).value.map Fin.val := by
  have checked := ExplorationSourceBridge.read_source (MeasuredAccess.table C) i
  rw [MeasuredMatching.readMatching_value] at checked
  change MatchingTable.read (matchingEntries C) i.val = (C.matchAt i).map Fin.val at checked
  rw [MeasuredAccess.matchAt_value]
  exact checked

theorem variable_position {width : Nat} (indices : List (Fin width)) (target : Fin width) :
    TableOwner.vertexOwner (indices.map (fun i => (⟨false,i.val⟩ : CNFLiteral))) target.val =
      if (MeasuredSelection.contains target indices).value then
        some (MeasuredSelection.position target indices).value else none := by
  have checked := CompactClauseSourceBridge.owner_position indices target 0
  simpa only [TableOwner.vertexOwner,CompactClauseSourceBridge.selectedVertices,Nat.zero_add] using checked

theorem transported_source {F : CNFFormula} (C : NativeContext.CutData F)
    (i : Fin (CNFCore.positions F).length) :
    CacheMode.transportedValue (matchingEntries C) (variableVertices C)
      (MeasuredAccess.atClause C i).value.val =
      (MeasuredChoice.transported C i).value.map Fin.val := by
  rw [CacheMode.transportedValue,matching_read]
  unfold MeasuredChoice.transported
  dsimp only
  split
  · rename_i absent
    simp only [absent,Option.map_none,Option.bind_none]
  · rename_i v found
    have member : v ∈ C.variableData := by
      rw [C.variable_eq]
      apply (CNFCore.variables_mem F v).mpr
      apply CNFCore.matched_inside F i v
      exact (MeasuredChoice.matchingLookup_value C i).symm.trans found
    have present : (MeasuredSelection.contains v C.variableData).value = true :=
      (MeasuredSelection.contains_value v C.variableData).trans (decide_eq_true member)
    simp only [found,Option.map_some,Option.bind_some]
    change TableOwner.vertexOwner (C.variableData.map (fun j => (⟨false,j.val⟩ : CNFLiteral))) v.val = _
    rw [variable_position,present]
    rfl

theorem choose_indices {n : Nat} (ls : Slot → Literal n) (v : Fin n) :
    CacheSlot.value (ls .first).index.val (ls .middle).index.val v.val =
      slotIndex (chooseSlot ls v) := by
  have flag (a : Fin n) : (a.val == v.val) = decide (a = v) := by
    by_cases eq : a = v
    · subst a
      change decide (v.val = v.val) = decide (v = v)
      rw [decide_eq_true rfl,decide_eq_true rfl]
    · have natNe : a.val ≠ v.val := fun h => eq (Fin.ext h)
      change decide (a.val = v.val) = decide (a = v)
      rw [decide_eq_false natNe,decide_eq_false eq]
  unfold CacheSlot.value chooseSlot
  rw [flag,flag]
  by_cases hf : (ls .first).index = v <;> by_cases hm : (ls .middle).index = v <;>
    simp only [hf,hm,decide_true,decide_false,Bool.false_eq_true,ite_false,ite_true,slotIndex]

theorem encodedValue_get (literals : List CNFLiteral) (target : Nat) (shape : literals.length = 3) :
    CacheSlot.encodedValue literals target =
      CacheSlot.value (literals[0]'(by omega)).variableIndex (literals[1]'(by omega)).variableIndex target := by
  cases literals with
  | nil => simp only [List.length_nil] at shape; omega
  | cons first rest =>
      cases rest with
      | nil => simp only [List.length_cons,List.length_nil] at shape; omega
      | cons middle rest =>
          rw [CacheSlot.encodedValue_cons_cons]
          rfl

theorem dense_get {F : CNFFormula} (C : NativeContext.Prepared F) (i : Fin (CNFCore.positions F).length) :
    C.literals[i.val]?.getD [] = C.denseLiterals i := by
  have bound : i.val < C.literals.length := by
    rw [C.literals_eq,CNFCore.compact_clauses,List.length_map]
    exact i.isLt
  rw [List.getElem?_eq_getElem bound]
  rfl

theorem choose_source {F : CNFFormula} (C : NativeContext.Prepared F) (three : ThreeCore F)
    (i : Fin (CNFCore.positions F).length) (v : Fin (CNFCore.variables F).length) :
    CacheSlot.encodedValue (C.literals[i.val]?.getD []) v.val =
      slotIndex (MeasuredChoice.choose (MeasuredAccess.literal C three i) v).value := by
  have shape : (C.denseLiterals i).length = 3 := by rw [C.denseLiterals_eq]; exact three i
  rw [dense_get,encodedValue_get _ _ shape,MeasuredChoice.choose_value]
  have checked := choose_indices (fun s => (MeasuredAccess.literal C three i s).value) v
  simpa only [MeasuredAccess.literal_value,NativeContext.Prepared.literal,slotIndex] using checked

theorem mode_source {F : CNFFormula} (C : NativeContext.Prepared F) (three : ThreeCore F)
    (i : Fin (CNFCore.positions F).length) :
    CacheMode.value (matchingEntries C.toCutData) (variableVertices C.toCutData) C.literals
      (MeasuredAccess.atClause C.toCutData i).value.val i.val =
      (MeasuredChoice.mode C three i).value.map slotIndex := by
  rw [CacheMode.value,transported_source]
  unfold MeasuredChoice.mode
  dsimp only
  cases h : (MeasuredChoice.transported C.toCutData i).value with
  | none => rfl
  | some v =>
      simp only [Option.map_some]
      exact congrArg some (choose_source C three i v)

theorem clauseData_ofFn {F : CNFFormula} (C : NativeContext.CutData F) :
    C.clauseData =
      List.ofFn (fun i : Fin (CNFCore.positions F).length => (MeasuredAccess.atClause C i).value) := by
  apply List.ext_getElem
  · rw [List.length_ofFn]
    exact congrArg List.length C.clause_eq
  · intro index before after
    simp only [List.getElem_ofFn,MeasuredAccess.atClause,MeasuredAccess.get_value]

theorem values_ofFn (table : MatchingTable.Entries) (variables : List CNFLiteral)
    (formula : List (List CNFLiteral)) (n : Nat) (entries : Fin n → CNFLiteral) (offset : Nat) :
    CacheMode.values table variables formula (List.ofFn entries) offset =
      List.ofFn (fun i => CacheMode.value table variables formula (entries i).variableIndex (offset + i.val)) := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ,CacheMode.values,List.ofFn_succ,ih]
      congr 1
      apply congrArg List.ofFn
      funext i
      have same : offset + 1 + i.val = offset + i.succ.val := by
        change offset + 1 + i.val = offset + (i.val + 1)
        omega
      rw [same]

def modeEntries {F : CNFFormula} (C : NativeContext.Prepared F) (three : ThreeCore F) : MatchingTable.Entries :=
  List.ofFn (fun i : Fin (CNFCore.positions F).length => (MeasuredChoice.mode C three i).value.map slotIndex)

theorem values_source {F : CNFFormula} (C : NativeContext.Prepared F) (three : ThreeCore F) :
    CacheMode.values (matchingEntries C.toCutData) (variableVertices C.toCutData) C.literals
      (clauseVertices C.toCutData) 0 = modeEntries C three := by
  unfold clauseVertices
  rw [clauseData_ofFn,List.map_ofFn,values_ofFn]
  unfold modeEntries
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_def,Nat.zero_add]
  exact mode_source C three i

theorem modeValues_source (F : CNFFormula) (three : ThreeCore F) :
    ModeCacheDriver.modeValues F.variableCount F.clauses =
      modeEntries (MeasuredPrepared.prepare F).value three := by
  dsimp only [ModeCacheDriver.modeValues]
  rw [CutTraceSourceBridge.trace_value_source,FullMatchingSourceBridge.fullTable_source,
    CutSelectionSourceBridge.selected_clauses,CutSelectionSourceBridge.selected_variables,
    ← CutSelectionSourceBridge.cut_clause_projection,← CutSelectionSourceBridge.cut_variable_projection,
    PreparedStateSourceBridge.denseValue_source]
  exact values_source (MeasuredPrepared.prepare F).value three

theorem result_source (F : CNFFormula) (three : ThreeCore F) :
    (ModeCacheDriver.result (MatchingDriver.encode F.variableCount F.clauses)).registers.output =
      MatchingTable.encode (modeEntries (MeasuredPrepared.prepare F).value three) := by
  rw [ModeCacheDriver.result_canonical,modeValues_source F three]
theorem polynomial_source (F : CNFFormula) (three : ThreeCore F) :
    ModeCacheDriver.polynomial.output (MatchingDriver.encode F.variableCount F.clauses) =
      MatchingTable.encode (modeEntries (MeasuredPrepared.prepare F).value three) := by
  rw [ModeCacheDriver.polynomial_canonical,modeValues_source F three]
theorem machine_source (F : CNFFormula) (three : ThreeCore F) :
    machineOutput (BitRegister.CompilerIO.rawMachine ModeCacheDriver.program)
      ((BitRegister.CompilerIO.runtimePolynomial 36 ModeCacheDriver.sourceFuel).eval
        (MatchingDriver.encode F.variableCount F.clauses).length)
      (MatchingDriver.encode F.variableCount F.clauses) =
        MatchingTable.encode (modeEntries (MeasuredPrepared.prepare F).value three) := by
  rw [ModeCacheDriver.machine_canonical,modeValues_source F three]

def cachedModes {n c : Nat} {selection : Selection n c}
    (ops : MeasuredOperations.Operations selection) : MatchingTable.Entries :=
  (MeasuredCache.build ops).value.modeData.map (fun cell => cell.map slotIndex)
theorem cache_modeData_source {F : CNFFormula} (C : NativeContext.Prepared F) (three : ThreeCore F) :
    modeEntries C three = cachedModes (MeasuredOperations.source C three) := by
  unfold cachedModes
  rw [(MeasuredCache.build (MeasuredOperations.source C three)).value.mode_eq,List.map_ofFn]
  unfold modeEntries
  apply congrArg List.ofFn
  funext i
  rw [MeasuredChoice.mode_value]
  rfl
theorem transport_cachedModes {n c n' c' : Nat} (hn : n = n') (hc : c = c')
    {selection : Selection n c} (ops : MeasuredOperations.Operations selection) :
    cachedModes (MeasuredOperations.transport hn hc ops) = cachedModes ops := by
  cases hn
  cases hc
  rfl
theorem sourceCache_modeData (F : CNFFormula) (three : ThreeCore F) :
    (MeasuredSourceCache.build F three).value.data.modeData.map (fun cell => cell.map slotIndex) =
      modeEntries (MeasuredPrepared.prepare F).value three := by
  change cachedModes (MeasuredOperations.transport _ _
    (MeasuredOperations.source (MeasuredPrepared.prepare F).value three)) = _
  rw [transport_cachedModes]
  exact (cache_modeData_source (MeasuredPrepared.prepare F).value three).symm
theorem machine_source_cache (F : CNFFormula) (three : ThreeCore F) :
    machineOutput (BitRegister.CompilerIO.rawMachine ModeCacheDriver.program)
      ((BitRegister.CompilerIO.runtimePolynomial 36 ModeCacheDriver.sourceFuel).eval
        (MatchingDriver.encode F.variableCount F.clauses).length)
      (MatchingDriver.encode F.variableCount F.clauses) =
        MatchingTable.encode ((MeasuredSourceCache.build F three).value.data.modeData.map
          (fun cell => cell.map slotIndex)) := by
  rw [machine_source F three,sourceCache_modeData]

end PNP.Concrete.NativeNormalization.ModeCacheSourceBridge


namespace PNP.Concrete.NativeNormalization.SourceCacheSourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks
open NativeBasis NativeSource

def ownerVertices {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S) : List CNFLiteral :=
  cache.ownerData.map (fun index => ⟨true,index.val⟩)
def ownerCells {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S) : MatchingTable.Entries :=
  cache.ownerData.map (fun index => some index.val)
def modeCells {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S) : MatchingTable.Entries :=
  cache.modeData.map (fun cell => cell.map slotIndex)
def slotCells {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S) : MatchingTable.Entries :=
  cache.slotData.map (fun slot => some (slotIndex slot))
def eraseLiteral {n : Nat} (literal : Literal n) : CNFLiteral := ⟨literal.positive,literal.index.val⟩
def literalRow {n : Nat} (triple : MeasuredCache.Triple n) : List CNFLiteral :=
  [eraseLiteral triple.1,eraseLiteral triple.2.1,eraseLiteral triple.2.2]
def literalRows {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S) : List (List CNFLiteral) :=
  cache.literalData.map literalRow

theorem owner_encoding {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S) :
    MatchingTable.encode (ownerCells cache) = SearchVertices.encodeVertices (ownerVertices cache) := by
  simp only [MatchingTable.encode,MatchingTable.clauses,SearchVertices.encodeVertices,ownerCells,
    ownerVertices,List.map_map,Function.comp_def,MatchingTable.entryClause]
theorem slots_from_modes {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S) :
    CacheSlots.values (modeCells cache) (ownerVertices cache) = slotCells cache := by
  unfold CacheSlots.values modeCells ownerVertices slotCells
  rw [cache.mode_eq,cache.owner_eq,cache.slot_eq]
  simp only [List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext v
  change MatchingTable.read (List.ofFn (fun i => (S.mode i).map slotIndex)) (S.owner v).val =
    some (slotIndex (S.slot v))
  unfold MatchingTable.read
  rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact (S.owner v).isLt),List.getElem_ofFn]
  simp only [Option.getD_some,S.ownerMode,Option.map_some]

theorem mode_input (F : CNFFormula) (three : ThreeCore F) :
    (ModeCacheDriver.result (MatchingDriver.encode F.variableCount F.clauses)).registers.output =
      MatchingTable.encode (modeCells (MeasuredSourceCache.build F three).value.data) := by
  rw [ModeCacheSourceBridge.result_source F three]
  unfold modeCells
  rw [ModeCacheSourceBridge.sourceCache_modeData]
theorem owner_input (F : CNFFormula) (three : ThreeCore F) :
    SourceCacheDriver.owners (ModeCacheDriver.result (MatchingDriver.encode F.variableCount F.clauses)) =
      SearchVertices.encodeVertices (ownerVertices (MeasuredSourceCache.build F three).value.data) := by
  rw [← owner_encoding]
  change ModeCacheDriver.owners (ModeCacheDriver.result _) = _
  rw [ModeCacheDriver.result_owners,OwnerCacheSourceBridge.result_source]
  unfold ownerCells
  rw [OwnerCacheSourceBridge.sourceCache_ownerData]
theorem slots_source (F : CNFFormula) (three : ThreeCore F) :
    SourceCacheDriver.slots (SourceCacheDriver.result (MatchingDriver.encode F.variableCount F.clauses)) =
      MatchingTable.encode (slotCells (MeasuredSourceCache.build F three).value.data) := by
  have checked := SourceCacheDriver.derived_slots
    (ModeCacheDriver.result (MatchingDriver.encode F.variableCount F.clauses))
    (modeCells (MeasuredSourceCache.build F three).value.data)
    (ownerVertices (MeasuredSourceCache.build F three).value.data)
    (mode_input F three) (owner_input F three)
  rw [slots_from_modes] at checked
  exact checked
theorem modes_source (F : CNFFormula) (three : ThreeCore F) :
    SourceCacheDriver.modes (SourceCacheDriver.result (MatchingDriver.encode F.variableCount F.clauses)) =
      MatchingTable.encode (modeCells (MeasuredSourceCache.build F three).value.data) :=
  (SourceCacheDriver.result_cache _).1.trans (mode_input F three)
theorem owners_source (F : CNFFormula) (three : ThreeCore F) :
    SourceCacheDriver.owners (SourceCacheDriver.result (MatchingDriver.encode F.variableCount F.clauses)) =
      MatchingTable.encode (ownerCells (MeasuredSourceCache.build F three).value.data) := by
  rw [owner_encoding]
  exact (SourceCacheDriver.result_cache _).2.1.trans (owner_input F three)

theorem three_gets (xs : List CNFLiteral) (shape : xs.length = 3) :
    xs = [xs[0]'(by omega),xs[1]'(by omega),xs[2]'(by omega)] := by
  apply List.ext_getElem
  · simp only [List.length_cons,List.length_nil]
    exact shape
  · intro index before after
    have casesIndex : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases casesIndex with h | h | h <;> subst index <;> rfl

theorem literal_rows_source {F : CNFFormula} (C : NativeContext.Prepared F) (three : ThreeCore F) :
    C.literals = List.ofFn (fun i : Fin (CNFCore.positions F).length =>
      literalRow (C.literal three i .first,C.literal three i .middle,C.literal three i .last)) := by
  apply List.ext_getElem
  · rw [List.length_ofFn,C.literals_eq,CNFCore.compact_clauses,List.length_map]
  · intro index before after
    have bound : index < (CNFCore.positions F).length := by
      rw [List.length_ofFn] at after
      exact after
    let i : Fin (CNFCore.positions F).length := ⟨index,bound⟩
    rw [List.getElem_ofFn]
    change C.denseLiterals i = literalRow (C.literal three i .first,C.literal three i .middle,C.literal three i .last)
    have shape : (C.denseLiterals i).length = 3 := by rw [C.denseLiterals_eq]; exact three i
    simpa only [literalRow,eraseLiteral,NativeContext.Prepared.literal,slotIndex] using three_gets (C.denseLiterals i) shape

def cachedLiterals {n c : Nat} {S : Selection n c} (ops : MeasuredOperations.Operations S) : List (List CNFLiteral) :=
  literalRows (MeasuredCache.build ops).value
theorem cached_literals_source {F : CNFFormula} (C : NativeContext.Prepared F) (three : ThreeCore F) :
    cachedLiterals (MeasuredOperations.source C three) = C.literals := by
  unfold cachedLiterals literalRows
  rw [(MeasuredCache.build (MeasuredOperations.source C three)).value.literal_eq,List.map_ofFn]
  exact (literal_rows_source C three).symm
theorem transport_cachedLiterals {n c n' c' : Nat} (hn : n = n') (hc : c = c')
    {S : Selection n c} (ops : MeasuredOperations.Operations S) :
    cachedLiterals (MeasuredOperations.transport hn hc ops) = cachedLiterals ops := by
  cases hn
  cases hc
  rfl
theorem sourceCache_literalData (F : CNFFormula) (three : ThreeCore F) :
    literalRows (MeasuredSourceCache.build F three).value.data = (MeasuredPrepared.prepare F).value.literals := by
  change cachedLiterals (MeasuredOperations.transport _ _
    (MeasuredOperations.source (MeasuredPrepared.prepare F).value three)) = _
  rw [transport_cachedLiterals]
  exact cached_literals_source (MeasuredPrepared.prepare F).value three
theorem literals_source (F : CNFFormula) (three : ThreeCore F) :
    SourceCacheDriver.literals (SourceCacheDriver.result (MatchingDriver.encode F.variableCount F.clauses)) =
      GraphQuery.clauseData (literalRows (MeasuredSourceCache.build F three).value.data) := by
  rw [(SourceCacheDriver.result_cache _).2.2.1,ModeCacheDriver.result_literals_canonical,
    PreparedStateSourceBridge.denseValue_source,sourceCache_literalData]

theorem retained_selections (F : CNFFormula) :
    (ModeCacheDriver.result (MatchingDriver.encode F.variableCount F.clauses)).variables =
      SearchVertices.encodeVertices (OwnerCacheSourceBridge.variableVertices (MeasuredPrepared.prepare F).value.toCutData) ∧
    (ModeCacheDriver.result (MatchingDriver.encode F.variableCount F.clauses)).clauses =
      SearchVertices.encodeVertices (OwnerCacheSourceBridge.clauseVertices (MeasuredPrepared.prepare F).value.toCutData) := by
  let input := MatchingDriver.encode F.variableCount F.clauses
  have mode := ModeCacheDriver.derived_frame (OwnerCacheDriver.result input)
  have owner := OwnerCacheDriver.derived_frame (PreparedDriver.result input)
  exact ⟨mode.2.2.2.2.2.trans (owner.2.2.2.2.2.trans (PreparedStateSourceBridge.variables_source F)),
    mode.2.2.2.2.1.trans (owner.2.2.2.2.1.trans (PreparedStateSourceBridge.clauses_source F))⟩
theorem source_dimensions (F : CNFFormula) (three : ThreeCore F) :
    (MeasuredSourceCache.build F three).value.columns = (MeasuredPrepared.prepare F).value.variableData.length ∧
    (MeasuredSourceCache.build F three).value.rows = (MeasuredPrepared.prepare F).value.clauseData.length := by
  constructor
  · exact MeasuredAccess.length_value _
  · exact MeasuredAccess.length_value _
theorem dimensions_source (F : CNFFormula) (three : ThreeCore F) :
    SourceCacheDriver.columns (SourceCacheDriver.result (MatchingDriver.encode F.variableCount F.clauses)) =
      List.replicate (MeasuredSourceCache.build F three).value.columns true ∧
    SourceCacheDriver.rows (SourceCacheDriver.result (MatchingDriver.encode F.variableCount F.clauses)) =
      List.replicate (MeasuredSourceCache.build F three).value.rows true := by
  have dimensions := SourceCacheDriver.result_dimensions (MatchingDriver.encode F.variableCount F.clauses)
  rw [(retained_selections F).1,(retained_selections F).2,
    SourceCacheDriver.count_vertices,SourceCacheDriver.count_vertices] at dimensions
  simp only [OwnerCacheSourceBridge.variableVertices,OwnerCacheSourceBridge.clauseVertices,List.length_map] at dimensions
  rw [(source_dimensions F three).1,(source_dimensions F three).2]
  exact dimensions

structure MatchesCache (F : CNFFormula) (three : ThreeCore F) (r : CutDriver.State) : Prop where
  columnsRead : SourceCacheDriver.columns r = List.replicate (MeasuredSourceCache.build F three).value.columns true
  rowsRead : SourceCacheDriver.rows r = List.replicate (MeasuredSourceCache.build F three).value.rows true
  literalRead : SourceCacheDriver.literals r = GraphQuery.clauseData (literalRows (MeasuredSourceCache.build F three).value.data)
  ownerRead : SourceCacheDriver.owners r = MatchingTable.encode (ownerCells (MeasuredSourceCache.build F three).value.data)
  slotRead : SourceCacheDriver.slots r = MatchingTable.encode (slotCells (MeasuredSourceCache.build F three).value.data)
  modeRead : SourceCacheDriver.modes r = MatchingTable.encode (modeCells (MeasuredSourceCache.build F three).value.data)

theorem complete_cache_source (F : CNFFormula) (three : ThreeCore F) :
    MatchesCache F three (SourceCacheDriver.result (MatchingDriver.encode F.variableCount F.clauses)) :=
  ⟨(dimensions_source F three).1,(dimensions_source F three).2,literals_source F three,
    owners_source F three,slots_source F three,modes_source F three⟩
theorem complete_cache_fromSource (F : CNFFormula) :
    MatchesCache (NativeTseitin.frontend F) (NativeFrontend.frontend_three F)
      (SourceCacheDriver.result (MatchingDriver.encode (NativeTseitin.frontend F).variableCount (NativeTseitin.frontend F).clauses)) :=
  complete_cache_source (NativeTseitin.frontend F) (NativeFrontend.frontend_three F)
theorem polynomial_source (F : CNFFormula) (three : ThreeCore F) :
    SourceCacheDriver.polynomial.output (MatchingDriver.encode F.variableCount F.clauses) =
      MatchingTable.encode (slotCells (MeasuredSourceCache.build F three).value.data) := by
  rw [SourceCacheDriver.polynomial_slots,slots_source F three]
theorem machine_source (F : CNFFormula) (three : ThreeCore F) :
    machineOutput (BitRegister.CompilerIO.rawMachine SourceCacheDriver.program)
      ((BitRegister.CompilerIO.runtimePolynomial 36 SourceCacheDriver.sourceFuel).eval
        (MatchingDriver.encode F.variableCount F.clauses).length)
      (MatchingDriver.encode F.variableCount F.clauses) =
        MatchingTable.encode (slotCells (MeasuredSourceCache.build F three).value.data) := by
  rw [SourceCacheDriver.machine_slots,slots_source F three]
theorem polynomial_all_raw_inputs (input : BitString) :
    boundedDecide (BitRegister.CompilerIO.rawMachine SourceCacheDriver.program)
      ((BitRegister.CompilerIO.runtimePolynomial 36 SourceCacheDriver.sourceFuel).eval input.length) input = .accept :=
  SourceCacheDriver.polynomial_accepts input
theorem bounded_all_raw_states (input : BitString) :
    (SourceCacheDriver.result input).store.Bounded (SourceCacheDriver.resultSize.eval input.length) :=
  SourceCacheDriver.result_bounded input

end PNP.Concrete.NativeNormalization.SourceCacheSourceBridge



namespace PNP.Concrete.NativeNormalization.CandidateSourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks
open NativeBasis NativeSource SourceCacheSourceBridge

theorem owner_lookup {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S) (v : Fin n) :
    MatchingTable.read (ownerCells cache) v.val = some (S.owner v).val := by
  unfold ownerCells
  rw [cache.owner_eq,List.map_ofFn]
  unfold MatchingTable.read
  rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact v.isLt),List.getElem_ofFn]
  rfl
theorem slot_lookup {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S) (v : Fin n) :
    MatchingTable.read (slotCells cache) v.val = some (slotIndex (S.slot v)) := by
  unfold slotCells
  rw [cache.slot_eq,List.map_ofFn]
  unfold MatchingTable.read
  rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact v.isLt),List.getElem_ofFn]
  rfl
theorem literal_lookup {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S) (i : Fin c) :
    (literalRows cache)[i.val]?.getD [] =
      [eraseLiteral (S.literal i .first),eraseLiteral (S.literal i .middle),eraseLiteral (S.literal i .last)] := by
  unfold literalRows
  rw [cache.literal_eq,List.map_ofFn]
  rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact i.isLt),List.getElem_ofFn]
  rfl
theorem literal_split {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S)
    (i : Fin c) (s : Slot) :
    ∃ leading rest : List CNFLiteral, leading.length = slotIndex s ∧
      (literalRows cache)[i.val]?.getD [] = leading ++ eraseLiteral (S.literal i s)::rest := by
  cases s with
  | first =>
      exact ⟨[],[eraseLiteral (S.literal i .middle),eraseLiteral (S.literal i .last)],
        rfl,literal_lookup cache i⟩
  | middle =>
      exact ⟨[eraseLiteral (S.literal i .first)],[eraseLiteral (S.literal i .last)],
        rfl,literal_lookup cache i⟩
  | last =>
      exact ⟨[eraseLiteral (S.literal i .first),eraseLiteral (S.literal i .middle)],[],
        rfl,literal_lookup cache i⟩
theorem literal_query_canonical {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S)
    (r : CacheLiteral.State) (i : Fin c) (s : Slot)
    (formulaRead : r.formula = GraphQuery.clauseData (literalRows cache))
    (rowRead : r.index = List.replicate i.val true)
    (positionRead : r.remaining = List.replicate (slotIndex s) true) :
    (CacheLiteral.result r).registers.target = List.replicate (S.literal i s).index.val true ∧
      (CacheLiteral.result r).registers.output = [(S.literal i s).positive] := by
  obtain ⟨leading,rest,length,split⟩ := literal_split cache i s
  rw [← length] at positionRead
  exact CacheLiteral.canonical r (literalRows cache) i.val leading (eraseLiteral (S.literal i s)) rest
    formulaRead rowRead positionRead split
theorem sigma_query_canonical {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S)
    (r : CacheSigma.State) (v : Fin n)
    (formulaRead : r.core.formula = GraphQuery.clauseData (literalRows cache))
    (ownerRead : r.matching = MatchingTable.encode (ownerCells cache))
    (slotRead : r.counter = MatchingTable.encode (slotCells cache))
    (indexRead : r.core.index = List.replicate v.val true) :
    (CacheSigma.result r).registers.output = [NativeBasis.sigma S v] := by
  obtain ⟨leading,rest,length,split⟩ := literal_split cache (S.owner v) (S.slot v)
  have slot := slot_lookup cache v
  rw [← length] at slot
  exact (CacheSigma.canonical r (ownerCells cache) (slotCells cache) (literalRows cache)
    v.val (S.owner v).val leading (eraseLiteral (S.literal (S.owner v) (S.slot v))) rest
    ownerRead slotRead formulaRead indexRead (owner_lookup cache v) slot split).2

def extendSigma {n c : Nat} (S : Selection n c) (i : Nat) : Bool :=
  if h : i < n then NativeBasis.sigma S ⟨i,h⟩ else false
theorem cache_reader_correct {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S) :
    CandidateBits.ReaderCorrect (GraphQuery.clauseData (literalRows cache))
      (MatchingTable.encode (ownerCells cache)) (MatchingTable.encode (slotCells cache)) n (extendSigma S) := by
  intro r i hi formulaRead ownerRead slotRead indexRead
  have checked := sigma_query_canonical cache r ⟨i,hi⟩ formulaRead ownerRead slotRead indexRead
  simpa only [extendSigma,dif_pos hi] using checked
theorem candidate_from_cache {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S)
    (r : CutDriver.State)
    (columns : SourceCacheDriver.columns r = List.replicate n true)
    (literals : SourceCacheDriver.literals r = GraphQuery.clauseData (literalRows cache))
    (owners : SourceCacheDriver.owners r = MatchingTable.encode (ownerCells cache))
    (slots : SourceCacheDriver.slots r = MatchingTable.encode (slotCells cache)) :
    (SourceCandidate.derived r).registers.output = List.ofFn (NativeBasis.sigma S) := by
  have dimensions : (SourceCacheDriver.columns r).length = n := by rw [columns,List.length_replicate]
  have correct : CandidateBits.ReaderCorrect (SourceCacheDriver.literals r)
      (SourceCacheDriver.owners r) (SourceCacheDriver.slots r) n (extendSigma S) := by
    rw [literals,owners,slots]
    exact cache_reader_correct cache
  rw [SourceCandidate.derived_canonical r n (extendSigma S) dimensions correct]
  apply congrArg List.ofFn
  funext i
  simp only [extendSigma,dif_pos i.isLt]

theorem result_source (F : CNFFormula) (three : ThreeCore F) :
    (SourceCandidate.result (MatchingDriver.encode F.variableCount F.clauses)).registers.output =
      (MeasuredCandidate.assignment (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value := by
  have cache := complete_cache_source F three
  rw [MeasuredCandidate.assignment_value]
  exact candidate_from_cache (MeasuredSourceCache.build F three).value.data
    (SourceCacheDriver.result (MatchingDriver.encode F.variableCount F.clauses))
    cache.columnsRead cache.literalRead cache.ownerRead cache.slotRead
theorem result_fromSource (F : CNFFormula) :
    (SourceCandidate.result (MatchingDriver.encode (NativeTseitin.frontend F).variableCount
      (NativeTseitin.frontend F).clauses)).registers.output =
      (MeasuredCandidate.assignment (MeasuredCache.operations (MeasuredSourceCache.fromSource F).value.data)).value :=
  result_source (NativeTseitin.frontend F) (NativeFrontend.frontend_three F)
theorem polynomial_source (F : CNFFormula) (three : ThreeCore F) :
    SourceCandidate.polynomial.output (MatchingDriver.encode F.variableCount F.clauses) =
      (MeasuredCandidate.assignment (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value := by
  rw [SourceCandidate.polynomial_output,result_source F three]
theorem machine_source (F : CNFFormula) (three : ThreeCore F) :
    machineOutput (BitRegister.CompilerIO.rawMachine SourceCandidate.program)
      ((BitRegister.CompilerIO.runtimePolynomial 36 SourceCandidate.sourceFuel).eval
        (MatchingDriver.encode F.variableCount F.clauses).length)
      (MatchingDriver.encode F.variableCount F.clauses) =
      (MeasuredCandidate.assignment (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value := by
  rw [SourceCandidate.machine_output,polynomial_source F three]
theorem cache_retained (F : CNFFormula) (three : ThreeCore F) :
    MatchesCache F three (SourceCandidate.result (MatchingDriver.encode F.variableCount F.clauses)) := by
  have before := complete_cache_source F three
  have fields := SourceCandidate.result_cache (MatchingDriver.encode F.variableCount F.clauses)
  exact ⟨fields.1.trans before.columnsRead,fields.2.1.trans before.rowsRead,
    fields.2.2.2.2.2.trans before.literalRead,fields.2.2.2.2.1.trans before.ownerRead,
    fields.2.2.1.trans before.slotRead,fields.2.2.2.1.trans before.modeRead⟩
theorem polynomial_all_raw_inputs (input : BitString) :
    boundedDecide (BitRegister.CompilerIO.rawMachine SourceCandidate.program)
      ((BitRegister.CompilerIO.runtimePolynomial 36 SourceCandidate.sourceFuel).eval input.length) input = .accept :=
  SourceCandidate.polynomial_accepts input
theorem bounded_all_raw_states (input : BitString) :
    (SourceCandidate.result input).store.Bounded (SourceCandidate.resultSize.eval input.length) :=
  SourceCandidate.result_bounded input

end PNP.Concrete.NativeNormalization.CandidateSourceBridge


namespace PNP.Concrete.NativeNormalization.CheckSourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks
open NativeBasis NativeSource SourceCacheSourceBridge

theorem assignment_get {n c : Nat} (S : Selection n c) (v : Fin n) :
    (List.ofFn (NativeBasis.sigma S))[v.val]?.getD false = NativeBasis.sigma S v := by
  rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact v.isLt),List.getElem_ofFn]
  rfl
theorem value_erased {n c : Nat} (S : Selection n c) (lit : Literal n) :
    CandidateTruth.value (List.ofFn (NativeBasis.sigma S)) (eraseLiteral lit) =
      decide (NativeBasis.sigma S lit.index = lit.positive) := by
  change decide ((List.ofFn (NativeBasis.sigma S))[lit.index.val]?.getD false = lit.positive) = _
  rw [assignment_get]
theorem clause_query_canonical {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S)
    (r : CandidateTruth.State) (i : Fin c)
    (formulaRead : r.core.formula = GraphQuery.clauseData (literalRows cache))
    (assignmentRead : r.matching = List.ofFn (NativeBasis.sigma S))
    (rowRead : r.core.index = List.replicate i.val true) :
    (CandidateTruth.clauseResult r).registers.output =
      [NativeSource.clauseTrue S (NativeBasis.sigma S) i] := by
  have checked := CandidateTruth.clause_canonical r (literalRows cache) i.val
    (eraseLiteral (S.literal i .first)) (eraseLiteral (S.literal i .middle))
    (eraseLiteral (S.literal i .last)) formulaRead rowRead (CandidateSourceBridge.literal_lookup cache i)
  rw [assignmentRead,value_erased,value_erased,value_erased] at checked
  exact checked

def extendTruth {n c : Nat} (S : Selection n c) (i : Nat) : Bool :=
  if h : i < c then NativeSource.clauseTrue S (NativeBasis.sigma S) ⟨i,h⟩ else false
theorem cache_reader_correct {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S) :
    FirstFailure.ReaderCorrect (GraphQuery.clauseData (literalRows cache))
      (List.ofFn (NativeBasis.sigma S)) c (extendTruth S) := by
  intro r i hi formulaRead assignmentRead indexRead
  have checked := clause_query_canonical cache r ⟨i,hi⟩ formulaRead assignmentRead indexRead
  simpa only [extendTruth,dif_pos hi] using checked

theorem find_finRange (test : Nat → Bool) (count : Nat) :
    FirstFailure.find test 0 count =
      ((List.finRange count).find? (fun i => !test i.val)).map Fin.val := by
  rw [FirstFailure.find_ofFn]
  simp only [Nat.zero_add]
  have mapped : List.ofFn (fun i : Fin count => i.val) = (List.finRange count).map Fin.val := by
    rw [List.finRange,List.map_ofFn]
    rfl
  rw [mapped,List.find?_map]
  rfl
theorem find_source {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S) :
    FirstFailure.find (extendTruth S) 0 c =
      (MeasuredCandidate.firstFailed (MeasuredCache.operations cache)).value.map Fin.val := by
  rw [find_finRange,MeasuredCandidate.firstFailed_value]
  have predicates : (fun i : Fin c => !extendTruth S i.val) =
      (fun i : Fin c => !NativeSource.clauseTrue S (NativeBasis.sigma S) i) := by
    funext i
    simp only [extendTruth,dif_pos i.isLt]
  rw [predicates]
theorem checked_from_cache {n c : Nat} {S : Selection n c} (cache : MeasuredCache.Cache S)
    (r : CutDriver.State)
    (rows : SourceCacheDriver.rows r = List.replicate c true)
    (literals : SourceCacheDriver.literals r = GraphQuery.clauseData (literalRows cache))
    (assignment : r.registers.output = List.ofFn (NativeBasis.sigma S)) :
    (SourceCheck.derived r).registers.output =
      TableOwner.answer ((MeasuredCandidate.firstFailed (MeasuredCache.operations cache)).value.map Fin.val) := by
  have dimensions : (SourceCacheDriver.rows r).length = c := by rw [rows,List.length_replicate]
  have correct : FirstFailure.ReaderCorrect (SourceCacheDriver.literals r) r.registers.output c
      (extendTruth S) := by
    rw [literals,assignment]
    exact cache_reader_correct cache
  rw [SourceCheck.derived_canonical r c (extendTruth S) dimensions correct,find_source]

theorem result_source (F : CNFFormula) (three : ThreeCore F) :
    (SourceCheck.result (MatchingDriver.encode F.variableCount F.clauses)).registers.output =
      TableOwner.answer ((MeasuredCandidate.firstFailed
        (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value.map Fin.val) := by
  have cache := CandidateSourceBridge.cache_retained F three
  have assignment := CandidateSourceBridge.result_source F three
  rw [MeasuredCandidate.assignment_value] at assignment
  exact checked_from_cache (MeasuredSourceCache.build F three).value.data
    (SourceCandidate.result (MatchingDriver.encode F.variableCount F.clauses))
    cache.rowsRead cache.literalRead assignment
theorem result_fromSource (F : CNFFormula) :
    (SourceCheck.result (MatchingDriver.encode (NativeTseitin.frontend F).variableCount
      (NativeTseitin.frontend F).clauses)).registers.output =
      TableOwner.answer ((MeasuredCandidate.firstFailed
        (MeasuredCache.operations (MeasuredSourceCache.fromSource F).value.data)).value.map Fin.val) :=
  result_source (NativeTseitin.frontend F) (NativeFrontend.frontend_three F)
theorem candidate_retained (F : CNFFormula) (three : ThreeCore F) :
    SourceCheck.candidate (SourceCheck.result (MatchingDriver.encode F.variableCount F.clauses)) =
      (MeasuredCandidate.assignment (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value := by
  rw [SourceCheck.result_candidate,CandidateSourceBridge.result_source F three]
theorem cache_retained (F : CNFFormula) (three : ThreeCore F) :
    MatchesCache F three (SourceCheck.result (MatchingDriver.encode F.variableCount F.clauses)) := by
  have before := CandidateSourceBridge.cache_retained F three
  have fields := SourceCheck.result_cache (MatchingDriver.encode F.variableCount F.clauses)
  exact ⟨fields.1.trans before.columnsRead,fields.2.1.trans before.rowsRead,
    fields.2.2.2.2.2.trans before.literalRead,fields.2.2.2.2.1.trans before.ownerRead,
    fields.2.2.1.trans before.slotRead,fields.2.2.2.1.trans before.modeRead⟩
theorem polynomial_source (F : CNFFormula) (three : ThreeCore F) :
    SourceCheck.polynomial.output (MatchingDriver.encode F.variableCount F.clauses) =
      TableOwner.answer ((MeasuredCandidate.firstFailed
        (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value.map Fin.val) := by
  rw [SourceCheck.polynomial_output,result_source F three]
theorem machine_source (F : CNFFormula) (three : ThreeCore F) :
    machineOutput (BitRegister.CompilerIO.rawMachine SourceCheck.program)
      ((BitRegister.CompilerIO.runtimePolynomial 36 SourceCheck.sourceFuel).eval
        (MatchingDriver.encode F.variableCount F.clauses).length)
      (MatchingDriver.encode F.variableCount F.clauses) =
      TableOwner.answer ((MeasuredCandidate.firstFailed
        (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value.map Fin.val) := by
  rw [SourceCheck.machine_output,polynomial_source F three]
theorem polynomial_all_raw_inputs (input : BitString) :
    boundedDecide (BitRegister.CompilerIO.rawMachine SourceCheck.program)
      ((BitRegister.CompilerIO.runtimePolynomial 36 SourceCheck.sourceFuel).eval input.length) input = .accept :=
  SourceCheck.polynomial_accepts input
theorem bounded_all_raw_states (input : BitString) :
    (SourceCheck.result input).store.Bounded (SourceCheck.resultSize.eval input.length) :=
  SourceCheck.result_bounded input

end PNP.Concrete.NativeNormalization.CheckSourceBridge
