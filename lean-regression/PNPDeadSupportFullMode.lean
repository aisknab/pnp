import PNP.PCCMinDeadSupportFullMode

open PNP PNP.DirectWire

example {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) :
    firstTerminalOpenObligation system current = none ↔ system.ObligationsDischarged current :=
  firstTerminalOpenObligation_eq_none_iff system current

example {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) (coordinate : Fin profileWidth)
    (foundAt : firstTerminalOpenObligation system current = some coordinate) :
    system.role coordinate = .obligation ∧ system.observe current coordinate = true ∧
      ∃ before after : List (Fin profileWidth),
        allFin profileWidth = before ++ coordinate :: after ∧
        ∀ earlier, earlier ∈ before → system.role earlier = .obligation →
          system.observe current earlier = false :=
  firstTerminalOpenObligation_spec system current coordinate foundAt

example {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {current : Implementation inputs outputs}
    (gain : DeadSupportFullModeGain system current) : system.ObligationsDischarged current :=
  gain.currentObligationsDischarged

example {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) :
    (classifyDeadSupportFullMode system current).tag = .accepted ↔
      (deadSupportProperGain current).isSome = true ∧
      (∀ coordinate, system.observe (deadSupportReplacementImplementation current) coordinate =
        system.observe current coordinate) ∧
      system.ObligationsDischarged (deadSupportReplacementImplementation current) :=
  classifyDeadSupportFullMode_accepted_iff system current

example {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) :
    (classifyDeadSupportFullMode system current).tag = .noProperSupport ↔
      deadSupportProperGain current = none :=
  classifyDeadSupportFullMode_noProperSupport_iff system current

example {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {current : Implementation inputs outputs} (gain : DeadSupportFullModeGain system current) :
    terminalFullProfileMinimum system (deadSupportReplacementImplementation current) =
      terminalFullProfileMinimum system current :=
  gain.fullProfileMinimum

example {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {current : Implementation inputs outputs} (gain : DeadSupportFullModeGain system current) :
    0 < deadSupportGateCount current ∧
      deadSupportGateCount current < current.gateCount ∧
      Equivalent (deadSupportReplacementImplementation current).candidate.program
        (deadSupportReplacementImplementation current).candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      (∀ coordinate, system.observe (deadSupportReplacementImplementation current) coordinate =
        system.observe current coordinate) ∧
      system.ObligationsDischarged current ∧
      system.ObligationsDischarged (deadSupportReplacementImplementation current) ∧
      (deadSupportReplacementImplementation current).gateCount + deadSupportGateCount current =
        current.gateCount ∧
      residualSlack current = residualSlack (deadSupportReplacementImplementation current) +
        deadSupportGateCount current ∧
      StrictEquivalentGain current (deadSupportReplacementImplementation current) ∧
      residualSlack (deadSupportReplacementImplementation current) < residualSlack current :=
  gain.checked

example {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) :
    match classifyDeadSupportFullMode system current with
    | .noProperSupport _ => deadSupportProperGain current = none
    | .profileMismatch _ _ coordinate _ =>
        system.observe (deadSupportReplacementImplementation current) coordinate ≠
          system.observe current coordinate ∧
        ∃ before after : List (Fin profileWidth),
          allFin profileWidth = before ++ coordinate :: after ∧
          ∀ earlier, earlier ∈ before →
            system.observe (deadSupportReplacementImplementation current) earlier =
              system.observe current earlier
    | .openObligation _ _ _ coordinate _ =>
        (∀ index, system.observe (deadSupportReplacementImplementation current) index =
          system.observe current index) ∧
        system.role coordinate = .obligation ∧
        system.observe (deadSupportReplacementImplementation current) coordinate = true ∧
        ∃ before after : List (Fin profileWidth),
          allFin profileWidth = before ++ coordinate :: after ∧
          ∀ earlier, earlier ∈ before → system.role earlier = .obligation →
            system.observe (deadSupportReplacementImplementation current) earlier = false
    | .accepted _ =>
        system.ObligationsDischarged current ∧
        system.ObligationsDischarged (deadSupportReplacementImplementation current) ∧
        StrictEquivalentGain current (deadSupportReplacementImplementation current) ∧
        residualSlack (deadSupportReplacementImplementation current) < residualSlack current :=
  classifyDeadSupportFullMode_checked system current

private def twoGates : Program 1 2 :=
  (Program.empty.snoc ⟨.input 0, .input 0⟩).snoc ⟨.gate 0, .constant true⟩

private def current : Implementation 1 1 :=
  (Candidate.ofDirectWireWord twoGates ⟨fun _ => .gate 0⟩).toImplementation

private def noDead : Implementation 1 1 :=
  (Candidate.ofDirectWireWord
    (Program.empty.snoc ⟨.input 0, .input 0⟩) ⟨fun _ => .gate 0⟩).toImplementation

private def allDead : Implementation 1 0 :=
  (Candidate.ofDirectWireWord twoGates ⟨Fin.elim0⟩).toImplementation

private def empty : Implementation 0 0 :=
  (Candidate.ofDirectWireWord Program.empty ⟨Fin.elim0⟩).toImplementation

private def zeroProfile {inputs outputs : Nat} : TerminalProfileSystem inputs outputs 0 where
  role := Fin.elim0
  observe := fun _ => Fin.elim0

private def role4 (coordinate : Fin 4) : TerminalProfileRole :=
  match coordinate.val with
  | 0 => .carrier
  | 1 => .obligation
  | 2 => .obligation
  | _ => .direction

private def closedSystem : TerminalProfileSystem 1 1 4 where
  role := role4
  observe := fun implementation coordinate =>
    match coordinate.val with
    | 0 => implementation.candidate.semantics (fun _ => false) 0
    | 3 => true
    | _ => false

private def openSystem : TerminalProfileSystem 1 1 4 where
  role := role4
  observe := fun implementation coordinate =>
    if coordinate.val = 2 then true else closedSystem.observe implementation coordinate

private def mismatchSystem : TerminalProfileSystem 1 1 4 where
  role := role4
  observe := fun implementation coordinate =>
    if coordinate.val = 0 then decide (implementation.gateCount = 2)
    else closedSystem.observe implementation coordinate

private def hidingProjection : TerminalProfileProjection 4 where
  keep := fun coordinate => decide (coordinate.val ≠ 0)

/- Guarded executable fixtures are bounded test evidence, not proof authority.
The classifier does not enumerate semantic reference minima or candidate sets. -/
#eval (show IO Unit from do
  let replacement := deadSupportReplacementImplementation current
  if (classifyDeadSupportFullMode closedSystem current).tag != .accepted then
    throw (IO.userError "complete matching closed profile was not accepted")
  if (firstTerminalOpenObligation closedSystem replacement).isSome then
    throw (IO.userError "true non-obligation coordinates were treated as open obligations")
  match classifyDeadSupportFullMode closedSystem current with
  | .accepted gain =>
      if gain.fullRealization.realization.implementation.gateCount != 1 ||
          !equivalentBool gain.fullRealization.realization.implementation.candidate
            current.candidate then
        throw (IO.userError "accepted full-carrier result is not the computed replacement")
  | _ => throw (IO.userError "accepted outcome lost its proof-bearing record")
  if (firstTerminalGainProfileMismatch openSystem current replacement).isSome then
    throw (IO.userError "open-obligation fixture unexpectedly changes profile")
  match classifyDeadSupportFullMode openSystem current with
  | .openObligation _ _ _ coordinate _ =>
      if coordinate.val != 2 || openSystem.role coordinate != .obligation ||
          !openSystem.observe replacement coordinate then
        throw (IO.userError "first open obligation or its actual role/value changed")
  | _ => throw (IO.userError "matching profile with open obligation was not rejected")
  let projectedMatch := (allFin 4).all fun coordinate =>
    !hidingProjection.keep coordinate ||
      boolEqual (mismatchSystem.observe replacement coordinate)
        (mismatchSystem.observe current coordinate)
  if !projectedMatch then
    throw (IO.userError "projection fixture did not hide exactly the full-profile mismatch")
  match classifyDeadSupportFullMode mismatchSystem current with
  | .profileMismatch _ _ coordinate _ =>
      if coordinate.val != 0 then throw (IO.userError "first profile mismatch changed")
  | _ => throw (IO.userError "projection-hidden mismatch was accepted as full equality")
  if (classifyDeadSupportFullMode zeroProfile current).tag != .accepted then
    throw (IO.userError "zero-width profile rejected a genuine proper physical gain")
  if (classifyDeadSupportFullMode closedSystem noDead).tag != .noProperSupport ||
      (classifyDeadSupportFullMode zeroProfile allDead).tag != .noProperSupport ||
      (classifyDeadSupportFullMode zeroProfile empty).tag != .noProperSupport then
    throw (IO.userError "no-dead, all-dead or empty case gained false proper support")
  IO.println "computed-dead-support-full-mode-fixtures: passed"
)
