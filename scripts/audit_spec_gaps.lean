import Lean
import FracLap

/-!
# Specification & Gap Audit Script

Inspects the compiled `FracLap` environment for structural indicators of
remaining formalization gaps:
1. **Structure Inhabitation Audit**: checks every `structure` in `FracLap.*`
   to see whether it has concrete non-wrapper inhabitants (`[OK]`), only
   specialized value instantiations (`[PARTIAL]`), only combinators taking
   other `FracLap.*` structures (`[GAP - combinators only]`), or no
   inhabitants at all (`[GAP - uninhabited]`).
2. **Direct-Projection / Tautology Audit**: flags theorems in `FracLap.*`
   whose entire proof term is just applying a bound hypothesis (`fun ... => h ...`).
3. **Non-Vacuity Witness Audit**: every concrete structure instance registered in `witnesses`
   must come with an existing witness theorem (`∃ u ≠ 0, ...`-style statement) showing that the
   underlying space/form is not trivial. A missing witness counts as a gap, because an instance
   over a trivial space would satisfy every structure field vacuously.
4. **Conditional Domain-Theorem Audit**: lists theorems in `FracLap.WholeLine.*`
   and `FracLap.HalfLine.*` whose hypotheses still assume non-fully-inhabited
   `FracLap.*` structures.

Run via `just audit-gaps` (or `just audit-gaps --strict` to fail with exit code 1).
-/

open Lean

private def stripForall : Expr → Array Expr × Expr
  | .forallE _ d b _ =>
    let (ds, ret) := stripForall b
    (#[d] ++ ds, ret)
  | e => (#[], e)

private def stripLam : Expr → Expr
  | .lam _ _ b _ => stripLam b
  | e => e

private def isBVarApp : Expr → Bool
  | e =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    fn.isBVar && args.all Expr.isBVar

private def collectConsts (e : Expr) (targets : NameSet) (acc : NameSet := {}) : NameSet :=
  match e with
  | .const c _ => if targets.contains c then acc.insert c else acc
  | .app f a => collectConsts a targets (collectConsts f targets acc)
  | .lam _ d b _ => collectConsts b targets (collectConsts d targets acc)
  | .forallE _ d b _ => collectConsts b targets (collectConsts d targets acc)
  | .letE _ t v b _ => collectConsts b targets (collectConsts v targets (collectConsts t targets acc))
  | .mdata _ e' => collectConsts e' targets acc
  | .proj _ _ e' => collectConsts e' targets acc
  | _ => acc

private def hasFracStruct (e : Expr) (targets : NameSet) : Bool :=
  !(collectConsts e targets).isEmpty

private def isDomainModule (modName : Name) : Bool :=
  let comps := modName.components
  comps.take 2 == [`FracLap, `WholeLine] || comps.take 2 == [`FracLap, `HalfLine]

private def hasValueParam (env : Environment) (sName : Name) : Bool :=
  let rec go : Expr → Bool
    | .forallE _ d b bi => (bi == .default && !d.isSort) || go b
    | _ => false
  match env.find? sName with
  | some cinfo => go cinfo.type
  | none => false

/-- Structures whose explicit value parameters (e.g. the norms of `OddSubspaceConjugation`) are
data of one concrete pairing, not a family to be instantiated in general. Having a concrete
inhabitant is exactly the intended content, so they are not reported as `PARTIAL`. -/
private def valueParamsAllowlisted : List Name :=
  [``FracLap.OddSubspaceConjugation]

/-- Registered non-vacuity witnesses: `(concrete instance, witness theorem)`. The witness must
exist in the environment (and is covered by the axiom audit for `sorryAx`). -/
private def witnesses : List (Name × Name) :=
  [ (``FracLap.gagliardoForm_isMarkovDirichletForm, ``FracLap.exists_restrictedGagliardoForm_pos)
  , (``FracLap.restrictedGagliardoForm_isMarkovDirichletForm,
      ``FracLap.exists_restrictedGagliardoForm_pos)
  , (``FracLap.stableHeatKernel, ``FracLap.fourier_stableKernel_eq) ]

private def auditEnvironment (strict : Bool) : CoreM UInt32 := do
  let env ← getEnv
  let allDecls := env.constants.toList

  -- 1. Collect all non-internal structures in `FracLap.*`
  let mut structNames : Array Name := #[]
  let mut structSet : NameSet := {}
  for (name, _) in allDecls do
    if name.getRoot == `FracLap && !name.isInternal && isStructure env name then
      structNames := structNames.push name
      structSet := structSet.insert name
  let sortedStructs := structNames.qsort Name.lt

  -- Maps structure -> (concrete names, hasGeneralConcrete, combinator names)
  let mut concreteMap : Std.HashMap Name (Array Name) := {}
  let mut generalConcreteMap : Std.HashMap Name Bool := {}
  let mut combMap : Std.HashMap Name (Array Name) := {}
  for s in sortedStructs do
    concreteMap := concreteMap.insert s #[]
    generalConcreteMap := generalConcreteMap.insert s false
    combMap := combMap.insert s #[]

  -- 2. Classify defs and theorems returning a `FracLap.*` structure
  let mut tautologies : Array Name := #[]
  for (name, cinfo) in allDecls do
    if name.getRoot == `FracLap && !name.isInternal then
      -- Check direct-projection tautologies on theorems
      if let .thmInfo tval := cinfo then
        let sName := name.toString
        if !sName.endsWith ".injEq" && !sName.endsWith ".ext" && !sName.endsWith ".ext_iff" then
          let body := stripLam tval.value
          if isBVarApp body then
            tautologies := tautologies.push name
      -- Check structure inhabitation via defs and Prop-structure theorems
      let isCandidate :=
        match cinfo with
        | .defnInfo _ => true
        | .thmInfo _ => true
        | _ => false
      if isCandidate then
        let (binders, ret) := stripForall cinfo.type
        if let some s := ret.getAppFn.constName? then
          if structSet.contains s && !s.isPrefixOf name then
            let usesWrapper := binders.any fun b => hasFracStruct b structSet
            if usesWrapper then
              let cur := combMap.getD s #[]
              combMap := combMap.insert s (cur.push name)
            else
              let cur := concreteMap.getD s #[]
              concreteMap := concreteMap.insert s (cur.push name)
              let hasLoose := ret.getAppArgs.any Expr.hasLooseBVars
              if hasLoose then
                generalConcreteMap := generalConcreteMap.insert s true

  -- 3. Report structure inhabitation status
  IO.println "=== 1. Structure Inhabitation Audit ==="
  let mut gapStructs : NameSet := {}
  let mut gapCount := 0
  for s in sortedStructs do
    let conc := concreteMap.getD s #[]
    let comb := combMap.getD s #[]
    let genConc := generalConcreteMap.getD s false
    let needsValueGen := hasValueParam env s && !genConc
    if conc.isEmpty && comb.isEmpty then
      IO.println s!"  [GAP - uninhabited] {s} (0 concrete, 0 combinators)"
      gapStructs := gapStructs.insert s
      gapCount := gapCount + 1
    else if conc.isEmpty then
      let combStr := ", ".intercalate (comb.toList.map toString)
      IO.println s!"  [GAP - combinators only] {s} (0 concrete; combinators: {combStr})"
      gapStructs := gapStructs.insert s
      gapCount := gapCount + 1
    else if needsValueGen && !valueParamsAllowlisted.contains s then
      let concStr := ", ".intercalate (conc.toList.map toString)
      IO.println s!"  [PARTIAL - specialized values only] {s} (concrete: {concStr})"
      gapStructs := gapStructs.insert s
      gapCount := gapCount + 1
    else if needsValueGen then
      IO.println s!"  [OK - concrete, value params allowlisted] {s} ({conc.size} concrete)"
    else
      IO.println s!"  [OK - concrete] {s} ({conc.size} concrete, {comb.size} combinators)"

  -- 4. Report tautology / direct-projection theorems
  IO.println "\n=== 2. Direct-Projection / Tautology Theorem Audit ==="
  let sortedTaut := tautologies.qsort Name.lt
  if sortedTaut.isEmpty then
    IO.println "  None detected."
  else
    for t in sortedTaut do
      IO.println s!"  [TAUTOLOGY] {t}"
    gapCount := gapCount + sortedTaut.size

  -- 4b. Non-vacuity witnesses
  IO.println "\n=== 3. Non-Vacuity Witness Audit ==="
  let mut missingWitnesses := 0
  for (inst, wit) in witnesses do
    if !env.contains inst then
      IO.println s!"  [STALE] registry entry {inst} no longer exists"
      missingWitnesses := missingWitnesses + 1
    else if env.contains wit then
      IO.println s!"  [OK] {inst} has non-vacuity witness {wit}"
    else
      IO.println s!"  [MISSING WITNESS] {inst} requires {wit}"
      missingWitnesses := missingWitnesses + 1
  gapCount := gapCount + missingWitnesses

  -- Collect auto-generated field names (`Struct.field`) and `.mk.inj`
  let mut fieldAccessors : NameSet := {}
  for s in sortedStructs do
    fieldAccessors := fieldAccessors.insert (s ++ `mk.inj)
    if let some sinfo := getStructureInfo? env s then
      for fname in sinfo.fieldNames do
        fieldAccessors := fieldAccessors.insert (s ++ fname)

  -- 5. Report WholeLine / HalfLine theorems conditional on gap/partial structures
  IO.println "\n=== 4. Conditional Domain Theorems (WholeLine / HalfLine) ==="
  let mut condList : Array (Name × List Name) := #[]
  for (name, cinfo) in allDecls do
    if name.getRoot == `FracLap && !name.isInternal && !fieldAccessors.contains name then
      if let .thmInfo _ := cinfo then
        if let some modIdx := env.getModuleIdxFor? name then
          let modName := env.header.moduleNames[modIdx]!
          if isDomainModule modName then
            let (binders, _) := stripForall cinfo.type
            let mut deps : NameSet := {}
            for b in binders do
              deps := collectConsts b gapStructs deps
            if !deps.isEmpty then
              condList := condList.push (name, deps.toList)
  let sortedCond := condList.qsort (fun a b => Name.lt a.1 b.1)
  if sortedCond.isEmpty then
    IO.println "  None detected."
  else
    for (tname, deps) in sortedCond do
      let depStr := ", ".intercalate (deps.map toString)
      IO.println s!"  [CONDITIONAL] {tname}  (depends on: {depStr})"

  -- 6. Soundness & Transparency Audit (Xena / SafeVerify checks)
  IO.println "\n=== 5. Soundness & Transparency Audit (Xena / SafeVerify) ==="
  let mut soundnessIssues : Array (String × Name) := #[]
  for (name, cinfo) in allDecls do
    if name.getRoot == `FracLap && !name.isInternal then
      match cinfo with
      | .axiomInfo _ =>
        soundnessIssues := soundnessIssues.push ("AXIOM", name)
      | .opaqueInfo _ =>
        soundnessIssues := soundnessIssues.push ("OPAQUE", name)
      | .defnInfo dval =>
        if dval.safety != .safe then
          soundnessIssues := soundnessIssues.push ("UNSAFE/PARTIAL", name)
      | _ => pure ()
      if (Compiler.getImplementedBy? env name).isSome || isExtern env name then
        soundnessIssues := soundnessIssues.push ("COMPILER-OVERRIDE", name)
  let sortedSoundness := soundnessIssues.qsort (fun a b => Name.lt a.2 b.2)
  if sortedSoundness.isEmpty then
    IO.println "  None detected."
  else
    for (tag, name) in sortedSoundness do
      IO.println s!"  [{tag}] {name}"
    gapCount := gapCount + sortedSoundness.size

  IO.println s!"\nSummary: {sortedStructs.size} structures, {gapStructs.size} non-fully-concrete structures, {sortedTaut.size} tautologies, {missingWitnesses} missing witnesses, {sortedCond.size} conditional domain theorems, {sortedSoundness.size} soundness/transparency issues."
  if strict && gapCount > 0 then
    return 1
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  let strict := args.contains "--strict"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `FracLap }] {}
  let ctx : Core.Context := { fileName := "<audit_spec_gaps>", fileMap := default }
  let state : Core.State := { env := env }
  (auditEnvironment strict).toIO' ctx state
