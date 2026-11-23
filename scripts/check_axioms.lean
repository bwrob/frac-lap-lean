import Lean
import FracLap

/-!
# Axiom Audit Script

Verifies that every non-internal declaration in `FracLap.*` depends only on
Lean's standard classical axioms (`propext`, `Classical.choice`, `Quot.sound`),
failing with exit code 1 if `sorryAx` or any unexpected axiom is present.
-/

open Lean

private def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Audit a chunk of declarations; returns `(name, disallowed axioms)` for offending ones. -/
private def auditChunk (ctx : Core.Context) (st : Core.State) (names : Array Name) :
    IO (Array (Name × List Name)) := do
  let mut bad : Array (Name × List Name) := #[]
  for name in names do
    let (axs, _) ← (Lean.collectAxioms name : CoreM (Array Name)).toIO ctx st
    let b := axs.toList.filter fun ax => !allowedAxioms.contains ax
    if !b.isEmpty then
      bad := bad.push (name, b)
  return bad

/-- Number of chunks (tasks) the audit is split into; the runtime schedules them on its thread pool. -/
private def numWorkers : Nat := 64

/-- Audit every non-internal `FracLap.*` declaration. Each declaration is independent, so the
declarations are split into chunks audited in parallel by separate tasks. -/
private def checkAllAxioms : CoreM UInt32 := do
  let env ← getEnv
  let ctx ← read
  let st ← get
  let names := env.constants.toList.filterMap fun (name, _) =>
    if name.getRoot == `FracLap && !name.isInternal then some name else none
  let arr := names.toArray
  let chunkSize := (arr.size + numWorkers - 1) / numWorkers
  let mut tasks : Array (Task (Except IO.Error (Array (Name × List Name)))) := #[]
  for i in [0:numWorkers] do
    let chunk := arr.extract (i * chunkSize) ((i + 1) * chunkSize)
    tasks := tasks.push (← IO.asTask (auditChunk ctx st chunk))
  let mut failed := false
  for t in tasks do
    match ← IO.wait t with
    | .ok bad =>
      for (name, b) in bad do
        IO.eprintln s!"ERROR: {name} uses disallowed axioms: {b}"
        failed := true
    | .error e =>
      IO.eprintln s!"ERROR: axiom audit worker failed: {e}"
      failed := true
  if failed then
    return 1
  IO.println s!"Axiom check passed ({arr.size} declarations in FracLap.*)."
  return 0

unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `FracLap }] {}
  let ctx : Core.Context := { fileName := "<check_axioms>", fileMap := default }
  let state : Core.State := { env := env }
  checkAllAxioms.toIO' ctx state
