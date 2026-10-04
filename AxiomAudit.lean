import SerreMarkov
import Lean.Util.CollectAxioms

open Lean Elab Command

/- The audit traverses actual compiled declarations and their transitive proof
dependencies. It fails if any project theorem uses an axiom outside Lean's
three standard logical axioms. In particular it rejects `sorryAx` and compiler
trust axioms used by external native evaluation. -/
run_cmd do
  let (names, definitions) ← (← getEnv).constants.foldM
      (init := ((#[] : Array Name), (#[] : Array Name))) fun (names, definitions) n c => do
    if !n.toString.startsWith "SerreMarkov." then return (names, definitions)
    match c with
    | .thmInfo _ =>
        return (names.push n, definitions)
    | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ =>
        return (names, definitions.push n)
    | _ => return (names, definitions)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  -- Share the visited set: finite certificates have large common dependencies.
  -- This traverses their union once, retaining the same transitive check.
  let action : CollectAxioms.M Unit := do
    for n in names do
      CollectAxioms.collect n
    for n in definitions do
      CollectAxioms.collect n
  let (_, state) := (action.run (← getEnv)).run {}
  for a in state.axioms do
    unless allowed.contains a do
      throwError "Disallowed axiom {a} in project proof dependencies"
  for n in names do
    logInfo m!"VERIFIED: {n}"
  logInfo m!"ALLOWED_AXIOMS_USED: {state.axioms}"
  logInfo m!"AUDITED_DEFINITIONS: {definitions.size} compiled definition/opaque/axiom declarations"
  logInfo m!"AUDIT_PASSED: {names.size} compiled theorem declarations"
