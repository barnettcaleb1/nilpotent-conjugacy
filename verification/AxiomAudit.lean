import NilpotentConjugacy
import Lean.Util.CollectAxioms

/-! Audit every declaration in the package namespace, including generated
declarations. Fail if any transitive axiom is outside Lean's standard
propositional extensionality, choice, and quotient axioms.
This audit does not check correspondence with the manuscript.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc name _ =>
    if (`NilpotentConjugacy).isPrefixOf name ||
        name.toString.startsWith "_private.NilpotentConjugacy." then acc.push name else acc
  if names.isEmpty then
    throwError "No NilpotentConjugacy declarations found"
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in names.qsort Name.lt do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"{name}: {axioms.qsort Name.lt}"
  logInfo m!"Axiom audit passed for {names.size} declarations."
