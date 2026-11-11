/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization
import Lean.Util.CollectAxioms

/-!
# Module-Based Kernel Axiom and Opacity Audit (`Audit`)

Verifies that:
1. Every `Formalization/**/*.lean` file on disk is imported into `Formalization`.
2. Every constant whose defining module is `Formalization` or under `Formalization.*`
   (including `_private` helpers and declarations outside `namespace SteinMethod`)
   is non-`opaque` and has transitive axiom closure inside
   `{propext, Classical.choice, Quot.sound}`.
3. At least one project declaration was audited.
-/

private def filePathToModuleName (p : System.FilePath) : Lean.Name :=
  let noExt := p.withExtension ""
  let comps := noExt.components.filter (fun c => c != "." && c != "")
  comps.foldl Lean.Name.mkStr Lean.Name.anonymous

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let importedMods : Std.HashSet Name :=
    env.header.moduleNames.foldl (fun s m => s.insert m) {}
  unless importedMods.contains `Formalization do
    throwError "Root module `Formalization` is missing from imported environment"
  let formDir : System.FilePath := System.FilePath.mk "Formalization"
  unless ← formDir.pathExists do
    throwError "Expected directory `Formalization/` is missing relative to the working directory"
  let gitOut ← IO.Process.output
    { cmd := "git", args := #["ls-files", "--cached", "Formalization"] }
  let files : Array System.FilePath ←
    if gitOut.exitCode == 0 then
      pure <| (gitOut.stdout.splitOn "\n").foldl (init := #[]) fun acc line =>
        let s := line.trimAscii.toString
        if s.isEmpty then acc else acc.push (System.FilePath.mk s)
    else
      formDir.walkDir
  for f in files do
    if !(← f.isDir) && f.extension == some "lean" then
      let modName := filePathToModuleName f
      unless importedMods.contains modName do
        throwError "Unimported project module on disk: {f} ({modName})"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, cinfo) in env.constants.toList do
    if let some modIdx := env.getModuleIdxFor? name then
      if h : modIdx.toNat < env.header.moduleNames.size then
        let modName := env.header.moduleNames[modIdx.toNat]
        if (`Formalization).isPrefixOf modName then
          if cinfo matches .opaqueInfo _ then
            throwError "Opaque stand-in {name} (in {modName}) is not permitted"
          let axioms ← liftCoreM <| Lean.collectAxioms name
          for ax in axioms do
            unless allowed.contains ax do
              throwError "Unapproved axiom {ax} in dependency closure of {name} ({modName})"
          checked := checked + 1
  if checked == 0 then
    throwError "The axiom audit found no project declarations"
  logInfo m!"Axiom audit passed for {checked} project declarations."
