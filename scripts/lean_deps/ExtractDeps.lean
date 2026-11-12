/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization

/-!
# Lean-extracted dependencies between statement entries

For every statement entry `E` with a proof wrapper `E_holds` (in `Formalization.Statements.*Proofs`),
the *roots* of `E` are the project declarations that `E_holds` refers to directly (excluding the
statement definitions themselves). The *closure* of `E` is every project declaration reachable from
those roots through types and proof terms (Mathlib and core are not traversed).

Entry `A` is reported as used by entry `B` when some root of `A` lies in the closure of `B`, together
with the shared declarations. This is a mechanical relation between proofs; it is not a curated
mathematical dependency (a shared helper lemma can create an edge, and a dependency proved twice
does not).

Run from the repository root:  `lake env lean scripts/lean_deps/ExtractDeps.lean > docs/graph/lean-deps.json`
-/

open Lean Elab Command

private def isProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    (`Formalization).isPrefixOf m
  | none => false

private def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => .anonymous

private def isStatementModule (m : Name) : Bool :=
  (`Formalization.Statements).isPrefixOf m

private def usedConsts (ci : ConstantInfo) : Array Name :=
  let a := ci.type.getUsedConstants
  match ci.value? (allowOpaque := true) with
  | some v => a ++ v.getUsedConstants
  | none => a

private def jsonStr (s : String) : String := (Json.str s).compress

run_cmd do
  let env ← getEnv
  -- statement entries with wrappers
  let mut entries : Array (Name × Name) := #[]
  for (n, _) in env.constants.toList do
    if isProject env n && isStatementModule (moduleOf env n) then
      match n with
      | .str p s =>
        if s.endsWith "_holds" then
          let e := Name.str p (String.ofList (s.toList.take (s.length - 6)))
          if env.contains e then entries := entries.push (e, n)
      | _ => pure ()
  let statementDefs : Std.HashSet Name := entries.foldl (fun s (e, _) => s.insert e) {}
  -- roots of each entry
  let mut roots : Std.HashMap Name (Array Name) := {}
  for (e, h) in entries do
    let some ci := env.find? h | continue
    -- roots are theorems only: a shared definition (`IsSizeBias`) is vocabulary, not a proof dependency
    let rs := (usedConsts ci).filter fun c =>
      isProject env c && !statementDefs.contains c && c != h && !isStatementModule (moduleOf env c) &&
        (match env.find? c with | some (.thmInfo _) => true | _ => false)
    roots := roots.insert e (rs.toList.eraseDups.toArray)
  -- closure of each entry through project declarations (memoized per declaration's direct uses)
  let mut direct : Std.HashMap Name (Array Name) := {}
  let mut out : Array String := #[]
  let rootOwners : Std.HashMap Name (Array Name) := roots.fold (init := {}) fun m e rs =>
    rs.foldl (fun m r => m.insert r ((m.getD r #[]).push e)) m
  for (e, _) in entries do
    let mut seen : Std.HashSet Name := {}
    let mut stack : Array Name := roots.getD e #[]
    while !stack.isEmpty do
      let x := stack.back!
      stack := stack.pop
      if seen.contains x then continue
      seen := seen.insert x
      let ds ← match direct.get? x with
        | some ds => pure ds
        | none =>
          let ds := match env.find? x with
            | some ci => (usedConsts ci).filter (isProject env)
            | none => #[]
          direct := direct.insert x ds
          pure ds
      for d in ds do
        unless seen.contains d do stack := stack.push d
    -- which other entries' roots are reached
    let mut uses : Std.HashMap Name (Array Name) := {}
    for x in seen.toList do
      for a in rootOwners.getD x #[] do
        if a != e then uses := uses.insert a ((uses.getD a #[]).push x)
    let usesJson := uses.toList.map fun (a, via) =>
      "{\"entry\":" ++ jsonStr a.toString ++ ",\"via\":[" ++
        ",".intercalate ((via.toList.take 20).map (jsonStr ·.toString)) ++ "]}"
    let rootsJson := (roots.getD e #[]).toList.map (jsonStr ·.toString)
    out := out.push ("{\"entry\":" ++ jsonStr e.toString ++ ",\"roots\":[" ++ ",".intercalate rootsJson ++
      "],\"closure_size\":" ++ toString seen.size ++ ",\"uses\":[" ++ ",".intercalate usesJson ++ "]}")
  IO.println ("{\"entries\":[\n" ++ ",\n".intercalate out.toList ++ "\n]}")
