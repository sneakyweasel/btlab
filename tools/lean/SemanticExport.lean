import Lean

/-! Compiler-derived declarations for Formalpedia. This executable inspects compiled
environments; it does not add declarations or change their evidence labels. -/

open Lean Meta

namespace Formalpedia

private def arr (xs : List Json) : Json := toJson xs

private def binderKind : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "instance"

private partial def levelJson (params : List Name) : Level → Json
  | .zero => arr [toJson "zero"]
  | .succ u => arr [toJson "succ", levelJson params u]
  | .max u v => arr [toJson "max", levelJson params u, levelJson params v]
  | .imax u v => arr [toJson "imax", levelJson params u, levelJson params v]
  | .param n => arr [toJson "param", toJson (params.idxOf n)]
  | .mvar _ => arr [toJson "unresolved_universe"]

/-- Alpha-normalized expression syntax: binder names and metadata are omitted. -/
private partial def exprJson (params : List Name) : Expr → Json
  | .bvar n => arr [toJson "bvar", toJson n]
  | .sort u => arr [toJson "sort", levelJson params u]
  | .const n us => arr [toJson "const", toJson n.toString, toJson (us.map (levelJson params))]
  | .app f x => arr [toJson "app", exprJson params f, exprJson params x]
  | .lam _ t b bi => arr [toJson "lam", toJson (binderKind bi), exprJson params t, exprJson params b]
  | .forallE _ t b bi => arr [toJson "forall", toJson (binderKind bi), exprJson params t, exprJson params b]
  | .letE _ t v b _ => arr [toJson "let", exprJson params t, exprJson params v, exprJson params b]
  | .lit (.natVal n) => arr [toJson "nat", toJson (toString n)]
  | .lit (.strVal s) => arr [toJson "string", toJson s]
  | .mdata _ b => exprJson params b
  | .proj n i b => arr [toJson "proj", toJson n.toString, toJson i, exprJson params b]
  | .fvar _ => arr [toJson "unexpected_free_variable"]
  | .mvar _ => arr [toJson "unresolved_metavariable"]

private def kind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

private def namesJson (names : Array Name) : Json :=
  toJson ((names.qsort Name.lt).map Name.toString)

private def describe (ci : ConstantInfo) (mod : Name) : MetaM Json := do
  let type ← ppExpr ci.type
  let binders ← forallTelescope ci.type fun xs conclusion => do
    let bs ← xs.mapM fun x => do
      let d ← x.fvarId!.getDecl
      return Json.mkObj [
        ("name", toJson d.userName.toString), ("kind", toJson (binderKind d.binderInfo)),
        ("type", toJson (← ppExpr d.type).pretty), ("is_proposition", toJson (← isProp d.type))]
    return (bs, (← ppExpr conclusion).pretty)
  let value := ci.value? true
  let axioms ← collectAxioms ci.name
  return Json.mkObj [
    ("name", toJson ci.name.toString), ("module", toJson mod.toString),
    ("kind", toJson (kind ci)), ("type", toJson type.pretty),
    ("type_ast", exprJson ci.levelParams ci.type),
    ("universe_parameters", toJson (ci.levelParams.map Name.toString)),
    ("binders", toJson binders.1), ("conclusion", toJson binders.2),
    ("type_dependencies", namesJson ci.type.getUsedConstants),
    ("value_dependencies", namesJson (value.map Expr.getUsedConstants |>.getD #[])),
    ("value_available", toJson value.isSome),
    ("value_hash64", toJson (value.map (fun e => toString e.hash))),
    ("axioms", namesJson axioms)]

end Formalpedia

/-- Read a module-list JSON request and emit one compiler-derived record per line. -/
unsafe def main (args : List String) : IO UInt32 := do
  let [requestPath, outputPath] := args | throw (IO.userError "expected request.json output.jsonl")
  let request ← IO.ofExcept <| Json.parse (← IO.FS.readFile requestPath)
  let modules ← IO.ofExcept <| (request.getObjValAs? (Array String) "modules")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let requested := modules.map String.toName
  let opts := ({} : Options).setBool `pp.universes true |>.setBool `pp.explicit true
    |>.setBool `pp.fullNames true |>.set `maxRecDepth (10000 : Nat)
    |>.set `maxHeartbeats (2000000 : Nat)
  let env ← importModules (requested.map fun m => { module := m }) opts (loadExts := true)
  let stream ← IO.FS.Handle.mk outputPath .write
  let objects ← env.header.moduleNames.mapM fun mod => do
    return Json.mkObj [("module", toJson mod.toString),
      ("path", toJson (← findOLean mod).toString)]
  stream.putStrLn (Json.mkObj [("record", toJson "environment"),
    ("objects", toJson objects)]).compress
  let constants := env.constants.toList.toArray.qsort (fun a b => Name.lt a.1 b.1)
  for (name, ci) in constants do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      if requested.contains mod then
        let row ← (Formalpedia.describe ci mod).run' |>.toIO
          { fileName := "<formalpedia>", fileMap := default, options := opts } { env := env }
        stream.putStrLn row.1.compress
  return 0
