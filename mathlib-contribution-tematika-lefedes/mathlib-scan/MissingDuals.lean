import Mathlib
open Lean

def dualize (s : String) : String :=
  ((((s.replace "sSup" "@@").replace "sInf" "sSup").replace "@@" "sInf"
      |>.replace "iSup" "%%" |>.replace "iInf" "iSup" |>.replace "%%" "iInf")
      |>.replace "ciSup" "ciSup")

run_cmd do
  let env ← Lean.getEnv
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    match ci with
    | .thmInfo _ =>
      let some mod := env.getModuleFor? n | continue
      let ms := mod.toString
      unless ms.startsWith "Mathlib.Order.CompleteLattice" || ms.startsWith "Mathlib.Order.ConditionallyCompleteLattice"
        || ms.startsWith "Mathlib.Topology.Order" || ms.startsWith "Mathlib.Analysis" do continue
      let s := n.toString
      unless (s.splitOn "sSup").length > 1 do continue
      let d := dualize s
      if d != s && (env.find? d.toName).isNone then
        out := out.push s!"{ms} | {s}  -->  missing {d}"
    | _ => continue
  logInfo (s!"count={out.size}\n" ++ String.intercalate "\n" out.toList)
