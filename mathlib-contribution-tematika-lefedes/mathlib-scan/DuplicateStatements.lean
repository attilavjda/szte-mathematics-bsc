import Mathlib
open Lean

run_cmd do
  let env ← Lean.getEnv
  let mut m : Std.HashMap Expr (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    match ci with
    | .thmInfo ti =>
      let some mod := env.getModuleFor? n | continue
      let ms := mod.toString
      unless ms.startsWith "Mathlib." do continue
      if (env.find? n).isNone then continue
      m := m.insert ti.type ((m.getD ti.type #[]).push n)
    | _ => continue
  let mut out : Array String := #[]
  for (ty, ns) in m.toList do
    if ns.size ≥ 2 then
      let mods := ns.map (fun n => (env.getModuleFor? n).getD `unknown)
      if mods.any (fun mo => let s := mo.toString
          s.startsWith "Mathlib.LinearAlgebra." || s.startsWith "Mathlib.Analysis.Calculus."
          || s.startsWith "Mathlib.Analysis.SpecialFunctions." || s.startsWith "Mathlib.Analysis.Complex."
          || s.startsWith "Mathlib.Analysis.Normed.Order" || s.startsWith "Mathlib.Order.Filter.") then
        out := out.push s!"{ns} in {mods}"
  logInfo (s!"count={out.size}\n" ++ String.intercalate "\n" out.toList)
