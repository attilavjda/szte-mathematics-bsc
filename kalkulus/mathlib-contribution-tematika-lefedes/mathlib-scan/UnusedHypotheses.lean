import Mathlib
open Lean

run_cmd do
  let env ← Lean.getEnv
  let prefixes := ["Mathlib.LinearAlgebra.", "Mathlib.Analysis.Calculus.",
    "Mathlib.Analysis.SpecialFunctions.", "Mathlib.Analysis.Complex."]
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    match ci with
    | .thmInfo ti =>
      let some mod := env.getModuleFor? n | continue
      let ms := mod.toString
      unless prefixes.any (fun p => ms.startsWith p) do continue
      let mut t := ti.type
      let mut v := ti.value
      let mut unused : Array Name := #[]
      repeat
        match t, v with
        | .forallE nm _ body bi, .lam _ _ vbody _ =>
            if bi.isExplicit && !body.hasLooseBVar 0 && !vbody.hasLooseBVar 0 then
              unused := unused.push nm
            t := body; v := vbody
        | _, _ => break
      if !unused.isEmpty then
        out := out.push s!"{ms} | {n} | {unused}"
    | _ => continue
  logInfo (String.intercalate "\n" out.toList)
