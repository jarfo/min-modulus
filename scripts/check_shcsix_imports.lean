/-
Check the generated certificate dependency graph using Lean's header parser.
Run with `lake env lean --run scripts/check_shcsix_imports.lean`.
This checks headers only; `lake build` checks every proof.
-/
import Lean

open Lean

private def twoDigits (n : Nat) : String :=
  if n < 10 then s!"0{n}" else toString n

private def checkImports (name : String) (expected : Array String) : IO Unit := do
  let path := System.FilePath.mk (name.replace "." "/" ++ ".lean")
  let ctx := Parser.mkInputContext (← IO.FS.readFile path) path.toString
  let (header, _, messages) ← Parser.parseHeader ctx
  if messages.hasErrors then
    for msg in messages.toList do IO.eprintln (← msg.toString)
    throw <| IO.userError s!"Invalid header: {path}"
  let mut actual := #[]
  if let `(Parser.Module.header| $[module]? $[prelude]? $imports*) := header then
    for i in imports do
      if let `(Parser.Module.import| $[public]? $[meta]? import $[all]? $mod) := i then
        actual := actual.push mod.getId.toString
  unless actual == expected do
    throw <| IO.userError s!"{path}: expected {expected}, got {actual}"

def main : IO Unit := do
  let mut blocks := 0
  let mut rows := 0
  for (stem, firstCount, dataModule) in #[
      ("SHCSixNormalizedN67", 61, "SHCSixCertificateData"),
      ("SHCSixNormalizedN69", 63, "SHCSixCertificateData"),
      ("SHCSixN105", 51, "SHCSixExceptionalCertificateData")] do
    let modulePrefix := "MinModulus.Generated." ++ stem
    let mut rowImports := #[]
    for a in [:firstCount] do
      let row := modulePrefix ++ "A" ++ twoDigits a
      rowImports := rowImports.push row
      let mut blockImports := #[]
      for b in [:firstCount - a] do
        let block := row ++ "B" ++ twoDigits b
        blockImports := blockImports.push block
        checkImports block #["MinModulus." ++ dataModule]
        blocks := blocks + 1
      checkImports row blockImports
      rows := rows + 1
    checkImports modulePrefix rowImports
  IO.println s!"Verified {blocks} independent blocks, {rows} row assemblers and 3 certificates."
  IO.println "Each certificate has three import edges to its data module; no predecessor imports."
