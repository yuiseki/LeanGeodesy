import LeanAtlas
import LeanAtlas.GraphData.Core
import LeanAtlas.GraphData.Json

/-!
Writes the lean-atlas graph of LeanGeodesy, with the main theorems marked in
`LeanGeodesyAtlas.MainTheorems`. `lake exe atlas graph-data` imports only the
library's root module, so it would not see those marks.
-/

open Lean

-- The lean-atlas linters ask project declarations for metadata; this is tooling.
set_option linter.confidenceCheck false
set_option linter.defProgressCheck false

unsafe def main (args : List String) : IO UInt32 := do
  let out := args.headD "graph.json"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `LeanGeodesy }, { module := `LeanGeodesyAtlas.MainTheorems }]
    {} (trustLevel := 1024) (loadExts := true)
  let scope : LeanAtlas.Config.ProjectScope := { projectNamespace := `LeanGeodesy }
  let now ← IO.monoNanosNow
  let graph ← LeanAtlas.GraphData.Core.buildGraphDataIO scope env "LeanGeodesy" s!"{now / 1000000000}"
  IO.FS.writeFile out (LeanAtlas.GraphData.Json.toJsonString graph)
  IO.println s!"{graph.statistics.totalNodes} nodes, {graph.statistics.totalEdges} edges → {out}"
  return 0
