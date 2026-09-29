import Lake
open Lake DSL

-- The shared package directory holds Mathlib's build and the Verso books'
-- build, so dependencies that VersoBlueprint shares with them are pinned here
-- to their revisions; otherwise VersoBlueprint's shallower requirements win
-- and Mathlib or the books rebuild against other versions:
-- ProofWidgets and Plausible as Mathlib has them, and Verso, SubVerso,
-- verso-slides and illuminate at Verso v4.34.0, as the books in manual/ use it.
require «lean-geodesy» from ".."
require proofwidgets from git
  "https://github.com/leanprover-community/ProofWidgets4"@"106ff4fafc74ef4ac99d81dbf3ab399118f497a5"
require verso from git "https://github.com/leanprover/verso"@"v4.34.0"
require subverso from git
  "https://github.com/leanprover/subverso"@"9b90b7f938d6169246325df002351014f49945ef"
require «verso-slides» from git "https://github.com/leanprover/verso-slides"@"v4.34.0"
require plausible from git
  "https://github.com/leanprover-community/plausible"@"118aa17ee84656b8bd727fef7c458ee8c833385c"
require illuminate from git
  "https://github.com/leanprover/illuminate"@"a1a61c9678da010e958ed24cdfa6f635b85f172a"
-- The v4.34.0 release branch at the merge of leanprover/verso-blueprint#471.
require VersoBlueprint from git
  "https://github.com/leanprover/verso-blueprint"@"5d230ee7369bb6c18e667803c75f96dee5377d94"

package LeanGeodesyBlueprintYaruo where
  packagesDir := "../.lake/packages"
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib LeanGeodesyBlueprintYaruo where
