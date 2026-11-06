import Lake
open Lake DSL

package «HardinTaylor» where
  -- Formalization of the Hardin-Taylor Nearly Perfect Prediction Theorem

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

@[default_target]
lean_lib «HardinTaylor» where
  -- one library, sources under HardinTaylor/
