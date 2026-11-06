import HardinTaylor.Basic
import HardinTaylor.WellOrdered

/-!
# The predictor

Fix a well-order `r` on the function space `ℝ → ℝ` (provided by AC, e.g.
`WellOrderingRel`). Given the observed past of `f` at `t`, the predictor picks
the `r`-minimal candidate continuation and outputs its value at `t`.
-/

noncomputable section

namespace HardinTaylor

variable {r : (ℝ → ℝ) → (ℝ → ℝ) → Prop} (hwf : WellFounded r)

/-- The chosen continuation at time `t`: the `r`-minimal candidate for the
observed history `f ↾ (-∞, t)`. -/
def predictedFunction (f : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  (hwf.has_min (candidates f t) (candidates_nonempty f t)).choose

theorem predictedFunction_mem (f : ℝ → ℝ) (t : ℝ) :
    predictedFunction hwf f t ∈ candidates f t :=
  ((hwf.has_min (candidates f t) (candidates_nonempty f t)).choose_spec).1

theorem predictedFunction_minimal (f : ℝ → ℝ) (t : ℝ) {g : ℝ → ℝ}
    (hg : g ∈ candidates f t) : ¬ r g (predictedFunction hwf f t) :=
  ((hwf.has_min (candidates f t) (candidates_nonempty f t)).choose_spec).2 g hg

/-- The Hardin–Taylor predictor (present-value version): at time `t`, predict
`f(t)` from the observed past `f ↾ (-∞, t)` alone. -/
def predict (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  predictedFunction hwf f t t

/-- Minimal choices over the same set coincide (proof irrelevance). -/
theorem predictedFunction_eq_of_candidates_eq {S T : Set (ℝ → ℝ)}
    (h : S = T) (hS : S.Nonempty) (hT : T.Nonempty) (t : ℝ) :
    (hwf.has_min S hS).choose t = (hwf.has_min T hT).choose t := by
  subst h
  rfl

/-- The prediction depends only on the observed past (it is *online*). -/
theorem predict_compatible {f g : ℝ → ℝ} {t : ℝ} (h : CompatibleWith f g t) :
    predict hwf f t = predict hwf g t :=
  predictedFunction_eq_of_candidates_eq hwf
    (candidates_eq_of_compatibleWith h) (candidates_nonempty f t)
    (candidates_nonempty g t) t

end HardinTaylor
