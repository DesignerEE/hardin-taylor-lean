import HardinTaylor.Monotone
import HardinTaylor.WellOrdered

/-!
# The exceptional set

The failure times of the predictor embed order-preservingly into the
well-order `r` via `t ↦ g_t`; hence they form a well-ordered subset of `ℝ`,
which is countable and nowhere dense.
-/

noncomputable section

namespace HardinTaylor

/-- The failure times of the predictor for `f`. -/
def exceptionalSet {r : (ℝ → ℝ) → (ℝ → ℝ) → Prop} (hwf : WellFounded r)
    (f : ℝ → ℝ) : Set ℝ :=
  {t | predict hwf f t ≠ f t}

/-- On failure times the map `t ↦ g_t` strictly preserves the order. -/
private theorem climb_on_exceptional {r : (ℝ → ℝ) → (ℝ → ℝ) → Prop}
    (hwf : WellFounded r) (htrich : ∀ a b, ¬ r a b → ¬ r b a → a = b)
    (f : ℝ → ℝ) {s t : ℝ}
    (hs : s ∈ exceptionalSet hwf f) (ht : t ∈ exceptionalSet hwf f) (hst : s < t) :
    r (predictedFunction hwf f s) (predictedFunction hwf f t) :=
  predictedFunction_strict_climb hwf htrich f hst hs ht

/-- The failure set is well-ordered by `<`. -/
theorem exceptional_wellOrdered {r : (ℝ → ℝ) → (ℝ → ℝ) → Prop}
    (hwf : WellFounded r) (htrich : ∀ a b, ¬ r a b → ¬ r b a → a = b)
    (f : ℝ → ℝ) : WellOrdered (exceptionalSet hwf f) := by
  show WellFounded (fun x y : ↥(exceptionalSet hwf f) => (x : ℝ) < y)
  refine WellFounded.mono
    (InvImage.wf (fun x : ↥(exceptionalSet hwf f) => predictedFunction hwf f x) hwf) ?_
  intro a b hlt
  exact climb_on_exceptional hwf htrich f a.2 b.2 hlt

theorem exceptional_countable {r : (ℝ → ℝ) → (ℝ → ℝ) → Prop}
    (hwf : WellFounded r) (htrich : ∀ a b, ¬ r a b → ¬ r b a → a = b)
    (f : ℝ → ℝ) : Set.Countable (exceptionalSet hwf f) :=
  wellOrdered_countable _ (exceptional_wellOrdered hwf htrich f)

theorem exceptional_nowhereDense {r : (ℝ → ℝ) → (ℝ → ℝ) → Prop}
    (hwf : WellFounded r) (htrich : ∀ a b, ¬ r a b → ¬ r b a → a = b)
    (f : ℝ → ℝ) : IsNowhereDense (exceptionalSet hwf f) :=
  wellOrdered_nowhereDense _ (exceptional_wellOrdered hwf htrich f)

end HardinTaylor
