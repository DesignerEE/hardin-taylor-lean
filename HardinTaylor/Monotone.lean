import HardinTaylor.Predictor

/-!
# Monotonicity and strict climb

Two structural facts about the chosen continuations:

* **Monotonicity** — moving forward in time only grows the chosen function in
  the well-order `r`, since the candidate set shrinks;
* **Strict climb** — at two distinct failure times `s < t` the climb is strict:
  `g_s ≠ g_t`, because the later candidate `g_t` agrees with `f` at `s` while
  the earlier choice failed there.

Together: the map `t ↦ g_t` is order-preserving on failure times, so the
failure set embeds into the well-order `r`.
-/

noncomputable section

namespace HardinTaylor

/-- Monotonicity: the chosen continuation at a later time is never `r`-below
the one at an earlier time. -/
theorem predictedFunction_mono {r : (ℝ → ℝ) → (ℝ → ℝ) → Prop}
    (hwf : WellFounded r) (f : ℝ → ℝ) {s t : ℝ} (hst : s < t) :
    ¬ r (predictedFunction hwf f t) (predictedFunction hwf f s) :=
  predictedFunction_minimal hwf f s
    (candidates_mono hst (predictedFunction_mem hwf f t))

/-- Strict climb at failures: if the predictor fails at both `s < t`, then the
chosen continuations are strictly `r`-increasing. -/
theorem predictedFunction_strict_climb {r : (ℝ → ℝ) → (ℝ → ℝ) → Prop}
    (hwf : WellFounded r) (htrich : ∀ a b, ¬ r a b → ¬ r b a → a = b)
    (f : ℝ → ℝ) {s t : ℝ} (hst : s < t)
    (hs : predict hwf f s ≠ f s) (_ht : predict hwf f t ≠ f t) :
    r (predictedFunction hwf f s) (predictedFunction hwf f t) := by
  by_contra hneg
  have hne : predictedFunction hwf f s ≠ predictedFunction hwf f t := by
    intro heq
    -- The later candidate agrees with `f` at `s`, the earlier choice failed there.
    have hmemt : predictedFunction hwf f t ∈ candidates f t :=
      predictedFunction_mem hwf f t
    have hagree : f s = predictedFunction hwf f t s := hmemt s hst
    have hsame : predictedFunction hwf f s s = predictedFunction hwf f t s :=
      congrFun heq s
    have hfinal : predictedFunction hwf f s s = f s := hsame.trans hagree.symm
    exact hs hfinal
  -- ¬r(a,b) + ¬r(b,a) → a = b, contradicting the strict climb.
  exact hne (htrich _ _ hneg (predictedFunction_mono hwf f hst))

end HardinTaylor
