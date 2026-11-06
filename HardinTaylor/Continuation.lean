import HardinTaylor.Exceptional

/-!
# Future prediction: the continuation version

The chosen continuation `g_t` is itself a total function, so the strategy
predicts not only the present value `f(t)` but also the immediate future.
A time `t` *fails in the future sense* when `g_t` disagrees with `f` at
points arbitrarily close to the right of `t` (on no right-neighbourhood of
`t` does the continuation agree with `f`).

The failure set is again countable and nowhere dense: at two failure times
`s < t` the climb is strict, because the later candidate `g_t` already agrees
with `f` on the whole interval `(s, t)`, while the failure at `s` produces a
disagreement point inside `(s, t)`.
-/

noncomputable section

namespace HardinTaylor

/-- The strategy fails to predict the immediate future at `t`: the chosen
continuation disagrees with `f` at points arbitrarily close to the right of
`t`. -/
def continuationFails {r : (ℝ → ℝ) → (ℝ → ℝ) → Prop} (hwf : WellFounded r)
    (f : ℝ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ x, t < x ∧ x < t + ε ∧ predictedFunction hwf f t x ≠ f x

/-- Strict climb at future-failure times. -/
theorem continuation_strict_climb {r : (ℝ → ℝ) → (ℝ → ℝ) → Prop}
    (hwf : WellFounded r) (htrich : ∀ a b, ¬ r a b → ¬ r b a → a = b)
    (f : ℝ → ℝ) {s t : ℝ} (hst : s < t)
    (hs : continuationFails hwf f s) (_ht : continuationFails hwf f t) :
    r (predictedFunction hwf f s) (predictedFunction hwf f t) := by
  by_contra hneg
  have hne : predictedFunction hwf f s ≠ predictedFunction hwf f t := by
    intro heq
    -- Fail at `s` on the scale `t - s`: a disagreement point `x ∈ (s, t)`.
    obtain ⟨x, hxs, hxt, hbad⟩ := hs (t - s) (by linarith)
    -- But the later candidate agrees with `f` on `(-∞, t) ∋ x`.
    have hmemt : predictedFunction hwf f t ∈ candidates f t :=
      predictedFunction_mem hwf f t
    have hgood : f x = predictedFunction hwf f t x := hmemt x (by linarith)
    rw [← heq] at hgood
    exact hbad hgood.symm
  exact hne (htrich _ _ hneg (predictedFunction_mono hwf f hst))

/-- The future-failure set is well-ordered by `<`. -/
theorem continuation_wellOrdered {r : (ℝ → ℝ) → (ℝ → ℝ) → Prop}
    (hwf : WellFounded r) (htrich : ∀ a b, ¬ r a b → ¬ r b a → a = b)
    (f : ℝ → ℝ) : WellOrdered {t | continuationFails hwf f t} := by
  show WellFounded (fun x y : ↥{t | continuationFails hwf f t} => (x : ℝ) < y)
  refine WellFounded.mono
    (InvImage.wf (fun x : ↥{t | continuationFails hwf f t} =>
      predictedFunction hwf f x) hwf) ?_
  intro a b hlt
  exact continuation_strict_climb hwf htrich f hlt a.2 b.2

theorem continuation_countable {r : (ℝ → ℝ) → (ℝ → ℝ) → Prop}
    (hwf : WellFounded r) (htrich : ∀ a b, ¬ r a b → ¬ r b a → a = b)
    (f : ℝ → ℝ) : Set.Countable {t | continuationFails hwf f t} :=
  wellOrdered_countable _ (continuation_wellOrdered hwf htrich f)

theorem continuation_nowhereDense {r : (ℝ → ℝ) → (ℝ → ℝ) → Prop}
    (hwf : WellFounded r) (htrich : ∀ a b, ¬ r a b → ¬ r b a → a = b)
    (f : ℝ → ℝ) : IsNowhereDense {t | continuationFails hwf f t} :=
  wellOrdered_nowhereDense _ (continuation_wellOrdered hwf htrich f)

/-- Finite unions of nowhere dense sets are nowhere dense. -/
theorem nowhereDense_union {s u : Set ℝ} (hs : IsNowhereDense s)
    (hu : IsNowhereDense u) : IsNowhereDense (s ∪ u) := by
  have e1 : interior (closure s) = ∅ := hs
  have e2 : interior (closure u) = ∅ := hu
  have hcl : closure (s ∪ u) = closure s ∪ closure u := closure_union
  show interior (closure (s ∪ u)) = ∅
  rw [hcl]
  apply Set.eq_empty_iff_forall_notMem.2
  intro x hx
  -- An open interval around `x` sits inside `closure s ∪ closure u`.
  obtain ⟨⟨l, u'⟩, ⟨hlx, hxu'⟩, hsub⟩ :=
    (nhds_basis_Ioo x).mem_iff.1 (isOpen_interior.mem_nhds hx)
  have hU : Set.Ioo l u' ⊆ closure s ∪ closure u := hsub.trans interior_subset
  by_cases h : Set.Ioo l u' ⊆ closure s
  · -- Then the interval witnesses `x ∈ interior (closure s)`.
    have hxs : x ∈ interior (closure s) :=
      interior_maximal h isOpen_Ioo ⟨hlx, hxu'⟩
    rw [e1] at hxs
    exact absurd hxs (by simp)
  · -- Else the interval has a point outside `closure s`; the open remainder
    -- lies inside `closure u`, contradicting `interior (closure u) = ∅`.
    obtain ⟨y, hy, hys⟩ := Set.not_subset.1 h
    have hWopen : IsOpen (Set.Ioo l u' ∩ (closure s)ᶜ) :=
      isOpen_Ioo.inter (isOpen_compl_iff.2 isClosed_closure)
    have hyW : y ∈ Set.Ioo l u' ∩ (closure s)ᶜ := ⟨hy, hys⟩
    have hWsub : Set.Ioo l u' ∩ (closure s)ᶜ ⊆ closure u := by
      intro z hz
      rcases hU hz.1 with hzs | hzu
      · exact absurd hzs hz.2
      · exact hzu
    have hyu : y ∈ interior (closure u) :=
      interior_maximal hWsub hWopen hyW
    rw [e2] at hyu
    exact absurd hyu (by simp)

end HardinTaylor
