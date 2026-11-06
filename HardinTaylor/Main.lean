import HardinTaylor.Exceptional
import HardinTaylor.Continuation

/-!
# The Hardin–Taylor Nearly Perfect Prediction Theorem

**Theorem** (C. Hardin, A. Taylor, *A peculiar connection between the axiom of
choice and predicting the future*, Am. Math. Monthly 115 (2008), 91–96).
Assuming the axiom of choice there is a prediction strategy which, given the
observed past `f ↾ (-∞, t)` of an arbitrary function `f : ℝ → ℝ`:

* predicts the present value `f(t)`, and
* predicts the immediate future — its continuation agrees with `f` on some
  right-neighbourhood of `t` —

and both predictions fail only on countable nowhere dense sets of times `t`.
The strategy is *nearly perfect*.

Present-value version; exceptional set = countable + nowhere dense, as in
U. Yurtsever, arXiv:2608.13899 (§II–III); expositions: J. D. Hamkins, "The
Nearly Perfect Prediction Theorem", Notices AMS, March 2025;
E. Moorhouse, "The Hardin–Taylor Theorem" (handout).
-/

noncomputable section

namespace HardinTaylor

/-- **The Hardin–Taylor Nearly Perfect Prediction Theorem** (present value). -/
theorem hardin_taylor :
    ∃ P : (ℝ → ℝ) → ℝ → ℝ,
      (∀ f g t, CompatibleWith f g t → P f t = P g t) ∧
      ∀ f, Set.Countable {t | P f t ≠ f t} ∧ IsNowhereDense {t | P f t ≠ f t} := by
  classical
  have hwo : IsWellOrder (ℝ → ℝ) (@WellOrderingRel (ℝ → ℝ)) :=
    WellOrderingRel.isWellOrder
  have hwf : WellFounded (@WellOrderingRel (ℝ → ℝ)) := hwo.wf
  have htrich : ∀ a b : ℝ → ℝ,
      ¬ WellOrderingRel a b → ¬ WellOrderingRel b a → a = b :=
    hwo.trichotomous
  refine ⟨fun f t => predict hwf f t, ?_, ?_⟩
  · intro f g t h
    exact predict_compatible hwf h
  · intro f
    exact ⟨exceptional_countable hwf htrich f, exceptional_nowhereDense hwf htrich f⟩

/-- **Full Hardin–Taylor: current *and* immediate future.** The chosen
continuation `Q f t` predicts both `f(t)` and the values of `f` just to the
right of `t`; both predictions fail only on a countable nowhere dense set of
times. -/
theorem hardin_taylor_full :
    ∃ Q : (ℝ → ℝ) → ℝ → (ℝ → ℝ),
      (∀ f g t, CompatibleWith f g t → Q f t = Q g t) ∧
      ∀ f,
        Set.Countable {t | Q f t t ≠ f t ∨
            ∀ ε > 0, ∃ x, t < x ∧ x < t + ε ∧ Q f t x ≠ f x} ∧
        IsNowhereDense {t | Q f t t ≠ f t ∨
            ∀ ε > 0, ∃ x, t < x ∧ x < t + ε ∧ Q f t x ≠ f x} := by
  classical
  have hwo : IsWellOrder (ℝ → ℝ) (@WellOrderingRel (ℝ → ℝ)) :=
    WellOrderingRel.isWellOrder
  have hwf : WellFounded (@WellOrderingRel (ℝ → ℝ)) := hwo.wf
  have htrich : ∀ a b : ℝ → ℝ,
      ¬ WellOrderingRel a b → ¬ WellOrderingRel b a → a = b :=
    hwo.trichotomous
  refine ⟨fun f t => predictedFunction hwf f t, ?_, ?_⟩
  · intro f g t h
    funext x
    exact predictedFunction_eq_of_candidates_eq hwf
      (candidates_eq_of_compatibleWith h) (candidates_nonempty f t)
      (candidates_nonempty g t) x
  · intro f
    have hset : {t | predictedFunction hwf f t t ≠ f t ∨
        continuationFails hwf f t} =
        {t | predict hwf f t ≠ f t} ∪ {t | continuationFails hwf f t} := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      exact Iff.rfl
    have hcount :
        Set.Countable {t | predictedFunction hwf f t t ≠ f t ∨
          continuationFails hwf f t} := by
      rw [hset]
      exact Set.Countable.union
        (exceptional_countable hwf htrich f) (continuation_countable hwf htrich f)
    have hnd :
        IsNowhereDense {t | predictedFunction hwf f t t ≠ f t ∨
          continuationFails hwf f t} := by
      rw [hset]
      exact nowhereDense_union
        (exceptional_nowhereDense hwf htrich f) (continuation_nowhereDense hwf htrich f)
    exact ⟨hcount, hnd⟩

end HardinTaylor
