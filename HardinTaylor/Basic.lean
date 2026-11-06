import Mathlib

/-!
# Basic: histories and compatibility

Present-value version of the Hardin–Taylor Nearly Perfect Prediction theorem.
Two functions are `t`-compatible iff they agree at every time strictly before `t`
(same observed past; the present value is *not* part of the history).
-/

noncomputable section

namespace HardinTaylor

/-- `f` and `g` have the same observed past at time `t`. -/
def CompatibleWith (f g : ℝ → ℝ) (t : ℝ) : Prop :=
  ∀ s : ℝ, s < t → f s = g s

@[simp] lemma compatibleWith_self (f : ℝ → ℝ) (t : ℝ) : CompatibleWith f f t :=
  fun _ _ => rfl

lemma compatibleWith_comm {f g : ℝ → ℝ} {t : ℝ} (h : CompatibleWith f g t) :
    CompatibleWith g f t :=
  fun s hs => (h s hs).symm

/-- The candidate continuations for the observed history at time `t`:
all total functions agreeing with `f` before `t`. -/
def candidates (f : ℝ → ℝ) (t : ℝ) : Set (ℝ → ℝ) :=
  {g | CompatibleWith f g t}

@[simp] lemma mem_candidates_iff {f g : ℝ → ℝ} {t : ℝ} :
    g ∈ candidates f t ↔ ∀ s < t, f s = g s :=
  Iff.rfl

lemma candidates_nonempty (f : ℝ → ℝ) (t : ℝ) : (candidates f t).Nonempty :=
  ⟨f, compatibleWith_self f t⟩

/-- `t`-compatible functions have the same candidate set. -/
lemma candidates_eq_of_compatibleWith {f g : ℝ → ℝ} {t : ℝ}
    (h : CompatibleWith f g t) : candidates f t = candidates g t := by
  ext k
  constructor <;> intro hk s hs
  · exact (h s hs).symm.trans (hk s hs)
  · exact (h s hs).trans (hk s hs)

/-- The candidate sets shrink as time moves forward. -/
lemma candidates_mono {f : ℝ → ℝ} {s t : ℝ} (hst : s < t) :
    candidates f t ⊆ candidates f s := by
  intro g hg u hu
  exact hg u (hu.trans hst)

end HardinTaylor
