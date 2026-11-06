import Mathlib

/-!
# Well-ordered subsets of ℝ

Every subset of `ℝ` well-ordered by `<` is countable and nowhere dense
(the engine room of the Hardin–Taylor exceptional-set argument).

Countability follows by injecting `A` into `ℚ` via the successor gaps;
nowhere density follows by taking the well-order minimum of `A ∩ U` for an
open interval `U ⊆ closure A` and finding a gap point below it.
-/

noncomputable section

namespace HardinTaylor

/-- `A` is well-ordered by the ambient order of `ℝ`. -/
abbrev WellOrdered (A : Set ℝ) : Prop :=
  WellFounded (fun x y : ↥A => (x : ℝ) < y)

/-- Each element of `A` owns a rational gap below the next element of `A`. -/
private theorem exists_rat_gap (A : Set ℝ) (hA : WellOrdered A) :
    ∀ a : ↥A, ∃ q : ℚ, (a : ℝ) < q ∧ ∀ y : ↥A, (a : ℝ) < y → (q : ℝ) < y := by
  intro a
  by_cases hex : ∃ b : ↥A, (a : ℝ) < b
  · have hsne : ({y : ↥A | (a : ℝ) < y} : Set ↥A).Nonempty := by
      obtain ⟨b, hb⟩ := hex
      exact ⟨b, hb⟩
    obtain ⟨m, hm, hmin⟩ := hA.has_min {y : ↥A | (a : ℝ) < y} hsne
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (a : ℝ) < m from hm)
    refine ⟨q, hq1, fun y hy => ?_⟩
    have hle : (m : ℝ) ≤ y := not_lt.mp (fun h => hmin y hy h)
    linarith
  · obtain ⟨q, hq⟩ := exists_rat_gt (a : ℝ)
    exact ⟨q, hq, fun y hy => (hex ⟨y, hy⟩).elim⟩

/-- **Well-ordered subsets of `ℝ` are countable.** -/
theorem wellOrdered_countable (A : Set ℝ) (hA : WellOrdered A) : Set.Countable A := by
  have hex := exists_rat_gap A hA
  set q : ↥A → ℚ := fun a => (hex a).choose
  have hq_lt : ∀ a : ↥A, (a : ℝ) < q a := fun a => (hex a).choose_spec.1
  have hq_gap : ∀ a : ↥A, ∀ y : ↥A, (a : ℝ) < y → (q a : ℝ) < y := fun a y h =>
    (hex a).choose_spec.2 y h
  have hinj : Function.Injective q := by
    intro a b hab
    by_contra hne
    rcases lt_trichotomy (a : ℝ) b with hlt | heq | hgt
    · have h1 : (q a : ℝ) < b := hq_gap a b hlt
      have h2 : (b : ℝ) < q b := hq_lt b
      rw [hab] at h1
      linarith
    · exact hne (Subtype.ext heq)
    · have h1 : (q b : ℝ) < a := hq_gap b a hgt
      have h2 : (a : ℝ) < q a := hq_lt a
      rw [← hab] at h1
      linarith
  exact Set.countable_iff_exists_injective.mpr
    ⟨fun a => Encodable.encode (q a), Encodable.encode_injective.comp hinj⟩

/-- **Well-ordered subsets of `ℝ` are nowhere dense.** -/
theorem wellOrdered_nowhereDense (A : Set ℝ) (hA : WellOrdered A) : IsNowhereDense A := by
  have h : interior (closure A) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    -- An open interval around `x` sits inside `closure A`.
    obtain ⟨⟨l, u⟩, ⟨hlx, hxu⟩, hsub⟩ :=
      (nhds_basis_Ioo x).mem_iff.1 (isOpen_interior.mem_nhds hx)
    have hU : Set.Ioo l u ⊆ closure A := hsub.trans interior_subset
    have hxcl : x ∈ closure A := interior_subset hx
    -- An open set inside the closure must meet `A`.
    have hmeet : (Set.Ioo l u ∩ A).Nonempty :=
      mem_closure_iff_nhds.1 hxcl _ (Ioo_mem_nhds hlx hxu)
    obtain ⟨a₀, ha₀U, ha₀A⟩ := hmeet
    -- Take the well-order minimum of `A ∩ Ioo l u`.
    have hsne : ({y : ↥A | (y : ℝ) ∈ Set.Ioo l u} : Set ↥A).Nonempty :=
      ⟨⟨a₀, ha₀A⟩, ha₀U⟩
    obtain ⟨m, hm, hmin⟩ := hA.has_min {y : ↥A | (y : ℝ) ∈ Set.Ioo l u} hsne
    have hmIoo : l < (m : ℝ) ∧ (m : ℝ) < u := Set.mem_Ioo.1 hm
    -- The gap `(l, m)` is a nonempty open piece of `closure A` missing `A`.
    have hV : (Set.Ioo l (m : ℝ)).Nonempty :=
      ⟨(l + (m : ℝ)) / 2, by constructor <;> linarith [hmIoo.1]⟩
    have hVU : Set.Ioo l (m : ℝ) ⊆ Set.Ioo l u :=
      fun y hy => ⟨hy.1, hy.2.trans hmIoo.2⟩
    have hVcapA : (Set.Ioo l (m : ℝ)) ∩ A = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro y hy
      have hyU : (y : ℝ) ∈ Set.Ioo l u := hVU hy.1
      have hymin : ¬ ((y : ℝ) < (m : ℝ)) := hmin ⟨y, hy.2⟩ hyU
      exact hymin hy.1.2
    -- But the open gap piece meets `A`, contradiction.
    obtain ⟨y, hy⟩ := hV
    have hycl : y ∈ closure A := hU (hVU hy)
    have hcap : (Set.Ioo l (m : ℝ) ∩ A).Nonempty :=
      mem_closure_iff_nhds.1 hycl _ (Ioo_mem_nhds hy.1 hy.2)
    rw [hVcapA] at hcap
    exact hcap.ne_empty rfl
  exact h

end HardinTaylor
