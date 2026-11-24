import PLAStochastic.Index.GEP.SurvivalBound.KilledRow.PointwiseBound
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Variation contraction for the real killed convolution

These are the two coefficient-one variation contractions in §2 of
`research/2026-09-28-gep-closure/kernel-bv.md`. The interval cutoff includes the
boundary jumps. Its proof uses monotone reparameterizations whose exterior
values tend to zero, rather than discarding the boundary terms.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

/-- Replace the portions outside an interval by two distant constant arguments. -/
def kBVClamp (a b A B x : ℝ) : ℝ := if x < a then A else if b < x then B else x

theorem kBVClamp_monotone {a b A B : ℝ} (hab : a ≤ b) (hA : A ≤ a) (hB : b ≤ B) :
    Monotone (kBVClamp a b A B) := by
  intro x y hxy
  unfold kBVClamp
  split_ifs <;> linarith

/-- Cutting to an interval does not increase whole-line variation when both
exterior limits are zero. No continuity at either endpoint is assumed. -/
theorem kBV_variation_indicator_le {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hleft : Tendsto f atBot (𝓝 0)) (hright : Tendsto f atTop (𝓝 0)) :
    eVariationOn ((Icc a b).indicator f) univ ≤ eVariationOn f univ := by
  let q : ℕ → ℝ → ℝ := fun n => kBVClamp a b (a - n) (b + n)
  have hm (n : ℕ) : Monotone (q n) :=
    kBVClamp_monotone hab (sub_le_self _ (Nat.cast_nonneg n)) (le_add_of_nonneg_right (Nat.cast_nonneg n))
  have hb (n : ℕ) : eVariationOn (f ∘ q n) univ ≤ eVariationOn f univ :=
    eVariationOn.comp_le_of_monotoneOn f (q n) ((hm n).monotoneOn univ) (fun _ _ => mem_univ _)
  have hpt : ∀ x ∈ (univ : Set ℝ), Tendsto (fun n => (f ∘ q n) x) atTop
      (𝓝 ((Icc a b).indicator f x)) := by
    intro x _
    by_cases hxa : x < a
    · have hseq : Tendsto (fun n : ℕ => a - (n : ℝ)) atTop atBot :=
        by simpa only [sub_eq_add_neg, Function.comp_def] using
          tendsto_const_nhds.add_atBot (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
      simpa [Function.comp_def, q, kBVClamp, hxa, indicator_of_notMem, not_le.mpr hxa] using hleft.comp hseq
    · by_cases hbx : b < x
      · have hseq : Tendsto (fun n : ℕ => b + (n : ℝ)) atTop atTop :=
          tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
        simpa [Function.comp_def, q, kBVClamp, hxa, hbx, indicator_of_notMem, not_le.mpr hbx] using hright.comp hseq
      · have hx : x ∈ Icc a b := ⟨le_of_not_gt hxa, le_of_not_gt hbx⟩
        simp [q, kBVClamp, hxa, hbx, indicator_of_mem hx]
  by_contra h
  have hev := eVariationOn.lowerSemicontinuous_aux hpt (lt_of_not_ge h)
  obtain ⟨n, hn⟩ := hev.exists
  exact (not_lt_of_ge (hb n)) hn

/-- An integrable bounded-variation function has zero exterior limits. -/
theorem kBV_tendsto_zero_of_integrable {f : ℝ → ℂ} (hf : BoundedVariationOn f univ)
    (h1 : Integrable f) : Tendsto f atBot (𝓝 0) ∧ Tendsto f atTop (𝓝 0) := by
  obtain ⟨l, hl⟩ := hf.exists_tendsto_atBot
  obtain ⟨r, hr⟩ := hf.exists_tendsto_atTop
  simp only [principal_univ, top_inf_eq] at hl hr
  have hl0 : l = 0 := (h1.integrableAtFilter atBot).eq_zero_of_tendsto (fun s hs => by
    obtain ⟨b, hb⟩ := mem_atBot_sets.mp hs
    rw [← top_le_iff, ← Real.volume_Iic (a := b)]
    exact measure_mono hb) hl
  have hr0 : r = 0 := (h1.integrableAtFilter atTop).eq_zero_of_tendsto (fun s hs => by
    obtain ⟨b, hb⟩ := mem_atTop_sets.mp hs
    rw [← top_le_iff, ← Real.volume_Ici (a := b)]
    exact measure_mono hb) hr
  exact ⟨hl0 ▸ hl, hr0 ▸ hr⟩

/-- Interval cutoff is a coefficient-one contraction on integrable BV functions. -/
theorem kBV_variation_indicator_le_of_integrable {f : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hf : BoundedVariationOn f univ) (h1 : Integrable f) :
    eVariationOn ((Icc a b).indicator f) univ ≤ eVariationOn f univ := by
  obtain ⟨hl, hr⟩ := kBV_tendsto_zero_of_integrable hf h1
  exact kBV_variation_indicator_le hab hl hr

/-- Probability convolution does not increase variation. This theorem applies to
an arbitrary finite-variation representative, including its jumps. -/
theorem kBV_variation_kConv_le {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {f : ℝ → ℂ} (hf : Measurable f) (hfv : BoundedVariationOn f univ) (β a : ℝ) :
    eVariationOn (kConv ρ β a f) univ ≤ eVariationOn f univ := by
  have hbound : ∀ x, ‖f x‖ ≤ (eVariationOn f univ).toReal + ‖f 0‖ := by
    intro x
    have h := hfv.dist_le (mem_univ x) (mem_univ 0)
    calc ‖f x‖ ≤ ‖f x - f 0‖ + ‖f 0‖ := by simpa only [sub_add_cancel] using (norm_add_le (f x - f 0) (f 0))
      _ ≤ (eVariationOn f univ).toReal + ‖f 0‖ := by simpa [dist_eq_norm] using add_le_add_right h ‖f 0‖
  have hi (x : ℝ) : Integrable (fun y => f (x + β - a * y)) ρ :=
    (integrable_const ((eVariationOn f univ).toReal + ‖f 0‖)).mono'
      (hf.comp (by fun_prop)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => hbound _)
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n, s, hs, _⟩
  change (∑ i ∈ Finset.range n,
    edist (kConv ρ β a f (s (i + 1))) (kConv ρ β a f (s i))) ≤ eVariationOn f univ
  calc (∑ i ∈ Finset.range n, edist (kConv ρ β a f (s (i + 1))) (kConv ρ β a f (s i)))
      ≤ ∑ i ∈ Finset.range n, ∫⁻ y, edist (f (s (i + 1) + β - a * y))
          (f (s i + β - a * y)) ∂ρ := by
        apply Finset.sum_le_sum
        intro i _
        exact edist_integral_le_lintegral_edist (hi _) (hi _)
    _ = ∫⁻ y, ∑ i ∈ Finset.range n, edist (f (s (i + 1) + β - a * y))
        (f (s i + β - a * y)) ∂ρ := by
      symm
      apply lintegral_finsetSum
      intro i _
      exact (hf.comp (by fun_prop)).edist (hf.comp (by fun_prop))
    _ ≤ ∫⁻ _y, eVariationOn f univ ∂ρ := by
      apply lintegral_mono
      intro y
      exact eVariationOn.sum_le (f := f) (s := univ)
        (u := fun i => s i + β - a * y)
        (fun i j hij => by dsimp; linarith only [hs hij])
        (fun _ => mem_univ _)
    _ = eVariationOn f univ := by simp

/-- The actual killed step is a coefficient-one BV contraction. In particular,
the newly created boundary jumps have already been paid for by exterior variation. -/
theorem kBV_variation_kStep_le {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {f : ℝ → ℂ} (hf : Measurable f) (hfv : BoundedVariationOn f univ)
    (h1 : Integrable f) {l r : ℝ} (hlr : l ≤ r) (β a : ℝ) :
    eVariationOn (kStep (Icc l r) ρ β a f) univ ≤ eVariationOn f univ := by
  have hconv := kBV_variation_kConv_le (ρ := ρ) hf hfv β a
  have hconvBV : BoundedVariationOn (kConv ρ β a f) univ :=
    ne_top_of_le_ne_top hfv hconv
  exact (kBV_variation_indicator_le_of_integrable hlr hconvBV
    (integrable_kConv ρ hf h1 β a)).trans hconv

/-- Variation remains bounded by the initial variation through any number of real
killed steps. The bound has no constant raised to the number of steps. -/
theorem kBV_variation_iterate_le {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {f : ℝ → ℂ} (hf : Measurable f) (hfv : BoundedVariationOn f univ)
    (h1 : Integrable f) {l r : ℝ} (hlr : l ≤ r) (β a : ℝ) (n : ℕ) :
    eVariationOn ((kStep (Icc l r) ρ β a)^[n] f) univ ≤ eVariationOn f univ := by
  have hall : ∀ n : ℕ, Measurable ((kStep (Icc l r) ρ β a)^[n] f) ∧
      Integrable ((kStep (Icc l r) ρ β a)^[n] f) ∧
      BoundedVariationOn ((kStep (Icc l r) ρ β a)^[n] f) univ ∧
      eVariationOn ((kStep (Icc l r) ρ β a)^[n] f) univ ≤ eVariationOn f univ := by
    intro m
    induction m with
    | zero => exact ⟨hf, h1, hfv, le_rfl⟩
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      have hvar := kBV_variation_kStep_le (ρ := ρ) ih.1 ih.2.2.1 ih.2.1 hlr β a
      refine ⟨measurable_kStep measurableSet_Icc ρ ih.1, ?_,
        ne_top_of_le_ne_top ih.2.2.1 hvar, hvar.trans ih.2.2.2⟩
      exact (integrable_kConv ρ ih.1 ih.2.1 β a).indicator measurableSet_Icc
  exact (hall n).2.2.2

end
end PGM
