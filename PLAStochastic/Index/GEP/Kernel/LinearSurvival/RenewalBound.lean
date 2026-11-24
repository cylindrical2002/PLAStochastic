import PLAStochastic.Index.GEP.Kernel.LinearSurvival.LaplaceExtraction
import PLAStochastic.Index.GEP.RawDisc.ProductLaws

/-!
# A class-uniform linear bound for the renewal function

Nonnegative iid heights with a fixed positive chance of exceeding `h` have a
renewal function bounded linearly in the level. A Laplace-transform argument
avoids introducing a negative-binomial stopping time. Identifying these heights
with the strict ladder heights is a separate probability-theoretic step.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- On the unit interval, an exponential loss is at least half its argument. -/
theorem linearSurvival_one_sub_exp_neg {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    u / 2 ≤ 1 - Real.exp (-u) := by
  have h := Real.add_one_le_exp u
  have hp : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hprod := mul_le_mul_of_nonneg_right h (Real.exp_pos (-u)).le
  have he1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hsmall := mul_nonneg (show 0 ≤ 1 - u by linarith) (show 0 ≤ 1 - Real.exp (-u) by linarith)
  nlinarith

/-- A positive mass of heights above `h` gives a uniform Laplace-transform gap. -/
theorem linearSurvival_height_laplace_gap (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x) {h p t : ℝ}
    (hh : 0 ≤ h) (ht : 0 ≤ t) (hp : p ≤ (μ : Measure ℝ).real (Ici h)) :
    Integrable (fun x => Real.exp (-t * x)) (μ : Measure ℝ) ∧
      (∫ x, Real.exp (-t * x) ∂(μ : Measure ℝ)) ≤ 1 - p * (1 - Real.exp (-t * h)) := by
  have hint : Integrable (fun x => Real.exp (-t * x)) (μ : Measure ℝ) := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    filter_upwards [hμ] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by nlinarith)
  have hgap : 0 ≤ 1 - Real.exp (-t * h) := by
    have := Real.exp_le_one_iff.2 (show -t * h ≤ 0 by nlinarith)
    linarith
  have hi : Integrable (fun x : ℝ =>
      (Ici h).indicator (fun _ => 1 - Real.exp (-t * h)) x) (μ : Measure ℝ) :=
    (integrable_const _).indicator measurableSet_Ici
  have hle : (∫ x, Real.exp (-t * x) ∂(μ : Measure ℝ)) ≤
      ∫ x, 1 - (Ici h).indicator (fun _ => 1 - Real.exp (-t * h)) x ∂(μ : Measure ℝ) := by
    apply integral_mono_ae hint ((integrable_const _).sub hi)
    filter_upwards [hμ] with x hx
    change Real.exp (-t * x) ≤ 1 - (Ici h).indicator (fun _ => 1 - Real.exp (-t * h)) x
    by_cases hxh : h ≤ x
    · simp only [indicator_of_mem (show x ∈ Ici h from hxh)]
      have he : Real.exp (-t * x) ≤ Real.exp (-t * h) :=
        Real.exp_le_exp.2 (by nlinarith)
      linarith
    · simp only [indicator_of_notMem (show x ∉ Ici h from hxh), sub_zero]
      exact Real.exp_le_one_iff.2 (by nlinarith)
  rw [integral_sub (integrable_const _) hi, integral_const, integral_indicator measurableSet_Ici,
    integral_const] at hle
  simp only [probReal_univ, measureReal_restrict_apply_univ, smul_eq_mul, mul_one] at hle
  exact ⟨hint, hle.trans (by nlinarith)⟩

/-- The Laplace transform of an iid partial sum is the power of the one-step
transform. This statement uses the actual infinite product law. -/
theorem linearSurvival_iid_laplace (μ : ProbabilityMeasure ℝ) {t L : ℝ}
    (hL : 0 ≤ L) (hint : Integrable (fun x => Real.exp (-t * x)) (μ : Measure ℝ))
    (hbound : (∫ x, Real.exp (-t * x) ∂(μ : Measure ℝ)) ≤ L) (j : ℕ) :
    Integrable (fun g => Real.exp (-t * gapKeys g j)) (iidLaw μ) ∧
      (∫ g, Real.exp (-t * gapKeys g j) ∂(iidLaw μ)) ≤ L ^ j := by
  have hl : (∫⁻ x, ENNReal.ofReal (Real.exp (-t * x)) ∂(μ : Measure ℝ)) ≤
      ENNReal.ofReal L := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hbound
  have hprod : (∫⁻ g, ENNReal.ofReal (Real.exp (-t * gapKeys g j)) ∂(iidLaw μ)) ≤
      ENNReal.ofReal L ^ j := lintegral_exp_gapKeys_le (ρ := fun _ => μ) (fun _ => hl) j
  have hm : Measurable (fun g : ℕ → ℝ => Real.exp (-t * gapKeys g j)) := by
    exact ((rawAsm_measurable_gapKeys j).const_mul (-t)).exp
  have hi : Integrable (fun g => Real.exp (-t * gapKeys g j)) (iidLaw μ) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    exact lt_of_le_of_lt hprod (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
    hm.aestronglyMeasurable]
  rw [← ENNReal.ofReal_pow hL] at hprod
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hprod).trans_eq
    (ENNReal.toReal_ofReal (pow_nonneg hL j))

/-- Exponential Markov inequality for a low iid partial sum. -/
theorem linearSurvival_renewal_term (μ : ProbabilityMeasure ℝ) {t L δ : ℝ}
    (ht : 0 ≤ t) (hL : 0 ≤ L)
    (hint : Integrable (fun x => Real.exp (-t * x)) (μ : Measure ℝ))
    (hbound : (∫ x, Real.exp (-t * x) ∂(μ : Measure ℝ)) ≤ L) (j : ℕ) :
    (iidLaw μ).real {g | gapKeys g j ≤ δ} ≤ Real.exp (t * δ) * L ^ j := by
  obtain ⟨hi, hib⟩ := linearSurvival_iid_laplace μ hL hint hbound j
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun g : ℕ → ℝ => (Real.exp_pos (-t * gapKeys g j)).le)
    hi (Real.exp (-t * δ))
  have hsub : {g : ℕ → ℝ | gapKeys g j ≤ δ} ⊆
      {g : ℕ → ℝ | Real.exp (-t * δ) ≤ Real.exp (-t * gapKeys g j)} := by
    intro g hg
    exact Real.exp_le_exp.2 (by dsimp at hg ⊢; nlinarith)
  have hle := (mul_le_mul_of_nonneg_left (measureReal_mono hsub)
    (Real.exp_pos _).le).trans (hmark.trans hib)
  have h := mul_le_mul_of_nonneg_left hle (Real.exp_pos (t * δ)).le
  have he : Real.exp (t * δ) * Real.exp (-t * δ) = 1 := by
    rw [← Real.exp_add]
    simp
  simpa only [← mul_assoc, he, one_mul] using h

/-- A geometric transform gap bounds the actual renewal sum. -/
theorem linearSurvival_renewal_le_geometric (μ : ProbabilityMeasure ℝ) {t L δ : ℝ}
    (ht : 0 ≤ t) (hL : 0 ≤ L) (hL1 : L < 1)
    (hint : Integrable (fun x => Real.exp (-t * x)) (μ : Measure ℝ))
    (hbound : (∫ x, Real.exp (-t * x) ∂(μ : Measure ℝ)) ≤ L) :
    Summable (fun j => (iidLaw μ).real {g | gapKeys g j ≤ δ}) ∧
      (∑' j, (iidLaw μ).real {g | gapKeys g j ≤ δ}) ≤ Real.exp (t * δ) / (1 - L) := by
  have hg := (summable_geometric_of_lt_one hL hL1).mul_left (Real.exp (t * δ))
  have hb := linearSurvival_renewal_term (δ := δ) μ ht hL hint hbound
  have hs := Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) hb hg
  refine ⟨hs, (hs.tsum_le_tsum hb hg).trans_eq ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hL hL1, div_eq_mul_inv]

/-- **Linear renewal bound.** The constants depend only on the lower mass `p`
and the height threshold `h`, uniformly over the entire law. -/
theorem linearSurvival_renewal_linear (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x) {h p δ : ℝ}
    (hh : 0 < h) (hp : 0 < p) (hpμ : p ≤ (μ : Measure ℝ).real (Ici h)) (hδ : 0 ≤ δ) :
    Summable (fun j => (iidLaw μ).real {g | gapKeys g j ≤ δ}) ∧
      (∑' j, (iidLaw μ).real {g | gapKeys g j ≤ δ}) ≤
        2 * Real.exp 1 * (δ + h) / (p * h) := by
  let t := (δ + h)⁻¹
  have hdh : 0 < δ + h := by linarith
  have ht : 0 < t := inv_pos.2 hdh
  have hth0 : 0 ≤ t * h := mul_nonneg ht.le hh.le
  have hth1 : t * h ≤ 1 := by
    dsimp [t]
    rw [inv_mul_eq_div, div_le_one hdh]
    linarith
  have htd : t * δ ≤ 1 := by
    dsimp [t]
    rw [inv_mul_eq_div, div_le_one hdh]
    linarith
  let L := 1 - p * (1 - Real.exp (-t * h))
  obtain ⟨hint, hgap⟩ := linearSurvival_height_laplace_gap μ hμ hh.le ht.le hpμ
  have hL0 : 0 ≤ L := (integral_nonneg (fun _ => (Real.exp_pos _).le)).trans hgap
  have hloss : t * h / 2 ≤ 1 - Real.exp (-t * h) := by
    simpa only [neg_mul] using linearSurvival_one_sub_exp_neg hth0 hth1
  have hL1 : L < 1 := by
    dsimp [L]
    have : 0 < 1 - Real.exp (-t * h) := lt_of_lt_of_le (by positivity) hloss
    nlinarith
  obtain ⟨hs, hsum⟩ := linearSurvival_renewal_le_geometric μ ht.le hL0 hL1 hint hgap
  refine ⟨hs, hsum.trans ?_⟩
  have hden : p * t * h / 2 ≤ 1 - L := by
    dsimp [L]
    nlinarith [mul_le_mul_of_nonneg_left hloss hp.le]
  calc
    Real.exp (t * δ) / (1 - L) ≤ Real.exp 1 / (p * t * h / 2) :=
      div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.2 htd) (by positivity) hden
    _ = 2 * Real.exp 1 * (δ + h) / (p * h) := by
      dsimp [t]
      field_simp

end

end PGM
