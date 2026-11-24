import PLAStochastic.ForMathlib.Analysis.Complex.TaylorDisc
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-! # Recovering finite Taylor coefficients from measurable samples -/

noncomputable section
open Complex Filter Topology MeasureTheory Finset
namespace PGM

theorem complexTaylorSum_succ (f : ℂ → ℂ) (n : ℕ) (c z : ℂ) :
    complexTaylorSum f (n + 1) c z = complexTaylorSum f n c z +
      (n.factorial : ℂ)⁻¹ * (z - c) ^ n * iteratedDeriv n f c := by
  simp only [complexTaylorSum, sum_range_succ]

theorem tendsto_taylorCoefficient_of_remainder {f : ℂ → ℂ} {h : ℕ → ℂ}
    (hne : ∀ i, h i ≠ 0) (hlim : Tendsto h atTop (𝓝 0)) (n : ℕ) {K : ℝ}
    (hbound : ∀ᶠ i in atTop,
      ‖f (h i) - complexTaylorSum f (n + 1) 0 (h i)‖ ≤ K * ‖h i‖ ^ (n + 1)) :
    Tendsto (fun i => ((h i) ^ n)⁻¹ * (f (h i) - complexTaylorSum f n 0 (h i)))
      atTop (𝓝 ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0)) := by
  have he (i : ℕ) :
      ((h i) ^ n)⁻¹ * (f (h i) - complexTaylorSum f n 0 (h i)) -
        (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 =
      ((h i) ^ n)⁻¹ * (f (h i) - complexTaylorSum f (n + 1) 0 (h i)) := by
    rw [complexTaylorSum_succ, sub_zero]
    field_simp [hne i]
    ring
  have ht : Tendsto (fun i =>
      ((h i) ^ n)⁻¹ * (f (h i) - complexTaylorSum f n 0 (h i)) -
        (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun i => K * ‖h i‖) ?_ ?_
    · filter_upwards [hbound] with i hi
      rw [he, norm_mul, norm_inv, norm_pow]
      calc (‖h i‖ ^ n)⁻¹ * ‖f (h i) - complexTaylorSum f (n + 1) 0 (h i)‖
          ≤ (‖h i‖ ^ n)⁻¹ * (K * ‖h i‖ ^ (n + 1)) :=
            mul_le_mul_of_nonneg_left hi (by positivity)
        _ = K * ‖h i‖ := by
          rw [pow_succ]
          field_simp [norm_ne_zero_iff.mpr (hne i)]
    · simpa using hlim.norm.const_mul K
  simpa only [sub_add_cancel, zero_add] using
    ht.add_const ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0)

theorem aestronglyMeasurable_taylorCoefficients_of_samples
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : α → ℂ → ℂ}
    {samples : ℕ → α → ℂ} {h : ℕ → ℂ}
    (hne : ∀ i, h i ≠ 0) (hlim : Tendsto h atTop (𝓝 0))
    (hm : ∀ i, AEStronglyMeasurable (samples i) μ)
    (he : ∀ a, ∀ᶠ i in atTop, samples i a = F a (h i))
    (hb : ∀ a n, ∃ K : ℝ, ∀ᶠ i in atTop,
      ‖F a (h i) - complexTaylorSum (F a) (n + 1) 0 (h i)‖ ≤
        K * ‖h i‖ ^ (n + 1)) (n : ℕ) :
    AEStronglyMeasurable (fun a => (n.factorial : ℂ)⁻¹ * iteratedDeriv n (F a) 0) μ := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hpoly (i : ℕ) : AEStronglyMeasurable
        (fun a => complexTaylorSum (F a) n 0 (h i)) μ := by
      unfold complexTaylorSum
      refine Finset.aestronglyMeasurable_fun_sum _ fun j hj => ?_
      have hjn : j < n := mem_range.mp hj
      simpa only [sub_zero, mul_left_comm, mul_assoc] using
        (ih j hjn).const_mul ((h i) ^ j)
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (fun i => ((hm i).sub (hpoly i)).const_mul (((h i) ^ n)⁻¹))
      (ae_of_all _ fun a => ?_)
    obtain ⟨K, hK⟩ := hb a n
    have ht := tendsto_taylorCoefficient_of_remainder hne hlim n hK
    exact ht.congr' ((he a).mono fun i hi => by simp only [Pi.sub_apply, hi])

end PGM
