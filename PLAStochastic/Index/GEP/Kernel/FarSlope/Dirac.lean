import PLAStochastic.Index.GEP.Kernel.Tail.Scalar.DiracTail
import PLAStochastic.Index.GEP.Kernel.FarSlope.FixedUniform

/-! # The actual short Dirac bridge is exponentially small on logarithmic input windows -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 1400000

/-- The forced slope is at least two when the designated gap is at most
half the band width. A genuine negative tilt then gives a fixed exponential
time rate with no increasing input factor. -/
theorem kernel_regLaw_dirac_pin_large_slope (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
      ∀ w x : ℝ, 1 ≤ w → 0 < x → 2 * x ≤ w + 1 →
      ∀ M : ℕ, 1 ≤ M →
        kernelDiracPin ν f w M x ≤ K * Real.exp (-c * M) := by
  obtain ⟨lam, c, hlam, hlR, hc, hrate⟩ :=
    kernel_regLaw_fixed_tilt_rates D θ vlo vhi (1 / 2) hθ hvlo hv (by norm_num) (by norm_num)
  have hlθ : |-lam| ≤ θ / 2 := by
    rw [abs_neg, abs_of_pos hlam]
    have hh := (hlR.trans (min_le_left _ _)).trans (saTiltRadius_le_half _ _ (show 0 < θ / 2 by positivity))
    linarith
  refine ⟨c, D * Real.exp θ * Real.exp lam, hc, by positivity, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe w x hw hx hax M hM
  let a := (w + 1) / x
  have hw0 : 0 < w := by linarith
  have ha2 : 2 ≤ a := (le_div_iff₀ hx).mpr hax
  have ha : 0 < a := by linarith
  have hU := hν.univClass hθ hvlo
  let := hU.isProbabilityMeasure_centeredTilt hlθ
  have hp : IsProbabilityMeasure ((ν : Measure ℝ).tilted (fun t => -lam * t)) := by
    rw [← kernel_centeredTilt_eq_raw]
    infer_instance
  let τ : ProbabilityMeasure ℝ := ⟨(ν : Measure ℝ).tilted (fun t => -lam * t), hp⟩
  have hτ : (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun t => -lam * t) := rfl
  have hftD := hν.kernelTiltDensity_le hθ hvlo hfz hfe hlθ
  have hft0 (t : ℝ) : 0 ≤ kernelTiltDensity ν (-lam) f t := mul_nonneg (Real.exp_nonneg _) (hf0 t)
  have hpin : kernelDiracPin τ (kernelTiltDensity ν (-lam) f) w M x ≤ D * Real.exp θ := by
    apply (kernelDiracPin_le_of_pin_bound τ _ hw0 hx M (by
      simpa only [abs_of_pos ha] using krDens_le_div (J := Icc 0 w) (β := 1) (a := a) τ hft0 hftD M 0 w)).trans
    exact div_le_self (by positivity) (by linarith)
  rw [kernel_dirac_pin_tilt ν τ hf hf0 hfD (hU.kernel_integrable_exp_raw hlθ) hτ hftD hw0 hx hM]
  have hr := mul_le_mul_of_nonneg_left ((hrate ν hν).1 a ha2) (Nat.cast_nonneg (α := ℝ) M)
  have hq : lam / a ≤ lam := (div_le_iff₀ ha).mpr (by nlinarith)
  have he : -(M : ℝ) * kernelTiltRate ν a (-lam) + -lam * x - -lam / a ≤ lam - c * M := by
    rw [neg_div]
    nlinarith
  calc
    _ ≤ Real.exp (lam - c * M) * (D * Real.exp θ) :=
      mul_le_mul (Real.exp_le_exp.mpr he) hpin (kernelDiracPin_nonneg τ hft0 w M hx.le) (Real.exp_nonneg _)
    _ = _ := by rw [show lam - c * M = lam + (-c * M) by ring, Real.exp_add]; ring

/-- On the forced large-slope range the entire actual Dirac time series,
including the two outer Green products, retains exponential width decay. -/
theorem kernel_regLaw_dirac_far_infinite (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
      ∀ w x : ℝ, 1 ≤ w → 0 < x → 2 * x ≤ w + 1 →
        Summable (kernelDiracTailTerm ν f w x) ∧
        (∑' m, kernelDiracTailTerm ν f w x m) ≤ K * w ^ 16 * Real.exp (-c * w) := by
  obtain ⟨c, B, hc, hB, hpin⟩ := kernel_regLaw_dirac_pin_large_slope D θ vlo vhi hD hθ hvlo hv
  obtain ⟨Os, Ol, hOs, hOl, ho⟩ := kernel_regLaw_outer_weight_bound D θ vlo vhi hD hθ hvlo hv
  refine ⟨c / 2, Ol * B * (3 * (1 + 1 / (c / 2)) ^ 4), by positivity, by positivity, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe w x hw hx hax
  have hw0 : 0 < w := by linarith
  let a := (w + 1) / x
  have ha2 : 2 ≤ a := (le_div_iff₀ hx).mpr hax
  have ha : 0 < a := by linarith
  have houter := ho ν hν w a hw ha
  rw [if_neg (by linarith : ¬ a ≤ 1 / 2)] at houter
  have hp (m : ℕ) : kernelDiracPin ν f w (m + 1) x ≤
      (B * Real.exp (-(c / 2) * w)) * Real.exp (-(c / 2) * ((m : ℝ) + 1)) := by
    by_cases hcross : w ≤ (m : ℝ) + 1
    · have hh := hpin ν hν f hf hf0 hfD hfz hfe w x hw hx hax (m + 1) (by omega)
      have hs := kernel_far_time_width_split hc.le hcross
      have hh' := mul_le_mul_of_nonneg_left hs hB.le
      apply hh.trans
      simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using hh'
    · unfold kernelDiracPin
      rw [kernel_density_up_zero_shift hν hθ hvlo hfz ha (by omega : 1 ≤ m + 1)
        (by push_cast; linarith), zero_div]
      positivity
  have hnonneg := kernelDiracTailTerm_nonneg ν hf0 hw0.le hx.le
  have hsum (N : ℕ) : (∑ m ∈ Finset.range N, kernelDiracTailTerm ν f w x m) ≤
      (Ol * B * (3 * (1 + 1 / (c / 2)) ^ 4)) * w ^ 16 * Real.exp (-(c / 2) * w) := by
    have hh : (∑ m ∈ Finset.range N, kernelDiracTailTerm ν f w x m) ≤
        (Ol * w ^ 6) * (B * Real.exp (-(c / 2) * w)) * ((2 + w) * (1 + 1 / (c / 2)) ^ 4) := by
      calc
        _ ≤ (Ol * w ^ 6) * (B * Real.exp (-(c / 2) * w)) *
            ∑ m ∈ Finset.range N, ((m : ℝ) + 1 + w) * Real.exp (-(c / 2) * ((m : ℝ) + 1)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro m hm
          have hh := mul_le_mul houter (mul_le_mul_of_nonneg_left (hp m) (show 0 ≤ (m : ℝ) + 1 + w by positivity))
            (mul_nonneg (by positivity) (kernelDiracPin_nonneg ν hf0 w (m + 1) hx.le)) (by positivity)
          exact hh.trans_eq (by ring)
        _ ≤ _ := mul_le_mul_of_nonneg_left (kernel_single_exp_sum_le (half_pos hc) hw0.le N) (by positivity)
    have ht : (2 + w) * (1 + 1 / (c / 2)) ^ 4 ≤ 3 * (1 + 1 / (c / 2)) ^ 4 * w := by
      have := mul_le_mul_of_nonneg_right (show 2 + w ≤ 3 * w by linarith) (show 0 ≤ (1 + 1 / (c / 2)) ^ 4 by positivity)
      nlinarith
    have hh' := hh.trans (mul_le_mul_of_nonneg_left ht (by positivity))
    have hw16 : w ^ 7 ≤ w ^ 16 := pow_le_pow_right₀ hw (by norm_num)
    have hlast := mul_le_mul_of_nonneg_left hw16
      (show 0 ≤ Ol * B * (3 * (1 + 1 / (c / 2)) ^ 4) * Real.exp (-(c / 2) * w) by positivity)
    apply hh'.trans
    convert hlast using 1 <;> ring
  exact ⟨summable_of_sum_range_le hnonneg hsum, Real.tsum_le_of_sum_range_le hnonneg hsum⟩

end
end PGM
