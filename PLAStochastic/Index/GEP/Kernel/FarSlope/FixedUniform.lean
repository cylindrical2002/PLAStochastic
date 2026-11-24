import PLAStochastic.Index.GEP.Kernel.Marked.Pin.FixedFar
import PLAStochastic.Index.GEP.Kernel.Marked.Pin.ShortBridge
import PLAStochastic.Index.GEP.Kernel.Tail.Scalar.PolynomialBudget

/-! # Fixed far-slope decay for the same density used by the actual IF -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 1200000

theorem kernel_regLaw_full_marked_pair_tilt_of_density (D θ vlo vhi : ℝ)
    (hθ : 0 < θ) (hvlo : 0 < vlo) :
    ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
        ∀ lam : ℝ, |lam| ≤ θ / 2 →
        ∀ J : Set ℝ, MeasurableSet J → volume J ≠ ⊤ →
        ∀ a : ℝ, 0 < a → ∀ t y z : ℝ, ∀ l r M : ℕ, 1 ≤ M →
          kernelMarkedFullDens J ν f 1 a t l r y z * krDens J ν f 1 a M z y ≤
            (D * Real.exp θ / a) ^ 2 *
              Real.exp (-((l : ℝ) + r + M) * kernelTiltRate ν a lam + lam * t - lam / a) := by
  intro ν hν f hf hf0 hfD hfz hfe hνf lam hlam J hJ hJfin a ha t y z l r M hM
  have hU := hν.univClass hθ hvlo
  let := hU.isProbabilityMeasure_centeredTilt hlam
  have hprob : IsProbabilityMeasure ((ν : Measure ℝ).tilted (fun x => lam * x)) := by
    rw [← kernel_centeredTilt_eq_raw]
    infer_instance
  let τ : ProbabilityMeasure ℝ := ⟨(ν : Measure ℝ).tilted (fun x => lam * x), hprob⟩
  have hτ : (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun x => lam * x) := rfl
  have hτf : (τ : Measure ℝ) = volume.withDensity
      (fun x => ENNReal.ofReal (kernelTiltDensity ν lam f x)) :=
    hτ.trans (kernel_tilt_density_measure ν hf hf0 hνf (hU.kernel_integrable_exp_raw hlam))
  have hftD := hν.kernelTiltDensity_le hθ hvlo hfz hfe hlam
  have hft : Measurable (kernelTiltDensity ν lam f) := by unfold kernelTiltDensity; fun_prop
  have hft0 (x : ℝ) : 0 ≤ kernelTiltDensity ν lam f x := by
    exact mul_nonneg (Real.exp_nonneg _) (hf0 x)
  have hh := kernel_full_marked_pin_tilt hJ ν τ hf hf0 hfD
    ((hν.univClass hθ hvlo).kernel_integrable_exp_raw hlam) hτ hftD 1 t ha.ne' l r hM y z
  simp only [mul_one] at hh
  rw [hh]
  have hb₁ := kernelFar_fullDens_le_div (β := 1) (t := t) hJ hJfin τ hft hft0 hftD hτf ha.ne' l r y z
  have hb₂ := krDens_le_div (J := J) (β := 1) (a := a) τ hft0 hftD M z y
  rw [abs_of_pos ha] at hb₁ hb₂
  have hp := mul_le_mul hb₁ hb₂ (krDens_nonneg τ hft0 _ _ _)
    (show 0 ≤ D * Real.exp θ / a from div_nonneg
      (mul_nonneg hν.D_nonneg (Real.exp_nonneg _)) ha.le)
  have hh' := mul_le_mul_of_nonneg_left hp
    (Real.exp_nonneg (-((l : ℝ) + r + M) * kernelTiltRate ν a lam + lam * t - lam / a))
  simpa only [kernelTiltRate, pow_two, mul_comm (Real.exp _) _] using hh'


theorem kernel_regLaw_full_pair_fixed_far_of_density (D θ vlo vhi δ : ℝ)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 2) :
    ∃ lam c : ℝ, 0 < lam ∧ 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
        ∀ J : Set ℝ, MeasurableSet J → volume J ≠ ⊤ →
        ∀ a : ℝ, 0 < a → δ ≤ |a - 1| → ∀ t : ℝ, 0 ≤ t → ∀ y z : ℝ,
        ∀ l r M : ℕ, 1 ≤ M →
          kernelMarkedFullDens J ν f 1 a t l r y z * krDens J ν f 1 a M z y ≤
            if a ≤ 1 / 2 then
              (D * Real.exp θ / a) ^ 2 *
                Real.exp (lam * t - c * ((l : ℝ) + r + M) / a)
            else
              (D * Real.exp θ / a) ^ 2 *
                Real.exp (lam * t + 2 * lam - c * ((l : ℝ) + r + M)) := by
  obtain ⟨lam, c, hlam, hlR, hc, hrate⟩ :=
    kernel_regLaw_fixed_tilt_rates D θ vlo vhi δ hθ hvlo hv hδ hδhi
  have hlθ : lam ≤ θ / 2 := by
    have hh := (hlR.trans (min_le_left _ _)).trans
      (saTiltRadius_le_half _ _ (show 0 < θ / 2 by positivity))
    linarith
  refine ⟨lam, c, hlam, hc, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe hνf
  have htilt := kernel_regLaw_full_marked_pair_tilt_of_density D θ vlo vhi hθ hvlo ν hν f hf hf0 hfD hfz hfe hνf
  intro J hJ hJfin a ha haway t ht y z l r M hM
  have hN : 0 ≤ (l : ℝ) + r + M := by positivity
  by_cases halo : a ≤ 1 / 2
  · rw [if_pos halo]
    have hh := htilt lam (by rwa [abs_of_pos hlam]) J hJ hJfin a ha t y z l r M hM
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    have hr := mul_le_mul_of_nonneg_left ((hrate ν hν).2.1 a ha halo) hN
    have he : ((l : ℝ) + r + M) * (c / a) = c * ((l : ℝ) + r + M) / a := by ring
    rw [he] at hr
    linarith [div_pos hlam ha]
  · rw [if_neg halo]
    let s := if a ≤ 1 then lam else -lam
    have hsabs : |s| ≤ θ / 2 := by
      dsimp [s]
      split_ifs <;> simp only [abs_neg, abs_of_pos hlam] <;> exact hlθ
    have hsrate : c ≤ kernelTiltRate ν a s := by
      by_cases hahi : 2 ≤ a
      · have ha1 : ¬ a ≤ 1 := by linarith
        simp only [s, if_neg ha1]
        exact (hrate ν hν).1 a hahi
      · exact (hrate ν hν).2.2 a (by linarith) (by linarith) haway
    have hsupper : s ≤ lam := by dsimp [s]; split_ifs <;> linarith
    have hslower : -lam ≤ s := by dsimp [s]; split_ifs <;> linarith
    have hquot : -s / a ≤ 2 * lam := by
      apply (div_le_iff₀ ha).mpr
      nlinarith
    have hh := htilt s hsabs J hJ hJfin a ha t y z l r M hM
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    have hr := mul_le_mul_of_nonneg_left hsrate hN
    have hi := mul_le_mul_of_nonneg_right hsupper ht
    rw [neg_div] at hquot
    linarith



/-- The positive-gap support forces an endpoint-to-endpoint marked pair to
vanish before its total number of steps can cross the width. -/
theorem kernel_full_pair_short_zero {D θ vlo vhi a w t : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo)
    {f : ℝ → ℝ} (hfz : ∀ x ≤ 0, f x = 0) (ha : 0 < a) (ht : 0 ≤ t)
    {y z : ℝ} (hyz : (y = 0 ∧ z = w) ∨ (y = w ∧ z = 0))
    (l r M : ℕ) (hM : 1 ≤ M) (hshort : (l : ℝ) + r + M + 1 ≤ w) :
    kernelMarkedFullDens (Icc 0 w) ν f 1 a t l r y z * krDens (Icc 0 w) ν f 1 a M z y = 0 := by
  rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [kernel_full_marked_up_short_zero hν hθ hvlo hfz ha ht l r (by
      nlinarith [Nat.cast_nonneg (α := ℝ) M]), zero_mul]
  · rw [kernel_density_up_zero_shift hν hθ hvlo hfz ha hM (by
      nlinarith [Nat.cast_nonneg (α := ℝ) l, Nat.cast_nonneg (α := ℝ) r]), mul_zero]

theorem kernel_far_time_width_split_add_one {c N w : ℝ} (hc : 0 ≤ c) (hwN : w ≤ N + 1) :
    Real.exp (-c * N) ≤ Real.exp (c / 2) * Real.exp (-(c / 2) * w) * Real.exp (-(c / 2) * N) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hwN hc]

/-- Outside the saddle neighborhood the actual pair has a genuine width
exponential, uniformly in both endpoint orientations and all random lengths.
The large-slope inverse square remains available for integrating to infinity. -/
theorem kernel_regLaw_full_pair_far_width (D θ vlo vhi δ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 2) :
    ∃ lam c K : ℝ, 0 < lam ∧ 0 < c ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ w a t : ℝ, 1 ≤ w → 0 < a → δ ≤ |a - 1| → 0 ≤ t →
      ∀ y z : ℝ, ((y = 0 ∧ z = w) ∨ (y = w ∧ z = 0)) →
      ∀ l r M : ℕ, 1 ≤ M →
        kernelMarkedFullDens (Icc 0 w) ν f 1 a t l r y z * krDens (Icc 0 w) ν f 1 a M z y ≤
          (if a ≤ 1 / 2 then K else K * a⁻¹ ^ 2) *
            Real.exp (lam * t - c * w) * Real.exp (-c * ((l : ℝ) + r + M)) := by
  obtain ⟨lam, c, hlam, hc, hfixed⟩ :=
    kernel_regLaw_full_pair_fixed_far_of_density D θ vlo vhi δ hθ hvlo hv hδ hδhi
  let S := (D * Real.exp θ) ^ 2 * (8 / c ^ 2)
  let L := (D * Real.exp θ) ^ 2 * Real.exp (2 * lam)
  let K := (S + L) * Real.exp (c / 2)
  have hS : 0 < S := by positivity
  have hL : 0 < L := by positivity
  have hK : 0 < K := by positivity
  refine ⟨lam, c / 2, K, hlam, by positivity, hK, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe hνf w a t hw ha haway ht y z hyz l r M hM
  let N : ℝ := (l : ℝ) + r + M
  have hN : 1 ≤ N := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    dsimp [N]
    nlinarith [Nat.cast_nonneg (α := ℝ) l, Nat.cast_nonneg (α := ℝ) r]
  by_cases hwN : w ≤ N + 1
  · have hh := hfixed ν hν f hf hf0 hfD hfz hfe hνf (Icc 0 w) measurableSet_Icc
      (by simp) a ha haway t ht y z l r M hM
    have hsplit := kernel_far_time_width_split_add_one hc.le hwN
    by_cases halo : a ≤ 1 / 2
    · rw [if_pos halo] at hh ⊢
      have hh' := hh.trans (kernel_small_pair_polynomial ha halo hc hN)
      have hwidth := mul_le_mul_of_nonneg_left hsplit (show 0 ≤ S * Real.exp (lam * t) by positivity)
      have hcoef : S * Real.exp (c / 2) ≤ K := by
        dsimp [K]
        gcongr
        linarith
      calc
        _ ≤ (S * Real.exp (lam * t)) *
            (Real.exp (c / 2) * Real.exp (-(c / 2) * w) * Real.exp (-(c / 2) * N)) := hh'.trans hwidth
        _ = (S * Real.exp (c / 2)) * Real.exp (lam * t - (c / 2) * w) * Real.exp (-(c / 2) * N) := by
          rw [show lam * t - (c / 2) * w = lam * t + (-(c / 2) * w) by ring, Real.exp_add]
          ring
        _ ≤ _ := by gcongr
    · rw [if_neg halo] at hh ⊢
      have he : (D * Real.exp θ / a) ^ 2 * Real.exp (lam * t + 2 * lam - c * N) =
          (L * a⁻¹ ^ 2 * Real.exp (lam * t)) * Real.exp (-c * N) := by
        rw [show lam * t + 2 * lam - c * N = 2 * lam + lam * t + (-c * N) by ring,
          Real.exp_add, Real.exp_add]
        dsimp [L]
        simp only [div_eq_mul_inv]
        ring
      change _ ≤ (D * Real.exp θ / a) ^ 2 * Real.exp (lam * t + 2 * lam - c * N) at hh
      rw [he] at hh
      have hwidth := mul_le_mul_of_nonneg_left hsplit (show 0 ≤ L * a⁻¹ ^ 2 * Real.exp (lam * t) by positivity)
      have hcoef : L * Real.exp (c / 2) ≤ K := by
        dsimp [K]
        gcongr
        linarith
      calc
        _ ≤ (L * a⁻¹ ^ 2 * Real.exp (lam * t)) *
            (Real.exp (c / 2) * Real.exp (-(c / 2) * w) * Real.exp (-(c / 2) * N)) := hh.trans hwidth
        _ = ((L * Real.exp (c / 2)) * a⁻¹ ^ 2) * Real.exp (lam * t - (c / 2) * w) * Real.exp (-(c / 2) * N) := by
          rw [show lam * t - (c / 2) * w = lam * t + (-(c / 2) * w) by ring, Real.exp_add]
          ring
        _ ≤ _ := by gcongr
  · rw [kernel_full_pair_short_zero hν hθ hvlo hfz ha ht hyz l r M hM (le_of_lt (not_le.mp hwN))]
    split_ifs <;> positivity

end
end PGM
