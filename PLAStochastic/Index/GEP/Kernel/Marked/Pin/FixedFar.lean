import PLAStochastic.Index.GEP.Kernel.Marked.Pin.FullTilt

/-! # Full marked pin estimates outside a fixed saddle neighborhood -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 800000

/-- The same fixed pair of genuine tilts covers all slopes outside the saddle
neighborhood, including both unbounded slope ends. The inverse slope factors
are preserved for the subsequent slope integral. -/
theorem kernel_regLaw_full_pair_fixed_far (D θ vlo vhi δ : ℝ)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 2) :
    ∃ lam c : ℝ, 0 < lam ∧ 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ D) ∧
        (∀ x ≤ 0, f x = 0) ∧ (∀ x, f x ≤ D * Real.exp (-θ * x)) ∧
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
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
  intro ν hν
  obtain ⟨f, hf, hf0, hfD, hfz, hfe, hνf, htilt⟩ :=
    kernel_regLaw_full_marked_pair_tilt D θ vlo vhi hθ hvlo ν hν
  refine ⟨f, hf, hf0, hfD, hfz, hfe, hνf, ?_⟩
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

/-- Once the actual admissible pair has total random length at least the
width, a fixed far-slope exponent retains both a width decay and a summable
time decay. -/
theorem kernel_far_time_width_split {c N w : ℝ} (hc : 0 ≤ c) (hwN : w ≤ N) :
    Real.exp (-c * N) ≤ Real.exp (-(c / 2) * w) * Real.exp (-(c / 2) * N) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hwN hc]

end
end PGM
