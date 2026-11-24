import PLAStochastic.Index.GEP.Kernel.Marked.Pin.FullTilt

/-!
# Full-input marked pin bounds over all positive slopes

The small-slope tilt is chosen after an arbitrary positive input-tail weight.
The large-slope estimate retains the actual inverse-square slope factor and is
independent of the designated input. These pointwise estimates precede the
outer Green sums, slope integration and the separate short Dirac bridge.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 800000

/-- Positive tilts can be made arbitrarily small while retaining a uniform
`1/a` rate on the whole small-slope half interval. -/
theorem kernel_regLaw_arbitrary_small_tilt (D θ vlo vhi ζ : ℝ)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (hζ : 0 < ζ) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ ζ ∧ lam ≤ θ / 2 ∧
      lam ≤ kernelTiltClassRadius D θ vlo vhi ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
        ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → lam / (4 * a) ≤ kernelTiltRate ν a lam := by
  let R := kernelTiltClassRadius D θ vlo vhi
  let lam := min R (min ζ (1 / (4 * vhi)))
  have hvhi : 0 < vhi := hvlo.trans_le hv
  have hR : 0 < R := kernelTiltClassRadius_pos hθ hvlo hv
  have hlam : 0 < lam := lt_min hR (lt_min hζ (by positivity))
  have hlR : lam ≤ R := min_le_left _ _
  have hlζ : lam ≤ ζ := (min_le_right _ _).trans (min_le_left _ _)
  have hlv : lam ≤ 1 / (4 * vhi) := (min_le_right _ _).trans (min_le_right _ _)
  have hlrad : |lam| ≤ saTiltRadius vlo (2 * D / θ) (θ / 2) := by
    rw [abs_of_pos hlam]
    exact hlR.trans (min_le_left _ _)
  have hlθ : lam ≤ θ / 2 := by
    have hh := hlrad.trans (saTiltRadius_le_half _ _ (show 0 < θ / 2 by positivity))
    rw [abs_of_pos hlam] at hh
    linarith
  refine ⟨lam, hlam, hlζ, hlθ, hlR, ?_⟩
  intro ν hν a ha halo
  have hU := hν.univClass hθ hvlo
  have hquad := hU.kernel_centered_cgf_upper hvlo (show 0 < θ / 2 by positivity) hlrad
  have hsmall : vhi * lam ^ 2 ≤ lam / 4 := by
    have hh := (le_div_iff₀ (show 0 < 4 * vhi by positivity)).mp hlv
    have hh' := mul_le_mul_of_nonneg_right hh hlam.le
    nlinarith
  rw [hU.kernelTiltRate_eq_centered (by rwa [abs_of_pos hlam])]
  have hcost : lam / (4 * a) ≤ lam * (1 / a - 1) - lam / 4 := by
    apply (mul_le_mul_iff_right₀ (show 0 < 4 * a by positivity)).mp
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left halo hlam.le]
  linarith

/-- The full marked pair has a bound for every positive slope and every
positive input. The small-slope input exponent is an arbitrary `ζ`, whereas
all powers of width in the large-slope part are fixed before `ζ` is chosen. -/
theorem kernel_regLaw_full_pair_all_slopes (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ k : ℝ, 0 < k ∧ ∀ ζ : ℝ, 0 < ζ → ∃ c : ℝ, 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ D) ∧
        (∀ x ≤ 0, f x = 0) ∧ (∀ x, f x ≤ D * Real.exp (-θ * x)) ∧
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ α w a : ℝ, 1 ≤ w → 0 < a → ∀ t : ℝ, 0 ≤ t → ∀ y z : ℝ,
        ∀ l r M : ℕ, 1 ≤ l + r → 1 ≤ M →
          kernelMarkedFullDens (Icc α (α + w)) ν f 1 a t l r y z *
            krDens (Icc α (α + w)) ν f 1 a M z y ≤
            if a ≤ 1 / 2 then
              (D * Real.exp θ / a) ^ 2 *
                Real.exp (ζ * t - c * ((l : ℝ) + r + M) / a)
            else
              ((D / a) * (1 + 3 * Real.sqrt (2 * D * w))) ^ 2 *
                Real.exp (-(k * (((l : ℝ) + r + M) - 8) / (4 * w ^ 2))) := by
  obtain ⟨k, hk, hspec⟩ := kernel_regLaw_full_marked_pair_spectral D θ vlo vhi (1 / 2)
    hD hθ hvlo hv (by norm_num)
  refine ⟨k, hk, ?_⟩
  intro ζ hζ
  obtain ⟨lam, hlam, hlζ, hlθ, _, hrate⟩ :=
    kernel_regLaw_arbitrary_small_tilt D θ vlo vhi ζ hθ hvlo hv hζ
  refine ⟨lam / 4, by positivity, ?_⟩
  intro ν hν
  obtain ⟨f, hf, hf0, hfD, hfz, hfe, hνf, htilt⟩ := kernel_regLaw_full_marked_pair_tilt D θ vlo vhi hθ hvlo ν hν
  refine ⟨f, hf, hf0, hfD, hfz, hfe, hνf, ?_⟩
  intro α w a hw ha t ht y z l r M hlr hM
  by_cases halo : a ≤ 1 / 2
  · rw [if_pos halo]
    have hh := htilt lam (by rwa [abs_of_pos hlam]) (Icc α (α + w)) measurableSet_Icc
      (by simp) a ha t y z l r M hM
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    have hN : 0 ≤ (l : ℝ) + r + M := by positivity
    have hrate' := mul_le_mul_of_nonneg_left (hrate ν hν a ha halo) hN
    have hinput := mul_le_mul_of_nonneg_right hlζ ht
    have hdiv : 0 ≤ lam / a := by positivity
    have he : ((l : ℝ) + r + M) * (lam / (4 * a)) =
        lam / 4 * ((l : ℝ) + r + M) / a := by ring
    rw [he] at hrate'
    linarith
  · rw [if_neg halo]
    have hh := hspec ν hν f hf hf0 hfD hνf α w 1 a hw
      (by rw [abs_of_pos ha]; linarith) t y z l r M hlr hM
    have he : D * w / (1 / 2) = 2 * D * w := by ring
    simpa only [abs_of_pos ha, he] using hh

end
end PGM
