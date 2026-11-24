import PLAStochastic.Index.GEP.PointwiseSmall.ThreeBumpDirections

/-!
# WP4 leaf `PointwiseSmall`: a.e. quadratic from the three-bump directions

If the response of a locally bounded kernel `J` to every pair of direction laws
`SigmaLaw (1 + e^{7θσ/2}) θσ` of equal variance is at most `δ`, then `J` is a.e. a quadratic
polynomial up to `δ / c(x)`, `c = pwC3 θσ` (`pw_quadratic_of_pair`): the three-bump directions
`pw_exists_sigmaTriple` give, for the averages `i_j` of `J` over the fixed bumps,
`|⨍_{[x-h,x+h]} J - ∑ w_j(x, x² + h²/3) i_j| ≤ δ/c(x)`, and `h → 0⁺` at Lebesgue points gives the
quadratic `∑ w_j(x, x²) i_j = l₀ + l₁ x + l₂ x²` whose coefficients are bounded by the size of `J`
on `[0, 7/2]`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- **A.e. quadratic from the three-bump directions.** -/
theorem pw_quadratic_of_pair {θσ : ℝ} (hθσ : 0 < θσ) {J : ℝ → ℝ} (hJ : Measurable J) {B κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ y, 0 ≤ y → |J y| ≤ B * Real.exp (κ * y)) {δ : ℝ}
    (hdir : ∀ σp σm : ProbabilityMeasure ℝ, SigmaLaw (1 + Real.exp (θσ * (7 / 2))) θσ σp →
      SigmaLaw (1 + Real.exp (θσ * (7 / 2))) θσ σm → lawVar σp = lawVar σm →
      |∫ y, J y ∂(σp : Measure ℝ) - ∫ y, J y ∂(σm : Measure ℝ)| ≤ δ) :
    ∃ l₀ l₁ l₂ : ℝ, |l₁| + |l₂| ≤ 7 * (|B| * Real.exp (κ * (7 / 2))) ∧
      ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
        |J x - (l₀ + l₁ * x + l₂ * x ^ 2)| ≤ δ / pwC3 θσ x := by
  set i₀ := ⨍ y in Icc (1 / 4 : ℝ) (3 / 4), J y with hi₀
  set i₁ := ⨍ y in Icc (3 / 2 : ℝ) (5 / 2), J y with hi₁
  set i₂ := ⨍ y in Icc (5 / 2 : ℝ) (7 / 2), J y with hi₂
  set l₀ : ℝ := (284 * i₀ - 179 * i₁) / 177 + 24 * i₂ / 59 with hl₀
  set l₁ : ℝ := (-240 * i₀ + 423 * i₁) / 177 - 61 * i₂ / 59 with hl₁
  set l₂ : ℝ := (48 * i₀ - 120 * i₁) / 177 + 24 * i₂ / 59 with hl₂
  set C : ℝ := |B| * Real.exp (κ * (7 / 2)) with hC
  -- the size of the averages
  have hbd : ∀ y ∈ Icc (0 : ℝ) (7 / 2), |J y| ≤ C := by
    intro y hy
    refine (hb y hy.1).trans ?_
    rw [hC]
    calc B * Real.exp (κ * y) ≤ |B| * Real.exp (κ * y) :=
          mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_pos _).le
      _ ≤ |B| * Real.exp (κ * (7 / 2)) := by
          gcongr
          exact hy.2
  have hi₀b : |i₀| ≤ C :=
    pw_abs_average_le (by norm_num) fun y hy => hbd y ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hi₁b : |i₁| ≤ C :=
    pw_abs_average_le (by norm_num) fun y hy => hbd y ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hi₂b : |i₂| ≤ C :=
    pw_abs_average_le (by norm_num) fun y hy => hbd y ⟨by linarith [hy.1], hy.2⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hi₀b
  have hl : |l₁| + |l₂| ≤ 7 * C := by
    obtain ⟨a0, b0⟩ := abs_le.1 hi₀b
    obtain ⟨a1, b1⟩ := abs_le.1 hi₁b
    obtain ⟨a2, b2⟩ := abs_le.1 hi₂b
    have h1 : |l₁| ≤ 5 * C := abs_le.2 ⟨by rw [hl₁]; linarith, by rw [hl₁]; linarith⟩
    have h2 : |l₂| ≤ 2 * C := abs_le.2 ⟨by rw [hl₂]; linarith, by rw [hl₂]; linarith⟩
    linarith
  refine ⟨l₀, l₁, l₂, hl, ?_⟩
  -- the compensation and its limit
  set L : ℝ → ℝ → ℝ := fun x h => pwW0 x (x ^ 2 + h ^ 2 / 3) * i₀ +
    pwW1 x (x ^ 2 + h ^ 2 / 3) * i₁ + pwW2 x (x ^ 2 + h ^ 2 / 3) * i₂ with hL
  have hL0 : ∀ x, L x 0 = l₀ + l₁ * x + l₂ * x ^ 2 := by
    intro x
    simp only [hL, hl₀, hl₁, hl₂, pwW0, pwW1, pwW2]
    ring
  have hLt : ∀ x, 0 < x → Tendsto (fun h => L x h) (𝓝[>] 0) (𝓝 (l₀ + l₁ * x + l₂ * x ^ 2)) := by
    intro x _
    have hc : Continuous fun h : ℝ => L x h := by
      simp only [hL, pwW0, pwW1, pwW2]
      fun_prop
    rw [← hL0 x]
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  -- the averaged bound for small bumps
  have hloc : ∀ x, 0 < x → ∀ h, 0 < h → h < x → h ≤ 1 →
      |(⨍ y in Metric.closedBall x h, J y) - L x h| ≤ δ / pwC3 θσ x := by
    intro x hx h hh hhx hh1
    obtain ⟨σp, σm, hσp, hσm, hvar, hdiff⟩ := pw_exists_sigmaTriple hθσ hx hh hhx hh1
    obtain ⟨-, -, heq⟩ := hdiff J (integrableOn_Icc_of_exp hJ hκ hb (by linarith))
      (integrableOn_Icc_of_exp hJ hκ hb (by norm_num))
      (integrableOn_Icc_of_exp hJ hκ hb (by norm_num))
      (integrableOn_Icc_of_exp hJ hκ hb (by norm_num))
    have h1 := hdir σp σm hσp hσm hvar
    have hc := pwC3_pos θσ hx
    rw [heq, abs_mul, abs_of_pos hc, ← hi₀, ← hi₁, ← hi₂] at h1
    rw [le_div_iff₀ hc]
    have e : (⨍ y in Metric.closedBall x h, J y) - L x h =
        (⨍ y in Metric.closedBall x h, J y) - pwW0 x (x ^ 2 + h ^ 2 / 3) * i₀ -
          pwW1 x (x ^ 2 + h ^ 2 / 3) * i₁ - pwW2 x (x ^ 2 + h ^ 2 / 3) * i₂ := by
      simp only [hL]
      ring
    rw [e, mul_comm]
    exact h1
  exact pw_lebesgue_point hJ hb hLt hloc

end

end PGM
