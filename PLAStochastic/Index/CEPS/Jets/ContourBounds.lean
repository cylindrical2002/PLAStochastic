import PLAStochastic.Index.CEPS.Jets.Reference
import PLAStochastic.Index.CEPS.Jets.Integrand
import PLAStochastic.Index.CEPS.Jets.Transform
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# X8: the contour-jet integrands near the reference transform

On the jet line `s = c + iy` (`c = cepsJetLine`) write `M^Λ(s)` for the reference transform.

* `norm_cepsJetTransform_ref_le`: `M^Λ` is bounded on the jet line;
* `cepsContour_integrand_data`: there is `ρ > 0` such that, for every `y`, the integrand
  `w ↦ G_{j,m,n}(s, w)` is holomorphic on the ball `‖w - M^Λ(s)‖ < 2ρ`, is jointly continuous in
  `(y, w)` there, oscillates on that ball by at most `C (1 + ‖s‖)^j`, and the base integrand
  `y ↦ G_{j,m,n}(s, M^Λ(s))` is integrable.

On the ball, `‖1 - w‖` stays bounded below and `F̃(s, w)` stays in a compact part of the right
half-plane, since `F̃(s, w) - F̃(s, M^Λ) = (M^Λ - w)(s² - 1)/s²` and `‖(s² - 1)/s²‖ ≤ 1 + 1/c²`.
Integrability uses the Sobolev decay of `M^Λ` and, for the logarithm, `‖log z‖ ≤ L ‖z - 1‖`.
-/

noncomputable section

open MeasureTheory Complex

namespace PGM

/-! ### The jet line -/

private theorem re_jetLinePt (y : ℝ) : ((cepsJetLine : ℂ) + y * I).re = cepsJetLine := by simp

private theorem im_jetLinePt (y : ℝ) : ((cepsJetLine : ℂ) + y * I).im = y := by simp

private theorem le_norm_jetLinePt (y : ℝ) : cepsJetLine ≤ ‖(cepsJetLine : ℂ) + y * I‖ := by
  have h := Complex.re_le_norm ((cepsJetLine : ℂ) + y * I)
  rwa [re_jetLinePt] at h

private theorem jetLinePt_ne_zero (y : ℝ) : (cepsJetLine : ℂ) + y * I ≠ 0 := by
  intro h
  have h' := re_jetLinePt y
  rw [h, zero_re] at h'
  exact cepsJetLine_pos.ne h'

private theorem one_add_sq_le_jetLinePt (y : ℝ) :
    1 + y ^ 2 ≤ (1 + ‖(cepsJetLine : ℂ) + y * I‖) ^ 2 := by
  have h1 : |y| ≤ ‖(cepsJetLine : ℂ) + y * I‖ := by
    have h := Complex.abs_im_le_norm ((cepsJetLine : ℂ) + y * I)
    rwa [im_jetLinePt] at h
  have h2 : y ^ 2 ≤ ‖(cepsJetLine : ℂ) + y * I‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg y) h1 2
  nlinarith [norm_nonneg ((cepsJetLine : ℂ) + y * I)]

private theorem norm_sq_jetLinePt (y : ℝ) :
    ‖(cepsJetLine : ℂ) + y * I‖ ^ 2 = cepsJetLine ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]

/-- `‖(s² - 1)/s²‖ ≤ 1 + 1/c²` on the jet line. -/
private theorem norm_jetLinePt_ratio_le (y : ℝ) :
    ‖(((cepsJetLine : ℂ) + y * I) ^ 2 - 1) / ((cepsJetLine : ℂ) + y * I) ^ 2‖ ≤
      1 + 1 / cepsJetLine ^ 2 := by
  have hs0 := jetLinePt_ne_zero y
  have hc := cepsJetLine_pos
  have e : (((cepsJetLine : ℂ) + y * I) ^ 2 - 1) / ((cepsJetLine : ℂ) + y * I) ^ 2 =
      1 - 1 / ((cepsJetLine : ℂ) + y * I) ^ 2 := by
    field_simp
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, norm_div, norm_one, norm_pow]
  exact add_le_add le_rfl (one_div_le_one_div_of_le (pow_pos hc 2)
    (pow_le_pow_left₀ hc.le (le_norm_jetLinePt y) 2))

/-! ### The reference transform on the jet line -/

private theorem cepsLambdaDensity_eq_zero_of_neg : ∀ x : ℝ, x < 0 → cepsLambdaDensity x = 0 :=
  fun _ hx => cepsLambdaDensity_of_nonpos hx.le

/-- `(1 + ‖s‖)^N ‖M^Λ(s)‖` is bounded on the jet line. -/
private theorem cepsJetRef_decay (N : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ y : ℝ,
    (1 + ‖(cepsJetLine : ℂ) + y * I‖) ^ N *
      ‖cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖ ≤ A := by
  obtain ⟨η, hη, hφ⟩ := exists_cepsSobolevClass_cepsLambdaDensity N
  refine ⟨2 ^ N * Real.exp cepsJetLine * cepsSobolev N η cepsLambdaDensity,
    mul_nonneg (by positivity) (cepsSobolev_nonneg _ _ _), fun y => ?_⟩
  have h := norm_cepsJetTransform_le_sobolev hφ hη.le cepsLambdaDensity_eq_zero_of_neg
    (s := (cepsJetLine : ℂ) + y * I) (by rw [re_jetLinePt]; exact cepsJetLine_pos.le)
  rwa [re_jetLinePt] at h

/-- The reference transform is bounded on the jet line. -/
theorem norm_cepsJetTransform_ref_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ,
    ‖cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖ ≤ K := by
  obtain ⟨A, hA, h⟩ := cepsJetRef_decay 0
  refine ⟨A, hA, fun y => ?_⟩
  have h' := h y
  rwa [pow_zero, one_mul] at h'

/-- `(1 + ‖s‖)^j ‖M^Λ(s)‖ ≤ A (1 + y²)⁻¹` on the jet line. -/
private theorem cepsJetRef_decay_sq (j : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ y : ℝ,
    (1 + ‖(cepsJetLine : ℂ) + y * I‖) ^ j *
      ‖cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖ ≤ A * (1 + y ^ 2)⁻¹ := by
  obtain ⟨A, hA, h⟩ := cepsJetRef_decay (j + 2)
  refine ⟨A, hA, fun y => ?_⟩
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hT := one_add_sq_le_jetLinePt y
  have hM := norm_nonneg (cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I))
  have ht : 0 ≤ 1 + ‖(cepsJetLine : ℂ) + y * I‖ := by positivity
  calc (1 + ‖(cepsJetLine : ℂ) + y * I‖) ^ j *
        ‖cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖ * (1 + y ^ 2)
      ≤ (1 + ‖(cepsJetLine : ℂ) + y * I‖) ^ j *
        ‖cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖ *
          (1 + ‖(cepsJetLine : ℂ) + y * I‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hT (mul_nonneg (pow_nonneg ht j) hM)
    _ = (1 + ‖(cepsJetLine : ℂ) + y * I‖) ^ (j + 2) *
        ‖cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖ := by ring
    _ ≤ A := h y

private theorem continuous_cepsJetRef :
    Continuous fun y : ℝ => cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I) := by
  obtain ⟨η, hη, hφ⟩ := exists_cepsSobolevClass_cepsLambdaDensity 0
  have hf : Integrable cepsLambdaDensity := by
    simpa using hφ.integrable_iteratedDeriv hη.le (le_refl 0)
  refine (continuousOn_cepsJetTransform hf cepsLambdaDensity_eq_zero_of_neg).comp_continuous
    (f := fun y : ℝ => (cepsJetLine : ℂ) + y * I) (by fun_prop) fun y => ?_
  show 0 ≤ ((cepsJetLine : ℂ) + y * I).re
  rw [re_jetLinePt]
  exact cepsJetLine_pos.le

/-! ### A neighbourhood of the reference transform -/

/-- On the balls `‖w - M^Λ(s)‖ < 2ρ` along the jet line, `‖1 - w‖` is bounded below, `w` is
bounded, and `F̃(s, w)` lies in `{Re ≥ d} ∩ {‖·‖ ≤ C₁}` with `d > 0`. -/
private theorem cepsContour_ball : ∃ ρ δ K d C₁ : ℝ, 0 < ρ ∧ 0 < δ ∧ 0 < d ∧
    ∀ y : ℝ, ∀ w : ℂ,
      ‖w - cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖ < 2 * ρ →
      δ ≤ ‖1 - w‖ ∧ ‖w‖ ≤ K ∧ d ≤ (cepsJetF (cepsJetLine + y * I) w).re ∧
        ‖cepsJetF (cepsJetLine + y * I) w‖ ≤ C₁ := by
  obtain ⟨K, -, hK⟩ := norm_cepsJetTransform_ref_le
  have hc := cepsJetLine_pos
  have hδ : 0 < min cepsRef.dom.g (cepsVarLo cepsRef.D * (cepsJetLine / 2) ^ 2 / 32) :=
    lt_min cepsRef.dom.g_pos (by have := cepsVarLo_pos cepsRef.hD; positivity)
  have hd₀ : 0 < cepsRef.dom.d₀ := cepsRef.dom.d₀_pos cepsRef.hD
  have hB : 0 < 1 + 1 / cepsJetLine ^ 2 := by positivity
  set δ := min cepsRef.dom.g (cepsVarLo cepsRef.D * (cepsJetLine / 2) ^ 2 / 32) with hδdef
  set B := 1 + 1 / cepsJetLine ^ 2 with hBdef
  set ρ := min (δ / 4) (cepsRef.dom.d₀ / (4 * B)) with hρdef
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρ1 : ρ ≤ δ / 4 := min_le_left _ _
  have hρ2 : ρ ≤ cepsRef.dom.d₀ / (4 * B) := min_le_right _ _
  refine ⟨ρ, δ / 2, K + 2 * ρ, cepsRef.dom.d₀ / 2, cepsRef.dom.CF + cepsRef.dom.d₀ / 2, hρ,
    by positivity, by positivity, fun y w hw => ?_⟩
  obtain ⟨h1, h2, h3⟩ := cepsRef_line_bounds y
  have hR := norm_jetLinePt_ratio_le y
  have hKy := hK y
  set s : ℂ := (cepsJetLine : ℂ) + y * I with hs
  set M := cepsJetTransform cepsLambdaDensity s with hM
  have hdiff : cepsJetF s w - cepsJetF s M = (M - w) * ((s ^ 2 - 1) / s ^ 2) := by
    unfold cepsJetF
    ring
  have hFd : ‖cepsJetF s w - cepsJetF s M‖ ≤ cepsRef.dom.d₀ / 2 := by
    rw [hdiff, norm_mul, norm_sub_rev]
    calc ‖w - M‖ * ‖(s ^ 2 - 1) / s ^ 2‖ ≤ (2 * ρ) * B :=
          mul_le_mul hw.le hR (norm_nonneg _) (by positivity)
      _ ≤ 2 * (cepsRef.dom.d₀ / (4 * B)) * B := by gcongr
      _ = cepsRef.dom.d₀ / 2 := by field_simp; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := norm_sub_le_norm_sub_add_norm_sub (1 : ℂ) w M
    linarith
  · have := norm_sub_norm_le w M
    linarith
  · have h := Complex.abs_re_le_norm (cepsJetF s w - cepsJetF s M)
    rw [sub_re] at h
    have := neg_abs_le ((cepsJetF s w).re - (cepsJetF s M).re)
    linarith
  · have := norm_sub_norm_le (cepsJetF s w) (cepsJetF s M)
    linarith

/-! ### Assembly -/

/-- `‖log z‖ ≤ (3/2 + 2(|log d| + |log C| + π)) ‖z - 1‖` for `d ≤ Re z`, `‖z‖ ≤ C`, `d > 0`. -/
private theorem norm_clog_le_mul_norm_sub_one_aux {z : ℂ} {d C : ℝ} (hd : 0 < d)
    (h1 : d ≤ z.re) (h2 : ‖z‖ ≤ C) :
    ‖Complex.log z‖ ≤ (3 / 2 + 2 * (|Real.log d| + |Real.log C| + Real.pi)) * ‖z - 1‖ := by
  have hΛ : 0 ≤ |Real.log d| + |Real.log C| + Real.pi := by positivity
  have hz := norm_nonneg (z - 1)
  by_cases h : ‖z - 1‖ ≤ 1 / 2
  · have h' := Complex.norm_log_one_add_half_le_self h
    have e : (1 : ℂ) + (z - 1) = z := by ring
    rw [e] at h'
    nlinarith
  · have h : 1 / 2 < ‖z - 1‖ := not_le.mp h
    have h' := norm_log_le_of_re_ge hd h1 h2
    nlinarith

/-- Pointwise holomorphy, joint continuity, a sup bound on the balls and a decaying base bound
give the conclusions of `cepsContour_integrand_data`. -/
private theorem contour_data_of_bounds {S M : ℝ → ℂ} {G : ℂ → ℂ → ℂ} {ρ C₀ A : ℝ} {j : ℕ}
    (hdiff : ∀ y w, ‖w - M y‖ < 2 * ρ → DifferentiableAt ℂ (G (S y)) w)
    (hcont : ∀ p : ℝ × ℂ, ‖p.2 - M p.1‖ < 2 * ρ →
      ContinuousAt (fun p : ℝ × ℂ => G (S p.1) p.2) p)
    (hsup : ∀ y w, ‖w - M y‖ < 2 * ρ → ‖G (S y) w‖ ≤ C₀ * (1 + ‖S y‖) ^ j)
    (hbase : ∀ y, ‖G (S y) (M y)‖ ≤ A * (1 + y ^ 2)⁻¹) (hρ : 0 < ρ) (hM : Continuous M) :
    (∀ y : ℝ, DifferentiableOn ℂ (G (S y)) (Metric.ball (M y) (2 * ρ))) ∧
      ContinuousOn (fun p : ℝ × ℂ => G (S p.1) p.2) {p | ‖p.2 - M p.1‖ < 2 * ρ} ∧
      (∀ y : ℝ, ∀ w ∈ Metric.ball (M y) (2 * ρ),
        ‖G (S y) w - G (S y) (M y)‖ ≤ 2 * C₀ * (1 + ‖S y‖) ^ j) ∧
      Integrable (fun y => G (S y) (M y)) := by
  have hself : ∀ y, ‖M y - M y‖ < 2 * ρ := fun y => by rw [sub_self, norm_zero]; positivity
  refine ⟨fun y w hw => (hdiff y w ?_).differentiableWithinAt,
    fun p hp => (hcont p hp).continuousWithinAt, fun y w hw => ?_, ?_⟩
  · rwa [Metric.mem_ball, dist_eq_norm] at hw
  · rw [Metric.mem_ball, dist_eq_norm] at hw
    calc ‖G (S y) w - G (S y) (M y)‖ ≤ ‖G (S y) w‖ + ‖G (S y) (M y)‖ := norm_sub_le _ _
      _ ≤ C₀ * (1 + ‖S y‖) ^ j + C₀ * (1 + ‖S y‖) ^ j :=
          add_le_add (hsup y w hw) (hsup y _ (hself y))
      _ = 2 * C₀ * (1 + ‖S y‖) ^ j := by ring
  · have hc : Continuous fun y => G (S y) (M y) :=
      ContinuousOn.comp_continuous (s := {p : ℝ × ℂ | ‖p.2 - M p.1‖ < 2 * ρ})
        (g := fun p : ℝ × ℂ => G (S p.1) p.2)
        (fun p hp => (hcont p hp).continuousWithinAt) (continuous_id.prodMk hM)
        fun y => hself y
    exact (integrable_inv_one_add_sq.const_mul A).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall hbase)

/-! ### The contour-jet integrands -/

/-- **Contour-jet integrands near the reference transform.** For some `ρ > 0` and `C ≥ 0`: the
reference transform is continuous along the jet line; `G_{j,m,n}(s, ·)` is holomorphic on the
ball of radius `2ρ` about `M^Λ(s)`; `G_{j,m,n}(c + iy, w)` is jointly continuous on the union of
these balls; it moves by at most `C (1 + ‖s‖)^j` on each ball; and the base integrand
`y ↦ G_{j,m,n}(s, M^Λ(s))` is integrable. -/
theorem cepsContour_integrand_data (j m n : ℕ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      Continuous (fun y : ℝ => cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)) ∧
      (∀ y : ℝ, DifferentiableOn ℂ (fun w => cepsJetIntegrand j m n (cepsJetLine + y * I) w)
        (Metric.ball (cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)) (2 * ρ))) ∧
      ContinuousOn (fun p : ℝ × ℂ => cepsJetIntegrand j m n (cepsJetLine + p.1 * I) p.2)
        {p | ‖p.2 - cepsJetTransform cepsLambdaDensity (cepsJetLine + p.1 * I)‖ < 2 * ρ} ∧
      (∀ y : ℝ, ∀ w ∈ Metric.ball (cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I))
          (2 * ρ),
        ‖cepsJetIntegrand j m n (cepsJetLine + y * I) w -
          cepsJetIntegrand j m n (cepsJetLine + y * I)
            (cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I))‖ ≤
          C * (1 + ‖(cepsJetLine : ℂ) + y * I‖) ^ j) ∧
      MeasureTheory.Integrable (fun y : ℝ => cepsJetIntegrand j m n (cepsJetLine + y * I)
        (cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I))) := by
  obtain ⟨ρ, δ, K, d, C₁, hρ, hδ, hd, hball⟩ := cepsContour_ball
  have hc := cepsJetLine_pos
  have hcm : 0 < cepsJetLine ^ (m + 1) := pow_pos hc _
  have hdiv : ∀ (y : ℝ) (a : ℂ) (A : ℝ), ‖a‖ ≤ A →
      ‖a / ((cepsJetLine : ℂ) + y * I) ^ (m + 1)‖ ≤ A / cepsJetLine ^ (m + 1) := by
    intro y a A ha
    rw [norm_div, norm_pow]
    exact div_le_div₀ ((norm_nonneg a).trans ha) ha hcm
      (pow_le_pow_left₀ hc.le (le_norm_jetLinePt y) _)
  have hself : ∀ y : ℝ,
      ‖cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I) -
        cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖ < 2 * ρ :=
    fun y => by rw [sub_self, norm_zero]; positivity
  have hsC : Continuous fun p : ℝ × ℂ => (cepsJetLine : ℂ) + p.1 * I := by fun_prop
  have key : ∃ C₀ A : ℝ, 0 ≤ C₀ ∧
      (∀ y : ℝ, ∀ w : ℂ,
        ‖w - cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖ < 2 * ρ →
        DifferentiableAt ℂ (cepsJetIntegrand j m n (cepsJetLine + y * I)) w) ∧
      (∀ p : ℝ × ℂ,
        ‖p.2 - cepsJetTransform cepsLambdaDensity (cepsJetLine + p.1 * I)‖ < 2 * ρ →
        ContinuousAt (fun p : ℝ × ℂ => cepsJetIntegrand j m n (cepsJetLine + p.1 * I) p.2) p) ∧
      (∀ y : ℝ, ∀ w : ℂ,
        ‖w - cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖ < 2 * ρ →
        ‖cepsJetIntegrand j m n (cepsJetLine + y * I) w‖ ≤
          C₀ * (1 + ‖(cepsJetLine : ℂ) + y * I‖) ^ j) ∧
      (∀ y : ℝ, ‖cepsJetIntegrand j m n (cepsJetLine + y * I)
          (cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I))‖ ≤ A * (1 + y ^ 2)⁻¹) := by
    by_cases hjn : j + n = 0
    · -- the logarithmic integrand `log F̃(s, w)/s^{m+1}`
      obtain rfl : j = 0 := by omega
      have hG : ∀ s w : ℂ,
          cepsJetIntegrand 0 m n s w = Complex.log (cepsJetF s w) / s ^ (m + 1) :=
        fun s w => if_pos hjn
      have hslit : ∀ (y : ℝ) (w : ℂ),
          ‖w - cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖ < 2 * ρ →
          cepsJetF (cepsJetLine + y * I) w ∈ slitPlane := fun y w hw =>
        mem_slitPlane_iff.mpr (Or.inl (hd.trans_le (hball y w hw).2.2.1))
      have hΛ : 0 ≤ |Real.log d| + |Real.log C₁| + Real.pi := by positivity
      have hL : 0 ≤ 3 / 2 + 2 * (|Real.log d| + |Real.log C₁| + Real.pi) := by positivity
      obtain ⟨A₂, hA₂, hdec⟩ := cepsJetRef_decay_sq 0
      refine ⟨(|Real.log d| + |Real.log C₁| + Real.pi) / cepsJetLine ^ (m + 1),
        (3 / 2 + 2 * (|Real.log d| + |Real.log C₁| + Real.pi)) *
          ((1 + 1 / cepsJetLine ^ 2) * A₂ + 1 / cepsJetLine ^ 2) / cepsJetLine ^ (m + 1),
        div_nonneg hΛ hcm.le, ?_, ?_, ?_, ?_⟩
      · intro y w hw
        have e : cepsJetIntegrand 0 m n (cepsJetLine + y * I) = fun w =>
            Complex.log (cepsJetF (cepsJetLine + y * I) w) /
              ((cepsJetLine : ℂ) + y * I) ^ (m + 1) := funext (hG _)
        rw [e]
        have hF : DifferentiableAt ℂ (fun w => cepsJetF (cepsJetLine + y * I) w) w := by
          unfold cepsJetF
          fun_prop
        exact (hF.clog (hslit y w hw)).div_const _
      · intro p hp
        have e : (fun p : ℝ × ℂ => cepsJetIntegrand 0 m n (cepsJetLine + p.1 * I) p.2) =
            fun p : ℝ × ℂ => Complex.log (cepsJetF (cepsJetLine + p.1 * I) p.2) /
              ((cepsJetLine : ℂ) + p.1 * I) ^ (m + 1) := funext fun p => hG _ _
        rw [e]
        have hF : ContinuousAt (fun p : ℝ × ℂ => cepsJetF (cepsJetLine + p.1 * I) p.2) p := by
          unfold cepsJetF
          exact ((continuous_const.sub continuous_snd).mul
            ((hsC.pow 2).sub continuous_const)).continuousAt.div (hsC.pow 2).continuousAt
            (pow_ne_zero 2 (jetLinePt_ne_zero p.1))
        exact (hF.clog (hslit p.1 p.2 hp)).div (hsC.pow (m + 1)).continuousAt
          (pow_ne_zero _ (jetLinePt_ne_zero p.1))
      · intro y w hw
        obtain ⟨-, -, hre, hnorm⟩ := hball y w hw
        rw [hG, pow_zero, mul_one]
        exact hdiv y _ _ (norm_log_le_of_re_ge hd hre hnorm)
      · intro y
        obtain ⟨-, -, hre, hnorm⟩ := hball y _ (hself y)
        have hlog := norm_clog_le_mul_norm_sub_one_aux hd hre hnorm
        have hR := norm_jetLinePt_ratio_le y
        have hdec' := hdec y
        rw [pow_zero, one_mul] at hdec'
        have hs2n := norm_sq_jetLinePt y
        have hs0 := jetLinePt_ne_zero y
        have hc2 : cepsJetLine ^ 2 ≤ 1 := pow_le_one₀ hc.le cepsJetLine_le_one
        rw [hG]
        set s : ℂ := (cepsJetLine : ℂ) + y * I with hs
        set M := cepsJetTransform cepsLambdaDensity s with hM
        have hF1 : cepsJetF s M - 1 = -(M * ((s ^ 2 - 1) / s ^ 2)) - 1 / s ^ 2 := by
          unfold cepsJetF
          field_simp
          ring
        have hs2 : 1 / ‖s‖ ^ 2 ≤ 1 / cepsJetLine ^ 2 * (1 + y ^ 2)⁻¹ := by
          rw [hs2n, ← one_div, div_mul_div_comm, one_mul,
            one_div_le_one_div (add_pos_of_pos_of_nonneg (pow_pos hc 2) (sq_nonneg y))
              (mul_pos (pow_pos hc 2) (by positivity))]
          nlinarith [mul_le_mul_of_nonneg_right hc2 (sq_nonneg y)]
        have hF1n : ‖cepsJetF s M - 1‖ ≤
            ((1 + 1 / cepsJetLine ^ 2) * A₂ + 1 / cepsJetLine ^ 2) * (1 + y ^ 2)⁻¹ := by
          rw [hF1]
          calc ‖-(M * ((s ^ 2 - 1) / s ^ 2)) - 1 / s ^ 2‖
              ≤ ‖M‖ * ‖(s ^ 2 - 1) / s ^ 2‖ + 1 / ‖s‖ ^ 2 := by
                refine (norm_sub_le _ _).trans (le_of_eq ?_)
                rw [norm_neg, norm_mul, norm_div (1 : ℂ) (s ^ 2), norm_one, norm_pow]
            _ ≤ A₂ * (1 + y ^ 2)⁻¹ * (1 + 1 / cepsJetLine ^ 2) +
                1 / cepsJetLine ^ 2 * (1 + y ^ 2)⁻¹ :=
                add_le_add (mul_le_mul hdec' hR (norm_nonneg _) (by positivity)) hs2
            _ = _ := by ring
        refine (hdiv y _ ((3 / 2 + 2 * (|Real.log d| + |Real.log C₁| + Real.pi)) *
          (((1 + 1 / cepsJetLine ^ 2) * A₂ + 1 / cepsJetLine ^ 2) * (1 + y ^ 2)⁻¹))
          (hlog.trans (mul_le_mul_of_nonneg_left hF1n hL))).trans_eq ?_
        ring
    · -- the rational integrands `s^j (-1)^n D_{j+n}(w)/s^{m+1}`
      have hG : ∀ s w : ℂ, cepsJetIntegrand j m n s w =
          s ^ j * (-1) ^ n * cepsLogDJet (j + n - 1) w / s ^ (m + 1) :=
        fun s w => if_neg hjn
      have hne : ∀ (y : ℝ) (w : ℂ),
          ‖w - cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖ < 2 * ρ → w ≠ 1 := by
        intro y w hw e
        have h := (hball y w hw).1
        rw [e, sub_self, norm_zero] at h
        linarith
      obtain ⟨CD, hCD0, hCD⟩ := norm_cepsLogDJet_le (j + n - 1) (K := K) hδ
      obtain ⟨Aj, hAj, hdec⟩ := cepsJetRef_decay_sq j
      have hK0 : 0 ≤ K := (norm_nonneg _).trans (hball 0 _ (hself 0)).2.1
      refine ⟨CD * K / cepsJetLine ^ (m + 1), CD * Aj / cepsJetLine ^ (m + 1),
        div_nonneg (mul_nonneg hCD0 hK0) hcm.le, ?_, ?_, ?_, ?_⟩
      · intro y w hw
        have e : cepsJetIntegrand j m n (cepsJetLine + y * I) = fun w =>
            ((cepsJetLine : ℂ) + y * I) ^ j * (-1) ^ n * cepsLogDJet (j + n - 1) w /
              ((cepsJetLine : ℂ) + y * I) ^ (m + 1) := funext (hG _)
        rw [e]
        exact ((differentiableAt_cepsLogDJet _ (hne y w hw)).const_mul _).div_const _
      · intro p hp
        have e : (fun p : ℝ × ℂ => cepsJetIntegrand j m n (cepsJetLine + p.1 * I) p.2) =
            fun p : ℝ × ℂ => ((cepsJetLine : ℂ) + p.1 * I) ^ j * (-1) ^ n *
              cepsLogDJet (j + n - 1) p.2 / ((cepsJetLine : ℂ) + p.1 * I) ^ (m + 1) :=
          funext fun p => hG _ _
        rw [e]
        have hD : ContinuousAt (fun p : ℝ × ℂ => cepsLogDJet (j + n - 1) p.2) p :=
          (differentiableAt_cepsLogDJet _ (hne p.1 p.2 hp)).continuousAt.comp
            (f := Prod.snd) continuous_snd.continuousAt
        exact (((hsC.pow j).continuousAt.mul continuousAt_const).mul hD).div
          (hsC.pow (m + 1)).continuousAt (pow_ne_zero _ (jetLinePt_ne_zero p.1))
      · intro y w hw
        obtain ⟨h1, h2, -, -⟩ := hball y w hw
        have hn : 0 ≤ ‖(cepsJetLine : ℂ) + y * I‖ := norm_nonneg _
        rw [hG]
        refine (hdiv y _ ((1 + ‖(cepsJetLine : ℂ) + y * I‖) ^ j * (CD * K)) ?_).trans_eq
          (by ring)
        rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, mul_one]
        exact mul_le_mul (pow_le_pow_left₀ hn (by linarith) j)
          ((hCD w h2 h1).trans (mul_le_mul_of_nonneg_left h2 hCD0)) (norm_nonneg _)
          (by positivity)
      · intro y
        obtain ⟨h1, h2, -, -⟩ := hball y _ (hself y)
        have hn : 0 ≤ ‖(cepsJetLine : ℂ) + y * I‖ := norm_nonneg _
        rw [hG]
        refine (hdiv y _ (CD * (Aj * (1 + y ^ 2)⁻¹)) ?_).trans_eq (by ring)
        rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, mul_one]
        calc ‖(cepsJetLine : ℂ) + y * I‖ ^ j *
              ‖cepsLogDJet (j + n - 1) (cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I))‖
            ≤ ‖(cepsJetLine : ℂ) + y * I‖ ^ j *
              (CD * ‖cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖) :=
              mul_le_mul_of_nonneg_left (hCD _ h2 h1) (by positivity)
          _ ≤ (1 + ‖(cepsJetLine : ℂ) + y * I‖) ^ j *
              (CD * ‖cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖) :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hn (by linarith) j) (by positivity)
          _ = CD * ((1 + ‖(cepsJetLine : ℂ) + y * I‖) ^ j *
              ‖cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖) := by ring
          _ ≤ CD * (Aj * (1 + y ^ 2)⁻¹) := mul_le_mul_of_nonneg_left (hdec y) hCD0
  obtain ⟨C₀, A, hC₀, hdiff, hcont, hsup, hbase⟩ := key
  obtain ⟨h1, h2, h3, h4⟩ := contour_data_of_bounds
    (S := fun y : ℝ => (cepsJetLine : ℂ) + y * I)
    (M := fun y : ℝ => cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I))
    (G := cepsJetIntegrand j m n) hdiff hcont hsup hbase hρ continuous_cepsJetRef
  exact ⟨ρ, 2 * C₀, hρ, by positivity, continuous_cepsJetRef, h1, h2, h3, h4⟩

end PGM
