import PLAStochastic.Affine.Process.IntervalExit.SideLaw

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- A real time density on the strictly positive half-line. -/
def positiveTimeDensity (f : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => ENNReal.ofReal (f t))

theorem positiveTimeDensity_ae_pos (f : ℝ → ℝ) : ∀ᵐ t ∂positiveTimeDensity f, 0 < t :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

theorem integral_positiveTimeDensity {f : ℝ → ℝ} (hf : Measurable f)
    (hn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ f t) (g : ℝ → ℝ) :
    (∫ t, g t ∂positiveTimeDensity f) = ∫ t in Ioi (0 : ℝ), f t*g t := by
  unfold positiveTimeDensity
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.toReal_ofReal (hn t ht),smul_eq_mul]

theorem integrable_positiveTimeDensity_iff {f g : ℝ → ℝ} (hf : Measurable f)
    (hn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ f t) :
    Integrable g (positiveTimeDensity f) ↔ IntegrableOn (fun t => f t*g t) (Ioi 0) := by
  unfold positiveTimeDensity
  rw [integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.toReal_ofReal (hn t ht),smul_eq_mul]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

private theorem intervalExitSideMeasure_eq_density_of_laplace (hB : IsBrownianReal B μ)
    {r x side : ℝ} (hr : 0 < r) {f : ℝ → ℝ} (hf : Measurable f)
    (hn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ f t)
    (hi : ∀ k : ℝ, 0 < k → IntegrableOn (fun t => Real.exp (-(k^2/2)*t)*f t) (Ioi 0))
    (he : ∀ k : ℝ, 0 < k →
      (∫ t, Real.exp (-(k^2/2)*t) ∂intervalExitSideMeasure B μ x r side) =
        ∫ t in Ioi (0 : ℝ), Real.exp (-(k^2/2)*t)*f t) :
    intervalExitSideMeasure B μ x r side = positiveTimeDensity f := by
  apply measure_eq_of_positive_laplace (intervalExitSideMeasure_ae_nonneg hB hr x side)
    ((positiveTimeDensity_ae_pos f).mono (fun _ ht => ht.le))
  · intro lam hlam
    exact integrable_intervalExitSideMeasure_exp hB hr hlam.le x side
  · intro lam hlam
    apply (integrable_positiveTimeDensity_iff hf hn).mpr
    have hk : 0 < Real.sqrt (2*lam) := Real.sqrt_pos.mpr (by positivity)
    have h := hi _ hk
    rw [Real.sq_sqrt (by positivity),mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at h
    simpa only [mul_comm] using h
  · intro lam hlam
    have hk : 0 < Real.sqrt (2*lam) := Real.sqrt_pos.mpr (by positivity)
    have h := he _ hk
    rw [Real.sq_sqrt (by positivity),mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at h
    rw [integral_positiveTimeDensity hf hn]
    simpa only [mul_comm] using h

/-- The left first-exit time density of the actual Brownian motion is A0/2. -/
theorem intervalExitSideMeasure_left_eq_density (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) :
    intervalExitSideMeasure B μ x r 0 = positiveTimeDensity (fun t => heatBoundaryLeft r t x/2) := by
  apply intervalExitSideMeasure_eq_density_of_laplace hB hr
  · exact ((measurable_heatBoundaryLeft r).comp (f := fun t : ℝ => (x,t)) (by fun_prop)).div_const 2
  · intro t ht
    exact div_nonneg (heatBoundaryLeft_strictlyPositive hr ht hx).le (by norm_num)
  · intro k hk
    unfold IntegrableOn
    convert! (integrableOn_laplace_heatBoundaryLeft hr hk hx).div_const 2 using 1
    funext t
    ring
  · intro k hk
    rw [integral_intervalExitSideMeasure_left_laplace hB hr hx hk]
    have he (t : ℝ) : Real.exp (-(k^2/2)*t)*(heatBoundaryLeft r t x/2) =
        (Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t x)/2 := by ring
    simp only [he]
    rw [integral_div,integral_laplace_heatBoundaryLeft_eq_sinh hr hk hx]
    ring

/-- The right first-exit time density of the actual Brownian motion is Ar/2. -/
theorem intervalExitSideMeasure_right_eq_density (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) :
    intervalExitSideMeasure B μ x r r = positiveTimeDensity (fun t => heatBoundaryRight r t x/2) := by
  apply intervalExitSideMeasure_eq_density_of_laplace hB hr
  · exact ((measurable_heatBoundaryRight r).comp (f := fun t : ℝ => (x,t)) (by fun_prop)).div_const 2
  · intro t ht
    exact div_nonneg (heatBoundaryRight_strictlyPositive hr ht hx).le (by norm_num)
  · intro k hk
    unfold IntegrableOn
    convert! (integrableOn_laplace_heatBoundaryRight hr hk hx).div_const 2 using 1
    funext t
    ring
  · intro k hk
    rw [integral_intervalExitSideMeasure_right_laplace hB hr hx hk]
    have he (t : ℝ) : Real.exp (-(k^2/2)*t)*(heatBoundaryRight r t x/2) =
        (Real.exp (-(k^2/2)*t)*heatBoundaryRight r t x)/2 := by ring
    simp only [he]
    rw [integral_div,integral_laplace_heatBoundaryRight_eq_sinh hr hk hx]
    ring

end BrownianAffine
