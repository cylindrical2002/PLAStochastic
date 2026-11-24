import PLAStochastic.Brownian.Killed.Resolvent
import PLAStochastic.Brownian.Killed.GreenFunction

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem integral_heatResolventSeries_mul_sine {r lam : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam)
    (x : ℝ) (m : ℕ) :
    (∫ z in Icc (0 : ℝ) r, heatResolventSeries r lam x z * Real.sin (heatFrequency r m * z)) =
      Real.sin (heatFrequency r m * x) / (lam + heatFrequency r m ^ 2 / 2) := by
  let F : ℕ → ℝ → ℝ := fun n z => heatResolventMode r lam n x z * Real.sin (heatFrequency r m * z)
  have hi (n : ℕ) : IntegrableOn (F n) (Icc 0 r) := by
    apply Continuous.integrableOn_Icc
    dsimp only [F, heatResolventMode]
    fun_prop
  have hb (n : ℕ) (z : ℝ) : ‖F n z‖ ≤ heatResolventBound r n := by
    dsimp only [F]
    rw [norm_mul]
    calc
      _ ≤ ‖heatResolventMode r lam n x z‖ * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (norm_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact heatResolventMode_bound hr hlam n x z
  have hbn (n : ℕ) : (∫ z in Icc (0 : ℝ) r, ‖F n z‖) ≤ r * heatResolventBound r n := by
    calc
      _ ≤ ∫ _z in Icc (0 : ℝ) r, heatResolventBound r n :=
        integral_mono_ae (hi n).norm (integrable_const _) (Eventually.of_forall (hb n))
      _ = _ := by
        rw [integral_const]
        simp only [measureReal_restrict_apply_univ, smul_eq_mul, Real.volume_real_Icc_of_le hr.le, sub_zero]
  have hs : Summable (fun n => ∫ z in Icc (0 : ℝ) r, ‖F n z‖) :=
    ((summable_heatResolventBound r).mul_left r).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hbn
  have heq (z : ℝ) : heatResolventSeries r lam x z * Real.sin (heatFrequency r m * z) =
      ∑' n, F n z := by
    unfold heatResolventSeries
    exact (tsum_mul_right).symm
  simp only [heq]
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  have hint (n : ℕ) : (∫ z in Icc (0 : ℝ) r, F n z) =
      (2 / r * Real.sin (heatFrequency r n * x) / (lam + heatFrequency r n ^ 2 / 2)) *
        (if n = m then r / 2 else 0) := by
    have hf (z : ℝ) : F n z =
        (2 / r * Real.sin (heatFrequency r n * x) / (lam + heatFrequency r n ^ 2 / 2)) *
          (Real.sin (heatFrequency r n * z) * Real.sin (heatFrequency r m * z)) := by
      dsimp only [F, heatResolventMode]
      ring
    simp only [hf]
    rw [integral_const_mul, integral_Icc_heatSine_mul_heatSine hr n m]
  simp only [hint]
  rw [tsum_eq_single m (fun n hnm => by rw [if_neg hnm, mul_zero]), if_pos rfl]
  field_simp


/-- Compact continuous nonnegative densities are identified by all Dirichlet sine observations. -/
theorem continuous_eqOn_of_nonneg_sine_integrals {r : ℝ} (hr : 0 < r) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfn : ∀ y ∈ Icc 0 r, 0 ≤ f y)
    (hgn : ∀ y ∈ Icc 0 r, 0 ≤ g y)
    (hs : ∀ n : ℕ, (∫ y in Icc (0 : ℝ) r, f y * Real.sin (heatFrequency r n*y)) =
      ∫ y in Icc (0 : ℝ) r, g y * Real.sin (heatFrequency r n*y)) : EqOn f g (Icc 0 r) := by
  let ρ := volume.restrict (Icc (0 : ℝ) r)
  let D (h : ℝ → ℝ) := ρ.withDensity (fun y => ENNReal.ofReal (h y))
  have hfinite {h : ℝ → ℝ} (hh : Continuous h) (hn : ∀ y ∈ Icc 0 r, 0 ≤ h y) : IsFiniteMeasure (D h) := by
    have hi : Integrable h ρ := hh.integrableOn_Icc
    apply isFiniteMeasure_withDensity
    apply (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable _).mpr hi
    exact (ae_restrict_mem measurableSet_Icc).mono (fun y hy => hn y hy)
  have hmem (h : ℝ → ℝ) : ∀ᵐ y ∂D h, y ∈ Ioo (0 : ℝ) r := by
    apply ae_mem_Ioo_of_ae_mem_Icc_of_ac
    · exact (withDensity_absolutelyContinuous ρ _).ae_le (ae_restrict_mem measurableSet_Icc)
    · exact (withDensity_absolutelyContinuous ρ _).trans Measure.absolutelyContinuous_restrict
  have hint {h : ℝ → ℝ} (hh : Continuous h) (hn : ∀ y ∈ Icc 0 r, 0 ≤ h y) (n : ℕ) :
      (∫ y, Real.sin (heatFrequency r n*y) ∂D h) =
        ∫ y in Icc (0 : ℝ) r, h y * Real.sin (heatFrequency r n*y) := by
    change (∫ y, Real.sin (heatFrequency r n*y) ∂ρ.withDensity (fun y => ENNReal.ofReal (h y))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hh.measurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    simp only [ENNReal.toReal_ofReal (hn y hy), smul_eq_mul]
  let := hfinite hf hfn
  let := hfinite hg hgn
  have heq : D f = D g := by
    apply measure_eq_of_sine_moments hr (hmem f) (hmem g)
    intro n
    rw [hint hf hfn, hint hg hgn, hs]
  have hae : (fun y => ENNReal.ofReal (f y)) =ᵐ[ρ] (fun y => ENNReal.ofReal (g y)) :=
    (withDensity_eq_iff_of_sigmaFinite hf.measurable.ennreal_ofReal.aemeasurable
      hg.measurable.ennreal_ofReal.aemeasurable).mp heq
  have hae' : f =ᵐ[ρ] g := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with y hy hmem
    exact (ENNReal.ofReal_eq_ofReal_iff (hfn y hmem) (hgn y hmem)).mp hy
  exact Measure.eqOn_Icc_of_ae_eq volume hr.ne hae' hf.continuousOn hg.continuousOn

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem heatResolventSeries_nonneg (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r lam x z : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam) (hx : x ∈ Icc 0 r) (hz : z ∈ Icc 0 r) :
    0 ≤ heatResolventSeries r lam x z := by
  rw [← integral_laplace_dirichletHeatKernel hr hlam]
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact mul_nonneg (Real.exp_nonneg _) (dirichletHeatKernel_nonneg_real hB hr ht hx hz)

/-- The actual time resolvent equals the explicit two-sided Green solution; no ODE identification is assumed. -/
theorem heatResolventSeries_eq_dirichletGreen (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r k x z : ℝ} (hr : 0 < r) (hk : 0 < k) (hx : x ∈ Icc 0 r) (hz : z ∈ Icc 0 r) :
    heatResolventSeries r (k^2/2) x z = dirichletGreen r k x z := by
  apply continuous_eqOn_of_nonneg_sine_integrals hr
    (continuous_heatResolventSeries_right hr (by positivity) x) (continuous_dirichletGreen_right r k x)
    (fun y hy => heatResolventSeries_nonneg hB hr (by positivity) hx hy)
    (fun y hy => dirichletGreen_nonneg hr hk hx hy) _ hz
  intro n
  rw [integral_heatResolventSeries_mul_sine hr (by positivity), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hr.le, integral_dirichletGreen_sine hr hk hx]

/-- Exact Laplace integral in the paper's generator normalization. -/
theorem integral_laplace_dirichletHeatKernel_eq_green (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r k x z : ℝ} (hr : 0 < r) (hk : 0 < k) (hx : x ∈ Icc 0 r) (hz : z ∈ Icc 0 r) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(k^2/2)*t)*dirichletHeatKernel r t x z) =
      2*Real.sinh (k*min x z)*Real.sinh (k*(r-max x z))/(k*Real.sinh (k*r)) := by
  rw [integral_laplace_dirichletHeatKernel hr (by positivity),
    heatResolventSeries_eq_dirichletGreen hB hr hk hx hz]
  rfl

end BrownianAffine
