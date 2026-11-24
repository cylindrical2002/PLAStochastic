import PLAStochastic.Index.CEPS.Final.PipelineDefs

/-!
# The analytic box-Taylor pipeline at complex frequencies

Under `CepsAnalyticPipeline`, on the strip `imagStrip δ = {|Re z| < δ}`:

* the coefficient functions `cepsPipelineCoeffZ α` and the kernels `cepsPipelinePsi q`
  (`q` in the polydisc) are holomorphic (`coeffZ_differentiableOn`, `psi_differentiableOn`);
* `‖cepsPipelinePsi q z‖ ≤ (K + ∫ g) W(z)` and
  `‖cepsPipelineCoeffZ α z‖ ≤ (K + ∫ g) (2/R)^{|α|} W(z)` with
  `W = cepsPipelineWeight c e` (`psi_bound`, `coeffZ_bound`);
* the box Taylor remainder of `cepsPipelinePsi` with the fixed coefficients
  `cepsPipelineCoeffZ α z` is `K(d,N) (K + ∫ g) W(z) (∑ᵢ |xᵢ| / R)^{N+1}` for `‖x‖ ≤ R/4`
  (`psi_box`).

The `λ`-integral is handled termwise: the box representation of each integrand (polydisc
Cauchy estimates for fixed `λ` and `z`) is integrated against the envelope `g`.
-/

noncomputable section
open Complex Finset Metric MeasureTheory Filter
namespace PGM
namespace CepsAnalyticPipeline

variable {Λ : Type*} [MeasurableSpace Λ] {μ : Measure Λ} {d : ℕ} {p₀ : ℕ → ℝ}
  {R δ K c : ℝ} {e : ℕ} {g : Λ → ℝ}
  {E : (Fin d → ℂ) → ℂ → ℂ} {H : (Fin d → ℂ) → Λ → ℂ → ℂ}

section

variable (hP : CepsAnalyticPipeline μ d p₀ R δ K c e g E H)
include hP

theorem center_mem :
    (fun i : Fin d => (p₀ i : ℂ)) ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R :=
  mem_ball_self hP.R_pos

theorem zero_mem_strip : (0 : ℂ) ∈ imagStrip δ := by
  simp [imagStrip, hP.δ_pos]

theorem E_bound' {q : Fin d → ℂ} (hq : q ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R) {z : ℂ}
    (hz : z ∈ imagStrip δ) : ‖E q z‖ ≤ K * cepsPipelineWeight c e z := by
  have h := hP.E_bound q hq z hz
  unfold cepsPipelineWeight
  rwa [← mul_assoc]

theorem g_nonneg : ∀ᵐ lam ∂μ, 0 ≤ g lam := by
  filter_upwards [hP.H_bound] with lam h
  have h0 := h _ hP.center_mem 0 hP.zero_mem_strip
  simp only [norm_zero, add_zero, one_pow, Real.sqrt_zero, mul_zero, Real.exp_zero,
    mul_one] at h0
  exact (norm_nonneg _).trans h0

theorem integral_g_nonneg : 0 ≤ ∫ lam, g lam ∂μ :=
  integral_nonneg_of_ae (by filter_upwards [hP.g_nonneg] with lam h using h)

theorem E_slice {z : ℂ} (hz : z ∈ imagStrip δ) :
    ∀ q ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R, AnalyticAt ℂ (fun q' => E q' z) q :=
  fun q hq => (hP.E_analytic q hq z hz).comp₂ (f := fun q' => q') (g := fun _ => z)
    analyticAt_id analyticAt_const

theorem E_freq {q : Fin d → ℂ} (hq : q ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R) :
    DifferentiableOn ℂ (fun z => E q z) (imagStrip δ) := fun z hz =>
  ((hP.E_analytic q hq z hz).comp₂ (f := fun _ : ℂ => q) (g := fun z' => z')
    analyticAt_const analyticAt_id).differentiableAt.differentiableWithinAt

theorem H_slice : ∀ᵐ lam ∂μ, ∀ z ∈ imagStrip δ,
    ∀ q ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R, AnalyticAt ℂ (fun q' => H q' lam z) q := by
  filter_upwards [hP.H_analytic] with lam ha z hz q hq
  exact (ha q hq z hz).comp₂ (f := fun q' => q') (g := fun _ => z) analyticAt_id
    analyticAt_const

theorem H_freq : ∀ᵐ lam ∂μ, ∀ q ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R,
    DifferentiableOn ℂ (fun z => H q lam z) (imagStrip δ) := by
  filter_upwards [hP.H_analytic] with lam ha q hq z hz
  exact ((ha q hq z hz).comp₂ (f := fun _ : ℂ => q) (g := fun z' => z') analyticAt_const
    analyticAt_id).differentiableAt.differentiableWithinAt

theorem H_integrable {q : Fin d → ℂ} (hq : q ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R) {z : ℂ}
    (hz : z ∈ imagStrip δ) : Integrable (fun lam => H q lam z) μ :=
  integrable_of_dominated_param (f := fun lam z => H q lam z) (U := imagStrip δ)
    hP.g_integrable (W := cepsPipelineWeight c e)
    (fun z _ => (cepsPipelineWeight_pos c e z).le) (fun z hz => hP.H_measurable q hq z hz)
    (by filter_upwards [hP.H_bound] with lam hb z hz using hb q hq z hz) hz

/-! ## Coefficients -/

theorem coeffE_bound {z : ℂ} (hz : z ∈ imagStrip δ) (α : Fin d → ℕ) :
    ‖polydiscTaylorCoeff (fun q => E q z) (fun i : Fin d => (p₀ i : ℂ)) α‖ ≤
      K * cepsPipelineWeight c e z * (2 / R) ^ (∑ i, α i) :=
  norm_polydiscTaylorCoeff_le hP.R_pos (hP.E_slice hz) (fun _ hq => hP.E_bound' hq hz) α

theorem coeffH_bound (α : Fin d → ℕ) : ∀ᵐ lam ∂μ, ∀ z ∈ imagStrip δ,
    ‖polydiscTaylorCoeff (fun q => H q lam z) (fun i : Fin d => (p₀ i : ℂ)) α‖ ≤
      g lam * (cepsPipelineWeight c e z * (2 / R) ^ (∑ i, α i)) := by
  filter_upwards [hP.H_slice, hP.H_bound] with lam ha hb z hz
  rw [← mul_assoc]
  exact norm_polydiscTaylorCoeff_le hP.R_pos (ha z hz) (fun q hq => hb q hq z hz) α

theorem coeffE_differentiableOn (α : Fin d → ℕ) :
    DifferentiableOn ℂ (fun z => polydiscTaylorCoeff (fun q => E q z)
      (fun i : Fin d => (p₀ i : ℂ)) α) (imagStrip δ) := fun _ hz =>
  (analyticAt_polydiscTaylorCoeff_param (isOpen_imagStrip δ)
    (fun z' hz' => hP.E_analytic _ hP.center_mem z' hz') α hz).differentiableAt.differentiableWithinAt

theorem coeffH_differentiableOn (α : Fin d → ℕ) : ∀ᵐ lam ∂μ,
    DifferentiableOn ℂ (fun z => polydiscTaylorCoeff (fun q => H q lam z)
      (fun i : Fin d => (p₀ i : ℂ)) α) (imagStrip δ) := by
  filter_upwards [hP.H_analytic] with lam ha z hz
  exact (analyticAt_polydiscTaylorCoeff_param (G := fun q z => H q lam z) (isOpen_imagStrip δ)
    (fun z' hz' => ha _ hP.center_mem z' hz') α hz).differentiableAt.differentiableWithinAt

theorem coeffH_measurable (α : Fin d → ℕ) {z : ℂ} (hz : z ∈ imagStrip δ) :
    AEStronglyMeasurable (fun lam => polydiscTaylorCoeff (fun q => H q lam z)
      (fun i : Fin d => (p₀ i : ℂ)) α) μ := by
  refine aestronglyMeasurable_polydiscTaylorCoeff (H := fun q lam => H q lam z) hP.R_pos ?_
    (fun q hq => hP.H_measurable q hq z hz) α
  filter_upwards [hP.H_slice] with lam ha
  exact ha z hz

theorem coeffH_integrable (α : Fin d → ℕ) {z : ℂ} (hz : z ∈ imagStrip δ) :
    Integrable (fun lam => polydiscTaylorCoeff (fun q => H q lam z)
      (fun i : Fin d => (p₀ i : ℂ)) α) μ :=
  integrable_of_dominated_param
    (f := fun lam z => polydiscTaylorCoeff (fun q => H q lam z) (fun i : Fin d => (p₀ i : ℂ)) α)
    (U := imagStrip δ) hP.g_integrable
    (W := fun z => cepsPipelineWeight c e z * (2 / R) ^ (∑ i, α i))
    (fun z _ => mul_nonneg (cepsPipelineWeight_pos c e z).le
      (pow_nonneg (div_nonneg zero_le_two hP.R_pos.le) _))
    (fun _ hz => hP.coeffH_measurable α hz) (hP.coeffH_bound α) hz

/-! ## Holomorphy in the frequency -/

theorem psi_differentiableOn {q : Fin d → ℂ} (hq : q ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R) :
    DifferentiableOn ℂ (cepsPipelinePsi μ E H q) (imagStrip δ) := by
  show DifferentiableOn ℂ (fun z => E q z - ∫ lam, H q lam z ∂μ) (imagStrip δ)
  refine (hP.E_freq hq).sub ?_
  refine differentiableOn_integral_of_dominated (f := fun lam z => H q lam z)
    (isOpen_imagStrip δ) hP.g_integrable (continuous_cepsPipelineWeight c e).continuousOn
    (fun z _ => (cepsPipelineWeight_pos c e z).le) (fun z hz => hP.H_measurable q hq z hz) ?_ ?_
  · filter_upwards [hP.H_freq] with lam h using h q hq
  · filter_upwards [hP.H_bound] with lam hb z hz using hb q hq z hz

theorem coeffZ_differentiableOn (α : Fin d → ℕ) :
    DifferentiableOn ℂ (cepsPipelineCoeffZ μ E H p₀ α) (imagStrip δ) := by
  show DifferentiableOn ℂ (fun z => polydiscTaylorCoeff (fun q => E q z)
      (fun i : Fin d => (p₀ i : ℂ)) α - ∫ lam, polydiscTaylorCoeff (fun q => H q lam z)
        (fun i : Fin d => (p₀ i : ℂ)) α ∂μ) (imagStrip δ)
  refine (hP.coeffE_differentiableOn α).sub ?_
  refine differentiableOn_integral_of_dominated
    (f := fun lam z => polydiscTaylorCoeff (fun q => H q lam z) (fun i : Fin d => (p₀ i : ℂ)) α)
    (isOpen_imagStrip δ) hP.g_integrable
    ((continuous_cepsPipelineWeight c e).mul continuous_const).continuousOn
    (fun z _ => mul_nonneg (cepsPipelineWeight_pos c e z).le
      (pow_nonneg (div_nonneg zero_le_two hP.R_pos.le) _))
    (fun _ hz => hP.coeffH_measurable α hz) (hP.coeffH_differentiableOn α) (hP.coeffH_bound α)

/-! ## Bounds -/

theorem norm_integral_H_le {q : Fin d → ℂ} (hq : q ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R)
    {z : ℂ} (hz : z ∈ imagStrip δ) :
    ‖∫ lam, H q lam z ∂μ‖ ≤ (∫ lam, g lam ∂μ) * cepsPipelineWeight c e z := by
  rw [← integral_mul_const]
  exact norm_integral_le_of_norm_le (hP.g_integrable.mul_const _)
    (by filter_upwards [hP.H_bound] with lam hb using hb q hq z hz)

theorem psi_bound {q : Fin d → ℂ} (hq : q ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R) {z : ℂ}
    (hz : z ∈ imagStrip δ) :
    ‖cepsPipelinePsi μ E H q z‖ ≤ (K + ∫ lam, g lam ∂μ) * cepsPipelineWeight c e z := by
  calc ‖cepsPipelinePsi μ E H q z‖
      ≤ ‖E q z‖ + ‖∫ lam, H q lam z ∂μ‖ := norm_sub_le _ _
    _ ≤ K * cepsPipelineWeight c e z + (∫ lam, g lam ∂μ) * cepsPipelineWeight c e z :=
        add_le_add (hP.E_bound' hq hz) (hP.norm_integral_H_le hq hz)
    _ = _ := by ring

theorem coeffZ_bound (α : Fin d → ℕ) {z : ℂ} (hz : z ∈ imagStrip δ) :
    ‖cepsPipelineCoeffZ μ E H p₀ α z‖ ≤
      (K + ∫ lam, g lam ∂μ) * (2 / R) ^ (∑ i, α i) * cepsPipelineWeight c e z := by
  have h2 : ‖∫ lam, polydiscTaylorCoeff (fun q => H q lam z)
      (fun i : Fin d => (p₀ i : ℂ)) α ∂μ‖ ≤
        (∫ lam, g lam ∂μ) * (cepsPipelineWeight c e z * (2 / R) ^ (∑ i, α i)) := by
    rw [← integral_mul_const]
    exact norm_integral_le_of_norm_le (hP.g_integrable.mul_const _)
      (by filter_upwards [hP.coeffH_bound α] with lam hb using hb z hz)
  calc ‖cepsPipelineCoeffZ μ E H p₀ α z‖
      ≤ ‖polydiscTaylorCoeff (fun q => E q z) (fun i : Fin d => (p₀ i : ℂ)) α‖ +
          ‖∫ lam, polydiscTaylorCoeff (fun q => H q lam z)
            (fun i : Fin d => (p₀ i : ℂ)) α ∂μ‖ := norm_sub_le _ _
    _ ≤ K * cepsPipelineWeight c e z * (2 / R) ^ (∑ i, α i) +
          (∫ lam, g lam ∂μ) * (cepsPipelineWeight c e z * (2 / R) ^ (∑ i, α i)) :=
        add_le_add (hP.coeffE_bound hz α) h2
    _ = _ := by ring

/-- **Box remainder at complex frequencies.** -/
theorem psi_box {z : ℂ} (hz : z ∈ imagStrip δ) (N : ℕ) {x : Fin d → ℂ} (hx : ‖x‖ ≤ R / 4) :
    ‖cepsPipelinePsi μ E H ((fun i : Fin d => (p₀ i : ℂ)) + x) z -
        ∑ α ∈ cepsTaylorBox d N, cepsPipelineCoeffZ μ E H p₀ α z * ∏ i, x i ^ α i‖ ≤
      polydiscRemainderConst d N * (K + ∫ lam, g lam ∂μ) * cepsPipelineWeight c e z *
        ((∑ i, ‖x i‖) / R) ^ (N + 1) := by
  set c₀ : Fin d → ℂ := fun i => (p₀ i : ℂ)
  set W := cepsPipelineWeight c e z
  set s := ((∑ i, ‖x i‖) / R) ^ (N + 1)
  set G := ∫ lam, g lam ∂μ
  set Kr := polydiscRemainderConst d N
  have hbox : finiteCoordinateTaylorBox d N = cepsTaylorBox d N := rfl
  have hxmem : c₀ + x ∈ ball c₀ R := by
    rw [mem_ball, dist_self_add_left]
    linarith [hP.R_pos]
  have hE := norm_sub_polydiscTaylorBox_le_sum hP.R_pos (hP.E_slice hz)
    (fun _ hq => hP.E_bound' hq hz) N hx
  rw [hbox] at hE
  have hHae : ∀ᵐ lam ∂μ, ‖H (c₀ + x) lam z - ∑ α ∈ cepsTaylorBox d N,
      polydiscTaylorCoeff (fun q => H q lam z) c₀ α * ∏ i, x i ^ α i‖ ≤
        Kr * s * W * g lam := by
    filter_upwards [hP.H_slice, hP.H_bound] with lam ha hb
    have h1 := norm_sub_polydiscTaylorBox_le_sum hP.R_pos (ha z hz)
      (fun q hq => hb q hq z hz) N hx
    rw [hbox] at h1
    exact h1.trans (le_of_eq (by simp only [Kr, s, W, cepsPipelineWeight]; ring))
  have hint_sum : ∀ α ∈ cepsTaylorBox d N, Integrable
      (fun lam => polydiscTaylorCoeff (fun q => H q lam z) c₀ α * ∏ i, x i ^ α i) μ :=
    fun α _ => (hP.coeffH_integrable α hz).mul_const _
  have hI : (∫ lam, H (c₀ + x) lam z ∂μ) - ∑ α ∈ cepsTaylorBox d N,
      (∫ lam, polydiscTaylorCoeff (fun q => H q lam z) c₀ α ∂μ) * ∏ i, x i ^ α i =
        ∫ lam, (H (c₀ + x) lam z - ∑ α ∈ cepsTaylorBox d N,
          polydiscTaylorCoeff (fun q => H q lam z) c₀ α * ∏ i, x i ^ α i) ∂μ := by
    rw [integral_sub (hP.H_integrable hxmem hz) (integrable_finsetSum _ hint_sum),
      integral_finsetSum _ hint_sum]
    congr 1
    exact sum_congr rfl fun α _ => (integral_mul_const _ _).symm
  have hH : ‖(∫ lam, H (c₀ + x) lam z ∂μ) - ∑ α ∈ cepsTaylorBox d N,
      (∫ lam, polydiscTaylorCoeff (fun q => H q lam z) c₀ α ∂μ) * ∏ i, x i ^ α i‖ ≤
        Kr * s * W * G := by
    rw [hI]
    calc _ ≤ ∫ lam, Kr * s * W * g lam ∂μ :=
          norm_integral_le_of_norm_le (hP.g_integrable.const_mul _) hHae
      _ = Kr * s * W * G := integral_const_mul _ _
  have hsplit : cepsPipelinePsi μ E H (c₀ + x) z -
      ∑ α ∈ cepsTaylorBox d N, cepsPipelineCoeffZ μ E H p₀ α z * ∏ i, x i ^ α i =
        (E (c₀ + x) z - ∑ α ∈ cepsTaylorBox d N,
          polydiscTaylorCoeff (fun q => E q z) c₀ α * ∏ i, x i ^ α i) -
        ((∫ lam, H (c₀ + x) lam z ∂μ) - ∑ α ∈ cepsTaylorBox d N,
          (∫ lam, polydiscTaylorCoeff (fun q => H q lam z) c₀ α ∂μ) * ∏ i, x i ^ α i) := by
    simp only [cepsPipelinePsi, cepsPipelineCoeffZ, sub_mul, sum_sub_distrib]
    ring
  rw [hsplit]
  calc _ ≤ Kr * (K * W) * s + Kr * s * W * G := (norm_sub_le _ _).trans (add_le_add hE hH)
    _ = Kr * (K + G) * W * s := by ring

end

end CepsAnalyticPipeline
end PGM
