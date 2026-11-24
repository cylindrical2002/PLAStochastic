import PLAStochastic.Brownian.Killed.GreenIdentification

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- A nonnegative pointwise limit is integrable and bounded by the limit of upper bounds
for the approximating integrals. -/
theorem nonnegative_fatou_integrable_bound {ρ : Measure ℝ} {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {upper : ℕ → ℝ} {C : ℝ}
    (hi : ∀ n, Integrable (F n) ρ) (hn : ∀ n, ∀ᵐ x ∂ρ, 0 ≤ F n x)
    (ht : ∀ᵐ x ∂ρ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hb : ∀ n, (∫ x, F n x ∂ρ) ≤ upper n) (hI : Tendsto upper atTop (𝓝 C)) :
    Integrable f ρ ∧ (∫ x, f x ∂ρ) ≤ C := by
  have hC : 0 ≤ C := ge_of_tendsto hI (Eventually.of_forall
    (fun n => (integral_nonneg_of_ae (hn n)).trans (hb n)))
  have hfn : ∀ᵐ x ∂ρ, 0 ≤ f x := by
    filter_upwards [ht, ae_all_iff.mpr hn] with x hx hxn
    exact ge_of_tendsto hx (Eventually.of_forall hxn)
  have heq (n : ℕ) : (∫⁻ x, ‖F n x‖ₑ ∂ρ) = ENNReal.ofReal (∫ x, F n x ∂ρ) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hi n)]
    congr 1
    apply integral_congr_ae
    filter_upwards [hn n] with x hx using Real.norm_of_nonneg hx
  have hl : Tendsto (fun n => ENNReal.ofReal (upper n)) atTop (𝓝 (ENNReal.ofReal C)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hI
  have hli : liminf (fun n => ∫⁻ x, ‖F n x‖ₑ ∂ρ) atTop ≤ ENNReal.ofReal C := by
    rw [← hl.liminf_eq]
    apply liminf_le_liminf (Eventually.of_forall (fun n => ?_))
    rw [heq]
    exact ENNReal.ofReal_le_ofReal (hb n)
  have hif : Integrable f ρ := integrable_of_tendsto ht (fun n => (hi n).aestronglyMeasurable)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hli)
  refine ⟨hif, ?_⟩
  have hbound := (lintegral_enorm_le_liminf_of_tendsto ht
    (fun n => (hi n).aestronglyMeasurable.aemeasurable.enorm)).trans hli
  rw [← ofReal_integral_norm_eq_lintegral_enorm hif] at hbound
  have hnorm : (∫ x, ‖f x‖ ∂ρ) = ∫ x, f x ∂ρ :=
    integral_congr_ae (hfn.mono (fun x hx => Real.norm_of_nonneg hx))
  rw [hnorm] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hbound

/-- Inward derivative of the explicit Green function. -/
theorem hasDerivAt_dirichletGreen_zero {r k x : ℝ} (hx : 0 < x) (hk : 0 < k) :
    HasDerivAt (dirichletGreen r k x) (2*Real.sinh (k*(r-x))/Real.sinh (k*r)) 0 := by
  have hd := (((hasDerivAt_id (0 : ℝ)).const_mul k).sinh).const_mul
    (2*Real.sinh (k*(r-x))/(k*Real.sinh (k*r)))
  have he : (fun z => (2*Real.sinh (k*(r-x))/(k*Real.sinh (k*r)))*Real.sinh (k*z)) =ᶠ[𝓝 0]
      dirichletGreen r k x := by
    filter_upwards [eventually_lt_nhds hx] with z hz
    exact (dirichletGreen_of_le hz.le).symm
  convert! hd.congr_of_eventuallyEq (by simpa only [id_eq] using he.symm) using 1
  simp only [id_eq, mul_zero, Real.cosh_zero, one_mul, mul_one]
  field_simp

private def boundaryApproach (r : ℝ) (n : ℕ) : ℝ := r/((n : ℝ)+1)

private theorem boundaryApproach_pos {r : ℝ} (hr : 0 < r) (n : ℕ) : 0 < boundaryApproach r n := by
  unfold boundaryApproach
  positivity

private theorem boundaryApproach_mem {r : ℝ} (hr : 0 < r) (n : ℕ) : boundaryApproach r n ∈ Icc 0 r := by
  constructor
  · exact (boundaryApproach_pos hr n).le
  · exact div_le_self hr.le (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)

private theorem tendsto_boundaryApproach {r : ℝ} (hr : 0 < r) :
    Tendsto (boundaryApproach r) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · change Tendsto (fun n : ℕ => r/((n : ℝ)+1)) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul r
  · exact Eventually.of_forall (boundaryApproach_pos hr)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Fatou's lemma controls the boundary Laplace integral without exchanging a boundary derivative
with an improper integral. -/
theorem laplace_heatBoundaryLeft_integrable_bound (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r k x : ℝ} (hr : 0 < r) (hk : 0 < k) (hx : x ∈ Ioo 0 r) :
    IntegrableOn (fun t => Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t x) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t x) ≤
        2*Real.sinh (k*(r-x))/Real.sinh (k*r) := by
  let F : ℕ → ℝ → ℝ := fun n t =>
    (Real.exp (-(k^2/2)*t)*dirichletHeatKernel r t x (boundaryApproach r n))/boundaryApproach r n
  have hi (n : ℕ) : IntegrableOn (F n) (Ioi 0) :=
    (integrableOn_laplace_dirichletHeatKernel hr (by positivity) x (boundaryApproach r n)).div_const _
  have hn (n : ℕ) : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ F n t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact div_nonneg (mul_nonneg (Real.exp_nonneg _)
      (dirichletHeatKernel_nonneg_real hB hr ht ⟨hx.1.le,hx.2.le⟩ (boundaryApproach_mem hr n)))
      (boundaryApproach_pos hr n).le
  have ht : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), Tendsto (fun n => F n t) atTop
      (𝓝 (Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hd := (hasDerivAt_heatKernel_zero hr ht x).tendsto_slope_zero_right.comp (tendsto_boundaryApproach hr)
    have hd' : Tendsto (fun n => dirichletHeatKernel r t x (boundaryApproach r n)/boundaryApproach r n)
        atTop (𝓝 (heatBoundaryLeft r t x)) := by
      simpa only [Function.comp_def, zero_add, dirichletHeatKernel_zero_right, sub_zero,
        smul_eq_mul, inv_mul_eq_div] using hd
    simpa only [F, mul_div_assoc] using hd'.const_mul (Real.exp (-(k^2/2)*t))
  have hG0 : dirichletGreen r k x 0 = 0 := by
    rw [dirichletGreen_of_le hx.1.le]
    simp
  have hI : Tendsto (fun n => ∫ t in Ioi (0 : ℝ), F n t) atTop
      (𝓝 (2*Real.sinh (k*(r-x))/Real.sinh (k*r))) := by
    have hd := (hasDerivAt_dirichletGreen_zero (r := r) hx.1 hk).tendsto_slope_zero_right.comp (tendsto_boundaryApproach hr)
    have hd' : Tendsto (fun n => dirichletGreen r k x (boundaryApproach r n)/boundaryApproach r n)
        atTop (𝓝 (2*Real.sinh (k*(r-x))/Real.sinh (k*r))) := by
      simpa only [Function.comp_def, zero_add, hG0, sub_zero, smul_eq_mul, inv_mul_eq_div] using hd
    convert! hd' using 1
    funext n
    dsimp only [F]
    rw [integral_div, integral_laplace_dirichletHeatKernel hr (by positivity),
      heatResolventSeries_eq_dirichletGreen hB hr hk ⟨hx.1.le,hx.2.le⟩ (boundaryApproach_mem hr n)]
  exact nonnegative_fatou_integrable_bound hi hn ht (fun _ => le_rfl) hI

/-- The reflected boundary satisfies the corresponding finite Laplace bound. -/
theorem laplace_heatBoundaryRight_integrable_bound (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r k x : ℝ} (hr : 0 < r) (hk : 0 < k) (hx : x ∈ Ioo 0 r) :
    IntegrableOn (fun t => Real.exp (-(k^2/2)*t)*heatBoundaryRight r t x) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), Real.exp (-(k^2/2)*t)*heatBoundaryRight r t x) ≤
        2*Real.sinh (k*x)/Real.sinh (k*r) := by
  simp only [heatBoundaryRight_reflection hr.ne']
  simpa only [sub_sub_cancel] using laplace_heatBoundaryLeft_integrable_bound hB hr hk
    (x := r-x) ⟨sub_pos.mpr hx.2, sub_lt_self _ hx.1⟩

/-- A second inward Fatou limit proves the cross-boundary Laplace integral finite. -/
theorem laplace_heatCrossBoundary_integrable_bound (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r k : ℝ} (hr : 0 < r) (hk : 0 < k) :
    IntegrableOn (fun t => Real.exp (-(k^2/2)*t)*heatCrossBoundary r t) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), Real.exp (-(k^2/2)*t)*heatCrossBoundary r t) ≤
        2*k/Real.sinh (k*r) := by
  let a : ℕ → ℝ := fun n => boundaryApproach r (n+1)
  have ha (n : ℕ) : 0 < a n := boundaryApproach_pos hr (n+1)
  have har (n : ℕ) : a n < r := by
    change r/(((n+1 : ℕ) : ℝ)+1) < r
    apply div_lt_self hr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    linarith
  have hax (n : ℕ) : r-a n ∈ Ioo (0 : ℝ) r := ⟨sub_pos.mpr (har n), sub_lt_self r (ha n)⟩
  have hal : Tendsto a atTop (𝓝[>] 0) := (tendsto_boundaryApproach hr).comp (tendsto_add_atTop_nat 1)
  let F : ℕ → ℝ → ℝ := fun n t =>
    (Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t (r-a n))/a n
  have hi (n : ℕ) : IntegrableOn (F n) (Ioi 0) :=
    (laplace_heatBoundaryLeft_integrable_bound hB hr hk (hax n)).1.div_const _
  have hn (n : ℕ) : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ F n t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact div_nonneg (mul_nonneg (Real.exp_nonneg _)
      (heatBoundaryLeft_nonneg hB hr (T := ⟨t,ht.le⟩) ht ⟨(hax n).1.le,(hax n).2.le⟩)) (ha n).le
  have ht : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), Tendsto (fun n => F n t) atTop
      (𝓝 (Real.exp (-(k^2/2)*t)*heatCrossBoundary r t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hd : HasDerivAt (fun z => heatBoundaryLeft r t (r-z)) (heatCrossBoundary r t) 0 := by
      simpa only [sub_zero, heatCrossBoundary] using
        (hasDerivAt_heatBoundaryLeft hr ht (r-0)).comp_const_sub r 0
    have hd' : Tendsto (fun n => heatBoundaryLeft r t (r-a n)/a n) atTop (𝓝 (heatCrossBoundary r t)) := by
      simpa only [Function.comp_def, zero_add, sub_zero, heatBoundaryLeft_at_width hr.ne',
        smul_eq_mul, inv_mul_eq_div] using hd.tendsto_slope_zero_right.comp hal
    simpa only [F, mul_div_assoc] using hd'.const_mul (Real.exp (-(k^2/2)*t))
  let upper : ℕ → ℝ := fun n => (2*Real.sinh (k*a n)/Real.sinh (k*r))/a n
  have hb (n : ℕ) : (∫ t in Ioi (0 : ℝ), F n t) ≤ upper n := by
    dsimp only [F, upper]
    rw [integral_div]
    apply div_le_div_of_nonneg_right _ (ha n).le
    simpa only [sub_sub_cancel] using (laplace_heatBoundaryLeft_integrable_bound hB hr hk (hax n)).2
  have hl : Tendsto upper atTop (𝓝 (2*k/Real.sinh (k*r))) := by
    have hd : HasDerivAt (fun z : ℝ => 2*Real.sinh (k*z)/Real.sinh (k*r)) (2*k/Real.sinh (k*r)) 0 := by
      convert! ((((hasDerivAt_id (0 : ℝ)).const_mul k).sinh).const_mul 2).div_const (Real.sinh (k*r)) using 1
      simp
    simpa only [upper, Function.comp_def, zero_add, mul_zero, Real.sinh_zero,
      zero_div, sub_zero, smul_eq_mul, inv_mul_eq_div] using hd.tendsto_slope_zero_right.comp hal
  exact nonnegative_fatou_integrable_bound hi hn ht hb hl

end BrownianAffine
