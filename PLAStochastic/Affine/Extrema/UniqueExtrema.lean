import PLAStochastic.Affine.Moments.Optimal.Slope.MomentFormula

/-!
# Unique extrema of actual Brownian paths at every fixed drift

Joint continuity makes envelope differentiability a Borel path event. The
Lebesgue-null bad slopes on each path are transferred to actual Brownian paths
by Gaussian endpoint density cancellation. No Cameron--Martin theorem or
probabilistic extremum-uniqueness hypothesis is used.
-/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

theorem slopeUpper_le_add_path_dist (g h : Path 1) (a : ℝ) :
    slopeUpper g a ≤ slopeUpper h a + dist g h := by
  obtain ⟨t, ht⟩ := slopeUpper_attained g a
  have hb := slopeResidual_le_upper h a t
  have hd : |g t - h t| ≤ dist g h := by
    simpa only [Real.dist_eq] using! ContinuousMap.dist_apply_le_dist (f := g) (g := h) t
  have hd' := (abs_le.mp hd).2
  unfold slopeResidual at *
  linarith

theorem slopeLower_le_add_path_dist (g h : Path 1) (a : ℝ) :
    slopeLower g a ≤ slopeLower h a + dist g h := by
  obtain ⟨t, ht⟩ := slopeLower_attained h a
  have hb := slopeLower_le_residual g a t
  have hd : |g t - h t| ≤ dist g h := by
    simpa only [Real.dist_eq] using! ContinuousMap.dist_apply_le_dist (f := g) (g := h) t
  have hd' := (abs_le.mp hd).2
  unfold slopeResidual at *
  linarith

private theorem envelope_joint_lipschitz (F : Path 1 → ℝ → ℝ)
    (hpath : ∀ g h a, F g a ≤ F h a + dist g h)
    (hslope : ∀ g a b, F g a ≤ F g b + |a - b|) :
    LipschitzWith 2 (fun p : Path 1 × ℝ => F p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hp : dist p.1 q.1 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_left _ _
  have ha : |p.2 - q.2| ≤ dist p q := by
    rw [Prod.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  have h₁ := hpath p.1 q.1 p.2
  have h₂ := hslope q.1 p.2 q.2
  have h₃ := hpath q.1 p.1 q.2
  have h₄ := hslope p.1 q.2 p.2
  rw [dist_comm q.1 p.1] at h₃
  rw [abs_sub_comm q.2 p.2] at h₄
  simp only [Real.dist_eq, NNReal.coe_ofNat]
  rw [abs_le]
  constructor <;> linarith

theorem slopeUpper_joint_lipschitz :
    LipschitzWith 2 (fun p : Path 1 × ℝ => slopeUpper p.1 p.2) :=
  envelope_joint_lipschitz _ slopeUpper_le_add_path_dist slopeUpper_le_add_abs

theorem slopeLower_joint_lipschitz :
    LipschitzWith 2 (fun p : Path 1 × ℝ => slopeLower p.1 p.2) :=
  envelope_joint_lipschitz _ slopeLower_le_add_path_dist slopeLower_le_add_abs

theorem measurable_slopeUpper_deriv_joint :
    Measurable (fun p : Path 1 × ℝ => deriv (slopeUpper p.1) p.2) :=
  measurable_deriv_with_param slopeUpper_joint_lipschitz.continuous

theorem measurable_slopeLower_deriv_joint :
    Measurable (fun p : Path 1 × ℝ => deriv (slopeLower p.1) p.2) :=
  measurable_deriv_with_param slopeLower_joint_lipschitz.continuous

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

private theorem bridge_lintegral_swap (hB : IsBrownianReal B μ)
    {Φ : Path 1 → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ ω, ∫⁻ y : ℝ, Φ (bridgeUnitPath B ω + y • timePath 1) ∂volume ∂μ) =
      ∫⁻ y : ℝ, ∫⁻ ω, Φ (bridgeUnitPath B ω + y • timePath 1) ∂μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hG : Measurable (fun p : Path 1 × ℝ => Φ (p.1 + p.2 • timePath 1)) :=
    hΦ.comp measurable_add_endpoint_path
  have hb := aemeasurable_bridgeUnitPath hB
  have hm : Measurable (fun g : Path 1 => ∫⁻ y : ℝ, Φ (g + y • timePath 1)) :=
    hG.lintegral_prod_right
  calc
    (∫⁻ ω, ∫⁻ y : ℝ, Φ (bridgeUnitPath B ω + y • timePath 1) ∂volume ∂μ) =
        ∫⁻ g, ∫⁻ y : ℝ, Φ (g + y • timePath 1) ∂volume ∂μ.map (bridgeUnitPath B) :=
      (lintegral_map' hm.aemeasurable hb).symm
    _ = ∫⁻ y : ℝ, ∫⁻ g, Φ (g + y • timePath 1) ∂μ.map (bridgeUnitPath B) :=
      lintegral_lintegral_swap hG.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro y
      exact lintegral_map' (hG.comp measurable_prodMk_right).aemeasurable hb

private theorem brownian_envelope_differentiable_ae (hB : IsBrownianReal B μ)
    (F : Path 1 → ℝ → ℝ) (hc : Continuous F.uncurry)
    (hl : ∀ g, LipschitzWith 1 (F g))
    (hshift : ∀ g y a, F (g + y • timePath 1) a = F g (a - y)) (a : ℝ) :
    ∀ᵐ ω ∂μ, DifferentiableAt ℝ (F (unitPath (processPath B ω) 1)) a := by
  classical
  let Φ : Path 1 → ℝ≥0∞ := fun g => if DifferentiableAt ℝ (F g) a then 0 else 1
  have hm : MeasurableSet {g : Path 1 | DifferentiableAt ℝ (F g) a} :=
    (measurableSet_of_differentiableAt_with_param ℝ hc).preimage
      (measurable_id.prodMk measurable_const)
  have hΦ : Measurable Φ := Measurable.ite hm measurable_const measurable_const
  have hΦshift (g : Path 1) (y : ℝ) :
      Φ (g + y • timePath 1) = if DifferentiableAt ℝ (F g) (a - y) then 0 else 1 := by
    dsimp only [Φ]
    rw [funext (hshift g y), differentiableAt_comp_sub_const]
  have hpath (g : Path 1) : (∫⁻ y : ℝ, Φ (g + y • timePath 1)) = 0 := by
    simp_rw [hΦshift]
    rw [lintegral_sub_left_eq_self
      (fun x : ℝ => if DifferentiableAt ℝ (F g) x then (0 : ℝ≥0∞) else 1) a]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [(hl g).ae_differentiableAt] with x hx
    simp only [hx, ↓reduceIte, Pi.zero_apply]
  have hzero : (∫⁻ y : ℝ, ∫⁻ ω, Φ (bridgeUnitPath B ω + y • timePath 1) ∂μ) = 0 := by
    rw [← bridge_lintegral_swap hB hΦ]
    simp_rw [hpath]
    simp
  have hweight : AEMeasurable (fun ω => gaussianEndpointWeight (B 1 ω) *
      Φ (unitPath (processPath B ω) 1)) μ :=
    (measurable_gaussianEndpointWeight.comp_aemeasurable (hB.aemeasurable 1)).mul
      (hΦ.comp_aemeasurable (aemeasurable_brownianUnitPath hB 1))
  have hz : (fun ω => gaussianEndpointWeight (B 1 ω) *
      Φ (unitPath (processPath B ω) 1)) =ᵐ[μ] 0 := by
    apply (lintegral_eq_zero_iff' hweight).mp
    rw [← brownian_bridge_endpoint_lintegral hB hΦ]
    exact hzero
  filter_upwards [hz] with ω hω
  by_contra hn
  have hp : gaussianEndpointWeight (B 1 ω) ≠ 0 := by
    unfold gaussianEndpointWeight
    apply (ENNReal.ofReal_pos.mpr _).ne'
    positivity
  exact hp (by simpa only [Φ, hn, ↓reduceIte, mul_one, Pi.zero_apply] using hω)

/-- Each fixed drift has its own full-measure differentiability event. -/
theorem brownian_upper_lower_differentiable_ae (hB : IsBrownianReal B μ) (a : ℝ) :
    ∀ᵐ ω ∂μ,
      DifferentiableAt ℝ (slopeUpper (unitPath (processPath B ω) 1)) a ∧
      DifferentiableAt ℝ (slopeLower (unitPath (processPath B ω) 1)) a := by
  filter_upwards [brownian_envelope_differentiable_ae hB slopeUpper
    slopeUpper_joint_lipschitz.continuous slopeUpper_lipschitz slopeUpper_add_drift a,
    brownian_envelope_differentiable_ae hB slopeLower
    slopeLower_joint_lipschitz.continuous slopeLower_lipschitz slopeLower_add_drift a]
    with ω hu hl
  exact ⟨hu, hl⟩

def upperTime (g : Path 1) (a : ℝ) : RangeTime := Classical.choose (slopeUpper_attained g a)
def lowerTime (g : Path 1) (a : ℝ) : RangeTime := Classical.choose (slopeLower_attained g a)

theorem upperTime_attains (g : Path 1) (a : ℝ) :
    slopeResidual g a (upperTime g a) = slopeUpper g a :=
  Classical.choose_spec (slopeUpper_attained g a)

theorem lowerTime_attains (g : Path 1) (a : ℝ) :
    slopeResidual g a (lowerTime g a) = slopeLower g a :=
  Classical.choose_spec (slopeLower_attained g a)

theorem upperTime_unique_of_differentiable (g : Path 1) {a : ℝ}
    (ha : DifferentiableAt ℝ (slopeUpper g) a) {t : RangeTime}
    (ht : slopeResidual g a t = slopeUpper g a) : t = upperTime g a := by
  apply Subtype.ext
  have h₁ := slopeUpper_deriv_of_maximizer g ha ht
  have h₂ := slopeUpper_deriv_of_maximizer g ha (upperTime_attains g a)
  linarith

theorem lowerTime_unique_of_differentiable (g : Path 1) {a : ℝ}
    (ha : DifferentiableAt ℝ (slopeLower g) a) {t : RangeTime}
    (ht : slopeResidual g a t = slopeLower g a) : t = lowerTime g a := by
  apply Subtype.ext
  have h₁ := slopeLower_deriv_of_minimizer g ha ht
  have h₂ := slopeLower_deriv_of_minimizer g ha (lowerTime_attains g a)
  linarith

theorem slopeRange_deriv_eq_extremal_times (g : Path 1) {a : ℝ}
    (hu : DifferentiableAt ℝ (slopeUpper g) a) (hl : DifferentiableAt ℝ (slopeLower g) a) :
    deriv (slopeRange g) a = (lowerTime g a : ℝ) - (upperTime g a : ℝ) := by
  change deriv (slopeUpper g - slopeLower g) a = _
  rw [deriv_sub hu hl, slopeUpper_deriv_of_maximizer g hu (upperTime_attains g a),
    slopeLower_deriv_of_minimizer g hl (lowerTime_attains g a)]
  ring

/-- At every fixed drift the actual residual maximum and minimum each have a unique time. -/
theorem brownian_extrema_unique_ae (hB : IsBrownianReal B μ) (a : ℝ) :
    ∀ᵐ ω ∂μ,
      (∃! t : RangeTime, slopeResidual (unitPath (processPath B ω) 1) a t =
        slopeUpper (unitPath (processPath B ω) 1) a) ∧
      (∃! t : RangeTime, slopeResidual (unitPath (processPath B ω) 1) a t =
        slopeLower (unitPath (processPath B ω) 1) a) := by
  filter_upwards [brownian_upper_lower_differentiable_ae hB a] with ω hω
  exact ⟨⟨upperTime _ a, upperTime_attains _ a,
    fun _ ht => upperTime_unique_of_differentiable _ hω.1 ht⟩,
    ⟨lowerTime _ a, lowerTime_attains _ a,
    fun _ ht => lowerTime_unique_of_differentiable _ hω.2 ht⟩⟩

theorem brownian_slopeRange_deriv_eq_extremal_times_ae (hB : IsBrownianReal B μ) (a : ℝ) :
    ∀ᵐ ω ∂μ, deriv (slopeRange (unitPath (processPath B ω) 1)) a =
      (lowerTime (unitPath (processPath B ω) 1) a : ℝ) -
        (upperTime (unitPath (processPath B ω) 1) a : ℝ) := by
  filter_upwards [brownian_upper_lower_differentiable_ae hB a] with ω hω
  exact slopeRange_deriv_eq_extremal_times _ hω.1 hω.2

/-- The actual selected maximizing time is a.e. measurable; arbitrary tie choices
do not matter because ties have already been proved null at each fixed drift. -/
theorem aemeasurable_brownian_upperTime (hB : IsBrownianReal B μ) (a : ℝ) :
    AEMeasurable (fun ω => (upperTime (unitPath (processPath B ω) 1) a : ℝ)) μ := by
  have hm : Measurable (fun g : Path 1 => -deriv (slopeUpper g) a) :=
    (measurable_slopeUpper_deriv_joint.comp (measurable_id.prodMk measurable_const)).neg
  apply (hm.comp_aemeasurable (aemeasurable_brownianUnitPath hB 1)).congr
  filter_upwards [brownian_upper_lower_differentiable_ae hB a] with ω hω
  dsimp only [Function.comp_def]
  simp only [NNReal.coe_one]
  rw [slopeUpper_deriv_of_maximizer _ hω.1 (upperTime_attains _ a), neg_neg]

theorem aemeasurable_brownian_lowerTime (hB : IsBrownianReal B μ) (a : ℝ) :
    AEMeasurable (fun ω => (lowerTime (unitPath (processPath B ω) 1) a : ℝ)) μ := by
  have hm : Measurable (fun g : Path 1 => -deriv (slopeLower g) a) :=
    (measurable_slopeLower_deriv_joint.comp (measurable_id.prodMk measurable_const)).neg
  apply (hm.comp_aemeasurable (aemeasurable_brownianUnitPath hB 1)).congr
  filter_upwards [brownian_upper_lower_differentiable_ae hB a] with ω hω
  dsimp only [Function.comp_def]
  simp only [NNReal.coe_one]
  rw [slopeLower_deriv_of_minimizer _ hω.2 (lowerTime_attains _ a), neg_neg]

end BrownianAffine
