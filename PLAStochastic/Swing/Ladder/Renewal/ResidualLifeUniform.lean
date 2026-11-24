import PLAStochastic.Swing.Ladder.Renewal.ResidualLife
import PLAStochastic.Swing.Ladder.Renewal.BlanchetGlynnInterface

/-! # The residual-life comparison, uniformly over a compact drift interval

`renewalOvershootTail_sub_equilibrium_le` bounds the distance between the
residual-life tail at level `b` and the equilibrium overshoot tail by an
exponentially small term plus two far-tail functionals of the ladder height.
This file instantiates that bound for the actual strict ascending ladder
heights of the positive-drift Gaussian walk and makes every constant in it
uniform over `a ∈ [δ,M]` and over the argument `t ≥ 0`, using only the
already-proved uniform second moment and the uniform mean lower bound.

The renewal expansion itself is still carried as the hypothesis
`UniformLadderRenewalExpansion`; nothing else here is assumed.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-! ### Mean and second moment as Bochner integrals -/

theorem ladderMean_eq_integral {ν : Measure ℝ} (hnn : 0 ≤ᵐ[ν] fun x : ℝ => x)
    (hid : Integrable (fun x : ℝ => x) ν) :
    ladderMean ν = ∫ x, x ∂ν := by
  rw [ladderMean, ladderMeanENN, ← ofReal_integral_eq_lintegral_ofReal hid hnn,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn)]

theorem ladderSecondMoment_eq_integral {ν : Measure ℝ}
    (hsq : Integrable (fun x : ℝ => x^2) ν) :
    ladderSecondMoment ν = ∫ x, x^2 ∂ν := by
  rw [ladderSecondMoment,
    ← ofReal_integral_eq_lintegral_ofReal hsq (ae_of_all _ fun x => sq_nonneg x),
    ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg x)]

/-! ### Chebyshev estimates for the far part -/

/-- The tail mass above a positive level is at most the second moment over the
square of the level. -/
theorem measureReal_Ioi_le_sq_moment {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x^2) ν) {s : ℝ} (hs : 0 < s) :
    ν.real (Ioi s) ≤ (∫ x, x^2 ∂ν) / s^2 := by
  have hconst : IntegrableOn (fun _ : ℝ => s^2) (Ioi s) ν := (integrable_const _).integrableOn
  have hlow : ∫ _x in Ioi s, (s^2 : ℝ) ∂ν ≤ ∫ x in Ioi s, x^2 ∂ν := by
    refine setIntegral_mono_on hconst hsq.integrableOn measurableSet_Ioi (fun x hx => ?_)
    have hx' : s < x := hx
    nlinarith
  rw [setIntegral_const, smul_eq_mul] at hlow
  have hup : ∫ x in Ioi s, x^2 ∂ν ≤ ∫ x, x^2 ∂ν :=
    setIntegral_le_integral hsq (ae_of_all _ fun x => sq_nonneg x)
  rw [le_div_iff₀ (by positivity)]
  calc ν.real (Ioi s) * s^2 = ν.real (Ioi s) * s^2 := rfl
    _ ≤ ∫ x, x^2 ∂ν := by linarith

/-- The far part of the first moment is at most the second moment over the
level. -/
theorem setIntegral_sub_le_sq_moment {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hid : Integrable (fun x : ℝ => x) ν) (hsq : Integrable (fun x : ℝ => x^2) ν)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 < s) :
    (∫ h in Ioi s, (h-t) ∂ν) ≤ (∫ x, x^2 ∂ν) / s := by
  have hsub : IntegrableOn (fun h : ℝ => h-t) (Ioi s) ν :=
    hid.integrableOn.sub (integrable_const t).integrableOn
  have hdiv : IntegrableOn (fun h : ℝ => h^2/s) (Ioi s) ν := hsq.integrableOn.div_const s
  calc (∫ h in Ioi s, (h-t) ∂ν) ≤ ∫ h in Ioi s, h^2/s ∂ν := by
        refine setIntegral_mono_on hsub hdiv measurableSet_Ioi (fun h hh => ?_)
        have hh' : s < h := hh
        rw [le_div_iff₀ hs]
        nlinarith
    _ = (∫ h in Ioi s, h^2 ∂ν)/s := by rw [integral_div]
    _ ≤ (∫ x, x^2 ∂ν)/s := by
        refine div_le_div_of_nonneg_right ?_ hs.le
        exact setIntegral_le_integral hsq (ae_of_all _ fun x => sq_nonneg x)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-! ### The Gaussian ladder law: nonnegativity, moments, renewal mass -/

theorem gaussianAscendingLadderLaw_ae_nonneg (hX : ∀ n, Measurable (X n)) (a : ℝ) :
    0 ≤ᵐ[gaussianAscendingLadderLaw X μ a] fun x : ℝ => x := by
  have hmeas : Measurable (gaussianAscendingLadderHeight X a) :=
    gaussianAscendingLadderHeight_measurable hX a
  rw [Filter.EventuallyLE, ae_iff]
  have hset : {x : ℝ | ¬ (0 : ℝ) ≤ x} = {x : ℝ | x < 0} := by
    ext x
    simp
  have hmsIio : MeasurableSet {x : ℝ | x < 0} := by
    have h : {x : ℝ | x < 0} = Iio (0 : ℝ) := by ext x; simp
    rw [h]
    exact measurableSet_Iio
  have hpre : (gaussianAscendingLadderHeight X a) ⁻¹' {x : ℝ | x < 0} = (∅ : Set Ω) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact gaussianAscendingLadderHeight_nonneg (X := X) a ω
  show gaussianAscendingLadderLaw X μ a {x : ℝ | ¬ (0 : ℝ) ≤ x} = 0
  rw [hset, show gaussianAscendingLadderLaw X μ a =
    μ.map (gaussianAscendingLadderHeight X a) from rfl,
    Measure.map_apply hmeas hmsIio, hpre, measure_empty]

theorem gaussianAscendingLadderLaw_id_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) :
    Integrable (fun x : ℝ => x) (gaussianAscendingLadderLaw X μ a) :=
  (integrable_map_measure aestronglyMeasurable_id
      (gaussianAscendingLadderHeight_measurable hX a).aemeasurable).mpr
    (gaussianAscendingLadderHeight_integrable_compact hX hi hG hδ hδa haM)

theorem gaussianAscendingLadderLaw_sq_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) :
    Integrable (fun x : ℝ => x^2) (gaussianAscendingLadderLaw X μ a) := by
  refine (integrable_map_measure ?_
      (gaussianAscendingLadderHeight_measurable hX a).aemeasurable).mpr ?_
  · exact (measurable_id.pow_const 2).aestronglyMeasurable
  · exact gaussianAscendingLadderHeight_pow_integrable hX hi hG hδ hδa haM 2

theorem gaussianAscendingLadderLaw_sq_integral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) :
    (∫ x, x^2 ∂(gaussianAscendingLadderLaw X μ a)) ≤
      gaussianAscendingLadderMomentBound δ M 2 := by
  have hasm : AEStronglyMeasurable (fun y : ℝ => y^2)
      (μ.map (gaussianAscendingLadderHeight X a)) :=
    (measurable_id.pow_const 2).aestronglyMeasurable
  have hmap : (∫ x, x^2 ∂(gaussianAscendingLadderLaw X μ a)) =
      ∫ ω, gaussianAscendingLadderHeight X a ω ^ 2 ∂μ := by
    rw [show gaussianAscendingLadderLaw X μ a =
      μ.map (gaussianAscendingLadderHeight X a) from rfl,
      integral_map (f := fun y : ℝ => y^2)
        (gaussianAscendingLadderHeight_measurable hX a).aemeasurable hasm]
  rw [hmap]
  exact gaussianAscendingLadderHeight_pow_integral_le hX hi hG hδ hδa haM 2

theorem gaussianAscendingLadderMomentBound_two_nonneg
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) :
    0 ≤ gaussianAscendingLadderMomentBound δ M 2 := by
  have h := gaussianAscendingLadderLaw_sq_integral_le hX hi hG hδ hδa haM (μ := μ)
  have h0 : (0 : ℝ) ≤ ∫ x, x^2 ∂(gaussianAscendingLadderLaw X μ a) :=
    integral_nonneg fun x => sq_nonneg x
  linarith

/-- The ladder mean of the actual Gaussian family is bounded below by the
common density, uniformly on `[δ,M]`. -/
theorem ladderMean_gaussianAscendingLadderLaw_ge
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) :
    gaussianAscendingLadderCommonDensity M ≤ ladderMean (gaussianAscendingLadderLaw X μ a) := by
  have hasm : AEStronglyMeasurable (fun y : ℝ => y)
      (μ.map (gaussianAscendingLadderHeight X a)) := aestronglyMeasurable_id
  have hmap : (∫ x, x ∂(gaussianAscendingLadderLaw X μ a)) =
      ∫ ω, gaussianAscendingLadderHeight X a ω ∂μ := by
    rw [show gaussianAscendingLadderLaw X μ a =
      μ.map (gaussianAscendingLadderHeight X a) from rfl,
      integral_map (f := fun y : ℝ => y)
        (gaussianAscendingLadderHeight_measurable hX a).aemeasurable hasm]
  rw [ladderMean_eq_integral (gaussianAscendingLadderLaw_ae_nonneg hX a)
      (gaussianAscendingLadderLaw_id_integrable hX hi hG hδ hδa haM), hmap]
  exact gaussianAscendingLadderHeight_mean_ge hX hi hG hδ hδa haM

/-- The constant term of the renewal expansion is uniformly bounded on the
compact drift interval. -/
theorem ladderRenewalConstant_gaussianAscendingLadderLaw_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) :
    |ladderRenewalConstant (gaussianAscendingLadderLaw X μ a)| ≤
      gaussianAscendingLadderMomentBound δ M 2 /
        (2*gaussianAscendingLadderCommonDensity M^2) := by
  have hc := gaussianAscendingLadderCommonDensity_pos M
  have hmean := ladderMean_gaussianAscendingLadderLaw_ge hX hi hG hδ hδa haM
  have hmean0 : 0 < ladderMean (gaussianAscendingLadderLaw X μ a) := lt_of_lt_of_le hc hmean
  have hsecond : ladderSecondMoment (gaussianAscendingLadderLaw X μ a) ≤
      gaussianAscendingLadderMomentBound δ M 2 := by
    rw [ladderSecondMoment_eq_integral (gaussianAscendingLadderLaw_sq_integrable hX hi hG hδ hδa haM)]
    exact gaussianAscendingLadderLaw_sq_integral_le hX hi hG hδ hδa haM
  have hsecond0 : 0 ≤ ladderSecondMoment (gaussianAscendingLadderLaw X μ a) := by
    rw [ladderSecondMoment_eq_integral (gaussianAscendingLadderLaw_sq_integrable hX hi hG hδ hδa haM)]
    exact integral_nonneg fun x => sq_nonneg x
  have hnn : 0 ≤ ladderRenewalConstant (gaussianAscendingLadderLaw X μ a) := by
    rw [ladderRenewalConstant]
    positivity
  rw [abs_of_nonneg hnn, ladderRenewalConstant]
  refine div_le_div₀ (by linarith) hsecond (by positivity) ?_
  nlinarith

/-- The renewal mass of every initial window is finite. -/
theorem gaussianAscendingLadderRenewal_Icc_ne_top
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {M a : ℝ} (ha : 0 < a) (haM : a ≤ M) (u : ℝ) :
    ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a) (Icc 0 u) ≠ ⊤ := by
  rcases le_or_gt 0 u with hu | hu
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (gaussianAscendingLadderRenewal_Icc_le hX hi hG ha haM hu)
  · rw [Icc_eq_empty (by linarith), measure_empty]
    exact ENNReal.zero_ne_top

theorem gaussianAscendingLadderLaw_max_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) (t : ℝ) :
    Integrable (fun h : ℝ => max (h-t) 0) (gaussianAscendingLadderLaw X μ a) := by
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  have hid := gaussianAscendingLadderLaw_id_integrable hX hi hG hδ hδa haM
  have hdom : Integrable (fun h : ℝ => |h| + |t|) (gaussianAscendingLadderLaw X μ a) :=
    hid.abs.add (integrable_const |t|)
  refine Integrable.mono' hdom ?_ ?_
  · exact ((measurable_id.sub measurable_const).max measurable_const).aestronglyMeasurable
  · filter_upwards with h
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    have h1 : max (h-t) 0 ≤ |h-t| := max_le (le_abs_self _) (abs_nonneg _)
    have h2 : |h-t| ≤ |h| + |t| := by
      calc |h-t| = |h + (-t)| := by rw [sub_eq_add_neg]
        _ ≤ |h| + |-t| := abs_add_le _ _
        _ = |h| + |t| := by rw [abs_neg]
    linarith

/-! ### The uniform bound -/

/-- The explicit uniform bound of the residual-life comparison: it depends only
on the drift interval, the expansion constants and the passage level. -/
noncomputable def gaussianResidualLifeBound (δ M C c b : ℝ) : ℝ :=
  2*C*Real.exp (-c*(b/2)) +
    (3*C + gaussianAscendingLadderMomentBound δ M 2 /
        (2*gaussianAscendingLadderCommonDensity M^2)) *
      (4*gaussianAscendingLadderMomentBound δ M 2/b^2) +
    4*gaussianAscendingLadderMomentBound δ M 2 /
      (gaussianAscendingLadderCommonDensity M * b)

/-- Instantiation of `renewalOvershootTail_sub_equilibrium_le` for the actual
Gaussian ladder family: the residual-life tail at level `b` differs from the
equilibrium overshoot tail by at most `gaussianResidualLifeBound`, which does
not depend on the drift `a ∈ [δ,M]` nor on the argument `t ≥ 0`. -/
theorem gaussianAscendingLadder_residual_life_uniform_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M C c : ℝ} (hδ : 0 < δ)
    (hexp : UniformLadderRenewalExpansion (gaussianAscendingLadderLaw X μ) (Icc δ M) C c)
    {a : ℝ} (hδa : δ ≤ a) (haM : a ≤ M) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    |(renewalOvershootTail (gaussianAscendingLadderLaw X μ a) b t).toReal -
        (equilibriumOvershootTail (gaussianAscendingLadderLaw X μ a) t).toReal| ≤
      gaussianResidualLifeBound δ M C c b := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  have hC : 0 ≤ C := hexp.2.1
  have hc := gaussianAscendingLadderCommonDensity_pos M
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  set B := gaussianAscendingLadderMomentBound δ M 2 with hBdef
  set cM := gaussianAscendingLadderCommonDensity M with hcMdef
  have hB0 : 0 ≤ B := gaussianAscendingLadderMomentBound_two_nonneg hX hi hG hδ hδa haM
  have hid := gaussianAscendingLadderLaw_id_integrable hX hi hG hδ hδa haM
  have hsq := gaussianAscendingLadderLaw_sq_integrable hX hi hG hδ hδa haM
  have hsqle : (∫ x, x^2 ∂ν) ≤ B :=
    gaussianAscendingLadderLaw_sq_integral_le hX hi hG hδ hδa haM
  have hmean := ladderMean_gaussianAscendingLadderLaw_ge hX hi hG hδ hδa haM
  have hmean0 : 0 < ladderMean ν := lt_of_lt_of_le hc hmean
  have hK := ladderRenewalConstant_gaussianAscendingLadderLaw_le hX hi hG hδ hδa haM
  have hs : 0 < t + b/2 := by linarith
  have hsb : b/2 ≤ t + b/2 := by linarith
  have hbase := renewalOvershootTail_sub_equilibrium_le hexp
    (show a ∈ Icc δ M from ⟨hδa, haM⟩)
    (gaussianAscendingLadderRenewal_Icc_ne_top hX hi hG ha haM)
    (gaussianAscendingLadderLaw_max_integrable hX hi hG hδ hδa haM t) hb.le
  refine hbase.trans ?_
  -- the three terms, each made uniform
  have htail : ν.real (Ioi (t+b/2)) ≤ 4*B/b^2 := by
    refine (measureReal_Ioi_le_sq_moment hsq hs).trans ?_
    have h1 : (∫ x, x^2 ∂ν)/(t+b/2)^2 ≤ B/(b/2)^2 := by
      refine div_le_div₀ (by linarith) hsqle (by positivity) ?_
      nlinarith
    calc (∫ x, x^2 ∂ν)/(t+b/2)^2 ≤ B/(b/2)^2 := h1
      _ = 4*B/b^2 := by field_simp; ring
  have hfar : (∫ h in Ioi (t+b/2), (h-t) ∂ν) ≤ 2*B/b := by
    refine (setIntegral_sub_le_sq_moment hid hsq ht hs).trans ?_
    have h1 : (∫ x, x^2 ∂ν)/(t+b/2) ≤ B/(b/2) :=
      div_le_div₀ hB0 hsqle (by linarith) hsb
    calc (∫ x, x^2 ∂ν)/(t+b/2) ≤ B/(b/2) := h1
      _ = 2*B/b := by field_simp
  have hfar0 : 0 ≤ ∫ h in Ioi (t+b/2), (h-t) ∂ν := by
    refine setIntegral_nonneg measurableSet_Ioi (fun h hh => ?_)
    have hh' : t+b/2 < h := hh
    linarith
  have hKcoef : (3*C + |ladderRenewalConstant ν|) ≤ 3*C + B/(2*cM^2) := by linarith
  have hKcoef0 : (0 : ℝ) ≤ 3*C + |ladderRenewalConstant ν| := by
    have := abs_nonneg (ladderRenewalConstant ν)
    linarith
  have hstep2 : (3*C + |ladderRenewalConstant ν|) * ν.real (Ioi (t+b/2)) ≤
      (3*C + B/(2*cM^2)) * (4*B/b^2) :=
    mul_le_mul hKcoef htail measureReal_nonneg (hKcoef0.trans hKcoef)
  have hmuinv : 2/ladderMean ν ≤ 2/cM := by
    rw [div_le_div_iff₀ hmean0 hc]
    linarith
  have hstep3 : (2/ladderMean ν) * (∫ h in Ioi (t+b/2), (h-t) ∂ν) ≤ 4*B/(cM*b) := by
    have h1 : (2/ladderMean ν) * (∫ h in Ioi (t+b/2), (h-t) ∂ν) ≤ (2/cM) * (2*B/b) :=
      mul_le_mul hmuinv hfar hfar0 (by positivity)
    calc (2/ladderMean ν) * (∫ h in Ioi (t+b/2), (h-t) ∂ν) ≤ (2/cM) * (2*B/b) := h1
      _ = 4*B/(cM*b) := by field_simp; ring
  rw [gaussianResidualLifeBound, ← hBdef, ← hcMdef]
  linarith

/-- Blanchet--Glynn's own normalisation, specialised to the Gaussian ladder
family: because the ladder mean is bounded below by the common density
uniformly on `[δ,M]`, the `μ²`-scaled remainder bound of the cited theorem
yields the project's expansion with the explicit constant `K / c_M²`. -/
theorem gaussianAscendingLadder_uniformExpansion_of_bg
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M K c : ℝ} (hδ : 0 < δ)
    (h : BGUniformRenewalRemainder (gaussianAscendingLadderLaw X μ) (Icc δ M) K c) :
    UniformLadderRenewalExpansion (gaussianAscendingLadderLaw X μ) (Icc δ M)
      (K / gaussianAscendingLadderCommonDensity M ^ 2) c :=
  uniformLadderRenewalExpansion_of_bgUniformRenewalRemainder
    (gaussianAscendingLadderCommonDensity_pos M)
    (fun _a ha => ladderMean_gaussianAscendingLadderLaw_ge hX hi hG hδ ha.1 ha.2) h

/-- The whole chain from Blanchet--Glynn's remainder bound, in its own
normalisation, to the uniform residual-life comparison for the actual Gaussian
ladder family.  The only input is the cited renewal remainder. -/
theorem gaussianAscendingLadder_residual_life_uniform_le_of_bg
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M K c : ℝ} (hδ : 0 < δ)
    (h : BGUniformRenewalRemainder (gaussianAscendingLadderLaw X μ) (Icc δ M) K c)
    {a : ℝ} (hδa : δ ≤ a) (haM : a ≤ M) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    |(renewalOvershootTail (gaussianAscendingLadderLaw X μ a) b t).toReal -
        (equilibriumOvershootTail (gaussianAscendingLadderLaw X μ a) t).toReal| ≤
      gaussianResidualLifeBound δ M
        (K / gaussianAscendingLadderCommonDensity M ^ 2) c b :=
  gaussianAscendingLadder_residual_life_uniform_le hX hi hG hδ
    (gaussianAscendingLadder_uniformExpansion_of_bg hX hi hG hδ h) hδa haM ht hb

/-- The uniform bound tends to zero, so the residual-life tail converges to the
equilibrium overshoot tail uniformly in the drift and in the argument. -/
theorem gaussianResidualLifeBound_tendsto {δ M C c : ℝ} (hc : 0 < c) :
    Tendsto (gaussianResidualLifeBound δ M C c) atTop (𝓝 0) := by
  have hcm := gaussianAscendingLadderCommonDensity_pos M
  set B := gaussianAscendingLadderMomentBound δ M 2 with hBdef
  set cM := gaussianAscendingLadderCommonDensity M with hcMdef
  have hhalf : Tendsto (fun b : ℝ => b/2) atTop atTop := by
    simpa only [id] using tendsto_id.atTop_div_const (by norm_num : (0:ℝ) < 2)
  have hmul : Tendsto (fun b : ℝ => c*(b/2)) atTop atTop := hhalf.const_mul_atTop hc
  have hneg : Tendsto (fun b : ℝ => -c*(b/2)) atTop atBot := by
    refine Filter.Tendsto.congr (fun b => ?_) (tendsto_neg_atTop_atBot.comp hmul)
    simp only [Function.comp_def]
    ring
  have h1 : Tendsto (fun b : ℝ => 2*C*Real.exp (-c*(b/2))) atTop (𝓝 0) := by
    have he : Tendsto (fun b : ℝ => Real.exp (-c*(b/2))) atTop (𝓝 0) := by
      simpa only [Function.comp_def] using Real.tendsto_exp_atBot.comp hneg
    simpa only [mul_zero] using (tendsto_const_nhds (x := 2*C)).mul he
  have hsq : Tendsto (fun b : ℝ => b^2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have h2 : Tendsto (fun b : ℝ =>
      (3*C + B/(2*cM^2)) * (4*B/b^2)) atTop (𝓝 0) := by
    have hd : Tendsto (fun b : ℝ => 4*B/b^2) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds hsq
    simpa only [mul_zero] using (tendsto_const_nhds (x := 3*C + B/(2*cM^2))).mul hd
  have h3 : Tendsto (fun b : ℝ => 4*B/(cM*b)) atTop (𝓝 0) := by
    have hden : Tendsto (fun b : ℝ => cM*b) atTop atTop := by
      simpa only [id] using tendsto_id.const_mul_atTop hcm
    exact Filter.Tendsto.div_atTop tendsto_const_nhds hden
  have heq : gaussianResidualLifeBound δ M C c = fun b : ℝ =>
      2*C*Real.exp (-c*(b/2)) + (3*C + B/(2*cM^2)) * (4*B/b^2) + 4*B/(cM*b) := rfl
  rw [heq]
  simpa only [add_zero] using (h1.add h2).add h3

end SwingRepair
