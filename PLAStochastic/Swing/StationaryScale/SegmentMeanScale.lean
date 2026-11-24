import PLAStochastic.Swing.StationaryScale.NegativeMarginMoment
import PLAStochastic.Swing.SecondSegment.FrozenMeanBridge

/-! # Theorem 4.2: the stationary mean is `O(E log E)`

The uniform conditional mean bound is integrated against `π_E`, the positive
margin is replaced by the slope envelope and the negative margin, and the
resulting residual coefficient is absorbed.  All inputs are the stationary
estimates proved in the preceding modules.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The absolute bound on the mean fresh-walk slope envelope. -/
def stationaryEnvelopeMeanBound : ℝ :=
  nativeGaussianEnvelopeExpTailConstant*expTailMomentSum 1 1

theorem stationaryEnvelopeMeanBound_nonneg : 0 ≤ stationaryEnvelopeMeanBound := by
  unfold stationaryEnvelopeMeanBound
  exact mul_nonneg nativeGaussianEnvelopeExpTailConstant_nonneg (expTailMomentSum_nonneg _ _)

theorem stationary_envelope_mean_le
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) :
    (∫ ω, nativeGaussianEnvelope X ω ∂μ) ≤ stationaryEnvelopeMeanBound := by
  simpa only [pow_one, stationaryEnvelopeMeanBound] using
    nativeGaussianEnvelope_integral_pow_le hX hi hG 1

/-! ### The stationary positive margin -/

theorem stationary_marginPos_integral_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryMarginThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    (∫ y, nativeRestartMarginPos E y ∂π) ≤
      5*(∫ y, nativeRestartExcess E y ∂π) +
        10*stationaryEnvelopeMeanBound + 10 := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEnum : (5120000 : ℝ) ≤ E := by simpa [stationaryMarginThreshold] using hE
  have hEpos : (0 : ℝ) < E := by linarith
  have henvint : Integrable (nativeGaussianEnvelope X) μ := by
    simpa only [pow_one] using nativeGaussianEnvelope_integrable_pow hX hi hG 1
  have hmp_meas : Measurable (nativeRestartMarginPos E) := measurable_nativeRestartMarginPos E
  have hmp_nonneg : ∀ y, 0 ≤ nativeRestartMarginPos E y := fun y => le_max_right _ _
  have hmp_upper : ∀ y, nativeRestartMarginPos E y ≤ E := by
    intro y
    exact max_le (by linarith [abs_nonneg y]) hEpos.le
  have hmp_int : Integrable (nativeRestartMarginPos E) π :=
    Doeblin.integrable_bounded_reward π hmp_meas hmp_nonneg hmp_upper
  have hFm : Measurable
      (fun p : ℝ × Ω => nativeRestartMarginPos E (nativeRestartNext X E p.1 p.2)) :=
    hmp_meas.comp (nativeRestartNext_measurable X hX E)
  have hFx : ∀ x : ℝ, Measurable
      (fun ω : Ω => nativeRestartMarginPos E (nativeRestartNext X E x ω)) :=
    fun x => hFm.comp ((measurable_const (a := x)).prodMk measurable_id)
  have hfm : Measurable
      (fun x : ℝ => ∫ ω, nativeRestartMarginPos E (nativeRestartNext X E x ω) ∂μ) :=
    hFm.stronglyMeasurable.integral_prod_right.measurable
  have hfn : ∀ x : ℝ, 0 ≤ ∫ ω, nativeRestartMarginPos E (nativeRestartNext X E x ω) ∂μ :=
    fun x => integral_nonneg (fun ω => hmp_nonneg _)
  have hslice_int : ∀ x : ℝ, Integrable
      (fun ω => nativeRestartMarginPos E (nativeRestartNext X E x ω)) μ :=
    fun x => Doeblin.integrable_bounded_reward μ (hFx x)
      (fun ω => hmp_nonneg _) (fun ω => hmp_upper _)
  have hfu : ∀ x : ℝ,
      (∫ ω, nativeRestartMarginPos E (nativeRestartNext X E x ω) ∂μ) ≤ E := by
    intro x
    calc (∫ ω, nativeRestartMarginPos E (nativeRestartNext X E x ω) ∂μ)
        ≤ ∫ _ω : Ω, E ∂μ :=
          integral_mono (hslice_int x) (integrable_const E) (fun ω => hmp_upper _)
      _ = E := by simp
  have hf_int : Integrable
      (fun x : ℝ => ∫ ω, nativeRestartMarginPos E (nativeRestartNext X E x ω) ∂μ) π :=
    Doeblin.integrable_bounded_reward π hfm hfn hfu
  have hexc_int : Integrable (nativeRestartExcess E) π :=
    stationary_excess_integrable hX hi hG hE hπ
  have hinner : ∀ x : ℝ,
      (∫ ω, nativeRestartMarginPos E (nativeRestartNext X E x ω) ∂μ) ≤
        5*nativeRestartExcess E x + 10*(∫ ω, nativeGaussianEnvelope X ω ∂μ) + 10 := by
    intro x
    have h1 : Integrable (fun ω : Ω => 10*nativeGaussianEnvelope X ω) μ :=
      henvint.const_mul 10
    have h2 : Integrable (fun _ : Ω => 5*nativeRestartExcess E x) μ := integrable_const _
    have h3 : Integrable (fun _ : Ω => (10 : ℝ)) μ := integrable_const _
    have hae : ∀ᵐ ω ∂μ,
        nativeRestartMarginPos E (nativeRestartNext X E x ω) ≤
          5*nativeRestartExcess E x+10*nativeGaussianEnvelope X ω+10 := by
      filter_upwards [nativeRestartLength_ae_finite hX hi hG hEpos x,
        nativeGaussianEnvelope_bounds_ae hX hi hG] with ω hfin hW
      exact nativeRestart_marginPos_next_le X hEpos.le x ω hW hfin
    have h12 : Integrable
        (fun ω : Ω => 5*nativeRestartExcess E x+10*nativeGaussianEnvelope X ω) μ := h2.add h1
    have h123 : Integrable
        (fun ω : Ω => 5*nativeRestartExcess E x+10*nativeGaussianEnvelope X ω+10) μ :=
      h12.add h3
    have hmono := integral_mono_ae (hslice_int x) h123 hae
    have heq : (∫ ω, (5*nativeRestartExcess E x+10*nativeGaussianEnvelope X ω+10) ∂μ) =
        5*nativeRestartExcess E x+10*(∫ ω, nativeGaussianEnvelope X ω ∂μ)+10 := by
      rw [integral_add h12 h3, integral_add h2 h1, integral_const, integral_const,
        integral_const_mul]
      simp
    rw [heq] at hmono
    exact hmono
  have hg1 : Integrable (fun x : ℝ => 5*nativeRestartExcess E x) π := hexc_int.const_mul 5
  have hg2 : Integrable
      (fun _ : ℝ => 10*(∫ ω, nativeGaussianEnvelope X ω ∂μ)) π := integrable_const _
  have hg3 : Integrable (fun _ : ℝ => (10 : ℝ)) π := integrable_const _
  have hg12 : Integrable (fun x : ℝ => 5*nativeRestartExcess E x +
      10*(∫ ω, nativeGaussianEnvelope X ω ∂μ)) π := hg1.add hg2
  have hg123 : Integrable (fun x : ℝ => 5*nativeRestartExcess E x +
      10*(∫ ω, nativeGaussianEnvelope X ω ∂μ) + 10) π := hg12.add hg3
  have hmono := integral_mono hf_int hg123 hinner
  have heq2 : (∫ x, (5*nativeRestartExcess E x +
      10*(∫ ω, nativeGaussianEnvelope X ω ∂μ) + 10) ∂π) =
      5*(∫ y, nativeRestartExcess E y ∂π) +
        10*(∫ ω, nativeGaussianEnvelope X ω ∂μ) + 10 := by
    rw [integral_add hg12 hg3, integral_add hg1 hg2, integral_const, integral_const,
      integral_const_mul]
    simp
  rw [heq2] at hmono
  have henvle := stationary_envelope_mean_le hX hi hG (μ := μ)
  rw [nativeRestart_invariant_integral_eq_fresh hX hπ hmp_meas hmp_int]
  linarith

/-! ### The uniform conditional mean integrated against `π_E` -/

theorem stationary_mean_le_marginPos [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE1 : 1 ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π] :
    (∫ x, nativeRestartMean X μ E x ∂π) ≤
      frozenUniformMeanConstant*E*Real.log (Real.exp 1*E)*
        (1+∫ x, nativeRestartMarginPos E x ∂π) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEpos : (0 : ℝ) < E := by linarith
  have hKf : 0 < frozenUniformMeanConstant := frozenUniformMeanConstant_pos
  have hlog : 0 ≤ Real.log (Real.exp 1*E) := by
    apply Real.log_nonneg
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hmp_meas : Measurable (nativeRestartMarginPos E) := measurable_nativeRestartMarginPos E
  have hmp_nonneg : ∀ y, 0 ≤ nativeRestartMarginPos E y := fun y => le_max_right _ _
  have hmp_upper : ∀ y, nativeRestartMarginPos E y ≤ E := by
    intro y
    exact max_le (by linarith [abs_nonneg y]) hEpos.le
  have hmp_int : Integrable (nativeRestartMarginPos E) π :=
    Doeblin.integrable_bounded_reward π hmp_meas hmp_nonneg hmp_upper
  have hmean_meas : Measurable (nativeRestartMean X μ E) := nativeRestartMean_measurable hX E
  have hbounds := nativeRestartMean_bounds hX hi hG hEpos
  have hmean_nonneg : ∀ x, 0 ≤ nativeRestartMean X μ E x :=
    fun x => (by norm_num : (0 : ℝ) ≤ 1).trans (hbounds x).1
  have hmean_int : Integrable (nativeRestartMean X μ E) π :=
    Doeblin.integrable_bounded_reward π hmean_meas hmean_nonneg (fun x => (hbounds x).2)
  have hpoint : ∀ x : ℝ, nativeRestartMean X μ E x ≤
      frozenUniformMeanConstant*E*Real.log (Real.exp 1*E)*
        (1+nativeRestartMarginPos E x) := by
    intro x
    have hfr := frozenPrefixLength_uniform_mean_bound hX hi hG (E-|x|) hE1
    rw [nativeRestartMean_eq_frozen_margin hX hi hG E x]
    calc (∫ ω, frozenPrefixLengthReal X (E-|x|) E ω ∂μ)
        ≤ frozenUniformMeanConstant*E*(1+max (E-|x|) 0)*Real.log (Real.exp 1*E) := hfr
      _ = frozenUniformMeanConstant*E*Real.log (Real.exp 1*E)*
            (1+nativeRestartMarginPos E x) := by
          rw [nativeRestartMarginPos]
          ring
  have hgint : Integrable (fun x : ℝ =>
      frozenUniformMeanConstant*E*Real.log (Real.exp 1*E)*(1+nativeRestartMarginPos E x)) π :=
    ((integrable_const (1 : ℝ)).add hmp_int).const_mul _
  have hmono := integral_mono hmean_int hgint hpoint
  rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hmp_int, integral_const] at hmono
  simpa using hmono

/-- The logarithm grows slower than any cube root: this is the only growth
comparison needed to absorb the residual coefficient. -/
theorem stationary_log_cube_le {E : ℝ} (hE1 : 1 ≤ E) : (Real.log E)^3/27 ≤ E := by
  have hEpos : (0 : ℝ) < E := by linarith
  have hL0 : 0 ≤ Real.log E := Real.log_nonneg hE1
  have hcube : (Real.exp (Real.log E/3))^3 = Real.exp (Real.log E) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hEeq : Real.exp (Real.log E) = E := Real.exp_log hEpos
  have hb : Real.log E/3 ≤ Real.exp (Real.log E/3) := by
    have := Real.add_one_le_exp (Real.log E/3)
    linarith
  have hpow : (Real.log E/3)^3 ≤ (Real.exp (Real.log E/3))^3 :=
    pow_le_pow_left₀ (by linarith) hb 3
  rw [hcube, hEeq] at hpow
  nlinarith

/-! ### Absorption and the scale bound -/

def stationaryAbsorptionConstant : ℝ :=
  135*frozenUniformMeanConstant*
    (20*stationaryBadBranchConstant+4*Real.exp 1*stationaryGeomExpSum)

def stationaryScaleThreshold : ℝ :=
  max (max stationaryMarginThreshold (Real.exp 1))
    (Real.exp (2*stationaryAbsorptionConstant))

def stationaryScaleConstant : ℝ :=
  4*frozenUniformMeanConstant*
    (11+5*stationaryMarginMomentConstant+10*stationaryEnvelopeMeanBound)

/-- Theorem 4.2, mean part: the stationary expected segment length of the
actual constrained-SSE restart chain is at most `C E log E`. -/
theorem nativeRestart_stationary_mean_scale [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    (∫ x, nativeRestartMean X μ E x ∂π) ≤ stationaryScaleConstant*E*Real.log E := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEm : stationaryMarginThreshold ≤ E :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hE
  have hEone : Real.exp 1 ≤ E :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hE
  have hEexp : Real.exp (2*stationaryAbsorptionConstant) ≤ E := le_trans (le_max_right _ _) hE
  have hEnum : (5120000 : ℝ) ≤ E := by simpa [stationaryMarginThreshold] using hEm
  have hEpos : (0 : ℝ) < E := by linarith
  have hE1 : (1 : ℝ) ≤ E := by linarith
  set K := frozenUniformMeanConstant with hKdef
  have hKpos : 0 < K := frozenUniformMeanConstant_pos
  set Kb := stationaryBadBranchConstant with hKbdef
  have hKbpos : 0 < Kb := stationaryBadBranchConstant_pos
  set g := stationaryGeomExpSum with hgdef
  have hgpos : 0 < g := stationaryGeomExpSum_pos
  set M₀ := stationaryMarginMomentConstant with hM0def
  have hM0 : 0 ≤ M₀ := stationaryMarginMomentConstant_nonneg
  set G' := stationaryEnvelopeMeanBound with hG'def
  have hG'0 : 0 ≤ G' := stationaryEnvelopeMeanBound_nonneg
  set L := Real.log E with hLdef
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]
    exact (Real.le_log_iff_exp_le hEpos).mpr hEone
  have hLK : 2*stationaryAbsorptionConstant ≤ L := by
    rw [hLdef]
    exact (Real.le_log_iff_exp_le hEpos).mpr hEexp
  have hlogeE : Real.log (Real.exp 1*E) = 1+L := by
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hEpos), Real.log_exp, hLdef]
  -- the three stationary inputs
  set C := ∫ x, nativeRestartMean X μ E x ∂π with hCdef
  set Iexc := ∫ y, nativeRestartExcess E y ∂π with hIdef
  set P := ∫ y, nativeRestartMarginPos E y ∂π with hPdef
  have hC1 : 1 ≤ C := one_le_stationary_mean hX hi hG hEpos
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hP : P ≤ 5*Iexc+10*G'+10 := stationary_marginPos_integral_le hX hi hG hEm hπ
  set Q := (8*L+2)*Kb+2*Real.exp 1*g with hQdef
  have hIexc : Iexc ≤ M₀+Q*C/E^2 := stationary_excess_integral_le hX hi hG hEm hπ
  have hmean := stationary_mean_le_marginPos hX hi hG hE1 (π := π)
  rw [hlogeE, ← hKdef, ← hCdef, ← hPdef] at hmean
  -- assemble the one-step inequality
  have hfac : (0 : ℝ) ≤ K*E*(1+L) := by positivity
  have hstep : 1+P ≤ 11+10*G'+5*M₀+5*(Q*C/E^2) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hstep hfac
  have hid : K*E*(1+L)*(11+10*G'+5*M₀+5*(Q*C/E^2)) =
      K*E*(1+L)*(11+10*G'+5*M₀)+(5*K*(1+L)*Q/E)*C := by
    field_simp
  have hineq : C ≤ K*E*(1+L)*(11+10*G'+5*M₀)+(5*K*(1+L)*Q/E)*C := by
    rw [← hid]
    exact le_trans hmean hmul
  -- the residual coefficient is at most one half
  have hcube : (Real.exp (L/3))^3 = Real.exp L := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hEeq : Real.exp L = E := by rw [hLdef, Real.exp_log hEpos]
  have hL3 : L^3/27 ≤ E := by
    have hb : L/3 ≤ Real.exp (L/3) := by
      have := Real.add_one_le_exp (L/3)
      linarith
    have hpow : (L/3)^3 ≤ (Real.exp (L/3))^3 :=
      pow_le_pow_left₀ (by linarith) hb 3
    rw [hcube, hEeq] at hpow
    nlinarith
  have hS0 : (0 : ℝ) ≤ 20*Kb+4*Real.exp 1*g := by positivity
  have hQle : (1+L)*Q ≤ L^2*(20*Kb+4*Real.exp 1*g) := by
    have heg : (0 : ℝ) ≤ Real.exp 1*g := by positivity
    have hA : (1+L)*(8*L+2) ≤ 20*L^2 := by nlinarith
    have hB : (1+L)*2 ≤ 4*L^2 := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hA hKbpos.le
    have h2 := mul_le_mul_of_nonneg_right hB heg
    rw [hQdef]
    nlinarith [h1, h2]
  have hKstar : 270*K*(20*Kb+4*Real.exp 1*g) ≤ L := by
    have h := hLK
    rw [stationaryAbsorptionConstant, ← hKdef, ← hKbdef, ← hgdef] at h
    linarith
  have hb2 : 5*K*(1+L)*Q/E ≤ 1/2 := by
    rw [div_le_iff₀ hEpos]
    have h1 : 5*K*(1+L)*Q ≤ 5*K*(L^2*(20*Kb+4*Real.exp 1*g)) := by
      have := mul_le_mul_of_nonneg_left hQle (by positivity : (0:ℝ) ≤ 5*K)
      nlinarith
    have h2 : 5*K*(L^2*(20*Kb+4*Real.exp 1*g)) ≤ E*(1/2) := by
      have hcube2 : L^2*(270*K*(20*Kb+4*Real.exp 1*g)) ≤ L^2*L :=
        mul_le_mul_of_nonneg_left hKstar (by positivity)
      nlinarith
    linarith
  have hb0 : (0 : ℝ) ≤ 5*K*(1+L)*Q/E := by
    have hQ0 : 0 ≤ Q := by
      rw [hQdef]
      have : (0 : ℝ) ≤ 8*L+2 := by linarith
      positivity
    positivity
  have hA0 : (0 : ℝ) ≤ K*E*(1+L)*(11+10*G'+5*M₀) := by positivity
  have habs := stationary_absorb_half hC0 hA0 hb0 hb2 hineq
  refine habs.trans ?_
  rw [stationaryScaleConstant, ← hKdef, ← hM0def, ← hG'def]
  have hS : (0 : ℝ) ≤ 11+10*G'+5*M₀ := by linarith
  have hKE : (0 : ℝ) ≤ K*E := mul_nonneg hKpos.le hEpos.le
  have hcoef : (0 : ℝ) ≤ 2*(K*E)*(11+10*G'+5*M₀) :=
    mul_nonneg (by linarith) hS
  calc 2*(K*E*(1+L)*(11+10*G'+5*M₀))
      = (2*(K*E)*(11+10*G'+5*M₀))*(1+L) := by ring
    _ ≤ (2*(K*E)*(11+10*G'+5*M₀))*(2*L) :=
        mul_le_mul_of_nonneg_left (by linarith) hcoef
    _ = 4*K*(11+5*M₀+10*G')*E*L := by ring

/-- The last sentence of Appendix `app:margins`: the complementary branch has
stationary probability `O(log E / E)`. -/
theorem measure_prod_nativeRestart_bad_branch_log_scale [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    (π.prod μ) (nativeRestartFavorableSet X E)ᶜ ≤
      ENNReal.ofReal (stationaryBadBranchConstant*stationaryScaleConstant*
        Real.log E/E) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEm : stationaryMarginThreshold ≤ E :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hE
  have hEnum : (5120000 : ℝ) ≤ E := by simpa [stationaryMarginThreshold] using hEm
  have hEpos : (0 : ℝ) < E := by linarith
  have hE2 : (0 : ℝ) < E^2 := by positivity
  have hKb : 0 < stationaryBadBranchConstant := stationaryBadBranchConstant_pos
  have hscale := nativeRestart_stationary_mean_scale hX hi hG hE hπ
  refine (measure_prod_nativeRestart_bad_branch_le hX hi hG hEm hπ).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff₀ hE2 hEpos]
  nlinarith [mul_le_mul_of_nonneg_left hscale (mul_nonneg hKb.le hEpos.le)]


/-! ### The uniform first margin moment

`eq:stationarymarginmoments` at `p = 1`: once the mean scale is known, the
stationary mean absolute margin is bounded by an absolute constant.
-/

def stationaryMarginAbsBound : ℝ :=
  6*(stationaryMarginMomentConstant+
      27*stationaryScaleConstant*(10*stationaryBadBranchConstant+
        2*Real.exp 1*stationaryGeomExpSum))+
    10*stationaryEnvelopeMeanBound+10

omit mΩ in
theorem abs_margin_eq_add (E y : ℝ) :
    |E-abs y| = nativeRestartMarginPos E y+nativeRestartExcess E y := by
  unfold nativeRestartMarginPos nativeRestartExcess
  rcases le_total (|y|) E with h | h
  · rw [abs_of_nonneg (by linarith), max_eq_left (by linarith : (0:ℝ) ≤ E-|y|),
      max_eq_right (by linarith : |y|-E ≤ 0)]
    ring
  · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith : E-|y| ≤ 0),
      max_eq_left (by linarith : (0:ℝ) ≤ |y|-E)]
    ring

/-- Theorem 4.2, moment part at `p = 1`: the stationary mean absolute boundary
margin is bounded uniformly in the tolerance. -/
theorem nativeRestart_stationary_margin_abs_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    (∫ y, |E-abs y| ∂π) ≤ stationaryMarginAbsBound := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEm : stationaryMarginThreshold ≤ E :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hE
  have hEone : Real.exp 1 ≤ E :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hE
  have hEnum : (5120000 : ℝ) ≤ E := by simpa [stationaryMarginThreshold] using hEm
  have hEpos : (0 : ℝ) < E := by linarith
  have hE1 : (1 : ℝ) ≤ E := by linarith
  set K := frozenUniformMeanConstant with hKdef
  have hKpos : 0 < K := frozenUniformMeanConstant_pos
  set Kb := stationaryBadBranchConstant with hKbdef
  have hKbpos : 0 < Kb := stationaryBadBranchConstant_pos
  set g := stationaryGeomExpSum with hgdef
  have hgpos : 0 < g := stationaryGeomExpSum_pos
  set M₀ := stationaryMarginMomentConstant with hM0def
  have hM0 : 0 ≤ M₀ := stationaryMarginMomentConstant_nonneg
  set G' := stationaryEnvelopeMeanBound with hG'def
  have hG'0 : 0 ≤ G' := stationaryEnvelopeMeanBound_nonneg
  set SC := stationaryScaleConstant with hSCdef
  have hSC0 : 0 ≤ SC := by
    rw [hSCdef, stationaryScaleConstant, ← hKdef, ← hM0def, ← hG'def]
    positivity
  set L := Real.log E with hLdef
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]
    exact (Real.le_log_iff_exp_le hEpos).mpr hEone
  have hL3 : L^3/27 ≤ E := by
    rw [hLdef]
    exact stationary_log_cube_le hE1
  set C := ∫ x, nativeRestartMean X μ E x ∂π with hCdef
  set Iexc := ∫ y, nativeRestartExcess E y ∂π with hIdef
  set P := ∫ y, nativeRestartMarginPos E y ∂π with hPdef
  have hC1 : 1 ≤ C := one_le_stationary_mean hX hi hG hEpos
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hCscale : C ≤ SC*E*L := by
    rw [hSCdef, hCdef, hLdef]
    exact nativeRestart_stationary_mean_scale hX hi hG hE hπ
  set Q := (8*L+2)*Kb+2*Real.exp 1*g with hQdef
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    have : (0 : ℝ) ≤ 8*L+2 := by linarith
    positivity
  have hIexc : Iexc ≤ M₀+Q*C/E^2 := stationary_excess_integral_le hX hi hG hEm hπ
  have hP : P ≤ 5*Iexc+10*G'+10 := stationary_marginPos_integral_le hX hi hG hEm hπ
  -- the residual term is uniformly bounded
  have hLsq : L^2/E ≤ 27 := by
    rw [div_le_iff₀ hEpos]
    nlinarith
  have hLlin : L/E ≤ 27 := by
    rw [div_le_iff₀ hEpos]
    nlinarith
  have hQL : Q*L/E ≤ 27*(10*Kb+2*Real.exp 1*g) := by
    have hexp : Q*L/E = 8*Kb*(L^2/E)+2*Kb*(L/E)+2*Real.exp 1*g*(L/E) := by
      rw [hQdef]
      field_simp
    rw [hexp]
    have h1 : 8*Kb*(L^2/E) ≤ 8*Kb*27 := by nlinarith
    have h2 : 2*Kb*(L/E) ≤ 2*Kb*27 := by nlinarith
    have h3 : 2*Real.exp 1*g*(L/E) ≤ 2*Real.exp 1*g*27 := by
      have hpos : (0 : ℝ) ≤ 2*Real.exp 1*g := by positivity
      nlinarith
    linarith
  have hres : Q*C/E^2 ≤ 27*(10*Kb+2*Real.exp 1*g)*SC := by
    have hstep : Q*C/E^2 ≤ Q*(SC*E*L)/E^2 := by
      apply div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hCscale hQ0
    have heq : Q*(SC*E*L)/E^2 = (Q*L/E)*SC := by
      field_simp
    rw [heq] at hstep
    refine hstep.trans ?_
    exact mul_le_mul_of_nonneg_right hQL hSC0
  -- assemble
  have hmp_meas : Measurable (nativeRestartMarginPos E) := measurable_nativeRestartMarginPos E
  have hmp_nonneg : ∀ y, 0 ≤ nativeRestartMarginPos E y := fun y => le_max_right _ _
  have hmp_upper : ∀ y, nativeRestartMarginPos E y ≤ E := by
    intro y
    exact max_le (by linarith [abs_nonneg y]) hEpos.le
  have hmp_int : Integrable (nativeRestartMarginPos E) π :=
    Doeblin.integrable_bounded_reward π hmp_meas hmp_nonneg hmp_upper
  have hexc_int : Integrable (nativeRestartExcess E) π :=
    stationary_excess_integrable hX hi hG hEm hπ
  have hsplit : (∫ y, |E-abs y| ∂π) = P+Iexc := by
    rw [hPdef, hIdef, ← integral_add hmp_int hexc_int]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => abs_margin_eq_add E y)
  rw [hsplit, stationaryMarginAbsBound, ← hM0def, ← hKbdef, ← hgdef, ← hG'def, ← hSCdef]
  have hIexcB : Iexc ≤ M₀+27*(10*Kb+2*Real.exp 1*g)*SC := by linarith
  have hkey : 6*(M₀+27*SC*(10*Kb+2*Real.exp 1*g)) =
      6*(M₀+27*(10*Kb+2*Real.exp 1*g)*SC) := by ring
  rw [hkey]
  linarith

end SwingRepair
