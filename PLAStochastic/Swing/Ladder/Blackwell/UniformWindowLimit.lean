import PLAStochastic.Swing.Ladder.Blackwell.ConvolutionMinorization
import PLAStochastic.Swing.Ladder.Blackwell.ShiftReduction

/-!
# The uniform Blackwell renewal theorem for the Gaussian ladder family

This file proves `UniformRenewalWindowLimit X μ` unconditionally, closing the
last standing hypothesis of Theorem 4.3.

The argument is the quantitative harmonic-function proof of Blackwell's theorem,
made uniform over the drift strip.  Write `W(u) = U_a((u-x, u])` for the window
mass, `L(β) = sup_{u ≥ β} W(u)`, and pick `b* ≥ β + T` with `W(b*)` within `ϵ`
of `L(β + T)`.  The deficit `Ψ(y) = L(β) - W(b* - y)` is nonnegative on
`y ≤ b* - β` and its `ν^{*m}`-averages are exactly `L(β) - W(b*)` plus the
boundary correction of `ladderRenewalMeasure_Ioc_split`.  Three tools turn this
into a bound on `L(β) - x/μ_a`:

* the exact stationary identity `∫ W(b - y) dQ_a(y) = x/μ_a`, transported
  through the convolution `σ = ν^{*m₀} ∗ Q_a`, whose mass on `[0,1)` is
  geometrically small (`(1-κ)^{m₀}`), whose density is at most `1/κ`, and whose
  far tail is controlled by Chebyshev;
* the explicit Lebesgue component `κ^{m+1} η^m · Leb|_{I_m} ≤ ν^{*(m+1)}` of
  `RenewalIntervalMinorization`, whose intervals cover `[1, n]` up to the gap
  `(2, 2+2η)`, which converts Lebesgue smallness of `Ψ` on `[1,n]` into the
  already controlled `ν^{*(m+1)}`-averages;
* a pigeonhole over `N` consecutive blocks of length `T`, which makes
  `L(β) - L(β + T)` at most `P/N` for some block.

Every constant depends only on `(δ, M, K, ε)`, so the resulting threshold is
uniform in the drift and the window length.  The lower bound is symmetric.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-! ## Generic convolution estimates on the line -/

/-- Union bound for the tail of a convolution: `z + y > c` forces `z > c - t`
or `y > t`. -/
theorem conv_Ioi_le_add (ρ ν : Measure ℝ) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ν] (c t : ℝ) :
    (ρ ∗ ν) (Ioi c) ≤ ρ (Ioi (c - t)) + ν (Ioi t) := by
  rw [measure_conv_apply _ _ measurableSet_Ioi]
  have hpt : ∀ z : ℝ, ν {y : ℝ | z + y ∈ Ioi c} ≤
      (Ioi (c - t)).indicator (fun _ => (1 : ℝ≥0∞)) z + ν (Ioi t) := by
    intro z
    by_cases hz : z ∈ Ioi (c - t)
    · rw [Set.indicator_of_mem hz]
      exact le_add_right prob_le_one
    · rw [Set.indicator_of_notMem hz, zero_add]
      refine measure_mono fun y hy => ?_
      have hy' : c < z + y := hy
      have hz' : ¬ (c - t < z) := hz
      show t < y
      linarith [not_lt.mp hz']
  calc (∫⁻ z, ν {y : ℝ | z + y ∈ Ioi c} ∂ρ)
      ≤ ∫⁻ z, ((Ioi (c - t)).indicator (fun _ => (1 : ℝ≥0∞)) z + ν (Ioi t)) ∂ρ :=
        lintegral_mono hpt
    _ = ρ (Ioi (c - t)) + ν (Ioi t) := by
        rw [lintegral_add_right _ measurable_const, lintegral_indicator_const measurableSet_Ioi,
          lintegral_const, measure_univ, one_mul, mul_one]

/-- The `m`-fold convolution power exceeds `m t` only if one increment exceeds
`t`. -/
theorem measureConvPow_Ioi_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ) (m : ℕ) :
    measureConvPow ν m (Ioi ((m : ℝ) * t)) ≤ (m : ℝ≥0∞) * ν (Ioi t) := by
  induction m with
  | zero =>
    rw [measureConvPow_zero, Measure.dirac_apply' _ measurableSet_Ioi]
    have h0 : (0 : ℝ) ∉ Ioi ((0 : ℕ) * t : ℝ) := by
      simp
    rw [Set.indicator_of_notMem h0]
    simp
  | succ m ih =>
    rw [measureConvPow_succ]
    have hstep := conv_Ioi_le_add (measureConvPow ν m) ν (((m + 1 : ℕ) : ℝ) * t) t
    have hEq : ((m + 1 : ℕ) : ℝ) * t - t = (m : ℝ) * t := by
      push_cast
      ring
    rw [hEq] at hstep
    refine hstep.trans ?_
    push_cast
    calc measureConvPow ν m (Ioi ((m : ℝ) * t)) + ν (Ioi t)
        ≤ (m : ℝ≥0∞) * ν (Ioi t) + ν (Ioi t) := add_le_add ih le_rfl
      _ = ((m : ℝ≥0∞) + 1) * ν (Ioi t) := by ring

/-- For measures living on `[0, ∞)`, `z + y < c` forces both `z < c` and
`y < c`. -/
theorem conv_Iio_le_mul (ρ ν : Measure ℝ) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ν] (hρ : ρ (Iio 0) = 0) (hν : ν (Iio 0) = 0) (c : ℝ) :
    (ρ ∗ ν) (Iio c) ≤ ρ (Iio c) * ν (Iio c) := by
  rw [measure_conv_apply _ _ measurableSet_Iio]
  have hpt : ∀ z : ℝ, ν {y : ℝ | z + y ∈ Iio c} ≤
      (Iio 0).indicator (fun _ => (1 : ℝ≥0∞)) z +
        (Ico 0 c).indicator (fun _ => ν (Iio c)) z := by
    intro z
    by_cases hz0 : z < 0
    · rw [Set.indicator_of_mem (show z ∈ Iio 0 from hz0)]
      exact le_add_right prob_le_one
    · rw [Set.indicator_of_notMem (show z ∉ Iio 0 from hz0), zero_add]
      have hz0' : 0 ≤ z := not_lt.mp hz0
      by_cases hzc : z < c
      · rw [Set.indicator_of_mem (show z ∈ Ico 0 c from ⟨hz0', hzc⟩)]
        refine measure_mono fun y hy => ?_
        have hy' : z + y < c := hy
        show y < c
        linarith
      · rw [Set.indicator_of_notMem (show z ∉ Ico 0 c from fun h => hzc h.2)]
        have hsub : {y : ℝ | z + y ∈ Iio c} ⊆ Iio 0 := by
          intro y hy
          have hy' : z + y < c := hy
          show y < 0
          linarith [not_lt.mp hzc]
        exact le_of_le_of_eq (measure_mono hsub) hν
  calc (∫⁻ z, ν {y : ℝ | z + y ∈ Iio c} ∂ρ)
      ≤ ∫⁻ z, ((Iio 0).indicator (fun _ => (1 : ℝ≥0∞)) z +
          (Ico 0 c).indicator (fun _ => ν (Iio c)) z) ∂ρ := lintegral_mono hpt
    _ = ρ (Iio 0) * 1 + ν (Iio c) * ρ (Ico 0 c) := by
        rw [lintegral_add_left (measurable_const.indicator measurableSet_Iio),
          lintegral_indicator_const measurableSet_Iio,
          lintegral_indicator_const measurableSet_Ico, mul_comm (ρ (Iio 0))]
    _ = ν (Iio c) * ρ (Ico 0 c) := by rw [hρ, zero_mul, zero_add]
    _ ≤ ρ (Iio c) * ν (Iio c) := by
        rw [mul_comm]
        exact mul_le_mul' (measure_mono Ico_subset_Iio_self) le_rfl

theorem measureConvPow_Iio_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) (m : ℕ) : measureConvPow ν m (Iio 0) = 0 := by
  induction m with
  | zero =>
    rw [measureConvPow_zero, Measure.dirac_apply' _ measurableSet_Iio,
      Set.indicator_of_notMem (show (0 : ℝ) ∉ Iio 0 by simp)]
  | succ m ih =>
    rw [measureConvPow_succ]
    refine le_antisymm ?_ bot_le
    calc (measureConvPow ν m ∗ ν) (Iio 0)
        ≤ measureConvPow ν m (Iio 0) * ν (Iio 0) :=
          conv_Iio_le_mul _ _ ih hν 0
      _ = 0 := by rw [ih, zero_mul]

theorem measureConvPow_Iio_one_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) (m : ℕ) :
    measureConvPow ν m (Iio 1) ≤ (ν (Iio 1)) ^ m := by
  induction m with
  | zero =>
    rw [measureConvPow_zero, Measure.dirac_apply' _ measurableSet_Iio,
      Set.indicator_of_mem (show (0 : ℝ) ∈ Iio 1 by simp), pow_zero]
    simp
  | succ m ih =>
    rw [measureConvPow_succ, pow_succ]
    calc (measureConvPow ν m ∗ ν) (Iio 1)
        ≤ measureConvPow ν m (Iio 1) * ν (Iio 1) :=
          conv_Iio_le_mul _ _ (measureConvPow_Iio_zero ν hν m) hν 1
      _ ≤ (ν (Iio 1)) ^ m * ν (Iio 1) := mul_le_mul' ih le_rfl

/-- Convolution with a probability measure preserves domination by a multiple
of Lebesgue measure. -/
theorem conv_le_smul_volume (ρ σ : Measure ℝ) [IsProbabilityMeasure ρ] [SFinite σ]
    {c : ℝ≥0∞} (hσ : σ ≤ c • volume) : ρ ∗ σ ≤ c • volume := by
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [measure_conv_apply _ _ hA]
  have hpt : ∀ z : ℝ, σ {y : ℝ | z + y ∈ A} ≤ c * volume A := by
    intro z
    have h := Measure.le_iff.mp hσ {y : ℝ | z + y ∈ A}
      (hA.preimage (measurable_const.add measurable_id))
    rw [Measure.smul_apply, smul_eq_mul] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    exact measure_preimage_add volume z A
  calc (∫⁻ z, σ {y : ℝ | z + y ∈ A} ∂ρ)
      ≤ ∫⁻ _z, c * volume A ∂ρ := lintegral_mono hpt
    _ = c * volume A := by rw [lintegral_const, measure_univ, mul_one]
    _ = (c • volume) A := by rw [Measure.smul_apply, smul_eq_mul]

/-! ## Uniform tail and density bounds for the Gaussian ladder family -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem gaussianAscendingLadderLaw_Iio_zero
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    gaussianAscendingLadderLaw X μ a (Iio 0) = 0 :=
  le_antisymm (le_of_le_of_eq (measure_mono Iio_subset_Iic_self)
    (gaussianAscendingLadderLaw_Iic_zero hX hi hG ha)) bot_le

/-- Chebyshev through the union bound: the real tail of every convolution
power, with a constant depending only on the strip. -/
theorem gaussianLadder_convPow_tail_le [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) (m : ℕ) {c : ℝ} (hc : 0 < c) :
    (measureConvPow (gaussianAscendingLadderLaw X μ a) m).real (Ioi c) ≤
      (m : ℝ) ^ 3 * gaussianAscendingLadderMomentBound δ M 2 / c ^ 2 := by
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  set B := gaussianAscendingLadderMomentBound δ M 2 with hBdef
  have hB0 : 0 ≤ B := gaussianAscendingLadderMomentBound_two_nonneg hX hi hG hδ hδa haM
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [measureConvPow_zero, Measure.real, Measure.dirac_apply' _ measurableSet_Ioi,
      Set.indicator_of_notMem (show (0 : ℝ) ∉ Ioi c from not_lt.mpr hc.le)]
    simp
  · have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hcm : 0 < c / m := div_pos hc hmpos
    have h1 := measureConvPow_Ioi_le ν (c / m) m
    rw [show (m : ℝ) * (c / m) = c by field_simp] at h1
    have hsq := gaussianAscendingLadderLaw_sq_integrable hX hi hG hδ hδa haM
    have hsqle := gaussianAscendingLadderLaw_sq_integral_le hX hi hG hδ hδa haM
    have h2 := measureReal_Ioi_le_sq_moment hsq hcm
    have h1r : (measureConvPow ν m).real (Ioi c) ≤ (m : ℝ) * ν.real (Ioi (c / m)) := by
      rw [Measure.real, Measure.real, ← ENNReal.toReal_natCast, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) (measure_ne_top _ _)) h1
    calc (measureConvPow ν m).real (Ioi c)
        ≤ (m : ℝ) * ν.real (Ioi (c / m)) := h1r
      _ ≤ (m : ℝ) * ((∫ x, x ^ 2 ∂ν) / (c / m) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hmpos.le
      _ ≤ (m : ℝ) * (B / (c / m) ^ 2) := by gcongr
      _ = (m : ℝ) ^ 3 * B / c ^ 2 := by
          field_simp

theorem gaussianLadder_Iio_one_le
    (hX : ∀ n, Measurable (X n)) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {M a : ℝ} (ha : 0 ≤ a) (haM : a ≤ M) [IsProbabilityMeasure (gaussianAscendingLadderLaw X μ a)] :
    gaussianAscendingLadderLaw X μ a (Iio 1) ≤
      ENNReal.ofReal (1 - gaussianAscendingLadderCommonDensity M) := by
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  set κ := gaussianAscendingLadderCommonDensity M with hκdef
  have hκ : 0 < κ := gaussianAscendingLadderCommonDensity_pos M
  have hmin := gaussianAscendingLadderLaw_common_minorization hX (hG 0) ha haM
  have hIcc : ENNReal.ofReal κ ≤ ν (Icc 1 2) := by
    have h := Measure.le_iff.mp hmin (Icc 1 2) measurableSet_Icc
    rwa [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply measurableSet_Icc,
      Set.inter_self, Real.volume_Icc, show (2 : ℝ) - 1 = 1 by norm_num,
      ENNReal.ofReal_one, mul_one] at h
  have hIci : ENNReal.ofReal κ ≤ ν (Ici 1) := hIcc.trans (measure_mono Icc_subset_Ici_self)
  have hcompl : ν (Iio 1) = 1 - ν (Ici 1) := by
    rw [← Set.compl_Ici, measure_compl measurableSet_Ici (measure_ne_top _ _), measure_univ]
  rw [hcompl, ENNReal.ofReal_sub 1 hκ.le, ENNReal.ofReal_one]
  exact tsub_le_tsub_left hIci 1

theorem gaussianLadder_convPow_Iio_one_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {M a : ℝ} (ha : 0 < a) (haM : a ≤ M) (m : ℕ) :
    (measureConvPow (gaussianAscendingLadderLaw X μ a) m).real (Iio 1) ≤
      (1 - gaussianAscendingLadderCommonDensity M) ^ m := by
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  set κ := gaussianAscendingLadderCommonDensity M with hκdef
  have hκ1 : κ ≤ 1 := gaussianAscendingLadderCommonDensity_le_one M
  have hν0 : ν (Iio 0) = 0 := gaussianAscendingLadderLaw_Iio_zero hX hi hG ha
  refine ENNReal.toReal_le_of_le_ofReal (pow_nonneg (by linarith) m) ?_
  calc measureConvPow ν m (Iio 1) ≤ (ν (Iio 1)) ^ m := measureConvPow_Iio_one_le ν hν0 m
    _ ≤ (ENNReal.ofReal (1 - κ)) ^ m := by
        gcongr
        exact gaussianLadder_Iio_one_le hX hG ha.le haM
    _ = ENNReal.ofReal ((1 - κ) ^ m) := (ENNReal.ofReal_pow (by linarith) m).symm

/-- The equilibrium law has Lebesgue density at most `1/κ`. -/
theorem gaussianEquilibrium_le_smul_volume
    (hX : ∀ n, Measurable (X n)) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {M a : ℝ} (ha : 0 < a) (haM : a ≤ M)
    [IsProbabilityMeasure (gaussianAscendingLadderLaw X μ a)] :
    equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a) ≤
      ENNReal.ofReal (1 / gaussianAscendingLadderCommonDensity M) • volume := by
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  set κ := gaussianAscendingLadderCommonDensity M with hκdef
  have hκ : 0 < κ := gaussianAscendingLadderCommonDensity_pos M
  have hmean : ENNReal.ofReal κ ≤ ladderMeanENN ν :=
    lintegral_ofReal_ge_of_minorization
      (gaussianAscendingLadderLaw_common_minorization hX (hG 0) ha.le haM)
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [equilibriumOvershootLaw_apply ν hA, Measure.smul_apply, smul_eq_mul]
  have hpt : ∀ o : ℝ, ν (Ioi o) / ladderMeanENN ν ≤ ENNReal.ofReal (1 / κ) := by
    intro o
    calc ν (Ioi o) / ladderMeanENN ν ≤ 1 / ladderMeanENN ν :=
          ENNReal.div_le_div_right prob_le_one _
      _ ≤ 1 / ENNReal.ofReal κ := ENNReal.div_le_div_left hmean 1
      _ = ENNReal.ofReal (1 / κ) := by
          rw [one_div, one_div, ENNReal.ofReal_inv_of_pos hκ]
  calc (∫⁻ o in A ∩ Ici 0, ν (Ioi o) / ladderMeanENN ν)
      ≤ ∫⁻ _o in A ∩ Ici 0, ENNReal.ofReal (1 / κ) := lintegral_mono hpt
    _ = ENNReal.ofReal (1 / κ) * volume (A ∩ Ici 0) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (1 / κ) * volume A :=
        mul_le_mul' le_rfl (measure_mono inter_subset_left)

/-! ## The smoothing measure `σ = ν^{*m₀} ∗ Q` -/

/-- The smoothed equilibrium law used to transport the stationary identity. -/
def blackwellSmoothing (ν : Measure ℝ) (m₀ : ℕ) : Measure ℝ :=
  measureConvPow ν m₀ ∗ equilibriumOvershootLaw ν

theorem blackwellSmoothing_isProbabilityMeasure (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hQ : IsProbabilityMeasure (equilibriumOvershootLaw ν)) (m₀ : ℕ) :
    IsProbabilityMeasure (blackwellSmoothing ν m₀) := by
  unfold blackwellSmoothing
  infer_instance

theorem blackwellSmoothing_Iio_one_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hQ : IsProbabilityMeasure (equilibriumOvershootLaw ν)) (hν : ν (Iio 0) = 0) (m₀ : ℕ) :
    blackwellSmoothing ν m₀ (Iio 1) ≤ measureConvPow ν m₀ (Iio 1) := by
  unfold blackwellSmoothing
  calc (measureConvPow ν m₀ ∗ equilibriumOvershootLaw ν) (Iio 1)
      ≤ measureConvPow ν m₀ (Iio 1) * equilibriumOvershootLaw ν (Iio 1) :=
        conv_Iio_le_mul _ _ (measureConvPow_Iio_zero ν hν m₀)
          (equilibriumOvershootLaw_Iio_zero ν) 1
    _ ≤ measureConvPow ν m₀ (Iio 1) * 1 := mul_le_mul' le_rfl prob_le_one
    _ = measureConvPow ν m₀ (Iio 1) := mul_one _

theorem blackwellSmoothing_Ioi_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hQ : IsProbabilityMeasure (equilibriumOvershootLaw ν)) (m₀ : ℕ) (t : ℝ) :
    blackwellSmoothing ν m₀ (Ioi (2 * t)) ≤
      measureConvPow ν m₀ (Ioi t) + equilibriumOvershootLaw ν (Ioi t) := by
  unfold blackwellSmoothing
  have h := conv_Ioi_le_add (measureConvPow ν m₀) (equilibriumOvershootLaw ν) (2 * t) t
  rwa [show 2 * t - t = t by ring] at h

theorem blackwellSmoothing_le_smul_volume (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [SFinite (equilibriumOvershootLaw ν)] {c : ℝ≥0∞}
    (hQ : equilibriumOvershootLaw ν ≤ c • volume) (m₀ : ℕ) :
    blackwellSmoothing ν m₀ ≤ c • volume :=
  conv_le_smul_volume _ _ hQ

/-! ## The window bound -/

/-- The position-uniform window bound for window lengths at most `K`. -/
def blackwellWindowBound (M K : ℝ) : ℝ := gaussianWindowConstant M * (1 + K)

theorem blackwellWindowBound_pos {M K : ℝ} (hK : 0 ≤ K) : 0 < blackwellWindowBound M K := by
  unfold blackwellWindowBound
  have := gaussianWindowConstant_pos M
  positivity

theorem ladderRenewalMeasure_window_le_ofReal [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {M a : ℝ} (ha : 0 < a) (haM : a ≤ M) {x K : ℝ} (hx : 0 ≤ x) (hxK : x ≤ K) (u : ℝ) :
    ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a) (Ioc (u - x) u) ≤
      ENNReal.ofReal (blackwellWindowBound M K) := by
  have h := ladderRenewalMeasure_Ioc_le_const hX hi hG ha haM (u - x) hx
  rw [show u - x + x = u by ring] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  unfold blackwellWindowBound gaussianWindowConstant
  have hκ := gaussianAscendingLadderCommonDensity_pos M
  have he := Real.exp_pos 1
  rw [div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ hκ.le
  nlinarith

theorem renewalWindow_le_blackwellWindowBound [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {M a : ℝ} (ha : 0 < a) (haM : a ≤ M) {x K : ℝ} (hx : 0 ≤ x) (hxK : x ≤ K) (u : ℝ) :
    renewalWindow (gaussianAscendingLadderLaw X μ a) x u ≤ blackwellWindowBound M K :=
  renewalWindow_le _ (blackwellWindowBound_pos (hx.trans hxK)).le
    (fun u => ladderRenewalMeasure_window_le_ofReal hX hi hG ha haM hx hxK u) u


/-! ## The stationary identity transported through the smoothing -/

/-- Transporting `∫ W(b - y) dQ(y) = x/μ` through `σ = ν^{*m₀} ∗ Q`: the only
error comes from the `ν^{*m₀}`-mass beyond `b - x`. -/
theorem integral_window_blackwellSmoothing_sub_le [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M)
    {x K : ℝ} (hx : 0 ≤ x) (hxK : x ≤ K) (m₀ : ℕ) (b : ℝ) :
    |(∫ w, renewalWindow (gaussianAscendingLadderLaw X μ a) x (b - w)
        ∂(blackwellSmoothing (gaussianAscendingLadderLaw X μ a) m₀)) -
      x / ladderMean (gaussianAscendingLadderLaw X μ a)| ≤
      (blackwellWindowBound M K + K / gaussianAscendingLadderCommonDensity M) *
        (measureConvPow (gaussianAscendingLadderLaw X μ a) m₀).real (Ioi (b - K)) := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  have hQprob := gaussianAscendingLadderEquilibrium_isProbabilityMeasure hX hi hG hδ hδa haM
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  set Q := equilibriumOvershootLaw ν with hQdef
  set ρ := measureConvPow ν m₀ with hρdef
  set κ := gaussianAscendingLadderCommonDensity M with hκdef
  set P := blackwellWindowBound M K with hPdef
  set μ0 := ladderMean ν with hμ0def
  set W : ℝ → ℝ := renewalWindow ν x with hWdef
  have hκ : 0 < κ := gaussianAscendingLadderCommonDensity_pos M
  have hμ0 : κ ≤ μ0 := ladderMean_gaussianAscendingLadderLaw_ge hX hi hG hδ hδa haM
  have hμ0pos : 0 < μ0 := lt_of_lt_of_le hκ hμ0
  have hP : 0 < P := blackwellWindowBound_pos (hx.trans hxK)
  have hW0 : ∀ u, 0 ≤ W u := fun u => renewalWindow_nonneg ν x u
  have hWP : ∀ u, W u ≤ P := fun u =>
    renewalWindow_le_blackwellWindowBound hX hi hG ha haM hx hxK u
  have hxμ : x / μ0 ≤ K / κ := by
    rw [div_le_div_iff₀ hμ0pos hκ]
    nlinarith
  have hxμ0 : 0 ≤ x / μ0 := div_nonneg hx hμ0pos.le
  have hρuniv : ρ.real univ = 1 := by
    rw [Measure.real, measure_univ, ENNReal.toReal_one]
  have hQuniv : Q.real univ = 1 := by
    rw [Measure.real, measure_univ, ENNReal.toReal_one]
  -- the function on the product
  set F : ℝ × ℝ → ℝ := fun p => W (b - (p.1 + p.2)) with hFdef
  have hWmeas : Measurable (fun w => W (b - w)) := measurable_renewalWindow_shift ν x b
  have hFmeas : Measurable F := hWmeas.comp (measurable_fst.add measurable_snd)
  have hFint : Integrable F (ρ.prod Q) := by
    refine (integrable_const P).mono' hFmeas.aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (hW0 _)]
    exact hWP _
  -- unfold the convolution
  have hconv : (∫ w, W (b - w) ∂(blackwellSmoothing ν m₀)) =
      ∫ z, ∫ y, W (b - (z + y)) ∂Q ∂ρ := by
    have h1 : (∫ w, W (b - w) ∂(blackwellSmoothing ν m₀)) = ∫ p, F p ∂(ρ.prod Q) := by
      unfold blackwellSmoothing Measure.conv
      rw [integral_map (by fun_prop) hWmeas.aestronglyMeasurable]
    rw [h1, integral_prod F hFint]
  -- the inner integral
  set g : ℝ → ℝ := fun z => ∫ y, W (b - (z + y)) ∂Q with hgdef
  have hg_eq : ∀ z, z ≤ b - x → g z = x / μ0 := by
    intro z hz
    have h := integral_equilibrium_window_eq_gaussian hX hi hG hδ hδa haM hx
      (show x ≤ b - z by linarith)
    rw [hgdef]
    simp only []
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show renewalWindow ν x (b - (z + y)) =
      (ladderRenewalMeasure ν (Ioc (b - z - x - y) (b - z - y))).toReal
    unfold renewalWindow
    rw [show b - (z + y) - x = b - z - x - y by ring, show b - (z + y) = b - z - y by ring]
  have hg0 : ∀ z, 0 ≤ g z := fun z => integral_nonneg fun y => hW0 _
  have hgP : ∀ z, g z ≤ P := by
    intro z
    have hint : Integrable (fun y => W (b - (z + y))) Q := by
      refine (integrable_const P).mono' ?_ ?_
      · exact (hWmeas.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      · filter_upwards with y
        rw [Real.norm_eq_abs, abs_of_nonneg (hW0 _)]
        exact hWP _
    calc g z ≤ ∫ _y, P ∂Q := integral_mono hint (integrable_const P) fun y => hWP _
      _ = P := by rw [integral_const, hQuniv, one_smul]
  have hgint : Integrable g ρ := hFint.integral_prod_left
  -- pointwise deviation
  have hdev : ∀ z, |g z - x / μ0| ≤ (Ioi (b - K)).indicator (fun _ => P + K / κ) z := by
    intro z
    by_cases hz : z ≤ b - x
    · rw [hg_eq z hz, sub_self, abs_zero]
      exact Set.indicator_nonneg (fun _ _ => add_nonneg hP.le (div_nonneg (hx.trans hxK) hκ.le)) z
    · have hz' : z ∈ Ioi (b - K) := by
        show b - K < z
        linarith [not_le.mp hz]
      rw [Set.indicator_of_mem hz', abs_sub_le_iff]
      constructor <;> linarith [hg0 z, hgP z]
  rw [hconv]
  have hsub : (∫ z, g z ∂ρ) - x / μ0 = ∫ z, (g z - x / μ0) ∂ρ := by
    rw [integral_sub hgint (integrable_const _), integral_const, hρuniv, one_smul]
  change |(∫ z, g z ∂ρ) - x / μ0| ≤ _
  rw [hsub]
  calc |∫ z, (g z - x / μ0) ∂ρ| ≤ ∫ z, |g z - x / μ0| ∂ρ := abs_integral_le_integral_abs
    _ ≤ ∫ z, (Ioi (b - K)).indicator (fun _ => P + K / κ) z ∂ρ :=
        integral_mono (hgint.sub (integrable_const _)).abs
          ((integrable_const _).indicator measurableSet_Ioi) hdev
    _ = (P + K / κ) * ρ.real (Ioi (b - K)) := by
        rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_comm]

/-! ## The core deficit estimate -/

/-- Bounded measurable functions are integrable on sets of finite Lebesgue
measure. -/
theorem integrableOn_of_bounded_of_finite {f : ℝ → ℝ} (hf : Measurable f) {P : ℝ}
    (hP : ∀ y, |f y| ≤ P) {S : Set ℝ} (hS : volume S ≠ ⊤) :
    IntegrableOn f S volume := by
  have : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hS⟩
  refine (integrable_const P).mono' hf.aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs]
  exact hP y

/-- `A_n`: the amplification factor from the minorization constants. -/
def blackwellAmplification (κ η : ℝ) (n : ℕ) : ℝ :=
  (1 / κ) * ∑ m ∈ Finset.range (n + 1), 1 / minorConst κ η m

/-- `R₀`: the remainder of the core estimate. -/
def blackwellRemainder (κ B P η T : ℝ) (n m₀ : ℕ) : ℝ :=
  P * (1 - κ) ^ m₀ +
  P * ((m₀ : ℝ) ^ 3 * B / ((n : ℝ) / 2) ^ 2 + B / (κ * ((n : ℝ) / 2))) +
  (1 / κ) * (P * (2 * η)) +
  (1 / κ) * ∑ m ∈ Finset.range (n + 1),
    (1 / minorConst κ η m) * (P * (((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2))

theorem minorConst_pos {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) (m : ℕ) :
    0 < minorConst κ η m := by
  unfold minorConst
  positivity

/--
**The core deficit estimate.**  For a measurable `Ψ` with `-P ≤ Ψ ≤ P`,
nonnegative on `(-∞, S]` with `S ≥ T`, and whose `ν^{*(m+1)}`-averages are at
most `D` for `m ≤ n`, the `σ`-average of `max Ψ 0` is at most `A_n D + R₀`.
-/
theorem deficit_integral_smoothing_le [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M)
    {K : ℝ} (hK : 0 ≤ K) {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) (n m₀ : ℕ) (hn : 1 ≤ n)
    {T S : ℝ} (hT : 0 < T) (hTS : T ≤ S)
    {Ψ : ℝ → ℝ} (hΨmeas : Measurable Ψ)
    (hΨP : ∀ y, Ψ y ≤ blackwellWindowBound M K)
    (hΨlow : ∀ y, -blackwellWindowBound M K ≤ Ψ y)
    (hΨnn : ∀ y, y ≤ S → 0 ≤ Ψ y)
    {D : ℝ}
    (hΨint : ∀ m, m < n + 1 →
      ∫ y, Ψ y ∂(measureConvPow (gaussianAscendingLadderLaw X μ a) (m + 1)) ≤ D) :
    ∫ y, max (Ψ y) 0 ∂(blackwellSmoothing (gaussianAscendingLadderLaw X μ a) m₀) ≤
      blackwellAmplification (gaussianAscendingLadderCommonDensity M) η n * D +
        blackwellRemainder (gaussianAscendingLadderCommonDensity M)
          (gaussianAscendingLadderMomentBound δ M 2) (blackwellWindowBound M K) η T n m₀ := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  have hQprob := gaussianAscendingLadderEquilibrium_isProbabilityMeasure hX hi hG hδ hδa haM
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  set Q := equilibriumOvershootLaw ν with hQdef
  set κ := gaussianAscendingLadderCommonDensity M with hκdef
  set B := gaussianAscendingLadderMomentBound δ M 2 with hBdef
  set P := blackwellWindowBound M K with hPdef
  have hσprob : IsProbabilityMeasure (blackwellSmoothing ν m₀) :=
    blackwellSmoothing_isProbabilityMeasure ν hQprob m₀
  set σ := blackwellSmoothing ν m₀ with hσdef
  have hκ : 0 < κ := gaussianAscendingLadderCommonDensity_pos M
  have hκ1 : κ ≤ 1 := gaussianAscendingLadderCommonDensity_le_one M
  have hB0 : 0 ≤ B := gaussianAscendingLadderMomentBound_two_nonneg hX hi hG hδ hδa haM
  have hP : 0 < P := blackwellWindowBound_pos hK
  have hν0 : ν (Iio 0) = 0 := gaussianAscendingLadderLaw_Iio_zero hX hi hG ha
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) / 2 := by positivity
  set Φ : ℝ → ℝ := fun y => max (Ψ y) 0 with hΦdef
  have hΦmeas : Measurable Φ := hΨmeas.max measurable_const
  have hΦ0 : ∀ y, 0 ≤ Φ y := fun y => le_max_right _ _
  have hΦP : ∀ y, Φ y ≤ P := fun y => max_le (hΨP y) hP.le
  have hΦabs : ∀ y, |Φ y| ≤ P := fun y => by
    rw [abs_of_nonneg (hΦ0 y)]
    exact hΦP y
  have hΦint : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], Integrable Φ ρ := by
    intro ρ _
    refine (integrable_const P).mono' hΦmeas.aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    exact hΦabs y
  -- Step B: split `σ` into `(-∞,1)`, `[1,n]`, `(n,∞)`
  have hsplit : ∀ y, Φ y ≤ (Iio (1 : ℝ)).indicator Φ y + (Icc (1 : ℝ) n).indicator Φ y +
      (Ioi (n : ℝ)).indicator Φ y := by
    intro y
    have h1 := Set.indicator_nonneg (fun z _ => hΦ0 z) (s := Iio (1 : ℝ)) y
    have h2 := Set.indicator_nonneg (fun z _ => hΦ0 z) (s := Icc (1 : ℝ) n) y
    have h3 := Set.indicator_nonneg (fun z _ => hΦ0 z) (s := Ioi (n : ℝ)) y
    by_cases hy1 : y < 1
    · rw [Set.indicator_of_mem (show y ∈ Iio 1 from hy1)]
      linarith
    · by_cases hyn : y ≤ n
      · rw [Set.indicator_of_mem (show y ∈ Icc (1 : ℝ) n from ⟨not_lt.mp hy1, hyn⟩)]
        linarith
      · rw [Set.indicator_of_mem (show y ∈ Ioi (n : ℝ) from not_le.mp hyn)]
        linarith
  have hI1 : Integrable ((Iio (1 : ℝ)).indicator Φ) σ :=
    (hΦint σ).indicator measurableSet_Iio
  have hI2 : Integrable ((Icc (1 : ℝ) n).indicator Φ) σ :=
    (hΦint σ).indicator measurableSet_Icc
  have hI3 : Integrable ((Ioi (n : ℝ)).indicator Φ) σ :=
    (hΦint σ).indicator measurableSet_Ioi
  have hB : (∫ y, Φ y ∂σ) ≤ (∫ y, (Iio (1 : ℝ)).indicator Φ y ∂σ) +
      (∫ y, (Icc (1 : ℝ) n).indicator Φ y ∂σ) + ∫ y, (Ioi (n : ℝ)).indicator Φ y ∂σ := by
    have h := integral_mono (hΦint σ) ((hI1.add hI2).add hI3) hsplit
    have e1 := integral_add (μ := σ) (hI1.add hI2) hI3
    have e2 := integral_add (μ := σ) hI1 hI2
    simp only [Pi.add_apply] at e1 e2 h
    linarith
  -- the two mass terms
  have hsetle : ∀ (S : Set ℝ), MeasurableSet S →
      (∫ y, S.indicator Φ y ∂σ) ≤ P * σ.real S := by
    intro S hS
    rw [integral_indicator hS]
    calc (∫ y in S, Φ y ∂σ) ≤ ∫ _y in S, P ∂σ :=
          integral_mono (hΦint _) (integrable_const P) hΦP
      _ = P * σ.real S := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hσ1 : σ.real (Iio 1) ≤ (1 - κ) ^ m₀ := by
    have h1 := blackwellSmoothing_Iio_one_le ν hQprob hν0 m₀
    have h2 := gaussianLadder_convPow_Iio_one_le hX hi hG ha haM (M := M) m₀
    exact (ENNReal.toReal_mono (measure_ne_top _ _) h1).trans h2
  have hσn : σ.real (Ioi (n : ℝ)) ≤
      (m₀ : ℝ) ^ 3 * B / ((n : ℝ) / 2) ^ 2 + B / (κ * ((n : ℝ) / 2)) := by
    have h1 := blackwellSmoothing_Ioi_le ν hQprob m₀ ((n : ℝ) / 2)
    rw [show 2 * ((n : ℝ) / 2) = n by ring] at h1
    have h1r : σ.real (Ioi (n : ℝ)) ≤
        (measureConvPow ν m₀).real (Ioi ((n : ℝ) / 2)) + Q.real (Ioi ((n : ℝ) / 2)) := by
      rw [Measure.real, Measure.real, Measure.real, ← ENNReal.toReal_add (measure_ne_top _ _)
        (measure_ne_top _ _)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h1
    have h2 := gaussianLadder_convPow_tail_le hX hi hG hδ hδa haM m₀ hn2
    have h3 := equilibriumOvershoot_tail_le hX hi hG hδ hδa haM hn2
    linarith
  -- the middle term through the Lebesgue domination
  have hσvol : σ ≤ ENNReal.ofReal (1 / κ) • volume :=
    blackwellSmoothing_le_smul_volume ν (gaussianEquilibrium_le_smul_volume hX hG ha haM) m₀
  have hIccfin : volume (Icc (1 : ℝ) n) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hΦIcc : IntegrableOn Φ (Icc (1 : ℝ) n) volume :=
    integrableOn_of_bounded_of_finite hΦmeas hΦabs hIccfin
  have hmid : (∫ y, (Icc (1 : ℝ) n).indicator Φ y ∂σ) ≤
      (1 / κ) * ∫ y in Icc (1 : ℝ) n, Φ y := by
    rw [integral_indicator measurableSet_Icc]
    have hle : σ.restrict (Icc (1 : ℝ) n) ≤
        ENNReal.ofReal (1 / κ) • volume.restrict (Icc (1 : ℝ) n) := by
      rw [← Measure.restrict_smul]
      exact Measure.restrict_mono subset_rfl hσvol
    have hint : Integrable Φ (ENNReal.ofReal (1 / κ) • volume.restrict (Icc (1 : ℝ) n)) :=
      hΦIcc.smul_measure ENNReal.ofReal_ne_top
    calc (∫ y in Icc (1 : ℝ) n, Φ y ∂σ)
        ≤ ∫ y, Φ y ∂(ENNReal.ofReal (1 / κ) • volume.restrict (Icc (1 : ℝ) n)) :=
          integral_mono_measure hle (Filter.Eventually.of_forall hΦ0) hint
      _ = (1 / κ) * ∫ y in Icc (1 : ℝ) n, Φ y := by
          rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal (by positivity)]
  -- Step C: cover `[1,n]` by the gap and the minorizing intervals
  have hgapfin : volume (Ioo (2 : ℝ) (2 + 2 * η)) ≠ ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hIfin : ∀ m : ℕ, volume (minorIcc η m) ≠ ⊤ := by
    intro m
    unfold minorIcc
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hImeas : ∀ m : ℕ, MeasurableSet (minorIcc η m) := fun m => by
    unfold minorIcc
    exact measurableSet_Icc
  have hcover : ∀ y, (Icc (1 : ℝ) n).indicator Φ y ≤
      (Ioo (2 : ℝ) (2 + 2 * η)).indicator Φ y +
        ∑ m ∈ Finset.range (n + 1), (minorIcc η m).indicator Φ y := by
    intro y
    have hgap0 := Set.indicator_nonneg (fun z _ => hΦ0 z) (s := Ioo (2 : ℝ) (2 + 2 * η)) y
    have hsum0 : 0 ≤ ∑ m ∈ Finset.range (n + 1), (minorIcc η m).indicator Φ y :=
      Finset.sum_nonneg fun m _ => Set.indicator_nonneg (fun z _ => hΦ0 z) y
    by_cases hy : y ∈ Icc (1 : ℝ) n
    · rw [Set.indicator_of_mem hy]
      by_cases hgap : y ∈ Ioo (2 : ℝ) (2 + 2 * η)
      · rw [Set.indicator_of_mem hgap]
        linarith
      · have hor : y ≤ 2 ∨ 2 + 2 * η ≤ y := by
          rcases le_or_gt y 2 with h2 | h2
          · exact Or.inl h2
          · right
            by_contra h3
            exact hgap ⟨h2, not_le.mp h3⟩
        obtain ⟨m, hym, hmy⟩ := exists_mem_minorIcc hη hη4 hy.1 hor
        have hmn : m ∈ Finset.range (n + 1) := by
          rw [Finset.mem_range]
          have : (m : ℝ) ≤ n := hmy.trans hy.2
          have : m ≤ n := by exact_mod_cast this
          omega
        have hterm : Φ y = (minorIcc η m).indicator Φ y := (Set.indicator_of_mem hym Φ).symm
        have hle : (minorIcc η m).indicator Φ y ≤
            ∑ k ∈ Finset.range (n + 1), (minorIcc η k).indicator Φ y :=
          Finset.single_le_sum (fun k _ => Set.indicator_nonneg (fun z _ => hΦ0 z) y) hmn
        linarith
    · rw [Set.indicator_of_notMem hy]
      linarith
  have hgapint : Integrable ((Ioo (2 : ℝ) (2 + 2 * η)).indicator Φ) volume :=
    (integrableOn_of_bounded_of_finite hΦmeas hΦabs hgapfin).integrable_indicator
      measurableSet_Ioo
  have hIint : ∀ m : ℕ, Integrable ((minorIcc η m).indicator Φ) volume := fun m =>
    (integrableOn_of_bounded_of_finite hΦmeas hΦabs (hIfin m)).integrable_indicator
      (hImeas m)
  have hC : (∫ y in Icc (1 : ℝ) n, Φ y) ≤
      (∫ y in Ioo (2 : ℝ) (2 + 2 * η), Φ y) +
        ∑ m ∈ Finset.range (n + 1), ∫ y in minorIcc η m, Φ y := by
    rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Ioo]
    have hsumint : Integrable
        (fun y => ∑ m ∈ Finset.range (n + 1), (minorIcc η m).indicator Φ y) volume :=
      integrable_finsetSum _ fun m _ => hIint m
    have hsum_eq : (∑ m ∈ Finset.range (n + 1), ∫ y in minorIcc η m, Φ y) =
        ∫ y, ∑ m ∈ Finset.range (n + 1), (minorIcc η m).indicator Φ y := by
      rw [integral_finsetSum _ fun m _ => hIint m]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [integral_indicator (hImeas m)]
    rw [hsum_eq, ← integral_add hgapint hsumint]
    exact integral_mono (hΦIcc.integrable_indicator measurableSet_Icc) (hgapint.add hsumint)
      hcover
  have hgap : (∫ y in Ioo (2 : ℝ) (2 + 2 * η), Φ y) ≤ P * (2 * η) := by
    have hfin : IsFiniteMeasure (volume.restrict (Ioo (2 : ℝ) (2 + 2 * η))) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hgapfin⟩
    calc (∫ y in Ioo (2 : ℝ) (2 + 2 * η), Φ y) ≤ ∫ _y in Ioo (2 : ℝ) (2 + 2 * η), P :=
          integral_mono (integrableOn_of_bounded_of_finite hΦmeas hΦabs hgapfin)
            (integrable_const P) hΦP
      _ = P * (2 * η) := by
          rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo,
            ENNReal.toReal_ofReal (by linarith), mul_comm]
          congr 1
          ring
  -- each minorizing interval is dominated by a convolution power
  have hIm : ∀ m : ℕ, (∫ y in minorIcc η m, Φ y) ≤
      (1 / minorConst κ η m) * ∫ y, Φ y ∂(measureConvPow ν (m + 1)) := by
    intro m
    have hc := minorConst_pos hκ hη m
    have hmin := measureConvPow_ge_minor ν hκ.le hη hη4
      (gaussianAscendingLadderLaw_common_minorization hX (hG 0) ha.le haM) m
    have hint : Integrable Φ (measureConvPow ν (m + 1)) := hΦint _
    have hstep : (∫ y, Φ y ∂(ENNReal.ofReal (minorConst κ η m) • volume.restrict (minorIcc η m))) ≤
        ∫ y, Φ y ∂(measureConvPow ν (m + 1)) :=
      integral_mono_measure hmin (Filter.Eventually.of_forall hΦ0) hint
    rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal hc.le] at hstep
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc, mul_comm]
    exact hstep
  -- Step D: from `Φ` back to `Ψ`
  have hD : ∀ m : ℕ, m < n + 1 → (∫ y, Φ y ∂(measureConvPow ν (m + 1))) ≤
      D + P * (((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2) := by
    intro m hm
    have hpt : ∀ y, Φ y ≤ Ψ y + (Ioi S).indicator (fun _ => P) y := by
      intro y
      by_cases hy : y ≤ S
      · rw [Set.indicator_of_notMem (show y ∉ Ioi S from not_lt.mpr hy), add_zero, hΦdef]
        simp only []
        rw [max_eq_left (hΨnn y hy)]
      · rw [Set.indicator_of_mem (show y ∈ Ioi S from not_le.mp hy)]
        refine max_le (by linarith [hP]) ?_
        linarith [hΨlow y]
    have hΨint' : Integrable Ψ (measureConvPow ν (m + 1)) := by
      refine (integrable_const P).mono' hΨmeas.aestronglyMeasurable ?_
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨hΨlow y, hΨP y⟩
    have hind : Integrable ((Ioi S).indicator (fun _ : ℝ => P)) (measureConvPow ν (m + 1)) :=
      (integrable_const P).indicator measurableSet_Ioi
    have htail : (measureConvPow ν (m + 1)).real (Ioi S) ≤
        ((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2 := by
      refine (measureReal_mono (Ioi_subset_Ioi hTS) (measure_ne_top _ _)).trans ?_
      exact gaussianLadder_convPow_tail_le hX hi hG hδ hδa haM (m + 1) hT
    calc (∫ y, Φ y ∂(measureConvPow ν (m + 1)))
        ≤ ∫ y, (Ψ y + (Ioi S).indicator (fun _ => P) y) ∂(measureConvPow ν (m + 1)) :=
          integral_mono (hΦint _) (hΨint'.add hind) hpt
      _ = (∫ y, Ψ y ∂(measureConvPow ν (m + 1))) +
          P * (measureConvPow ν (m + 1)).real (Ioi S) := by
          rw [integral_add hΨint' hind, integral_indicator_const _ measurableSet_Ioi,
            smul_eq_mul, mul_comm]
      _ ≤ D + P * (((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2) := by
          have := hΨint m hm
          have := mul_le_mul_of_nonneg_left htail hP.le
          linarith
  -- assemble
  have hsumle : (∑ m ∈ Finset.range (n + 1), ∫ y in minorIcc η m, Φ y) ≤
      ∑ m ∈ Finset.range (n + 1),
        (1 / minorConst κ η m) * (D + P * (((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2)) := by
    refine Finset.sum_le_sum fun m hm => ?_
    refine (hIm m).trans ?_
    exact mul_le_mul_of_nonneg_left (hD m (Finset.mem_range.mp hm))
      (le_of_lt (one_div_pos.mpr (minorConst_pos hκ hη m)))
  have hsum_split : (∑ m ∈ Finset.range (n + 1),
        (1 / minorConst κ η m) * (D + P * (((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2))) =
      (∑ m ∈ Finset.range (n + 1), 1 / minorConst κ η m) * D +
        ∑ m ∈ Finset.range (n + 1),
          (1 / minorConst κ η m) * (P * (((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2)) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hκinv : 0 < 1 / κ := one_div_pos.mpr hκ
  have h1 := hsetle (Iio 1) measurableSet_Iio
  have h3 := hsetle (Ioi (n : ℝ)) measurableSet_Ioi
  have h1' : (∫ y, (Iio (1 : ℝ)).indicator Φ y ∂σ) ≤ P * (1 - κ) ^ m₀ :=
    h1.trans (mul_le_mul_of_nonneg_left hσ1 hP.le)
  have h3' : (∫ y, (Ioi (n : ℝ)).indicator Φ y ∂σ) ≤
      P * ((m₀ : ℝ) ^ 3 * B / ((n : ℝ) / 2) ^ 2 + B / (κ * ((n : ℝ) / 2))) :=
    h3.trans (mul_le_mul_of_nonneg_left hσn hP.le)
  have hmid' : (∫ y, (Icc (1 : ℝ) n).indicator Φ y ∂σ) ≤
      (1 / κ) * (P * (2 * η) +
        ((∑ m ∈ Finset.range (n + 1), 1 / minorConst κ η m) * D +
          ∑ m ∈ Finset.range (n + 1),
            (1 / minorConst κ η m) * (P * (((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2)))) := by
    refine hmid.trans (mul_le_mul_of_nonneg_left ?_ hκinv.le)
    rw [← hsum_split]
    linarith [hC, hgap, hsumle]
  unfold blackwellAmplification blackwellRemainder
  show (∫ y, Φ y ∂σ) ≤ _
  linarith [hB, h1', h3', hmid']


/-! ## Suprema, infima and the pigeonhole -/

/-- `L(β) = sup_{u ≥ β} W(u)`. -/
def windowSup (W : ℝ → ℝ) (β : ℝ) : ℝ := sSup (W '' Ici β)

/-- `ℓ(β) = inf_{u ≥ β} W(u)`. -/
def windowInf (W : ℝ → ℝ) (β : ℝ) : ℝ := sInf (W '' Ici β)

section WindowSupInf

variable {W : ℝ → ℝ} {P : ℝ}

theorem windowSup_bddAbove (hWP : ∀ u, W u ≤ P) (β : ℝ) : BddAbove (W '' Ici β) := by
  refine ⟨P, ?_⟩
  rintro z ⟨u, -, rfl⟩
  exact hWP u

theorem windowInf_bddBelow (hW0 : ∀ u, 0 ≤ W u) (β : ℝ) : BddBelow (W '' Ici β) := by
  refine ⟨0, ?_⟩
  rintro z ⟨u, -, rfl⟩
  exact hW0 u

theorem le_windowSup (hWP : ∀ u, W u ≤ P) {β u : ℝ} (hβu : β ≤ u) : W u ≤ windowSup W β :=
  le_csSup (windowSup_bddAbove hWP β) ⟨u, hβu, rfl⟩

theorem windowInf_le (hW0 : ∀ u, 0 ≤ W u) {β u : ℝ} (hβu : β ≤ u) : windowInf W β ≤ W u :=
  csInf_le (windowInf_bddBelow hW0 β) ⟨u, hβu, rfl⟩

theorem windowSup_le (hWP : ∀ u, W u ≤ P) (β : ℝ) : windowSup W β ≤ P := by
  refine csSup_le ⟨W β, β, Set.mem_Ici.mpr le_rfl, rfl⟩ ?_
  rintro z ⟨u, -, rfl⟩
  exact hWP u

theorem windowInf_nonneg (hW0 : ∀ u, 0 ≤ W u) (β : ℝ) : 0 ≤ windowInf W β := by
  refine le_csInf ⟨W β, β, Set.mem_Ici.mpr le_rfl, rfl⟩ ?_
  rintro z ⟨u, -, rfl⟩
  exact hW0 u

theorem windowSup_nonneg (hW0 : ∀ u, 0 ≤ W u) (hWP : ∀ u, W u ≤ P) (β : ℝ) :
    0 ≤ windowSup W β :=
  (hW0 β).trans (le_windowSup hWP le_rfl)

theorem windowInf_le_bound (hW0 : ∀ u, 0 ≤ W u) (hWP : ∀ u, W u ≤ P) (β : ℝ) :
    windowInf W β ≤ P :=
  (windowInf_le hW0 le_rfl).trans (hWP β)

theorem windowSup_antitone (hWP : ∀ u, W u ≤ P) {β β' : ℝ} (h : β ≤ β') :
    windowSup W β' ≤ windowSup W β :=
  csSup_le_csSup (windowSup_bddAbove hWP β) ⟨W β', β', Set.mem_Ici.mpr le_rfl, rfl⟩
    (Set.image_mono (Ici_subset_Ici.mpr h))

theorem windowInf_monotone (hW0 : ∀ u, 0 ≤ W u) {β β' : ℝ} (h : β ≤ β') :
    windowInf W β ≤ windowInf W β' :=
  csInf_le_csInf (windowInf_bddBelow hW0 β) ⟨W β', β', Set.mem_Ici.mpr le_rfl, rfl⟩
    (Set.image_mono (Ici_subset_Ici.mpr h))

end WindowSupInf

/-- Pigeonhole: a `[0,P]`-valued sequence has a step whose decrease is at most
`P/N` among the first `N` steps. -/
theorem exists_block_small_decrease {f : ℕ → ℝ} {P : ℝ} (hf0 : ∀ j, 0 ≤ f j)
    (hfP : ∀ j, f j ≤ P) {N : ℕ} (hN : 0 < N) :
    ∃ j, j < N ∧ f j - f (j + 1) ≤ P / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : (∑ j ∈ Finset.range N, (f j - f (j + 1))) = f 0 - f N :=
    Finset.sum_range_sub' f N
  have hle : (∑ j ∈ Finset.range N, (f j - f (j + 1))) ≤
      ∑ _j ∈ Finset.range N, P / N := by
    rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_div_cancel₀ _ hNpos.ne']
    linarith [hf0 N, hfP 0]
  obtain ⟨j, hj, hle'⟩ := Finset.exists_le_of_sum_le ⟨0, Finset.mem_range.mpr hN⟩ hle
  exact ⟨j, Finset.mem_range.mp hj, hle'⟩

/-- Pigeonhole: a `[0,P]`-valued sequence has a step whose increase is at most
`P/N` among the first `N` steps. -/
theorem exists_block_small_increase {f : ℕ → ℝ} {P : ℝ} (hf0 : ∀ j, 0 ≤ f j)
    (hfP : ∀ j, f j ≤ P) {N : ℕ} (hN : 0 < N) :
    ∃ j, j < N ∧ f (j + 1) - f j ≤ P / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : (∑ j ∈ Finset.range N, (f (j + 1) - f j)) = f N - f 0 :=
    Finset.sum_range_sub f N
  have hle : (∑ j ∈ Finset.range N, (f (j + 1) - f j)) ≤
      ∑ _j ∈ Finset.range N, P / N := by
    rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_div_cancel₀ _ hNpos.ne']
    linarith [hf0 0, hfP N]
  obtain ⟨j, hj, hle'⟩ := Finset.exists_le_of_sum_le ⟨0, Finset.mem_range.mpr hN⟩ hle
  exact ⟨j, Finset.mem_range.mp hj, hle'⟩

/-! ## The remote tail -/

/-- `θ`: the common bound for the tails `ν^{*j}((c-K, ∞))`, `j ≤ n+1`,
`c ≥ β₀`. -/
def blackwellTheta (B K β₀ : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ 3 * B / (β₀ - K) ^ 2

theorem blackwellTheta_nonneg {B K β₀ : ℝ} (hB : 0 ≤ B) (n : ℕ) :
    0 ≤ blackwellTheta B K β₀ n := by
  unfold blackwellTheta
  positivity

theorem convPow_tail_le_theta [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M)
    {K β₀ : ℝ} (hβ₀ : K < β₀) (n : ℕ) {j : ℕ} (hj : j ≤ n + 1) {c : ℝ} (hc : β₀ ≤ c) :
    (measureConvPow (gaussianAscendingLadderLaw X μ a) j).real (Ioi (c - K)) ≤
      blackwellTheta (gaussianAscendingLadderMomentBound δ M 2) K β₀ n := by
  have hB0 := gaussianAscendingLadderMomentBound_two_nonneg hX hi hG hδ hδa haM
  set B := gaussianAscendingLadderMomentBound δ M 2 with hBdef
  have hpos : 0 < c - K := by linarith
  refine (gaussianLadder_convPow_tail_le hX hi hG hδ hδa haM j hpos).trans ?_
  unfold blackwellTheta
  have hj' : (j : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hj
  have h1 : (j : ℝ) ^ 3 * B ≤ ((n : ℝ) + 1) ^ 3 * B := by gcongr
  have h2 : (β₀ - K) ^ 2 ≤ (c - K) ^ 2 := by gcongr
  have hd : 0 < (β₀ - K) ^ 2 := by
    have : 0 < β₀ - K := by linarith
    positivity
  exact div_le_div₀ (by positivity) h1 hd h2

/-! ## Assembly at fixed drift and window length -/

/-- The full error bound of the Blackwell argument at the chosen parameters. -/
def blackwellTotal (κ B P K η T β₀ : ℝ) (n m₀ N : ℕ) : ℝ :=
  blackwellAmplification κ η n *
      (2 * P / N + ((n : ℝ) + 1) * blackwellTheta B K β₀ n) +
    blackwellRemainder κ B P η T n m₀ +
    (P + K / κ) * blackwellTheta B K β₀ n

/-- **Upper bound.**  Beyond `β₀ + N T` the window mass exceeds `x/μ_a` by at
most the total error. -/
theorem renewalWindow_sub_le_blackwellTotal [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M)
    {x K : ℝ} (hx : 0 ≤ x) (hxK : x ≤ K)
    {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) (n m₀ : ℕ) (hn : 1 ≤ n) (hm₀ : m₀ ≤ n)
    {T β₀ : ℝ} (hT : 0 < T) (hβ₀ : K < β₀) (N : ℕ) (hN : 0 < N)
    {b : ℝ} (hb : β₀ + N * T ≤ b) :
    renewalWindow (gaussianAscendingLadderLaw X μ a) x b -
        x / ladderMean (gaussianAscendingLadderLaw X μ a) ≤
      blackwellTotal (gaussianAscendingLadderCommonDensity M)
        (gaussianAscendingLadderMomentBound δ M 2) (blackwellWindowBound M K) K η T β₀
        n m₀ N := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  have hQprob := gaussianAscendingLadderEquilibrium_isProbabilityMeasure hX hi hG hδ hδa haM
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  set κ := gaussianAscendingLadderCommonDensity M with hκdef
  set B := gaussianAscendingLadderMomentBound δ M 2 with hBdef
  set P := blackwellWindowBound M K with hPdef
  set θ := blackwellTheta B K β₀ n with hθdef
  set A := blackwellAmplification κ η n with hAdef
  set R₀ := blackwellRemainder κ B P η T n m₀ with hR₀def
  set μ0 := ladderMean ν with hμ0def
  set W : ℝ → ℝ := renewalWindow ν x with hWdef
  have hσprob : IsProbabilityMeasure (blackwellSmoothing ν m₀) :=
    blackwellSmoothing_isProbabilityMeasure ν hQprob m₀
  set σ := blackwellSmoothing ν m₀ with hσdef
  have hK : 0 ≤ K := hx.trans hxK
  have hκ : 0 < κ := gaussianAscendingLadderCommonDensity_pos M
  have hB0 : 0 ≤ B := gaussianAscendingLadderMomentBound_two_nonneg hX hi hG hδ hδa haM
  have hP : 0 < P := blackwellWindowBound_pos hK
  have hθ0 : 0 ≤ θ := blackwellTheta_nonneg hB0 n
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    unfold blackwellAmplification
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ => ?_)
    exact (one_div_pos.mpr (minorConst_pos hκ hη m)).le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hW0 : ∀ u, 0 ≤ W u := fun u => renewalWindow_nonneg ν x u
  have hWP : ∀ u, W u ≤ P := fun u =>
    renewalWindow_le_blackwellWindowBound hX hi hG ha haM hx hxK u
  have hUP : ∀ u, ladderRenewalMeasure ν (Ioc (u - x) u) ≤ ENNReal.ofReal P := fun u =>
    ladderRenewalMeasure_window_le_ofReal hX hi hG ha haM hx hxK u
  set L : ℝ → ℝ := windowSup W with hLdef
  have hL0 : ∀ β, 0 ≤ L β := fun β => windowSup_nonneg hW0 hWP β
  have hLP : ∀ β, L β ≤ P := fun β => windowSup_le hWP β
  -- pigeonhole over the blocks
  obtain ⟨j, hjN, hjstep⟩ := exists_block_small_decrease
    (f := fun j : ℕ => L (β₀ + j * T)) (fun j => hL0 _) (fun j => hLP _) hN
  set β : ℝ := β₀ + j * T with hβdef
  set β' : ℝ := β₀ + (j + 1 : ℕ) * T with hβ'def
  have hββ' : β' = β + T := by
    rw [hβ'def, hβdef]
    push_cast
    ring
  have hβ₀β : β₀ ≤ β := by
    rw [hβdef]
    have : (0 : ℝ) ≤ j * T := by positivity
    linarith
  have hstep : L β - L β' ≤ P / N := hjstep
  -- the near-supremum point
  set ϵ : ℝ := P / N with hϵdef
  have hϵ : 0 < ϵ := by positivity
  obtain ⟨bs, hbs, hWbs⟩ := exists_near_window_sSup hWP β' hϵ
  have hbsβ : β ≤ bs := by linarith [hbs, hββ', hT]
  -- the deficit
  set S : ℝ := bs - β with hSdef
  have hTS : T ≤ S := by linarith [hbs, hββ']
  set Ψ : ℝ → ℝ := fun y => L β - W (bs - y) with hΨdef
  have hΨmeas : Measurable Ψ := measurable_const.sub (measurable_renewalWindow_shift ν x bs)
  have hΨP : ∀ y, Ψ y ≤ P := fun y => by
    show L β - W (bs - y) ≤ P
    linarith [hLP β, hW0 (bs - y)]
  have hΨlow : ∀ y, -P ≤ Ψ y := fun y => by
    show -P ≤ L β - W (bs - y)
    linarith [hL0 β, hWP (bs - y)]
  have hΨnn : ∀ y, y ≤ S → 0 ≤ Ψ y := fun y hy => by
    show 0 ≤ L β - W (bs - y)
    have : W (bs - y) ≤ L β := le_windowSup hWP (by linarith)
    linarith
  -- the correction terms are bounded by `θ`
  have hcorr : ∀ m : ℕ, m < n + 1 →
      (∑ i ∈ Finset.range (m + 1),
        (measureConvPow ν i (Ioc (bs - x) bs)).toReal) ≤ ((n : ℝ) + 1) * θ := by
    intro m hm
    have hterm : ∀ i ∈ Finset.range (m + 1),
        (measureConvPow ν i (Ioc (bs - x) bs)).toReal ≤ θ := by
      intro i hi'
      have hi'' : i ≤ n + 1 := by
        have := Finset.mem_range.mp hi'
        omega
      have hsub : Ioc (bs - x) bs ⊆ Ioi (bs - K) := by
        intro y hy
        show bs - K < y
        linarith [hy.1]
      calc (measureConvPow ν i (Ioc (bs - x) bs)).toReal
          ≤ (measureConvPow ν i).real (Ioi (bs - K)) :=
            measureReal_mono hsub (measure_ne_top _ _)
        _ ≤ θ := convPow_tail_le_theta hX hi hG hδ hδa haM hβ₀ n hi'' (hβ₀β.trans hbsβ)
    calc (∑ i ∈ Finset.range (m + 1), (measureConvPow ν i (Ioc (bs - x) bs)).toReal)
        ≤ ∑ _i ∈ Finset.range (m + 1), θ := Finset.sum_le_sum hterm
      _ = ((m : ℝ) + 1) * θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ((n : ℝ) + 1) * θ := by
          have : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
            have : (m : ℝ) ≤ n := by exact_mod_cast (Nat.lt_succ_iff.mp hm)
            linarith
          exact mul_le_mul_of_nonneg_right this hθ0
  set D : ℝ := 2 * P / N + ((n : ℝ) + 1) * θ with hDdef
  have hΨint : ∀ m : ℕ, m < n + 1 → (∫ y, Ψ y ∂(measureConvPow ν (m + 1))) ≤ D := by
    intro m hm
    have h := window_deficit_integral_eq ν hP.le hUP (m + 1) bs (L β)
    change (∫ y, (L β - W (bs - y)) ∂(measureConvPow ν (m + 1))) ≤ D
    rw [h]
    have hc := hcorr m hm
    have hWbs' : L β' - ϵ ≤ W bs := hWbs
    rw [hDdef]
    have : 2 * P / N = P / N + P / N := by ring
    rw [this]
    linarith
  -- the core estimate
  have hcore := deficit_integral_smoothing_le hX hi hG hδ hδa haM hK hη hη4 n m₀ hn hT hTS
    hΨmeas hΨP hΨlow hΨnn hΨint
  -- the stationary identity through the smoothing
  have hstat := integral_window_blackwellSmoothing_sub_le hX hi hG hδ hδa haM hx hxK m₀ bs
  have htail : (measureConvPow ν m₀).real (Ioi (bs - K)) ≤ θ :=
    convPow_tail_le_theta hX hi hG hδ hδa haM hβ₀ n (by omega) (hβ₀β.trans hbsβ)
  have hstat' : (∫ w, W (bs - w) ∂σ) - x / μ0 ≤ (P + K / κ) * θ := by
    have h1 := (abs_le.mp hstat).2
    have h2 : (P + K / κ) * (measureConvPow ν m₀).real (Ioi (bs - K)) ≤ (P + K / κ) * θ :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    linarith
  -- `∫ Ψ dσ = L β - ∫ W(bs - ·) dσ`
  have hWint : Integrable (fun w => W (bs - w)) σ := by
    refine (integrable_const P).mono' (measurable_renewalWindow_shift ν x bs).aestronglyMeasurable ?_
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (hW0 _)]
    exact hWP _
  have hΨσ : (∫ y, Ψ y ∂σ) = L β - ∫ w, W (bs - w) ∂σ := by
    change (∫ y, (L β - W (bs - y)) ∂σ) = _
    rw [integral_sub (integrable_const _) hWint, integral_const, Measure.real, measure_univ,
      ENNReal.toReal_one, one_smul]
  have hΨΦ : (∫ y, Ψ y ∂σ) ≤ ∫ y, max (Ψ y) 0 ∂σ := by
    refine integral_mono ?_ ?_ fun y => le_max_left _ _
    · refine (integrable_const P).mono' hΨmeas.aestronglyMeasurable ?_
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨hΨlow y, hΨP y⟩
    · refine (integrable_const P).mono' (hΨmeas.max measurable_const).aestronglyMeasurable ?_
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (hΨP y) hP.le
  -- from `L β` to `W b`
  have hWb : W b ≤ L β := by
    have h1 : W b ≤ L (β₀ + N * T) := le_windowSup hWP hb
    have h2 : L (β₀ + N * T) ≤ L β := by
      refine windowSup_antitone hWP ?_
      rw [hβdef]
      have : (j : ℝ) ≤ N := by exact_mod_cast hjN.le
      nlinarith
    exact h1.trans h2
  -- assemble
  have hmain : L β - x / μ0 ≤ A * D + R₀ + (P + K / κ) * θ := by
    have : L β - x / μ0 = (∫ y, Ψ y ∂σ) + ((∫ w, W (bs - w) ∂σ) - x / μ0) := by
      rw [hΨσ]
      ring
    rw [this]
    linarith
  unfold blackwellTotal
  change W b - x / μ0 ≤ A * D + R₀ + (P + K / κ) * θ
  linarith

/-- **Lower bound.**  Beyond `β₀ + N T` the window mass falls short of `x/μ_a`
by at most the total error. -/
theorem sub_renewalWindow_le_blackwellTotal [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M)
    {x K : ℝ} (hx : 0 ≤ x) (hxK : x ≤ K)
    {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) (n m₀ : ℕ) (hn : 1 ≤ n) (hm₀ : m₀ ≤ n)
    {T β₀ : ℝ} (hT : 0 < T) (hβ₀ : K < β₀) (N : ℕ) (hN : 0 < N)
    {b : ℝ} (hb : β₀ + N * T ≤ b) :
    x / ladderMean (gaussianAscendingLadderLaw X μ a) -
        renewalWindow (gaussianAscendingLadderLaw X μ a) x b ≤
      blackwellTotal (gaussianAscendingLadderCommonDensity M)
        (gaussianAscendingLadderMomentBound δ M 2) (blackwellWindowBound M K) K η T β₀
        n m₀ N := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  have hQprob := gaussianAscendingLadderEquilibrium_isProbabilityMeasure hX hi hG hδ hδa haM
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  set κ := gaussianAscendingLadderCommonDensity M with hκdef
  set B := gaussianAscendingLadderMomentBound δ M 2 with hBdef
  set P := blackwellWindowBound M K with hPdef
  set θ := blackwellTheta B K β₀ n with hθdef
  set A := blackwellAmplification κ η n with hAdef
  set R₀ := blackwellRemainder κ B P η T n m₀ with hR₀def
  set μ0 := ladderMean ν with hμ0def
  set W : ℝ → ℝ := renewalWindow ν x with hWdef
  have hσprob : IsProbabilityMeasure (blackwellSmoothing ν m₀) :=
    blackwellSmoothing_isProbabilityMeasure ν hQprob m₀
  set σ := blackwellSmoothing ν m₀ with hσdef
  have hK : 0 ≤ K := hx.trans hxK
  have hκ : 0 < κ := gaussianAscendingLadderCommonDensity_pos M
  have hB0 : 0 ≤ B := gaussianAscendingLadderMomentBound_two_nonneg hX hi hG hδ hδa haM
  have hP : 0 < P := blackwellWindowBound_pos hK
  have hθ0 : 0 ≤ θ := blackwellTheta_nonneg hB0 n
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    unfold blackwellAmplification
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ => ?_)
    exact (one_div_pos.mpr (minorConst_pos hκ hη m)).le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hW0 : ∀ u, 0 ≤ W u := fun u => renewalWindow_nonneg ν x u
  have hWP : ∀ u, W u ≤ P := fun u =>
    renewalWindow_le_blackwellWindowBound hX hi hG ha haM hx hxK u
  have hWlow : ∀ u, -P ≤ W u := fun u => by linarith [hW0 u, hP]
  have hUP : ∀ u, ladderRenewalMeasure ν (Ioc (u - x) u) ≤ ENNReal.ofReal P := fun u =>
    ladderRenewalMeasure_window_le_ofReal hX hi hG ha haM hx hxK u
  set ℓ : ℝ → ℝ := windowInf W with hℓdef
  have hℓ0 : ∀ β, 0 ≤ ℓ β := fun β => windowInf_nonneg hW0 β
  have hℓP : ∀ β, ℓ β ≤ P := fun β => windowInf_le_bound hW0 hWP β
  -- pigeonhole over the blocks
  obtain ⟨j, hjN, hjstep⟩ := exists_block_small_increase
    (f := fun j : ℕ => ℓ (β₀ + j * T)) (fun j => hℓ0 _) (fun j => hℓP _) hN
  set β : ℝ := β₀ + j * T with hβdef
  set β' : ℝ := β₀ + (j + 1 : ℕ) * T with hβ'def
  have hββ' : β' = β + T := by
    rw [hβ'def, hβdef]
    push_cast
    ring
  have hβ₀β : β₀ ≤ β := by
    rw [hβdef]
    have : (0 : ℝ) ≤ j * T := by positivity
    linarith
  have hstep : ℓ β' - ℓ β ≤ P / N := hjstep
  -- the near-infimum point
  set ϵ : ℝ := P / N with hϵdef
  have hϵ : 0 < ϵ := by positivity
  obtain ⟨bs, hbs, hWbs⟩ := exists_near_window_sInf hWlow β' hϵ
  have hbsβ : β ≤ bs := by linarith [hbs, hββ', hT]
  -- the deficit
  set S : ℝ := bs - β with hSdef
  have hTS : T ≤ S := by linarith [hbs, hββ']
  set Ψ : ℝ → ℝ := fun y => W (bs - y) - ℓ β with hΨdef
  have hΨmeas : Measurable Ψ := (measurable_renewalWindow_shift ν x bs).sub measurable_const
  have hΨP : ∀ y, Ψ y ≤ P := fun y => by
    show W (bs - y) - ℓ β ≤ P
    linarith [hℓ0 β, hWP (bs - y)]
  have hΨlow : ∀ y, -P ≤ Ψ y := fun y => by
    show -P ≤ W (bs - y) - ℓ β
    linarith [hℓP β, hW0 (bs - y)]
  have hΨnn : ∀ y, y ≤ S → 0 ≤ Ψ y := fun y hy => by
    show 0 ≤ W (bs - y) - ℓ β
    have : ℓ β ≤ W (bs - y) := windowInf_le hW0 (by linarith)
    linarith
  set D : ℝ := 2 * P / N + ((n : ℝ) + 1) * θ with hDdef
  have hΨint : ∀ m : ℕ, m < n + 1 → (∫ y, Ψ y ∂(measureConvPow ν (m + 1))) ≤ D := by
    intro m _hm
    have h := window_deficit_integral_eq ν hP.le hUP (m + 1) bs (ℓ β)
    have hneg : (∫ y, Ψ y ∂(measureConvPow ν (m + 1))) =
        -∫ y, (ℓ β - W (bs - y)) ∂(measureConvPow ν (m + 1)) := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show W (bs - y) - ℓ β = -(ℓ β - W (bs - y))
      ring
    rw [hneg, h]
    have hc : 0 ≤ ∑ i ∈ Finset.range (m + 1), (measureConvPow ν i (Ioc (bs - x) bs)).toReal :=
      Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
    have hWbs' : W bs ≤ ℓ β' + ϵ := hWbs
    have hθ' : 0 ≤ ((n : ℝ) + 1) * θ := by positivity
    rw [hDdef]
    have : 2 * P / N = P / N + P / N := by ring
    rw [this]
    linarith
  -- the core estimate
  have hcore := deficit_integral_smoothing_le hX hi hG hδ hδa haM hK hη hη4 n m₀ hn hT hTS
    hΨmeas hΨP hΨlow hΨnn hΨint
  -- the stationary identity through the smoothing
  have hstat := integral_window_blackwellSmoothing_sub_le hX hi hG hδ hδa haM hx hxK m₀ bs
  have htail : (measureConvPow ν m₀).real (Ioi (bs - K)) ≤ θ :=
    convPow_tail_le_theta hX hi hG hδ hδa haM hβ₀ n (by omega) (hβ₀β.trans hbsβ)
  have hstat' : x / μ0 - (∫ w, W (bs - w) ∂σ) ≤ (P + K / κ) * θ := by
    have h1 := (abs_le.mp hstat).1
    have h2 : (P + K / κ) * (measureConvPow ν m₀).real (Ioi (bs - K)) ≤ (P + K / κ) * θ :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    linarith
  -- `∫ Ψ dσ = ∫ W(bs - ·) dσ - ℓ β`
  have hWint : Integrable (fun w => W (bs - w)) σ := by
    refine (integrable_const P).mono' (measurable_renewalWindow_shift ν x bs).aestronglyMeasurable ?_
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (hW0 _)]
    exact hWP _
  have hΨσ : (∫ y, Ψ y ∂σ) = (∫ w, W (bs - w) ∂σ) - ℓ β := by
    change (∫ y, (W (bs - y) - ℓ β) ∂σ) = _
    rw [integral_sub hWint (integrable_const _), integral_const, Measure.real, measure_univ,
      ENNReal.toReal_one, one_smul]
  have hΨΦ : (∫ y, Ψ y ∂σ) ≤ ∫ y, max (Ψ y) 0 ∂σ := by
    refine integral_mono ?_ ?_ fun y => le_max_left _ _
    · refine (integrable_const P).mono' hΨmeas.aestronglyMeasurable ?_
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨hΨlow y, hΨP y⟩
    · refine (integrable_const P).mono' (hΨmeas.max measurable_const).aestronglyMeasurable ?_
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (hΨP y) hP.le
  -- from `ℓ β` to `W b`
  have hWb : ℓ β ≤ W b := by
    have h1 : ℓ (β₀ + N * T) ≤ W b := windowInf_le hW0 hb
    have h2 : ℓ β ≤ ℓ (β₀ + N * T) := by
      refine windowInf_monotone hW0 ?_
      rw [hβdef]
      have : (j : ℝ) ≤ N := by exact_mod_cast hjN.le
      nlinarith
    exact h2.trans h1
  -- assemble
  have hmain : x / μ0 - ℓ β ≤ A * D + R₀ + (P + K / κ) * θ := by
    have : x / μ0 - ℓ β = (x / μ0 - (∫ w, W (bs - w) ∂σ)) + ∫ y, Ψ y ∂σ := by
      rw [hΨσ]
      ring
    rw [this]
    linarith
  unfold blackwellTotal
  change x / μ0 - W b ≤ A * D + R₀ + (P + K / κ) * θ
  linarith

/-! ## Choosing the parameters -/

/-- A real function tending to `0` at `+∞` drops below any positive threshold
at some point beyond any prescribed `c`. -/
theorem exists_gt_lt_of_tendsto_zero {g : ℝ → ℝ} (h : Tendsto g atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (c : ℝ) : ∃ t, c < t ∧ g t < ε := by
  obtain ⟨t, h1, h2⟩ := (((tendsto_order.1 h).2 ε hε).and (eventually_gt_atTop c)).exists
  exact ⟨t, h2, h1⟩

theorem exists_nat_gt_lt_of_tendsto_zero {g : ℕ → ℝ} (h : Tendsto g atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (c : ℕ) : ∃ n, c < n ∧ g n < ε := by
  obtain ⟨t, h1, h2⟩ := (((tendsto_order.1 h).2 ε hε).and (eventually_gt_atTop c)).exists
  exact ⟨t, h2, h1⟩

/-- **Parameter selection.**  For any admissible constants the total error can
be made smaller than any `ε > 0` by choosing, in this order, the minorization
margin `η`, the smoothing order `m₀`, the convolution depth `n`, the block
length `T`, the number of blocks `N` and the starting point `β₀`. -/
theorem exists_blackwellTotal_le {κ B P K ε : ℝ} (hκ : 0 < κ) (hP : 0 < P)
    (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ (η T β₀ : ℝ) (n m₀ N : ℕ), 0 < η ∧ η ≤ 1 / 4 ∧ 1 ≤ n ∧ m₀ ≤ n ∧ 0 < T ∧ K < β₀ ∧
      0 < N ∧ blackwellTotal κ B P K η T β₀ n m₀ N ≤ ε := by
  -- the margin `η`
  set η : ℝ := min (1 / 4) (κ * ε / (10 * P)) with hηdef
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη4 : η ≤ 1 / 4 := min_le_left _ _
  have hηterm : (1 / κ) * (P * (2 * η)) ≤ ε / 5 := by
    have hle : η ≤ κ * ε / (10 * P) := min_le_right _ _
    calc (1 / κ) * (P * (2 * η)) ≤ (1 / κ) * (P * (2 * (κ * ε / (10 * P)))) := by gcongr
      _ = ε / 5 := by field_simp; norm_num
  -- the smoothing order `m₀`
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one (x := ε / (5 * P)) (y := 1 - κ)
    (by positivity) (by linarith)
  have hm₀term : P * (1 - κ) ^ m₀ ≤ ε / 5 := by
    calc P * (1 - κ) ^ m₀ ≤ P * (ε / (5 * P)) := mul_le_mul_of_nonneg_left hm₀.le hP.le
      _ = ε / 5 := by field_simp
  -- the convolution depth `n`
  have hntend : Tendsto (fun n : ℕ =>
      P * ((m₀ : ℝ) ^ 3 * B / ((n : ℝ) / 2) ^ 2 + B / (κ * ((n : ℝ) / 2)))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) / 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
    have h3 : Tendsto (fun n : ℕ => ((n : ℝ) / 2) ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp h2
    have h4 : Tendsto (fun n : ℕ => κ * ((n : ℝ) / 2)) atTop atTop := h2.const_mul_atTop hκ
    have h5 : Tendsto (fun n : ℕ => (m₀ : ℝ) ^ 3 * B / ((n : ℝ) / 2) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop h3
    have h6 : Tendsto (fun n : ℕ => B / (κ * ((n : ℝ) / 2))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop h4
    have := (h5.add h6).const_mul P
    simpa only [add_zero, mul_zero] using this
  obtain ⟨n, hnmax, hnterm⟩ :=
    exists_nat_gt_lt_of_tendsto_zero hntend (by positivity : (0 : ℝ) < ε / 5) (max m₀ 1)
  have hn : 1 ≤ n := le_trans (le_max_right m₀ 1) hnmax.le
  have hm₀n : m₀ ≤ n := le_trans (le_max_left m₀ 1) hnmax.le
  -- the block length `T`
  have hTtend : Tendsto (fun T : ℝ => (1 / κ) * ∑ m ∈ Finset.range (n + 1),
      (1 / minorConst κ η m) * (P * (((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2))) atTop (𝓝 0) := by
    have hsum : Tendsto (fun T : ℝ => ∑ m ∈ Finset.range (n + 1),
        (1 / minorConst κ η m) * (P * (((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2))) atTop
        (𝓝 (∑ m ∈ Finset.range (n + 1), (0 : ℝ))) := by
      refine tendsto_finsetSum _ fun m _ => ?_
      have h1 : Tendsto (fun T : ℝ => (((m + 1 : ℕ) : ℝ) ^ 3 * B) / T ^ 2) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
      have := (h1.const_mul P).const_mul (1 / minorConst κ η m)
      simpa only [mul_zero] using this
    have := hsum.const_mul (1 / κ)
    simpa only [Finset.sum_const_zero, mul_zero] using this
  obtain ⟨T, hT, hTterm⟩ :=
    exists_gt_lt_of_tendsto_zero hTtend (by positivity : (0 : ℝ) < ε / 5) 0
  -- the number of blocks `N`
  set A : ℝ := blackwellAmplification κ η n with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    unfold blackwellAmplification
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ => ?_)
    exact (one_div_pos.mpr (minorConst_pos hκ hη m)).le
  have hNtend : Tendsto (fun N : ℕ => A * (2 * P / (N : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (2 * P)).const_mul A
    simpa only [mul_zero] using this
  obtain ⟨N, hN, hNterm⟩ :=
    exists_nat_gt_lt_of_tendsto_zero hNtend (by positivity : (0 : ℝ) < ε / 10) 0
  -- the starting point `β₀`
  set θc : ℝ := A * ((n : ℝ) + 1) + (P + K / κ) with hθcdef
  have hθc : 0 ≤ θc := by positivity
  have hβtend : Tendsto (fun β₀ : ℝ => θc * blackwellTheta B K β₀ n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun β₀ : ℝ => β₀ - K) atTop atTop :=
      tendsto_atTop_atTop.2 fun c => ⟨c + K, fun x hx => by linarith⟩
    have h2 : Tendsto (fun β₀ : ℝ => (β₀ - K) ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp h1
    have h3 : Tendsto (fun β₀ : ℝ => ((n : ℝ) + 1) ^ 3 * B / (β₀ - K) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop h2
    have := h3.const_mul θc
    rw [mul_zero] at this
    exact this
  obtain ⟨β₀, hβ₀, hβterm⟩ :=
    exists_gt_lt_of_tendsto_zero hβtend (by positivity : (0 : ℝ) < ε / 10) K
  -- assemble
  refine ⟨η, T, β₀, n, m₀, N, hη, hη4, hn, hm₀n, hT, hβ₀, hN, ?_⟩
  set θ : ℝ := blackwellTheta B K β₀ n with hθdef
  have hsplit : θc * θ = A * ((n : ℝ) + 1) * θ + (P + K / κ) * θ := by
    rw [hθcdef]
    ring
  have hkey : blackwellTotal κ B P K η T β₀ n m₀ N =
      A * (2 * P / N) + A * ((n : ℝ) + 1) * θ +
        (P * (1 - κ) ^ m₀ +
          P * ((m₀ : ℝ) ^ 3 * B / ((n : ℝ) / 2) ^ 2 + B / (κ * ((n : ℝ) / 2))) +
          (1 / κ) * (P * (2 * η)) +
          (1 / κ) * ∑ m ∈ Finset.range (n + 1),
            (1 / minorConst κ η m) * (P * (((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2))) +
        (P + K / κ) * θ := by
    unfold blackwellTotal blackwellRemainder
    rw [← hAdef, ← hθdef]
    ring
  rw [hkey]
  linarith

/-! ## The uniform Blackwell renewal theorem -/

/--
**The uniform Blackwell renewal theorem for the Gaussian ascending ladder
family.**  For every positive compact drift strip `[δ, M]`, every window range
`[0, K]` and every `ε > 0`, there is a threshold `b₀` beyond which
`U_a((b-x, b]) ≈ x / μ_a` within `ε`, uniformly in `a ∈ [δ, M]` and
`x ∈ [0, K]`.  This is `UniformRenewalWindowLimit X μ`, proved without any
provider hypothesis.
-/
theorem uniformRenewalWindowLimit_gaussian
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    UniformRenewalWindowLimit X μ := by
  have _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  intro δ M K ε hδ _hM hK hε
  have hκ := gaussianAscendingLadderCommonDensity_pos M
  have hP : 0 < blackwellWindowBound M K := blackwellWindowBound_pos hK
  obtain ⟨η, T, β₀, n, m₀, N, hη, hη4, hn, hm₀, hT, hβ₀, hN, htot⟩ :=
    exists_blackwellTotal_le (B := gaussianAscendingLadderMomentBound δ M 2) hκ hP hK hε
  refine ⟨β₀ + N * T, ?_, fun a ha b hb x hx hxK => ?_⟩
  · have hNT : (0 : ℝ) < (N : ℝ) * T := by
      have : (0 : ℝ) < N := by exact_mod_cast hN
      positivity
    linarith
  · have h1 := renewalWindow_sub_le_blackwellTotal hX hi hG hδ ha.1 ha.2 hx hxK hη hη4 n m₀
      hn hm₀ hT hβ₀ N hN hb
    have h2 := sub_renewalWindow_le_blackwellTotal hX hi hG hδ ha.1 ha.2 hx hxK hη hη4 n m₀
      hn hm₀ hT hβ₀ N hN hb
    unfold renewalWindow at h1 h2
    rw [abs_le]
    constructor <;> linarith

end SwingRepair
