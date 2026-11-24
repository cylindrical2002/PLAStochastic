import PLAStochastic.Swing.SecondSegment.Coefficient.Window
import PLAStochastic.Swing.SecondSegment.MeanLowerBound

/-! # The remainders off the window

`second-coefficient.md`, §3.  Off the window `ψ` of `Window`, three regions
remain and each is small uniformly in the budget:

* the far negative tail `r < -M`, where `g_E(r)/E ≤ 25` for `-r ≥ 1`
  (`frozenPrefixLength_negative_mean_large_c`) and `ℓ(r) ≤ 2/|r|`, while the
  entrance laws have mass `O(1/M)` there;
* the zero neighbourhood `-δ < r < 0`, where both kernels are at most
  `C(1 + log₊(1/|r|))` (Lemma H.1 and its limit) and the small-ball bound
  integrates the logarithm (C2.8);
* the positive side `r ≥ 0`, where `g_E(r)/E ≤ C(1 + log E)(1 + r_+)` and the
  first entrance has `ρ_{1,E}[0,∞) + ∫ r_+ dρ_{1,E} = O(E^{-1/4})` (C2.9).
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### Finite-budget pointwise bounds -/

theorem secondSegmentFrozenMean_div_le_linear
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ E) (r : ℝ) :
    secondSegmentFrozenMean X μ E r / E ≤
      frozenUniformMeanConstant * (1 + Real.log E) * (1 + max r 0) := by
  have hE0 : 0 < E := by linarith
  have h := frozenPrefixLength_uniform_mean_bound hX hi hG r hE
  have hlog : Real.log (Real.exp 1 * E) = 1 + Real.log E := by
    rw [Real.log_mul (Real.exp_ne_zero 1) hE0.ne', Real.log_exp]
  rw [hlog] at h
  rw [div_le_iff₀ hE0]
  calc secondSegmentFrozenMean X μ E r
      ≤ frozenUniformMeanConstant*E*(1+max r 0)*(1 + Real.log E) := h
    _ = _ := by ring

theorem secondSegmentFrozenMean_div_le_far
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ E) {r : ℝ} (hr : r ≤ -1) :
    secondSegmentFrozenMean X μ E r / E ≤ 25 := by
  have hE0 : 0 < E := by linarith
  have h := frozenPrefixLength_negative_mean_large_c hX hi hG (c := -r) (by linarith) hE
  rw [neg_neg] at h
  rw [div_le_iff₀ hE0]
  exact h

theorem secondSegmentFrozenMean_div_le_log
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 16 ≤ E) {r : ℝ} (hr : r < 0) :
    secondSegmentFrozenMean X μ E r / E ≤
      frozenNegativeCarryLogConstant * (1 + nearZeroLogWeight r) := by
  have hE0 : 0 < E := by linarith
  have h := frozenPrefixLength_negative_mean_log_bound hX hi hG (c := -r) (by linarith) hE
  rw [neg_neg] at h
  have hw : max (Real.log (1/(-r))) 0 = nearZeroLogWeight r := by
    unfold nearZeroLogWeight
    rw [abs_of_neg hr]
  rw [hw] at h
  rw [div_le_iff₀ hE0]
  calc secondSegmentFrozenMean X μ E r
      ≤ frozenNegativeCarryLogConstant*E*(1+nearZeroLogWeight r) := h
    _ = _ := by ring

theorem secondSegmentLimitKernel_le_log
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {r : ℝ} (hr : r < 0) :
    secondSegmentLimitKernel X μ r ≤
      frozenNegativeCarryLogConstant * (1 + nearZeroLogWeight r) := by
  have h := secondSegmentLimitKernel_neg_le_log hX hi hG (c := -r) (by linarith)
  rw [neg_neg] at h
  have hw : max (Real.log (1/(-r))) 0 = nearZeroLogWeight r := by
    unfold nearZeroLogWeight
    rw [abs_of_neg hr]
  rwa [hw] at h

/-! ### The finite-budget remainder -/

/-- The finite-budget remainder off the window, with every constant explicit. -/
theorem integral_frozenMean_mul_one_sub_window_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E δ M : ℝ} (hE : 16 ≤ E) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hM : 1 ≤ M) :
    Integrable (fun r => secondSegmentFrozenMean X μ E r / E) (nativeTransientMarginLaw X μ E 1) ∧
      (∫ r, secondSegmentFrozenMean X μ E r / E * (1 - secondSegmentWindow δ M r)
          ∂(nativeTransientMarginLaw X μ E 1)) ≤
        25 * (nativeFirstMarginMomentBound 1 / M) +
        frozenNegativeCarryLogConstant * (2 * nativeFirstMarginConcentrationConstant 1 * δ +
          4 * nativeFirstMarginConcentrationConstant 1 * Real.sqrt δ) +
        frozenUniformMeanConstant * (firstMarginNonnegConstant + secondMarginPosConstant) *
          ((1 + Real.log E) / Real.sqrt (Real.sqrt E)) := by
  have := hi.isProbabilityMeasure
  set ρ := nativeTransientMarginLaw X μ E 1 with hρ
  have : IsProbabilityMeasure ρ := nativeTransientMarginLaw_isProbability hX E 1
  have hE0 : 0 < E := by linarith
  have hE1 : 1 ≤ E := by linarith
  have hE2 : 1 ≤ 2*E := by linarith
  set f : ℝ → ℝ := fun r => secondSegmentFrozenMean X μ E r / E with hfdef
  set ψ : ℝ → ℝ := secondSegmentWindow δ M with hψdef
  have hfm : Measurable f := (secondSegmentFrozenMean_measurable hX E).div_const E
  have hf0 : ∀ r, 0 ≤ f r := fun r => div_nonneg (secondSegmentFrozenMean_nonneg X μ E r) hE0.le
  set K : ℝ := frozenNegativeCarryLogConstant with hKdef
  set Ku : ℝ := frozenUniformMeanConstant with hKudef
  set C1 : ℝ := nativeFirstMarginConcentrationConstant 1 with hC1def
  set m1 : ℝ := nativeFirstMarginMomentBound 1 with hm1def
  set Λ : ℝ := 1 + Real.log E with hΛdef
  have hK : 0 < K := frozenNegativeCarryLogConstant_pos
  have hKu : 0 < Ku := frozenUniformMeanConstant_pos
  have hC1 : 0 ≤ C1 := nativeFirstMarginConcentrationConstant_nonneg (by norm_num)
  have hΛ : 0 ≤ Λ := by have := Real.log_nonneg hE1; rw [hΛdef]; linarith
  have hKuΛ : 0 ≤ Ku * Λ := mul_nonneg hKu.le hΛ
  -- integrability of `f`
  obtain ⟨habs_int, -⟩ := integral_transientMarginLaw_one_abs_le hX hi hG hE2
  have hfint : Integrable f ρ := by
    refine ((integrable_const (Ku*Λ)).add (habs_int.const_mul (Ku*Λ))).mono'
      hfm.aestronglyMeasurable (ae_of_all _ fun r => ?_)
    rw [Real.norm_of_nonneg (hf0 r)]
    have h1 := secondSegmentFrozenMean_div_le_linear hX hi hG hE1 r
    have hmax : max r 0 ≤ |r| := max_le (le_abs_self r) (abs_nonneg r)
    simp only [Pi.add_apply]
    calc f r ≤ Ku * Λ * (1 + max r 0) := h1
      _ ≤ Ku * Λ * (1 + |r|) := mul_le_mul_of_nonneg_left (by linarith) hKuΛ
      _ = Ku * Λ + Ku * Λ * |r| := by ring
  refine ⟨hfint, ?_⟩
  have hψm : Measurable ψ := (continuous_secondSegmentWindow δ M).measurable
  have hrem_int : Integrable (fun r => f r * (1 - ψ r)) ρ :=
    hfint.mul_bdd (c := 1) (measurable_const.sub hψm).aestronglyMeasurable
      (ae_of_all _ fun r => by
        rw [Real.norm_of_nonneg (by linarith [secondSegmentWindow_le_one δ M r])]
        linarith [secondSegmentWindow_nonneg δ M r])
  -- the three dominating pieces
  set S : Set ℝ := {r : ℝ | |r| < δ} with hSdef
  set I1 : ℝ → ℝ := (Iio (-M)).indicator (fun _ => (1 : ℝ)) with hI1def
  set I2 : ℝ → ℝ := S.indicator (fun r => 1 + nearZeroLogWeight r) with hI2def
  set I3 : ℝ → ℝ := (Ici 0).indicator (fun _ => (1 : ℝ)) with hI3def
  have hpt : ∀ r, f r * (1 - ψ r) ≤ 25 * I1 r + K * I2 r + Ku * Λ * (I3 r + max r 0) := by
    intro r
    have hψ0 := secondSegmentWindow_nonneg δ M r
    have hψ1 := secondSegmentWindow_le_one δ M r
    have hT1 : 0 ≤ I1 r := Set.indicator_nonneg (fun _ _ => zero_le_one) r
    have hT2 : 0 ≤ I2 r :=
      Set.indicator_nonneg (fun r _ => by linarith [nearZeroLogWeight_nonneg r]) r
    have hT3 : 0 ≤ I3 r + max r 0 :=
      add_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) r) (le_max_right _ _)
    have hT2' : 0 ≤ K * I2 r := mul_nonneg hK.le hT2
    have hT3' : 0 ≤ Ku * Λ * (I3 r + max r 0) := mul_nonneg hKuΛ hT3
    have hle : f r * (1 - ψ r) ≤ f r := mul_le_of_le_one_right (hf0 r) (by linarith)
    by_cases h1 : r < -M
    · have hI : I1 r = 1 := Set.indicator_of_mem (show r ∈ Iio (-M) from h1) _
      have hf := secondSegmentFrozenMean_div_le_far hX hi hG hE1 (r := r) (by linarith)
      rw [hI]
      linarith
    · by_cases h2 : r ≤ -δ
      · have hw : ψ r = 1 := secondSegmentWindow_eq_one hδ (not_lt.mp h1) h2
        rw [hw, sub_self, mul_zero]
        linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 25) hT1]
      · by_cases h3 : r < 0
        · have hS : r ∈ S := by
            show |r| < δ
            rw [abs_of_neg h3]
            linarith
          have hI : I2 r = 1 + nearZeroLogWeight r := Set.indicator_of_mem hS _
          have hf := secondSegmentFrozenMean_div_le_log hX hi hG hE h3
          rw [hI]
          linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 25) hT1]
        · have hI : I3 r = 1 := Set.indicator_of_mem (show r ∈ Ici 0 from not_lt.mp h3) _
          have hf := secondSegmentFrozenMean_div_le_linear hX hi hG hE1 r
          rw [hI]
          linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 25) hT1]
  -- integrability and integrals of the pieces
  have hball : ∀ s, 0 < s → s ≤ δ → ρ {r : ℝ | |r| < s} ≤ ENNReal.ofReal (2*C1*s) :=
    fun s hs hsδ => transientMarginLaw_one_ball_le hX hi hG hE2 hs.le (hsδ.trans hδ1)
  obtain ⟨hI2int, hI2le⟩ := integral_indicator_one_add_nearZeroLogWeight_le (ρ := ρ) hC1 hδ hball
  have hI1int : Integrable I1 ρ := (integrable_const (1 : ℝ)).indicator measurableSet_Iio
  have hI3int : Integrable I3 ρ := (integrable_const (1 : ℝ)).indicator measurableSet_Ici
  obtain ⟨hposint, hposle⟩ := integral_transientMarginLaw_one_pos_le hX hi hG hE
  have hdomint : Integrable (fun r => 25 * I1 r + K * I2 r + Ku * Λ * (I3 r + max r 0)) ρ :=
    ((hI1int.const_mul 25).add (hI2int.const_mul K)).add ((hI3int.add hposint).const_mul (Ku*Λ))
  have hmono := integral_mono hrem_int hdomint hpt
  have hdomval : (∫ r, (25 * I1 r + K * I2 r + Ku * Λ * (I3 r + max r 0)) ∂ρ) =
      25 * ρ.real (Iio (-M)) + K * (∫ r, I2 r ∂ρ) +
        Ku * Λ * (ρ.real (Ici 0) + ∫ r, max r 0 ∂ρ) := by
    have h1 : Integrable (fun r => 25 * I1 r) ρ := hI1int.const_mul 25
    have h2 : Integrable (fun r => K * I2 r) ρ := hI2int.const_mul K
    have h3 : Integrable (fun r => Ku * Λ * (I3 r + max r 0)) ρ :=
      (hI3int.add hposint).const_mul (Ku*Λ)
    have e1 := integral_add (f := fun r => 25 * I1 r + K * I2 r)
      (g := fun r => Ku * Λ * (I3 r + max r 0)) (h1.add h2) h3
    have e2 := integral_add (f := fun r => 25 * I1 r) (g := fun r => K * I2 r) h1 h2
    have e3 := integral_add (f := I3) (g := fun r => max r 0) hI3int hposint
    have e4 : (∫ r, I1 r ∂ρ) = ρ.real (Iio (-M)) := by
      rw [hI1def, integral_indicator_const _ measurableSet_Iio, smul_eq_mul, mul_one]
    have e5 : (∫ r, I3 r ∂ρ) = ρ.real (Ici 0) := by
      rw [hI3def, integral_indicator_const _ measurableSet_Ici, smul_eq_mul, mul_one]
    rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul, e3, e4, e5]
  rw [hdomval] at hmono
  -- numerical estimates
  have hm1 : 0 ≤ m1 := nativeFirstMarginMomentBound_nonneg 1
  have htail : ρ.real (Iio (-M)) ≤ m1 / M := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      (transientMarginLaw_one_Iio_le hX hi hG hE2 (by linarith))
  have hCs := secondMarginPosConstant_nonneg
  have hCp : 0 ≤ firstMarginNonnegConstant := by
    unfold firstMarginNonnegConstant
    positivity
  set Sq : ℝ := Real.sqrt (Real.sqrt E) with hSqdef
  have hSq1 : 1 ≤ Sq := by
    rw [hSqdef, Real.one_le_sqrt, Real.one_le_sqrt]
    exact hE1
  have hSq0 : 0 < Sq := by linarith
  have hsqE : Real.sqrt E = Sq^2 := by
    rw [hSqdef, Real.sq_sqrt (Real.sqrt_nonneg E)]
  have hnonneg : ρ.real (Ici 0) ≤ firstMarginNonnegConstant / Sq := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      (transientMarginLaw_one_Ici_le hX hi hG hE)
  have hpos' : (∫ r, max r 0 ∂ρ) ≤ secondMarginPosConstant / Sq := by
    refine hposle.trans ?_
    rw [hsqE]
    apply div_le_div_of_nonneg_left hCs hSq0
    nlinarith
  have hsum : ρ.real (Ici 0) + (∫ r, max r 0 ∂ρ) ≤
      (firstMarginNonnegConstant + secondMarginPosConstant) / Sq := by
    rw [add_div]
    linarith
  have hthird : Ku * Λ * (ρ.real (Ici 0) + ∫ r, max r 0 ∂ρ) ≤
      Ku * (firstMarginNonnegConstant + secondMarginPosConstant) * (Λ / Sq) := by
    calc Ku * Λ * (ρ.real (Ici 0) + ∫ r, max r 0 ∂ρ)
        ≤ Ku * Λ * ((firstMarginNonnegConstant + secondMarginPosConstant) / Sq) :=
          mul_le_mul_of_nonneg_left hsum hKuΛ
      _ = _ := by ring
  have hfirst : 25 * ρ.real (Iio (-M)) ≤ 25 * (m1 / M) := by linarith
  have hsecond : K * (∫ r, I2 r ∂ρ) ≤ K * (2 * C1 * δ + 4 * C1 * Real.sqrt δ) :=
    mul_le_mul_of_nonneg_left hI2le hK.le
  calc (∫ r, f r * (1 - ψ r) ∂ρ)
      ≤ 25 * ρ.real (Iio (-M)) + K * (∫ r, I2 r ∂ρ) +
          Ku * Λ * (ρ.real (Ici 0) + ∫ r, max r 0 ∂ρ) := hmono
    _ ≤ _ := by linarith

/-! ### The limiting remainder -/

/-- The remainder of `ℓ` off the window against any law carried by `(-∞, 0)` with
the small-ball and far-tail bounds. -/
theorem integral_kernel_mul_one_sub_window_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hneg : ∀ᵐ r ∂ρ, r < 0) {D : ℝ} (hD : 0 ≤ D)
    (hball : ∀ s, 0 < s → s ≤ 1 → ρ {r : ℝ | |r| < s} ≤ ENNReal.ofReal (2*D*s))
    {δ M T : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : 1 ≤ M) (hT : 0 ≤ T)
    (htail : ρ (Iio (-M)) ≤ ENNReal.ofReal T) :
    (∫ r, secondSegmentLimitKernel X μ r * (1 - secondSegmentWindow δ M r) ∂ρ) ≤
      2 * T + frozenNegativeCarryLogConstant * (2 * D * δ + 4 * D * Real.sqrt δ) := by
  have := hi.isProbabilityMeasure
  set ψ : ℝ → ℝ := secondSegmentWindow δ M with hψdef
  set K : ℝ := frozenNegativeCarryLogConstant with hKdef
  have hK : 0 < K := frozenNegativeCarryLogConstant_pos
  have hℓint := secondSegmentLimitKernel_integrable_of_ball hX hi hG hneg hD hball
  have hψm : Measurable ψ := (continuous_secondSegmentWindow δ M).measurable
  have hrem_int : Integrable (fun r => secondSegmentLimitKernel X μ r * (1 - ψ r)) ρ :=
    hℓint.mul_bdd (c := 1) (measurable_const.sub hψm).aestronglyMeasurable
      (ae_of_all _ fun r => by
        rw [Real.norm_of_nonneg (by linarith [secondSegmentWindow_le_one δ M r])]
        linarith [secondSegmentWindow_nonneg δ M r])
  set S : Set ℝ := {r : ℝ | |r| < δ} with hSdef
  set I1 : ℝ → ℝ := (Iio (-M)).indicator (fun _ => (1 : ℝ)) with hI1def
  set I2 : ℝ → ℝ := S.indicator (fun r => 1 + nearZeroLogWeight r) with hI2def
  have hpt : ∀ᵐ r ∂ρ, secondSegmentLimitKernel X μ r * (1 - ψ r) ≤ 2 * I1 r + K * I2 r := by
    filter_upwards [hneg] with r hr0
    have hψ0 := secondSegmentWindow_nonneg δ M r
    have hψ1 := secondSegmentWindow_le_one δ M r
    have hℓ0 := secondSegmentLimitKernel_nonneg hX hi hG r
    have hT1 : 0 ≤ I1 r := Set.indicator_nonneg (fun _ _ => zero_le_one) r
    have hT2 : 0 ≤ I2 r :=
      Set.indicator_nonneg (fun r _ => by linarith [nearZeroLogWeight_nonneg r]) r
    have hT2' : 0 ≤ K * I2 r := mul_nonneg hK.le hT2
    have hle : secondSegmentLimitKernel X μ r * (1 - ψ r) ≤ secondSegmentLimitKernel X μ r :=
      mul_le_of_le_one_right hℓ0 (by linarith)
    by_cases h1 : r < -M
    · have hI : I1 r = 1 := Set.indicator_of_mem (show r ∈ Iio (-M) from h1) _
      have hℓ := secondSegmentLimitKernel_le hX hi hG hr0
      have habs : 1 ≤ |r| := by rw [abs_of_neg hr0]; linarith
      have h2 : 2 / |r| ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      rw [hI]
      linarith
    · by_cases h2 : r ≤ -δ
      · have hw : ψ r = 1 := secondSegmentWindow_eq_one hδ (not_lt.mp h1) h2
        rw [hw, sub_self, mul_zero]
        linarith
      · have hS : r ∈ S := by
          show |r| < δ
          rw [abs_of_neg hr0]
          linarith
        have hI : I2 r = 1 + nearZeroLogWeight r := Set.indicator_of_mem hS _
        have hℓ := secondSegmentLimitKernel_le_log hX hi hG hr0
        rw [hI]
        linarith
  have hball' : ∀ s, 0 < s → s ≤ δ → ρ {r : ℝ | |r| < s} ≤ ENNReal.ofReal (2*D*s) :=
    fun s hs hsδ => hball s hs (hsδ.trans hδ1)
  obtain ⟨hI2int, hI2le⟩ := integral_indicator_one_add_nearZeroLogWeight_le (ρ := ρ) hD hδ hball'
  have hI1int : Integrable I1 ρ := (integrable_const (1 : ℝ)).indicator measurableSet_Iio
  have hdomint : Integrable (fun r => 2 * I1 r + K * I2 r) ρ :=
    (hI1int.const_mul 2).add (hI2int.const_mul K)
  have hmono := integral_mono_ae hrem_int hdomint hpt
  have hdomval : (∫ r, (2 * I1 r + K * I2 r) ∂ρ) = 2 * ρ.real (Iio (-M)) + K * ∫ r, I2 r ∂ρ := by
    have e1 := integral_add (f := fun r => 2 * I1 r) (g := fun r => K * I2 r)
      (hI1int.const_mul 2) (hI2int.const_mul K)
    have e4 : (∫ r, I1 r ∂ρ) = ρ.real (Iio (-M)) := by
      rw [hI1def, integral_indicator_const _ measurableSet_Iio, smul_eq_mul, mul_one]
    rw [e1, integral_const_mul, integral_const_mul, e4]
  rw [hdomval] at hmono
  have htail' : ρ.real (Iio (-M)) ≤ T := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hT htail
  have hsecond : K * (∫ r, I2 r ∂ρ) ≤ K * (2 * D * δ + 4 * D * Real.sqrt δ) :=
    mul_le_mul_of_nonneg_left hI2le hK.le
  linarith

end SwingRepair
