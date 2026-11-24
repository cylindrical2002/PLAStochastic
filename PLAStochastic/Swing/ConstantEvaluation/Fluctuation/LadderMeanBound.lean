import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.OvershootMonotone
import PLAStochastic.Swing.Gaussian.ZeroLadder.MeanValue
import PLAStochastic.Swing.Gaussian.HalfLine.PrefixStability

/-! # `p_a ≤ √2 a`: the ladder mean is at least its zero-drift value (roadmap 1.5)

* `measure_posWalkSet_mul_lintegral_ladderHeight`: `p_a · 𝔼H_a = a` (duality with `f = id₊`).
* `lintegral_ladderHeight_mono`: `𝔼H_a ≤ 𝔼H_c` for `0 < a ≤ c` (Spitzer: `p_c a ≤ p_a c`).
* `lintegral_ladderHeight_zero`: `𝔼H_0 = 1/√2` (the library value `V(0) = 1/√2`, applied to `-X`).
* `lintegral_ladderHeight_zero_le`: `𝔼H_0 ≤ 𝔼H_a` by Fatou along `a_k = 1/(k+1) ↓ 0`, using the
  pathwise convergence `H_{a_k} → H_0` from the small-drift continuity of the exit problem.
* `measure_posWalkSet_le_sqrt_two_mul`: `p_a ≤ √2 a`, i.e. `p_a/a ≤ √2 = lim_{a↓0} p_a/a`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
open Fluctuation

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- The ladder mean in `ℝ≥0∞`. -/
def ladderMeanLIntegral (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (gaussianAscendingLadderHeight X a ω) ∂μ

/-- `p_a · 𝔼H_a = a`. -/
theorem measure_posWalkSet_mul_ladderMeanLIntegral (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    μ (posWalkSet X a) * ladderMeanLIntegral X μ a = ENNReal.ofReal a := by
  have h := ladder_duality hX hi hG ha (f := ENNReal.ofReal) ENNReal.measurable_ofReal
  unfold ladderMeanLIntegral
  rw [h]
  have hind : ∀ y : ℝ, (Ioi 0).indicator ENNReal.ofReal y = ENNReal.ofReal y := by
    intro y
    by_cases hy : 0 < y
    · rw [indicator_of_mem (show y ∈ Ioi 0 from hy)]
    · rw [indicator_of_notMem (show y ∉ Ioi 0 from hy), ENNReal.ofReal_of_nonpos (not_lt.mp hy)]
  simp_rw [hind]
  have := dualPosPartLIntegral_zero hX hi hG ha
  unfold dualPosPartLIntegral at this
  simp only [sub_zero] at this
  exact this

theorem ladderMeanLIntegral_ne_top (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    ladderMeanLIntegral X μ a ≠ ⊤ := by
  intro htop
  have h := measure_posWalkSet_mul_ladderMeanLIntegral hX hi hG ha
  rw [htop, ENNReal.mul_top (measure_posWalkSet_pos hX hi hG ha)] at h
  exact ENNReal.top_ne_ofReal h

/-- `𝔼H_a ≤ 𝔼H_c` for `0 < a ≤ c`. -/
theorem ladderMeanLIntegral_mono (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a c : ℝ} (ha : 0 < a)
    (hac : a ≤ c) : ladderMeanLIntegral X μ a ≤ ladderMeanLIntegral X μ c := by
  have hc : 0 < c := ha.trans_le hac
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set pa := μ (posWalkSet X a)
  set pc := μ (posWalkSet X c)
  have hpa0 : pa ≠ 0 := measure_posWalkSet_pos hX hi hG ha
  have hpat : pa ≠ ⊤ := measure_ne_top _ _
  have hpc0 : pc ≠ 0 := measure_posWalkSet_pos hX hi hG hc
  have hpct : pc ≠ ⊤ := measure_ne_top _ _
  have h1 := measure_posWalkSet_mul_ladderMeanLIntegral hX hi hG ha
  have h2 := measure_posWalkSet_mul_ladderMeanLIntegral hX hi hG hc
  have hsp := measure_posWalkSet_mul_ofReal_le hX hi hG ha hac
  have hprod : (pa * pc) * ladderMeanLIntegral X μ a ≤ (pa * pc) * ladderMeanLIntegral X μ c := by
    calc (pa * pc) * ladderMeanLIntegral X μ a = pc * (pa * ladderMeanLIntegral X μ a) := by ring
      _ = pc * ENNReal.ofReal a := by rw [h1]
      _ ≤ pa * ENNReal.ofReal c := hsp
      _ = pa * (pc * ladderMeanLIntegral X μ c) := by rw [h2]
      _ = (pa * pc) * ladderMeanLIntegral X μ c := by ring
  exact (ENNReal.mul_le_mul_iff_right (mul_ne_zero hpa0 hpc0) (ENNReal.mul_ne_top hpat hpct)).mp
    hprod

omit [MeasurableSpace Ω] in
/-- `H_0 = ` the zero-drift descending overshoot of `-X`. -/
theorem gaussianAscendingLadderHeight_zero_eq :
    gaussianAscendingLadderHeight X 0 = gaussianHalfLineOvershoot (fun n ω => -X n ω) 0 0 := by
  unfold gaussianAscendingLadderHeight
  rw [neg_zero]

theorem gaussianAscendingLadderHeight_zero_integrable (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    Integrable (gaussianAscendingLadderHeight X 0) μ := by
  obtain ⟨hXn, hin, hGn⟩ := iidGaussian_neg hX hi hG
  rw [gaussianAscendingLadderHeight_zero_eq]
  exact (gaussianHalfLineOvershoot_mean_convergence hXn hin hGn (x := fun _ : ℕ => (0 : ℝ))
    (a := fun _ : ℕ => (0 : ℝ)) (w := 0) (fun _ => le_rfl) (fun _ => le_rfl) tendsto_const_nhds
    tendsto_const_nhds le_rfl).1

/-- **`𝔼H_0 = 1/√2`.** -/
theorem ladderMeanLIntegral_zero (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ladderMeanLIntegral X μ 0 = ENNReal.ofReal (1 / Real.sqrt 2) := by
  obtain ⟨hXn, hin, hGn⟩ := iidGaussian_neg hX hi hG
  have hV := gaussianRenewalPotential_zero_value hXn hin hGn
  unfold gaussianRenewalPotential at hV
  rw [zero_add] at hV
  have hint := gaussianAscendingLadderHeight_zero_integrable hX hi hG
  unfold ladderMeanLIntegral
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun ω => gaussianAscendingLadderHeight_nonneg 0 ω)]
  congr 1
  rw [← hV, gaussianAscendingLadderHeight_zero_eq]

/-- Pathwise: `H_{1/(k+1)} → H_0` almost surely. -/
theorem tendsto_ladderHeight_inv_succ (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∀ᵐ ω ∂μ, Tendsto (fun k : ℕ => gaussianAscendingLadderHeight X (1 / ((k : ℝ) + 1)) ω) atTop
      (𝓝 (gaussianAscendingLadderHeight X 0 ω)) := by
  obtain ⟨hXn, hin, hGn⟩ := iidGaussian_neg hX hi hG
  have hlim : Tendsto (fun k : ℕ => -(1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    rw [← neg_zero]
    exact tendsto_one_div_add_atTop_nhds_zero_nat.neg
  filter_upwards [gaussianHalfLine_small_drift_ae hXn hin hGn (x := fun _ : ℕ => (0 : ℝ))
    (a := fun k : ℕ => -(1 / ((k : ℝ) + 1))) (w := 0) tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => le_rfl) le_rfl] with ω hω
  rw [gaussianAscendingLadderHeight_zero_eq]
  exact hω.2

/-- **Fatou**: `𝔼H_0 ≤ 𝔼H_a` for every `a > 0`. -/
theorem ladderMeanLIntegral_zero_le (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    ladderMeanLIntegral X μ 0 ≤ ladderMeanLIntegral X μ a := by
  set f : ℕ → Ω → ℝ≥0∞ := fun k ω =>
    ENNReal.ofReal (gaussianAscendingLadderHeight X (1 / ((k : ℝ) + 1)) ω) with hf
  have hmeas : ∀ k, Measurable (f k) := fun k =>
    ENNReal.measurable_ofReal.comp (gaussianAscendingLadderHeight_measurable hX _)
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => f k ω) atTop
      (𝓝 (ENNReal.ofReal (gaussianAscendingLadderHeight X 0 ω))) := by
    filter_upwards [tendsto_ladderHeight_inv_succ hX hi hG] with ω hω
    exact (ENNReal.continuous_ofReal.tendsto _).comp hω
  -- eventually `1/(k+1) ≤ a`
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt ha
  have hev : ∀ k ≥ K, ∫⁻ ω, f k ω ∂μ ≤ ladderMeanLIntegral X μ a := by
    intro k hk
    have hk' : 1 / ((k : ℝ) + 1) ≤ a := by
      refine le_trans ?_ hK.le
      have : (K : ℝ) + 1 ≤ (k : ℝ) + 1 := by
        have : (K : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      exact one_div_le_one_div_of_le (by positivity) this
    exact ladderMeanLIntegral_mono hX hi hG (by positivity) hk'
  calc ladderMeanLIntegral X μ 0
      = ∫⁻ ω, liminf (fun k => f k ω) atTop ∂μ := by
        unfold ladderMeanLIntegral
        refine lintegral_congr_ae ?_
        filter_upwards [hlim] with ω hω
        exact hω.liminf_eq.symm
    _ ≤ liminf (fun k => ∫⁻ ω, f k ω ∂μ) atTop := lintegral_liminf_le hmeas
    _ ≤ ladderMeanLIntegral X μ a := by
        refine liminf_le_of_frequently_le' ?_
        exact (eventually_atTop.mpr ⟨K, hev⟩).frequently

/-- **`p_a ≤ √2 a`.** -/
theorem measure_posWalkSet_le_sqrt_two_mul (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    μ (posWalkSet X a) ≤ ENNReal.ofReal (Real.sqrt 2 * a) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have h1 := measure_posWalkSet_mul_ladderMeanLIntegral hX hi hG ha
  have h0 := ladderMeanLIntegral_zero_le hX hi hG ha
  rw [ladderMeanLIntegral_zero hX hi hG] at h0
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hinv : 0 < 1 / Real.sqrt 2 := by positivity
  have hmul : μ (posWalkSet X a) * ENNReal.ofReal (1 / Real.sqrt 2) ≤ ENNReal.ofReal a := by
    calc μ (posWalkSet X a) * ENNReal.ofReal (1 / Real.sqrt 2)
        ≤ μ (posWalkSet X a) * ladderMeanLIntegral X μ a := by gcongr
      _ = ENNReal.ofReal a := h1
  have hne0 : ENNReal.ofReal (1 / Real.sqrt 2) ≠ 0 := (ENNReal.ofReal_pos.mpr hinv).ne'
  have hnet : ENNReal.ofReal (1 / Real.sqrt 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdiv : μ (posWalkSet X a) ≤ ENNReal.ofReal a / ENNReal.ofReal (1 / Real.sqrt 2) :=
    (ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl hnet)).mpr hmul
  rw [← ENNReal.ofReal_div_of_pos hinv] at hdiv
  have : a / (1 / Real.sqrt 2) = Real.sqrt 2 * a := by field_simp
  rwa [this] at hdiv

theorem measureReal_posWalkSet_le_sqrt_two_mul (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    μ.real (posWalkSet X a) ≤ Real.sqrt 2 * a := by
  have h := measure_posWalkSet_le_sqrt_two_mul hX hi hG ha
  have hnn : 0 ≤ Real.sqrt 2 * a := by positivity
  rw [Measure.real, ← ENNReal.toReal_ofReal hnn]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top h

end SwingRepair
