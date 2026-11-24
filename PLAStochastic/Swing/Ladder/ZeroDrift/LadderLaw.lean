import PLAStochastic.Swing.Ladder.ZeroDrift.SpreadOutKeyRenewal
import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.LadderMeanBound

/-!
# The zero-drift strict ascending ladder law

Let `X` be i.i.d. standard Gaussian and `ν₀ = gaussianAscendingLadderLaw X μ 0` the law of
the first strict ascending ladder height `H₀` of the zero-drift walk.  This file proves:

* the first ladder epoch is a.s. finite, so `ν₀` is a probability law on `(0,∞)`;
* the first-step minorization `φ · 1_{(0,∞)} ≤ ν₀`, hence `κ₀ · Leb|[1,2] ≤ ν₀` with
  `κ₀ = φ(2)`;
* the Gaussian tail `ν₀((t,∞)) ≤ e^{-t²/2}` for `t ≥ 0`: on the event that the walk enters
  `(0,∞)` at step `n+1`, the overshoot is the excess of a fresh Gaussian over the
  nonnegative past-measurable threshold `-W_n`, and `Φ̄(v+t)/Φ̄(v) ≤ e^{-t²/2}` for
  `v ≥ 0`;
* all exponential and polynomial moments;
* `E H₀ = 1/√2`, so `0 < ladderMeanENN ν₀ < ⊤`;
* consequently `ν₀` is a `SpreadOutLaw`, and Blackwell's theorem and the key renewal
  theorem of the preceding files apply to it.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-! ### The Gaussian tail of the zero-drift overshoot -/

/-! ### The zero-drift ascending ladder law -/

omit mΩ in
theorem gaussianAscendingLadderTime_zero_eq :
    gaussianAscendingLadderTime X 0 = gaussianHalfLineExit (fun n ω => -X n ω) 0 0 := by
  unfold gaussianAscendingLadderTime
  rw [neg_zero]

/-- The zero-drift ladder epoch is almost surely finite. -/
theorem gaussianAscendingLadderTime_zero_finite_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∀ᵐ ω ∂μ, gaussianAscendingLadderTime X 0 ω ≠ ⊤ := by
  obtain ⟨hXn, hin, hGn⟩ := iidGaussian_neg hX hi hG
  rw [gaussianAscendingLadderTime_zero_eq]
  exact gaussianHalfLineExit_zero_finite_ae hXn hin hGn (le_refl (0 : ℝ))

theorem gaussianAscendingLadderHeight_zero_pos_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∀ᵐ ω ∂μ, 0 < gaussianAscendingLadderHeight X 0 ω :=
  (gaussianAscendingLadderTime_zero_finite_ae hX hi hG).mono
    fun _ hT => gaussianAscendingLadderHeight_pos_of_finite hT

/-- `ν₀` lives on `(0,∞)`. -/
theorem gaussianAscendingLadderLaw_zero_Iic
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    gaussianAscendingLadderLaw X μ 0 (Iic 0) = 0 := by
  rw [gaussianAscendingLadderLaw,
    Measure.map_apply (gaussianAscendingLadderHeight_measurable hX 0) measurableSet_Iic,
    measure_eq_zero_iff_ae_notMem]
  filter_upwards [gaussianAscendingLadderHeight_zero_pos_ae hX hi hG] with ω hω
  simpa using hω

/-- The Lebesgue component `φ(2) · Leb|[1,2] ≤ ν₀`. -/
theorem gaussianAscendingLadderLaw_zero_minor
    (hX : ∀ n, Measurable (X n)) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ENNReal.ofReal (gaussianAscendingLadderCommonDensity 0) • volume.restrict (Icc (1 : ℝ) 2) ≤
      gaussianAscendingLadderLaw X μ 0 :=
  gaussianAscendingLadderLaw_common_minorization hX (hG 0) le_rfl le_rfl

/-- Every exponential moment of `ν₀` is finite. -/
theorem gaussianAscendingLadderLaw_zero_exp_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {θ : ℝ} (hθ : 0 ≤ θ) :
    Integrable (fun x : ℝ => Real.exp (θ * x)) (gaussianAscendingLadderLaw X μ 0) := by
  obtain ⟨hXn, hin, hGn⟩ := iidGaussian_neg hX hi hG
  apply (integrable_map_measure (by fun_prop)
    (gaussianAscendingLadderHeight_measurable hX 0).aemeasurable).mpr
  rw [gaussianAscendingLadderHeight_zero_eq]
  exact gaussianHalfLineOvershoot_integrable_exp hXn hin hGn (le_refl (0 : ℝ)) le_rfl hθ

/-- Every polynomial moment of `ν₀` is finite. -/
theorem gaussianAscendingLadderLaw_zero_pow_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianAscendingLadderLaw X μ 0) := by
  have hexp := (gaussianAscendingLadderLaw_zero_exp_integrable hX hi hG
    (le_refl (0 : ℝ) |>.trans zero_le_one)).const_mul (k.factorial : ℝ)
  have hpos : ∀ᵐ x ∂gaussianAscendingLadderLaw X μ 0, 0 < x := by
    rw [gaussianAscendingLadderLaw,
      ae_map_iff (gaussianAscendingLadderHeight_measurable hX 0).aemeasurable measurableSet_Ioi]
    exact gaussianAscendingLadderHeight_zero_pos_ae hX hi hG
  refine hexp.mono' (by fun_prop) ?_
  filter_upwards [hpos] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx.le k), one_mul]
  have h := Real.pow_div_factorial_le_exp (x := x) hx.le k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hf] at h
  linarith

/-- **`E H₀ = 1/√2`.** -/
theorem ladderMeanENN_gaussianAscendingLadderLaw_zero
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ladderMeanENN (gaussianAscendingLadderLaw X μ 0) = ENNReal.ofReal (1 / Real.sqrt 2) := by
  rw [ladderMeanENN, gaussianAscendingLadderLaw,
    lintegral_map ENNReal.measurable_ofReal (gaussianAscendingLadderHeight_measurable hX 0)]
  exact ladderMeanLIntegral_zero hX hi hG

theorem ladderMeanENN_gaussianAscendingLadderLaw_zero_pos
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    0 < ladderMeanENN (gaussianAscendingLadderLaw X μ 0) ∧
      ladderMeanENN (gaussianAscendingLadderLaw X μ 0) < ⊤ := by
  rw [ladderMeanENN_gaussianAscendingLadderLaw_zero hX hi hG]
  exact ⟨ENNReal.ofReal_pos.mpr (by positivity), ENNReal.ofReal_lt_top⟩

/-- **`ν₀` is a spread-out law** with constant `κ₀ = φ(2)`. -/
theorem gaussianAscendingLadderLaw_zero_spreadOut
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    SpreadOutLaw (gaussianAscendingLadderLaw X μ 0) (gaussianAscendingLadderCommonDensity 0) where
  isProbabilityMeasure := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi 0
  Iic_zero := gaussianAscendingLadderLaw_zero_Iic hX hi hG
  pos := gaussianAscendingLadderCommonDensity_pos 0
  minor := gaussianAscendingLadderLaw_zero_minor hX hG
  sq_integrable := gaussianAscendingLadderLaw_zero_pow_integrable hX hi hG 2

/-! ### Blackwell and key renewal for `ν₀` -/

/-- **The key renewal theorem for `ν₀`**: the residual-life tail converges to the
equilibrium overshoot tail. -/
theorem gaussianZeroLadder_renewalOvershootTail_tendsto
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun b : ℝ => (renewalOvershootTail (gaussianAscendingLadderLaw X μ 0) b t).toReal)
      atTop (𝓝 (equilibriumOvershootTail (gaussianAscendingLadderLaw X μ 0) t).toReal) :=
  (gaussianAscendingLadderLaw_zero_spreadOut hX hi hG).renewalOvershootTail_tendsto ht

end SwingRepair
