import PLAStochastic.Swing.SecondSegment.FrozenMeanBridge
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The logarithmic moment of the actual first margin

Lemma H.2 gives no atom near zero, so the layer-cake integral of
`log_+(1/|R_1|)` converges with a constant free of the budget.  This is the
step `eq:secondlogarithmicmoment` of the second-segment theorem.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The layer-cake weight `log_+(1/|R_1|)`. -/
def marginLogWeight (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) : ℝ :=
  max (Real.log (1/|nativeFirstMargin X E ω|)) 0

omit mΩ in
theorem marginLogWeight_nonneg (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) :
    0 ≤ marginLogWeight X E ω := le_max_right _ _

theorem marginLogWeight_measurable (hX : ∀ j, Measurable (X j)) (E : ℝ) :
    Measurable (marginLogWeight X E) :=
  ((Real.measurable_log.comp ((measurable_const.div
    (nativeFirstMargin_measurable hX E).abs))).max measurable_const)

omit mΩ in
/-- Above a positive level the weight forces the margin into a small window. -/
theorem marginLogWeight_level_subset (X : ℕ → Ω → ℝ) (E : ℝ) {t : ℝ} (ht : 0 < t) :
    {ω | t < marginLogWeight X E ω} ⊆ {ω | |nativeFirstMargin X E ω| ≤ Real.exp (-t)} := by
  intro ω hω
  change t < max (Real.log (1/|nativeFirstMargin X E ω|)) 0 at hω
  show |nativeFirstMargin X E ω| ≤ Real.exp (-t)
  have hlog : t < Real.log (1/|nativeFirstMargin X E ω|) := by
    rcases max_cases (Real.log (1/|nativeFirstMargin X E ω|)) (0 : ℝ) with ⟨he, _⟩ | ⟨he, _⟩
    · rwa [he] at hω
    · rw [he] at hω; linarith
  by_cases hzero : |nativeFirstMargin X E ω| = 0
  · rw [hzero]
    exact (Real.exp_pos _).le
  · have hpos : 0 < |nativeFirstMargin X E ω| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hzero)
    have hinv : Real.exp t < 1/|nativeFirstMargin X E ω| := by
      have := Real.exp_lt_exp.mpr hlog
      rwa [Real.exp_log (by positivity)] at this
    rw [lt_div_iff₀ hpos] at hinv
    have hexp : 0 < Real.exp t := Real.exp_pos t
    have hid : Real.exp (-t)*Real.exp t = 1 := by rw [← Real.exp_add]; simp
    nlinarith [hinv, hexp, hid]

/-- Equation `eq:secondlogarithmicmoment`: the logarithmic moment of the actual
first margin is bounded independently of the budget. -/
theorem integral_marginLogWeight_le
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E) :
    (∫ ω, marginLogWeight X E ω ∂μ) ≤ 2*nativeFirstMarginConcentrationConstant 1 := by
  have hprob := hi.isProbabilityMeasure
  set C : ℝ := nativeFirstMarginConcentrationConstant 1 with hC
  have hCnn : 0 ≤ C := nativeFirstMarginConcentrationConstant_nonneg (by norm_num)
  have hmeas := marginLogWeight_measurable hX E
  have hnn : 0 ≤ᵐ[μ] marginLogWeight X E :=
    Eventually.of_forall (marginLogWeight_nonneg X E)
  have hlayer := lintegral_eq_lintegral_meas_lt μ hnn hmeas.aemeasurable
  have hlevel : ∀ t ∈ Ioi (0 : ℝ), μ {ω | t < marginLogWeight X E ω} ≤
      ENNReal.ofReal (2*C*Real.exp (-t)) := by
    intro t ht
    have hsub := measure_mono (μ := μ) (marginLogWeight_level_subset X E ht)
    refine hsub.trans ?_
    have hb := measureReal_nativeFirstMargin_abs_le hX hi hG hE
      (δ := Real.exp (-t)) (B := 1) (Real.exp_pos _).le
      (by
        have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith [mem_Ioi.mp ht])
        linarith)
    calc
      μ {ω | |nativeFirstMargin X E ω| ≤ Real.exp (-t)}
          = ENNReal.ofReal (μ.real {ω | |nativeFirstMargin X E ω| ≤ Real.exp (-t)}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (C*(2*Real.exp (-t))) := ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal (2*C*Real.exp (-t)) := by rw [show C*(2*Real.exp (-t)) = 2*C*Real.exp (-t) by ring]
  have hint : (∫⁻ ω, ENNReal.ofReal (marginLogWeight X E ω) ∂μ) ≤ ENNReal.ofReal (2*C) := by
    rw [hlayer]
    have hmono : (∫⁻ t in Ioi (0 : ℝ), μ {ω | t < marginLogWeight X E ω}) ≤
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2*C*Real.exp (-t)) := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro t ht
      exact hlevel t ht
    refine hmono.trans ?_
    have hintegrable : IntegrableOn (fun t : ℝ => 2*C*Real.exp (-t)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul (2*C)
    have hnn2 : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t => 2*C*Real.exp (-t) :=
      Eventually.of_forall (fun t => by positivity)
    rw [← ofReal_integral_eq_lintegral_ofReal hintegrable hnn2]
    have hval : (∫ t in Ioi (0 : ℝ), 2*C*Real.exp (-t)) = 2*C := by
      rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
    rw [hval]
  have hnonneg : 0 ≤ᵐ[μ] marginLogWeight X E := hnn
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeas.aestronglyMeasurable]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hint
  rwa [ENNReal.toReal_ofReal (by positivity)] at h

theorem integrable_marginLogWeight
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E) :
    Integrable (marginLogWeight X E) μ := by
  have hprob := hi.isProbabilityMeasure
  set C : ℝ := nativeFirstMarginConcentrationConstant 1 with hC
  have hCnn : 0 ≤ C := nativeFirstMarginConcentrationConstant_nonneg (by norm_num)
  have hmeas := marginLogWeight_measurable hX E
  have hnn : 0 ≤ᵐ[μ] marginLogWeight X E :=
    Eventually.of_forall (marginLogWeight_nonneg X E)
  apply (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable hnn).mp
  -- reuse the layer-cake estimate of the previous theorem
  have hlayer := lintegral_eq_lintegral_meas_lt μ hnn hmeas.aemeasurable
  have hlevel : ∀ t ∈ Ioi (0 : ℝ), μ {ω | t < marginLogWeight X E ω} ≤
      ENNReal.ofReal (2*C*Real.exp (-t)) := by
    intro t ht
    have hsub := measure_mono (μ := μ) (marginLogWeight_level_subset X E ht)
    refine hsub.trans ?_
    have hb := measureReal_nativeFirstMargin_abs_le hX hi hG hE
      (δ := Real.exp (-t)) (B := 1) (Real.exp_pos _).le
      (by
        have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith [mem_Ioi.mp ht])
        linarith)
    calc
      μ {ω | |nativeFirstMargin X E ω| ≤ Real.exp (-t)}
          = ENNReal.ofReal (μ.real {ω | |nativeFirstMargin X E ω| ≤ Real.exp (-t)}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (C*(2*Real.exp (-t))) := ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal (2*C*Real.exp (-t)) := by
        rw [show C*(2*Real.exp (-t)) = 2*C*Real.exp (-t) by ring]
  have hint : (∫⁻ ω, ENNReal.ofReal (marginLogWeight X E ω) ∂μ) ≤ ENNReal.ofReal (2*C) := by
    rw [hlayer]
    have hmono : (∫⁻ t in Ioi (0 : ℝ), μ {ω | t < marginLogWeight X E ω}) ≤
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2*C*Real.exp (-t)) := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro t ht
      exact hlevel t ht
    refine hmono.trans ?_
    have hintegrable : IntegrableOn (fun t : ℝ => 2*C*Real.exp (-t)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul (2*C)
    have hnn2 : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t => 2*C*Real.exp (-t) :=
      Eventually.of_forall (fun t => by positivity)
    rw [← ofReal_integral_eq_lintegral_ofReal hintegrable hnn2]
    have hval : (∫ t in Ioi (0 : ℝ), 2*C*Real.exp (-t)) = 2*C := by
      rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
    rw [hval]
  exact (hint.trans_lt ENNReal.ofReal_lt_top).ne

end SwingRepair
