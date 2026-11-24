import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Uniform
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Discount
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Uniform ladder estimates over the centred step class

The CEPS blueprint's step class `𝒲(D, θ, v)` (`IsStepLaw ρW fW D θ v`): `W` has a density
`f_W ≤ D e^{-θ|x|}`, `E W = 0` and `E W² ≤ v`. It is closed under `W ↦ -W` (`IsStepLaw.neg`) and
contains `W = 1 - X` for every gap law `X` of `IsGapLaw` (`IsGapLaw.toStepLaw`, with `D e^{θ}`).

For `Y = W + μ` (`driftStep ρW μ`), `|μ| ≤ δ ≤ 1/(64 D)`, `‖s‖ ≤ 1`, and
`K = 1024 D² v / (1 - e^{-θ/(64D)})`:

* `stepLaw_gaps`: both ladder gaps are at least `K⁻¹`;
* `norm_ladderDensity_asc_le_of_stepLaw`: `‖g₊(s, h)‖ ≤ ‖s‖ D e^{θδ} K e^{-θ h}`;
* `norm_ladderDensity_desc_le_of_stepLaw`: `‖g₋(s, h)‖ ≤ ‖s‖ D e^{θδ} K e^{θ h}`;
* `preEntryOccupation_asc_Ioc_le_of_stepLaw`, `preEntryOccupation_desc_Ioc_le_of_stepLaw`:
  both pre-ladder occupation measures give unit intervals mass at most `e^{θ} K`;
* `lintegral_weighted_sq_ladderDensity_asc_le`: `∫ e^{2 c h} |g₊(s, h)|² dh ≤ (D e^{θδ} K)² / (2 (θ - c))`
  for `0 ≤ c < θ`;
* `lintegral_ladderHeight_asc_ge`: `E[H₊; τ₊ < ∞] ≥ b P(Y ≥ b)`, in particular
  `≥ 1/(64 D) · 1/(1024 D² v)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex Finset
open scoped ENNReal

namespace PGM.WienerHopf

/-- The centred step class: `ρW` has a density `fW ≤ D e^{-θ|x|}`, mean zero and second moment at
most `v`. -/
structure IsStepLaw (ρW : Measure ℝ) (fW : ℝ → ℝ) (D θ v : ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure ρW
  eq_withDensity : ρW = volume.withDensity fun x => ENNReal.ofReal (fW x)
  measurable : Measurable fW
  nonneg : ∀ x, 0 ≤ fW x
  le_exp : ∀ x, fW x ≤ D * Real.exp (-θ * |x|)
  integrable_sq : Integrable (fun x => x ^ 2) ρW
  integral_id : ∫ x, x ∂ρW = 0
  integral_sq_le : ∫ x, x ^ 2 ∂ρW ≤ v

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

namespace IsStepLaw

theorem le_D (hW : IsStepLaw ρW fW D θ v) (hθ : 0 ≤ θ) (hD : 0 ≤ D) (x : ℝ) : fW x ≤ D :=
  (hW.le_exp x).trans (mul_le_of_le_one_right hD
    (Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg x])))

theorem integrable_id (hW : IsStepLaw ρW fW D θ v) : Integrable (fun x : ℝ => x) ρW := by
  have := hW.isProbabilityMeasure
  refine ((integrable_const 1).add hW.integrable_sq).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  show |x| ≤ 1 + x ^ 2
  nlinarith [abs_nonneg x, sq_abs x, sq_nonneg (|x| - 1)]

/-- Reflection `W ↦ -W` stays in the class. -/
theorem neg (hW : IsStepLaw ρW fW D θ v) :
    IsStepLaw (ρW.map Neg.neg) (fun x => fW (-x)) D θ v := by
  have := hW.isProbabilityMeasure
  have hfE : Measurable fun x => ENNReal.ofReal (fW x) :=
    ENNReal.measurable_ofReal.comp hW.measurable
  refine ⟨Measure.isProbabilityMeasure_map (by fun_prop), ?_, hW.measurable.comp measurable_neg,
    fun x => hW.nonneg _, fun x => by simpa [abs_neg] using hW.le_exp (-x), ?_, ?_, ?_⟩
  · refine Measure.ext_of_lintegral _ fun g hg => ?_
    have hgN : Measurable fun x : ℝ => g (-x) := hg.comp measurable_neg
    have hfN : Measurable fun x => ENNReal.ofReal (fW (-x)) :=
      ENNReal.measurable_ofReal.comp (hW.measurable.comp measurable_neg)
    rw [lintegral_map hg measurable_neg, hW.eq_withDensity,
      lintegral_withDensity_eq_lintegral_mul _ hfE hgN,
      lintegral_withDensity_eq_lintegral_mul _ hfN hg]
    simp only [Pi.mul_apply]
    have hmap : (volume : Measure ℝ).map Neg.neg = volume := Measure.map_neg_eq_self volume
    conv_rhs => rw [← hmap]
    have hF : Measurable fun x => ENNReal.ofReal (fW (-x)) * g x := hfN.mul hg
    rw [lintegral_map hF measurable_neg]
    simp only [neg_neg]
  · exact (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
      (by simpa [Function.comp_def] using hW.integrable_sq)
  · rw [integral_map (by fun_prop) (by fun_prop), integral_neg, hW.integral_id, neg_zero]
  · rw [integral_map (by fun_prop) (by fun_prop)]
    simpa using hW.integral_sq_le

/-- A density bounded by `D` puts mass at most `2 D η` near any point. -/
theorem measureReal_Ioo_le (hW : IsStepLaw ρW fW D θ v) (hθ : 0 ≤ θ) (hD : 0 ≤ D) (a η : ℝ)
    (hη : 0 ≤ η) : ρW.real (Ioo (a - η) (a + η)) ≤ 2 * D * η := by
  have h : ρW (Ioo (a - η) (a + η)) ≤ ENNReal.ofReal (2 * D * η) := by
    rw [hW.eq_withDensity, withDensity_apply _ measurableSet_Ioo]
    calc ∫⁻ x in Ioo (a - η) (a + η), ENNReal.ofReal (fW x)
        ≤ ∫⁻ _ in Ioo (a - η) (a + η), ENNReal.ofReal D :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hW.le_D hθ hD x)
      _ = ENNReal.ofReal D * ENNReal.ofReal (2 * η) := by
          rw [setLIntegral_const, Real.volume_Ioo]
          congr 1; congr 1; ring
      _ = ENNReal.ofReal (2 * D * η) := by
          rw [← ENNReal.ofReal_mul hD]; congr 1; ring
  calc ρW.real (Ioo (a - η) (a + η)) ≤ (ENNReal.ofReal (2 * D * η)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = 2 * D * η := ENNReal.toReal_ofReal (by positivity)

/-- `E W⁺ ≥ 1/(16 D)`. -/
theorem integral_pos_part_ge (hW : IsStepLaw ρW fW D θ v) (hθ : 0 ≤ θ) (hD : 0 < D) :
    1 / (16 * D) ≤ ∫ x, max x 0 ∂ρW := by
  have := hW.isProbabilityMeasure
  set η : ℝ := 1 / (4 * D)
  have hη : 0 < η := by positivity
  have hI : ρW.real (Ioo (0 - η) (0 + η)) ≤ 1 / 2 := by
    have := hW.measureReal_Ioo_le hθ hD.le 0 η hη.le
    have h2 : 2 * D * η = 1 / 2 := by simp only [η]; field_simp; ring
    linarith
  have hcompl : ρW.real (Ioo (0 - η) (0 + η))ᶜ = 1 - ρW.real (Ioo (0 - η) (0 + η)) := by
    rw [measureReal_compl measurableSet_Ioo, probReal_univ]
  have hle : ∀ x, η * (Ioo (0 - η) (0 + η))ᶜ.indicator (fun _ => (1 : ℝ)) x ≤ |x| := by
    intro x
    by_cases hx : x ∈ Ioo (0 - η) (0 + η)
    · rw [indicator_of_notMem (by simpa using hx), mul_zero]; exact abs_nonneg _
    · rw [indicator_of_mem (by simpa using hx), mul_one]
      simp only [Set.mem_Ioo, not_and_or, not_lt, zero_sub, zero_add] at hx
      rcases hx with hx | hx
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
  have hint := hW.integrable_id
  have habs : 1 / (8 * D) ≤ ∫ x, |x| ∂ρW :=
    calc 1 / (8 * D) = η * (1 / 2) := by simp only [η]; field_simp; ring
      _ ≤ η * ρW.real (Ioo (0 - η) (0 + η))ᶜ := by
          rw [hcompl]; exact mul_le_mul_of_nonneg_left (by linarith) hη.le
      _ = ∫ x, η * (Ioo (0 - η) (0 + η))ᶜ.indicator (fun _ => (1 : ℝ)) x ∂ρW := by
          rw [integral_const_mul, integral_indicator measurableSet_Ioo.compl, setIntegral_const,
            smul_eq_mul, mul_one]
      _ ≤ ∫ x, |x| ∂ρW :=
          integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_Ioo.compl
            |>.const_mul η) hint.abs hle
  have e2 : (fun x : ℝ => max x 0) = fun x => (|x| + x) / 2 := by
    funext x; rcases le_total x 0 with h | h
    · rw [max_eq_right h, abs_of_nonpos h]; ring
    · rw [max_eq_left h, abs_of_nonneg h]; ring
  rw [e2, integral_div, integral_add hint.abs hint, hW.integral_id]
  have h8 : 1 / (8 * D) = 2 * (1 / (16 * D)) := by field_simp; ring
  linarith

/-- `P(W ≥ t) ≥ (1/(16 D) - t)² / v` for `0 ≤ t < 1/(16 D)`. -/
theorem measureReal_Ici_ge (hW : IsStepLaw ρW fW D θ v) (hθ : 0 ≤ θ) (hD : 0 < D) (hv : 0 < v)
    {t : ℝ} (ht : 0 ≤ t) (htD : t < 1 / (16 * D)) :
    (1 / (16 * D) - t) ^ 2 / v ≤ ρW.real (Ici t) := by
  have := hW.isProbabilityMeasure
  set c := 1 / (16 * D) - t
  have hc : 0 < c := by simp only [c]; linarith
  set lam := v / c
  have hlam : 0 < lam := div_pos hv hc
  have h := hW.integral_pos_part_ge hθ hD
  have hle : ∀ x, max x 0 ≤ t + x ^ 2 / (2 * lam) +
      lam / 2 * (Ici t).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    have hsq : 0 ≤ x ^ 2 / (2 * lam) := by positivity
    by_cases hxt : t ≤ x
    · rw [indicator_of_mem (show x ∈ Ici t from hxt), mul_one]
      have hamgm : x ≤ x ^ 2 / (2 * lam) + lam / 2 := by
        rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (x - lam)]
      exact max_le (by linarith) (by positivity)
    · rw [indicator_of_notMem (show x ∉ Ici t from hxt), mul_zero, add_zero]
      push Not at hxt
      exact max_le (by linarith) (by linarith)
  have hint : Integrable (fun x => max x 0) ρW :=
    (hW.integrable_id.abs).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _))
  have hSq : Integrable (fun x => x ^ 2 / (2 * lam)) ρW := hW.integrable_sq.div_const _
  have hR1 : Integrable (fun x => t + x ^ 2 / (2 * lam)) ρW := (integrable_const t).add hSq
  have hR2 : Integrable (fun x => lam / 2 * (Ici t).indicator (fun _ => (1 : ℝ)) x) ρW :=
    ((integrable_const (1 : ℝ)).indicator measurableSet_Ici).const_mul _
  have hR : Integrable (fun x => t + x ^ 2 / (2 * lam) +
      lam / 2 * (Ici t).indicator (fun _ => (1 : ℝ)) x) ρW := hR1.add hR2
  have := integral_mono hint hR hle
  rw [integral_add hR1 hR2, integral_add (integrable_const t) hSq, integral_const,
    integral_div, integral_const_mul, integral_indicator measurableSet_Ici, setIntegral_const]
    at this
  simp only [probReal_univ, smul_eq_mul, mul_one, one_mul] at this
  have hv' := hW.integral_sq_le
  set p := ρW.real (Ici t)
  have hdiv : (∫ x, x ^ 2 ∂ρW) / (2 * lam) ≤ c / 2 := by
    rw [div_le_iff₀ (by positivity)]
    simp only [lam]
    rw [show c / 2 * (2 * (v / c)) = v by field_simp]
    exact hv'
  have hmain : c / 2 ≤ lam / 2 * p := by simp only [c] at *; linarith
  rw [div_le_iff₀ hv]
  have : c / 2 * c ≤ lam / 2 * p * c := mul_le_mul_of_nonneg_right hmain hc.le
  have hlc : lam / 2 * p * c = v * p / 2 := by simp only [lam]; field_simp
  nlinarith

/-- `P(W ≤ -t) ≥ (1/(16 D) - t)² / v` for `0 ≤ t < 1/(16 D)`, by reflection. -/
theorem measureReal_Iic_ge (hW : IsStepLaw ρW fW D θ v) (hθ : 0 ≤ θ) (hD : 0 < D) (hv : 0 < v)
    {t : ℝ} (ht : 0 ≤ t) (htD : t < 1 / (16 * D)) :
    (1 / (16 * D) - t) ^ 2 / v ≤ ρW.real (Iic (-t)) := by
  have h := hW.neg.measureReal_Ici_ge hθ hD hv ht htD
  rwa [map_measureReal_apply measurable_neg measurableSet_Ici,
    show Neg.neg ⁻¹' Ici t = Iic (-t) by ext x; simp] at h

end IsStepLaw

/-- The gap laws of `IsGapLaw` give steps `W = 1 - X` in the step class (with `D e^{θ}`). -/
theorem IsGapLaw.toStepLaw {ν : Measure ℝ} {fX : ℝ → ℝ} (hX : IsGapLaw ν fX D θ v)
    (hθ : 0 ≤ θ) (hD : 0 ≤ D) :
    IsStepLaw (ν.map fun x => 1 - x) (fun w => fX (1 - w)) (D * Real.exp θ) θ v := by
  have := hX.isProbabilityMeasure
  have hT : Measurable fun x : ℝ => 1 - x := by fun_prop
  refine ⟨Measure.isProbabilityMeasure_map hT.aemeasurable, ?_,
    hX.measurable.comp hT, fun w => hX.nonneg _, fun w => ?_, ?_, ?_, ?_⟩
  · have h := shiftedStep_eq_withDensity hX 0
    simp only [shiftedStep, add_zero] at h
    exact h
  · rcases le_or_gt (1 - w) 0 with h | h
    · rw [hX.eq_zero_of_nonpos _ h]; positivity
    · calc fX (1 - w) ≤ D * Real.exp (-θ * (1 - w)) := hX.le_exp _ h
        _ ≤ D * Real.exp (θ + -θ * |w|) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD
            rcases le_total 0 w with hw | hw
            · rw [abs_of_nonneg hw]; nlinarith
            · rw [abs_of_nonpos hw]; nlinarith
        _ = D * Real.exp θ * Real.exp (-θ * |w|) := by rw [Real.exp_add]; ring
  · refine (integrable_map_measure (by fun_prop) hT.aemeasurable).mpr ?_
    refine hX.integrable_sq.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply]; ring
  · rw [integral_map hT.aemeasurable (by fun_prop)]
    have h := hX.integral_sub_one
    rw [show (fun x : ℝ => 1 - x) = fun x => -(x - 1) by funext x; ring, integral_neg, h,
      neg_zero]
  · rw [integral_map hT.aemeasurable (by fun_prop)]
    calc ∫ x, (1 - x) ^ 2 ∂ν = ∫ x, (x - 1) ^ 2 ∂ν := by congr 1; funext x; ring
      _ ≤ v := hX.integral_sq_le

/-! ### Drifted steps of the class -/

theorem driftStep_eq_withDensity (hW : IsStepLaw ρW fW D θ v) (μ : ℝ) :
    driftStep ρW μ = volume.withDensity fun y => ENNReal.ofReal (fW (y - μ)) := by
  have hT : Measurable fun x : ℝ => x + μ := by fun_prop
  have hfE : Measurable fun x => ENNReal.ofReal (fW x) :=
    ENNReal.measurable_ofReal.comp hW.measurable
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have hgT : Measurable fun x => g (x + μ) := hg.comp hT
  have hfE' : Measurable fun y => ENNReal.ofReal (fW (y - μ)) :=
    ENNReal.measurable_ofReal.comp (hW.measurable.comp (by fun_prop))
  rw [driftStep, lintegral_map hg hT, hW.eq_withDensity,
    lintegral_withDensity_eq_lintegral_mul _ hfE hgT,
    lintegral_withDensity_eq_lintegral_mul _ hfE' hg]
  simp only [Pi.mul_apply]
  rw [← lintegral_add_right_eq_self (fun y => ENNReal.ofReal (fW (y - μ)) * g y) μ]
  simp only [add_sub_cancel_right]

theorem driftStep_density_le (hW : IsStepLaw ρW fW D θ v) (hθ : 0 ≤ θ) (hD : 0 ≤ D)
    {μ δ : ℝ} (hμ : |μ| ≤ δ) (y : ℝ) :
    fW (y - μ) ≤ D * Real.exp (θ * δ) * Real.exp (-θ * |y|) := by
  calc fW (y - μ) ≤ D * Real.exp (-θ * |y - μ|) := hW.le_exp _
    _ ≤ D * Real.exp (θ * δ + -θ * |y|) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD
        have h1 : |y| ≤ |y - μ| + |μ| := by
          calc |y| = |(y - μ) + μ| := by ring_nf
            _ ≤ |y - μ| + |μ| := abs_add_le _ _
        nlinarith
    _ = _ := by rw [Real.exp_add]; ring

/-- The first-step masses of `Y = W + μ`: `P(Y ≤ -b) ≥ 1/(1024 D² v)` and
`P(Y ≥ b) ≥ 1/(1024 D² v)` for `b = 1/(64 D)` and `|μ| ≤ δ ≤ 1/(64 D)`. -/
theorem driftStep_masses (hW : IsStepLaw ρW fW D θ v) (hθ : 0 ≤ θ) (hD : 0 < D) (hv : 0 < v)
    {μ δ : ℝ} (hμ : |μ| ≤ δ) (hδ : δ ≤ 1 / (64 * D)) :
    1 / (1024 * D ^ 2 * v) ≤ (driftStep ρW μ).real (Iic (-(1 / (64 * D)))) ∧
      1 / (1024 * D ^ 2 * v) ≤ (driftStep ρW μ).real (Ici (1 / (64 * D))) := by
  have := hW.isProbabilityMeasure
  have hT : Measurable fun x : ℝ => x + μ := by fun_prop
  have hμ1 := le_of_abs_le hμ
  have hμ2 := neg_le_of_abs_le hμ
  set t := 1 / (32 * D)
  have ht : 0 ≤ t := by positivity
  have htD : t < 1 / (16 * D) := by
    simp only [t]; rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hb : 1 / (64 * D) + δ ≤ t := by
    have : 1 / (64 * D) + 1 / (64 * D) = t := by simp only [t]; field_simp; ring
    linarith
  have h2 : (1 / (16 * D) - t) ^ 2 / v = 1 / (1024 * D ^ 2 * v) := by
    simp only [t]; field_simp; ring
  constructor
  · have hsub : Iic (-t) ⊆ (fun x : ℝ => x + μ) ⁻¹' Iic (-(1 / (64 * D))) := by
      intro x hx
      simp only [Set.mem_Iic] at hx
      simp only [Set.mem_preimage, Set.mem_Iic]
      linarith
    rw [driftStep, map_measureReal_apply hT measurableSet_Iic]
    calc 1 / (1024 * D ^ 2 * v) = (1 / (16 * D) - t) ^ 2 / v := h2.symm
      _ ≤ ρW.real (Iic (-t)) := hW.measureReal_Iic_ge hθ hD hv ht htD
      _ ≤ _ := measureReal_mono hsub
  · have hsub : Ici t ⊆ (fun x : ℝ => x + μ) ⁻¹' Ici (1 / (64 * D)) := by
      intro x hx
      simp only [Set.mem_Ici] at hx
      simp only [Set.mem_preimage, Set.mem_Ici]
      linarith
    rw [driftStep, map_measureReal_apply hT measurableSet_Ici]
    calc 1 / (1024 * D ^ 2 * v) = (1 / (16 * D) - t) ^ 2 / v := h2.symm
      _ ≤ ρW.real (Ici t) := hW.measureReal_Ici_ge hθ hD hv ht htD
      _ ≤ _ := measureReal_mono hsub

/-- The common gap constant `K = 1024 D² v / (1 - e^{-θ/(64D)})`. -/
def stepGapConst (D θ v : ℝ) : ℝ := 1024 * D ^ 2 * v / (1 - Real.exp (-(θ / (64 * D))))

theorem stepGapConst_pos (hθ : 0 < θ) (hD : 0 < D) (hv : 0 < v) : 0 < stepGapConst D θ v := by
  have he : 0 < 1 - Real.exp (-(θ / (64 * D))) := by
    rw [sub_pos, Real.exp_lt_one_iff]; have : 0 < θ / (64 * D) := by positivity
    linarith
  unfold stepGapConst; positivity

/-- Both ladder gaps of `Y = W + μ` are at least `K⁻¹`:
`(1 - E[e^{θ H₋}; τ₋ < ∞])⁻¹ ≤ K` and `(1 - E[e^{-θ H₊}; τ₊ < ∞])⁻¹ ≤ K`. -/
theorem stepLaw_gaps (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D) (hv : 0 < v)
    {μ δ : ℝ} (hμ : |μ| ≤ δ) (hδ : δ ≤ 1 / (64 * D)) :
    haveI := hW.isProbabilityMeasure
    expEntryMass (driftStep ρW μ) (Iic 0) θ < 1 ∧
      (1 - expEntryMass (driftStep ρW μ) (Iic 0) θ)⁻¹ ≤ stepGapConst D θ v ∧
      expEntryMass (driftStep ρW μ) (Ioi 0) (-θ) < 1 ∧
      (1 - expEntryMass (driftStep ρW μ) (Ioi 0) (-θ))⁻¹ ≤ stepGapConst D θ v := by
  have := hW.isProbabilityMeasure
  obtain ⟨hm1, hm2⟩ := driftStep_masses hW hθ.le hD hv hμ hδ
  have he : 0 < 1 - Real.exp (-(θ / (64 * D))) := by
    rw [sub_pos, Real.exp_lt_one_iff]; have : 0 < θ / (64 * D) := by positivity
    linarith
  have hθb : θ * (1 / (64 * D)) = θ / (64 * D) := by ring
  have key : ∀ g : ℝ, (1 - Real.exp (-(θ / (64 * D)))) * (1 / (1024 * D ^ 2 * v)) ≤ g →
      0 < g ∧ g⁻¹ ≤ stepGapConst D θ v := by
    intro g hg
    have hpos : 0 < (1 - Real.exp (-(θ / (64 * D)))) * (1 / (1024 * D ^ 2 * v)) := by positivity
    refine ⟨lt_of_lt_of_le hpos hg, ?_⟩
    rw [inv_le_comm₀ (lt_of_lt_of_le hpos hg) (stepGapConst_pos hθ hD hv), stepGapConst,
      inv_div]
    calc (1 - Real.exp (-(θ / (64 * D)))) / (1024 * D ^ 2 * v)
        = (1 - Real.exp (-(θ / (64 * D)))) * (1 / (1024 * D ^ 2 * v)) := by ring
      _ ≤ g := hg
  have g1 := one_sub_expEntryMass_Iic_ge (ρ := driftStep ρW μ) hθ.le
    (b := 1 / (64 * D)) (by positivity)
  have g2 := one_sub_expEntryMass_Ioi_ge (ρ := driftStep ρW μ) hθ.le
    (b := 1 / (64 * D)) (by positivity)
  rw [hθb] at g1 g2
  obtain ⟨p1, q1⟩ := key _ ((mul_le_mul_of_nonneg_left hm1 he.le).trans g1)
  obtain ⟨p2, q2⟩ := key _ ((mul_le_mul_of_nonneg_left hm2 he.le).trans g2)
  exact ⟨by linarith, q1, by linarith, q2⟩

/-- **Class-uniform envelope of the strict ascending ladder density** of `Y = W + μ`. -/
theorem norm_ladderDensity_asc_le_of_stepLaw (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ)
    (hD : 0 < D) (hv : 0 < v) {μ δ : ℝ} (hμ : |μ| ≤ δ) (hδ : δ ≤ 1 / (64 * D))
    {s : ℂ} (hs : ‖s‖ ≤ 1) (h : ℝ) :
    haveI := hW.isProbabilityMeasure
    ‖ladderDensity (driftStep ρW μ) (fun y => fW (y - μ)) (Ioi 0) s h‖ ≤
      ‖s‖ * (D * Real.exp (θ * δ) * stepGapConst D θ v) * Real.exp (-θ * h) := by
  have := hW.isProbabilityMeasure
  obtain ⟨hlt, hK, -, -⟩ := stepLaw_gaps hW hθ hD hv hμ hδ
  have hbound := norm_ladderDensity_asc_le (ρ := driftStep ρW μ) (f := fun y => fW (y - μ))
    (D := D * Real.exp (θ * δ)) hθ.le hlt (fun y => hW.nonneg _)
    (fun y hy => by
      have := driftStep_density_le hW hθ.le hD.le hμ y
      rwa [abs_of_pos hy] at this) hs h
  refine hbound.trans (le_of_le_of_eq (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hK (by positivity)) (Real.exp_pos _).le) ?_)
  ring

/-- **Class-uniform envelope of the weak descending ladder density** of `Y = W + μ`. -/
theorem norm_ladderDensity_desc_le_of_stepLaw (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ)
    (hD : 0 < D) (hv : 0 < v) {μ δ : ℝ} (hμ : |μ| ≤ δ) (hδ : δ ≤ 1 / (64 * D))
    {s : ℂ} (hs : ‖s‖ ≤ 1) (h : ℝ) :
    haveI := hW.isProbabilityMeasure
    ‖ladderDensity (driftStep ρW μ) (fun y => fW (y - μ)) (Iic 0) s h‖ ≤
      ‖s‖ * (D * Real.exp (θ * δ) * stepGapConst D θ v) * Real.exp (θ * h) := by
  have := hW.isProbabilityMeasure
  obtain ⟨-, -, hlt, hK⟩ := stepLaw_gaps hW hθ hD hv hμ hδ
  have hbound := norm_ladderDensity_desc_le (ρ := driftStep ρW μ) (f := fun y => fW (y - μ))
    (D := D * Real.exp (θ * δ)) hθ.le hlt (fun y => hW.nonneg _)
    (fun y hy => by
      have := driftStep_density_le hW hθ.le hD.le hμ y
      rwa [abs_of_nonpos hy, show -θ * -y = θ * y by ring] at this) hs h
  refine hbound.trans (le_of_le_of_eq (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hK (by positivity)) (Real.exp_pos _).le) ?_)
  ring

/-- Unit intervals for the strict ascending pre-ladder occupation measure of `Y = W + μ`:
`u₋((x - 1, x]) ≤ e^{θ} K`. -/
theorem preEntryOccupation_asc_Ioc_le_of_stepLaw (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ)
    (hD : 0 < D) (hv : 0 < v) {μ δ : ℝ} (hμ : |μ| ≤ δ) (hδ : δ ≤ 1 / (64 * D)) (x : ℝ) :
    haveI := hW.isProbabilityMeasure
    preEntryOccupation (driftStep ρW μ) (Ioi 0) (Ioc (x - 1) x) ≤
      ENNReal.ofReal (Real.exp θ * stepGapConst D θ v) := by
  have := hW.isProbabilityMeasure
  obtain ⟨hlt, hK, -, -⟩ := stepLaw_gaps hW hθ hD hv hμ hδ
  exact (preEntryOccupation_asc_Ioc_le hθ.le hlt x).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hK (Real.exp_pos _).le))

/-- Unit intervals for the weak descending pre-ladder occupation measure of `Y = W + μ`:
`u₊((x - 1, x]) ≤ e^{θ} K`. -/
theorem preEntryOccupation_desc_Ioc_le_of_stepLaw (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ)
    (hD : 0 < D) (hv : 0 < v) {μ δ : ℝ} (hμ : |μ| ≤ δ) (hδ : δ ≤ 1 / (64 * D)) (x : ℝ) :
    haveI := hW.isProbabilityMeasure
    preEntryOccupation (driftStep ρW μ) (Iic 0) (Ioc (x - 1) x) ≤
      ENNReal.ofReal (Real.exp θ * stepGapConst D θ v) := by
  have := hW.isProbabilityMeasure
  obtain ⟨-, -, hlt, hK⟩ := stepLaw_gaps hW hθ hD hv hμ hδ
  have hθA : ∀ y ∈ Ioi (0 : ℝ), -θ * y ≤ 0 := fun y hy => by
    have := mul_pos hθ (show (0 : ℝ) < y from hy); linarith
  have h1 := preEntryOccupation_Ioc_le (ρ := driftStep ρW μ) (measurableSet_Ioi (a := (0 : ℝ))) x
  have h2 := preEntryOccupation_unitWindow_le (ρ := driftStep ρW μ) measurableSet_Ioi
    isLadderSet_Ioi hθA hlt
  rw [compl_Ioi, abs_neg, abs_of_pos hθ] at *
  exact (h1.trans h2).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hK (Real.exp_pos _).le))

/-- The weighted `L²` bound of the ascending ladder density:
`∫ e^{2 c h} |g₊(s, h)|² dh ≤ (D e^{θδ} K)² / (2 (θ - c))` for `0 ≤ c < θ`. -/
theorem lintegral_weighted_sq_ladderDensity_asc_le (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ)
    (hD : 0 < D) (hv : 0 < v) {μ δ : ℝ} (hμ : |μ| ≤ δ) (hδ : δ ≤ 1 / (64 * D))
    {s : ℂ} (hs : ‖s‖ ≤ 1) {c : ℝ} (hc : c < θ) :
    haveI := hW.isProbabilityMeasure
    ∫⁻ h, ENNReal.ofReal (Real.exp (2 * c * h) *
        ‖ladderDensity (driftStep ρW μ) (fun y => fW (y - μ)) (Ioi 0) s h‖ ^ 2) ≤
      ENNReal.ofReal ((D * Real.exp (θ * δ) * stepGapConst D θ v) ^ 2 / (2 * (θ - c))) := by
  have := hW.isProbabilityMeasure
  set K₁ := D * Real.exp (θ * δ) * stepGapConst D θ v
  have hK₁ : 0 ≤ K₁ := by
    have := stepGapConst_pos hθ hD hv; positivity
  have hpt : ∀ h, ENNReal.ofReal (Real.exp (2 * c * h) *
      ‖ladderDensity (driftStep ρW μ) (fun y => fW (y - μ)) (Ioi 0) s h‖ ^ 2) ≤
      (Ioi (0 : ℝ)).indicator (fun h => ENNReal.ofReal (K₁ ^ 2 *
        Real.exp ((2 * c - 2 * θ) * h))) h := by
    intro h
    by_cases hh : h ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hh]
      refine ENNReal.ofReal_le_ofReal ?_
      have hb := norm_ladderDensity_asc_le_of_stepLaw hW hθ hD hv hμ hδ hs h
      have hb' : ‖ladderDensity (driftStep ρW μ) (fun y => fW (y - μ)) (Ioi 0) s h‖ ≤
          K₁ * Real.exp (-θ * h) :=
        hb.trans (by
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hK₁)
            (Real.exp_pos (-θ * h)).le
          simpa using this)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hb' 2
      calc Real.exp (2 * c * h) *
            ‖ladderDensity (driftStep ρW μ) (fun y => fW (y - μ)) (Ioi 0) s h‖ ^ 2
          ≤ Real.exp (2 * c * h) * (K₁ * Real.exp (-θ * h)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
        _ = K₁ ^ 2 * Real.exp ((2 * c - 2 * θ) * h) := by
            rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc, mul_comm (Real.exp (2 * c * h)),
              mul_assoc, ← Real.exp_add]
            congr 2; push_cast; ring
    · have : ladderDensity (driftStep ρW μ) (fun y => fW (y - μ)) (Ioi 0) s h = 0 := by
        unfold ladderDensity; rw [indicator_of_notMem hh]
      rw [this, norm_zero]; simp
  have ha : 2 * c - 2 * θ < 0 := by linarith
  calc _ ≤ ∫⁻ h, (Ioi (0 : ℝ)).indicator (fun h => ENNReal.ofReal (K₁ ^ 2 *
          Real.exp ((2 * c - 2 * θ) * h))) h := lintegral_mono hpt
    _ = ∫⁻ h in Ioi (0 : ℝ), ENNReal.ofReal (K₁ ^ 2 * Real.exp ((2 * c - 2 * θ) * h)) :=
        lintegral_indicator measurableSet_Ioi _
    _ = ENNReal.ofReal (∫ h in Ioi (0 : ℝ), K₁ ^ 2 * Real.exp ((2 * c - 2 * θ) * h)) :=
        (ofReal_integral_eq_lintegral_ofReal ((integrableOn_exp_mul_Ioi ha 0).const_mul _)
          ((ae_restrict_iff' measurableSet_Ioi).mpr
            (Filter.Eventually.of_forall fun _ _ => by positivity))).symm
    _ = _ := by
        rw [integral_const_mul, integral_exp_mul_Ioi ha 0]
        congr 1
        rw [mul_zero, Real.exp_zero, div_eq_mul_inv, div_eq_mul_inv,
          show 2 * c - 2 * θ = -(2 * (θ - c)) by ring, inv_neg]
        ring

/-- The strict ascending ladder height has mean at least `b P(Y ≥ b)`:
`E[H₊; τ₊ < ∞] ≥ b ρ[b, ∞)` (as a lower integral), for any step law and `b ≥ 0`. -/
theorem lintegral_ladderHeight_asc_ge (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {b : ℝ}
    (hb : 0 ≤ b) :
    ENNReal.ofReal b * ρ (Ici b) ≤
      ∫⁻ ω in {ω | ascLadderEpoch ω < ⊤}, ENNReal.ofReal (entryValue (Ioi 0) ω) ∂pathLaw ρ := by
  by_cases hb0 : b = 0
  · subst hb0; simp
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hsub : {ω : ℕ → ℝ | b ≤ ω 0} ⊆ {ω | ascLadderEpoch ω < ⊤} := by
    intro ω hω
    have h1 : firstEntry (Ioi 0) ω = ((1 : ℕ) : ℕ∞) := by
      rw [firstEntry_eq_coe_iff]
      refine ⟨Nat.one_pos, ?_, fun j hj hj1 => by omega⟩
      simp only [partialSum, Finset.range_one, Finset.sum_singleton, Set.mem_Ioi]
      exact lt_of_lt_of_le hbpos hω
    show firstEntry (Ioi 0) ω < ⊤
    rw [h1]; exact ENat.natCast_lt_top 1
  have hpt : ∀ ω ∈ {ω : ℕ → ℝ | b ≤ ω 0}, ENNReal.ofReal b ≤
      ENNReal.ofReal (entryValue (Ioi 0) ω) := by
    intro ω hω
    have h1 : firstEntry (Ioi 0) ω = ((1 : ℕ) : ℕ∞) := by
      rw [firstEntry_eq_coe_iff]
      refine ⟨Nat.one_pos, ?_, fun j hj hj1 => by omega⟩
      simp only [partialSum, Finset.range_one, Finset.sum_singleton, Set.mem_Ioi]
      exact lt_of_lt_of_le hbpos hω
    rw [entryValue_of_eq h1]
    simp only [partialSum, Finset.range_one, Finset.sum_singleton]
    exact ENNReal.ofReal_le_ofReal hω
  have hmeas : MeasurableSet {ω : ℕ → ℝ | b ≤ ω 0} :=
    measurableSet_le measurable_const (measurable_pi_apply 0)
  have hρ : pathLaw ρ {ω : ℕ → ℝ | b ≤ ω 0} = ρ (Ici b) := by
    rw [← (measurePreserving_eval (ρ := ρ) 0).measure_preimage measurableSet_Ici.nullMeasurableSet]
    rfl
  calc ENNReal.ofReal b * ρ (Ici b)
      = ∫⁻ _ in {ω : ℕ → ℝ | b ≤ ω 0}, ENNReal.ofReal b ∂pathLaw ρ := by
        rw [setLIntegral_const, hρ]
    _ ≤ ∫⁻ ω in {ω : ℕ → ℝ | b ≤ ω 0}, ENNReal.ofReal (entryValue (Ioi 0) ω) ∂pathLaw ρ :=
        setLIntegral_mono' hmeas hpt
    _ ≤ _ := lintegral_mono_set hsub

/-- **Class-uniform lower bound for the ascending ladder height mean** of `Y = W + μ`:
`E[H₊; τ₊ < ∞] ≥ 1/(64 D) · 1/(1024 D² v)`. -/
theorem lintegral_ladderHeight_asc_ge_of_stepLaw (hW : IsStepLaw ρW fW D θ v) (hθ : 0 ≤ θ)
    (hD : 0 < D) (hv : 0 < v) {μ δ : ℝ} (hμ : |μ| ≤ δ) (hδ : δ ≤ 1 / (64 * D)) :
    haveI := hW.isProbabilityMeasure
    ENNReal.ofReal (1 / (64 * D) * (1 / (1024 * D ^ 2 * v))) ≤
      ∫⁻ ω in {ω | ascLadderEpoch ω < ⊤}, ENNReal.ofReal (entryValue (Ioi 0) ω)
        ∂pathLaw (driftStep ρW μ) := by
  have := hW.isProbabilityMeasure
  have hm := (driftStep_masses hW hθ hD hv hμ hδ).2
  refine le_trans ?_ (lintegral_ladderHeight_asc_ge (driftStep ρW μ) (b := 1 / (64 * D))
    (by positivity))
  rw [ENNReal.ofReal_mul (by positivity)]
  gcongr
  rw [← ENNReal.ofReal_toReal (measure_ne_top (driftStep ρW μ) _)]
  exact ENNReal.ofReal_le_ofReal hm

/-- **`|g_s| ≤ |s| g_1`** for the strict ascending ladder density of `Y = W + μ`. -/
theorem norm_ladderDensity_asc_le_one_of_stepLaw (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ)
    (hD : 0 < D) (hv : 0 < v) {μ δ : ℝ} (hμ : |μ| ≤ δ) (hδ : δ ≤ 1 / (64 * D))
    {s : ℂ} (hs : ‖s‖ ≤ 1) (h : ℝ) :
    haveI := hW.isProbabilityMeasure
    ‖ladderDensity (driftStep ρW μ) (fun y => fW (y - μ)) (Ioi 0) s h‖ ≤
      ‖s‖ * ‖ladderDensity (driftStep ρW μ) (fun y => fW (y - μ)) (Ioi 0) 1 h‖ := by
  have := hW.isProbabilityMeasure
  obtain ⟨hlt, -, -, -⟩ := stepLaw_gaps hW hθ hD hv hμ hδ
  by_cases hh : 0 < h
  · have hθA : ∀ x ∈ Iic (0 : ℝ), θ * x ≤ 0 := fun x hx =>
      mul_nonpos_of_nonneg_of_nonpos hθ.le hx
    have hc : ∀ x, (x ∈ Iic (0 : ℝ) ∨ x = 0) → fW (h - x - μ) ≤
        (D * Real.exp (θ * δ) * Real.exp (-θ * h)) * Real.exp (θ * x) := by
      intro x hx
      have hx0 : x ≤ 0 := by rcases hx with hx | hx; exact hx; exact hx.le
      calc fW (h - x - μ) ≤ D * Real.exp (θ * δ) * Real.exp (-θ * |h - x|) :=
            driftStep_density_le hW hθ.le hD.le hμ _
        _ = D * Real.exp (θ * δ) * Real.exp (-θ * h) * Real.exp (θ * x) := by
            rw [abs_of_pos (by linarith), show -θ * (h - x) = -θ * h + θ * x by ring,
              Real.exp_add]
            ring
    have hsum := (summable_ladderKernel_of_le (ρ := driftStep ρW μ) (f := fun y => fW (y - μ))
      measurableSet_Iic isLadderSet_Iic hθA hlt (fun y => hW.nonneg _) hc).1
    rw [compl_Iic] at hsum
    exact norm_ladderDensity_le_one (fun y => hW.nonneg _) hs hsum
  · have h0 : ∀ t : ℂ, ladderDensity (driftStep ρW μ) (fun y => fW (y - μ)) (Ioi 0) t h = 0 := by
      intro t; unfold ladderDensity; rw [indicator_of_notMem (show h ∉ Ioi (0 : ℝ) from hh)]
    rw [h0, h0, norm_zero, mul_zero]

end PGM.WienerHopf
