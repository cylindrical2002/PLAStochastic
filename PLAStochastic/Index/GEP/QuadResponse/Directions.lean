import PLAStochastic.Index.GEP.PointwiseSmall.ThreeBumpDirections

/-!
# WP4 leaf `QuadResponse`: the two direction laws of the quadratic direction

`quadDir = ½ 1_{(0,1]} - 1_{(1,2]} + ½ 1_{(2,3]}` is `2 (σ₊ - σ₋)` for the direction laws
`σ₊ = ¾ U(0,1) + ¼ U(2,3)` and `σ₋ = ½ U(0,1) + ½ U(1,2)` (both of mean one, with
`∫ e^{θσ y} dσ± ≤ 1 + e^{3θσ}`), so that for every locally integrable kernel
`∫ J · quadDir = 2 (∫ J dσ₊ - ∫ J dσ₋)` (`quad_exists_pair`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

theorem quad_unifM_Iic_zero : unifM (Icc (0 : ℝ) 1) (Iic 0) = 0 := by
  rw [unifM, Measure.smul_apply, Measure.restrict_apply measurableSet_Iic]
  have : Iic (0 : ℝ) ∩ Icc 0 1 = {0} := by
    ext y
    simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, -⟩
      linarith
    · rintro rfl
      exact ⟨le_rfl, le_rfl, zero_le_one⟩
  rw [this, Real.volume_singleton, smul_zero]

/-- A mixture of `U(0,1), U(1,2), U(2,3)` with mean one is a direction law. -/
theorem quad_sigmaLaw {A θσ w₁ w₂ w₃ : ℝ} (hθσ : 0 ≤ θσ) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hw₃ : 0 ≤ w₃) (hmean : w₁ * (1 / 2) + w₂ * (3 / 2) + w₃ * (5 / 2) = 1)
    (hexp : w₁ * Real.exp (θσ * 1) + w₂ * Real.exp (θσ * 2) + w₃ * Real.exp (θσ * 3) ≤ A)
    {σ : ProbabilityMeasure ℝ}
    (hσ : (σ : Measure ℝ) = mix3 w₁ w₂ w₃ (unifM (Icc (0 : ℝ) 1)) (unifM (Icc (1 : ℝ) 2))
      (unifM (Icc (2 : ℝ) 3))) :
    SigmaLaw A θσ σ := by
  have h01 : (0 : ℝ) < 1 := one_pos
  have h12 : (1 : ℝ) < 2 := by norm_num
  have h23 : (2 : ℝ) < 3 := by norm_num
  have := isProbabilityMeasure_unifM h01
  have := isProbabilityMeasure_unifM h12
  have := isProbabilityMeasure_unifM h23
  have hid : ∀ {a b : ℝ}, a < b → Integrable (fun y : ℝ => y) (unifM (Icc a b)) :=
    fun hab => integrable_unifM hab (continuous_id.integrableOn_Icc)
  have hex : ∀ {a b : ℝ}, a < b → Integrable (fun y : ℝ => Real.exp (θσ * y)) (unifM (Icc a b)) :=
    fun hab => integrable_unifM hab ((by fun_prop : Continuous fun y : ℝ =>
      Real.exp (θσ * y)).integrableOn_Icc)
  have hexle : ∀ {a b : ℝ}, a < b → ∫ y, Real.exp (θσ * y) ∂(unifM (Icc a b)) ≤
      Real.exp (θσ * b) := fun hab => integral_unifM_le hab
    ((by fun_prop : Continuous fun y : ℝ => Real.exp (θσ * y)).integrableOn_Icc)
    fun y hy => Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hy.2 hθσ)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hσ, mix3]
    simp only [Measure.add_apply, Measure.smul_apply, quad_unifM_Iic_zero,
      unifM_Iic_zero h01, unifM_Iic_zero (by norm_num : (0 : ℝ) < 2), smul_zero, add_zero]
  · rw [hσ, mix3]
    exact ((((unifM_ac _).smul_left _).add_left ((unifM_ac _).smul_left _)).add_left
      ((unifM_ac _).smul_left _))
  · rw [lawMean, hσ, integral_mix3 hw₁ hw₂ hw₃ (hid h01) (hid h12) (hid h23),
      integral_id_unifM h01, integral_id_unifM h12, integral_id_unifM h23]
    norm_num
    linarith
  · rw [hσ]
    exact integrable_mix3 (hex h01) (hex h12) (hex h23)
  · rw [hσ, integral_mix3 hw₁ hw₂ hw₃ (hex h01) (hex h12) (hex h23)]
    refine le_trans ?_ hexp
    gcongr
    · exact hexle h01
    · exact hexle h12
    · exact hexle h23

/-- `∫_{(a, a+1]} J = ⨍_{[a, a+1]} J`. -/
theorem quad_integral_Ioc_eq_average (J : ℝ → ℝ) {a b : ℝ} (hab : b - a = 1) :
    ∫ x in Ioc a b, J x = ⨍ y in Icc a b, J y := by
  rw [setAverage_eq, measureReal_def, Real.volume_Icc, hab, ENNReal.toReal_ofReal zero_le_one,
    inv_one, one_smul, integral_Icc_eq_integral_Ioc]

/-- The pointwise form of `J · quadDir`. -/
theorem quad_mul_quadDir (J : ℝ → ℝ) (x : ℝ) :
    J x * quadDir x = 1 / 2 * (Ioc (0 : ℝ) 1).indicator J x - (Ioc (1 : ℝ) 2).indicator J x +
      1 / 2 * (Ioc (2 : ℝ) 3).indicator J x := by
  simp only [quadDir, indicator_apply]
  split_ifs <;> ring

/-- **The two direction laws of the quadratic direction.** -/
theorem quad_exists_pair {θσ : ℝ} (hθσ : 0 < θσ) :
    ∃ σp σm : ProbabilityMeasure ℝ, SigmaLaw (1 + Real.exp (θσ * 3)) θσ σp ∧
      SigmaLaw (1 + Real.exp (θσ * 3)) θσ σm ∧
      ∀ J : ℝ → ℝ, IntegrableOn J (Icc (0 : ℝ) 3) →
        ∫ x, J x * quadDir x = 2 * (∫ y, J y ∂(σp : Measure ℝ) - ∫ y, J y ∂(σm : Measure ℝ)) := by
  have h01 : (0 : ℝ) < 1 := one_pos
  have h12 : (1 : ℝ) < 2 := by norm_num
  have h23 : (2 : ℝ) < 3 := by norm_num
  have := isProbabilityMeasure_unifM h01
  have := isProbabilityMeasure_unifM h12
  have := isProbabilityMeasure_unifM h23
  have hPp : IsProbabilityMeasure (mix3 (3 / 4) 0 (1 / 4) (unifM (Icc (0 : ℝ) 1))
      (unifM (Icc (1 : ℝ) 2)) (unifM (Icc (2 : ℝ) 3))) :=
    isProbabilityMeasure_mix3 (by norm_num) le_rfl (by norm_num) (by norm_num)
  have hPm : IsProbabilityMeasure (mix3 (1 / 2) (1 / 2) 0 (unifM (Icc (0 : ℝ) 1))
      (unifM (Icc (1 : ℝ) 2)) (unifM (Icc (2 : ℝ) 3))) :=
    isProbabilityMeasure_mix3 (by norm_num) (by norm_num) le_rfl (by norm_num)
  have he1 : Real.exp (θσ * 1) ≤ Real.exp (θσ * 3) := Real.exp_le_exp.2 (by nlinarith)
  have he2 : Real.exp (θσ * 2) ≤ Real.exp (θσ * 3) := Real.exp_le_exp.2 (by nlinarith)
  have hp : 0 < Real.exp (θσ * 3) := Real.exp_pos _
  refine ⟨⟨_, hPp⟩, ⟨_, hPm⟩, ?_, ?_, ?_⟩
  · refine quad_sigmaLaw hθσ.le (by norm_num) le_rfl (by norm_num) (by norm_num) ?_ rfl
    linarith
  · refine quad_sigmaLaw hθσ.le (by norm_num) (by norm_num) le_rfl (by norm_num) ?_ rfl
    linarith
  · intro J hJ
    have hi : ∀ a b : ℝ, 0 ≤ a → b ≤ 3 → IntegrableOn J (Icc a b) :=
      fun a b ha hb => hJ.mono_set (Icc_subset_Icc ha hb)
    have hi' : ∀ a b : ℝ, 0 ≤ a → b ≤ 3 → Integrable ((Ioc a b).indicator J) :=
      fun a b ha hb => (integrable_indicator_iff measurableSet_Ioc).2
        ((hi a b ha hb).mono_set Ioc_subset_Icc_self)
    have e : (fun x => J x * quadDir x) = fun x => 1 / 2 * (Ioc (0 : ℝ) 1).indicator J x -
        (Ioc (1 : ℝ) 2).indicator J x + 1 / 2 * (Ioc (2 : ℝ) 3).indicator J x :=
      funext (quad_mul_quadDir J)
    have i0 : Integrable (fun x => 1 / 2 * (Ioc (0 : ℝ) 1).indicator J x) :=
      (hi' 0 1 le_rfl (by norm_num)).const_mul _
    have i1 : Integrable (fun x => 1 / 2 * (Ioc (0 : ℝ) 1).indicator J x -
        (Ioc (1 : ℝ) 2).indicator J x) := i0.sub (hi' 1 2 (by norm_num) (by norm_num))
    have i2 : Integrable (fun x => 1 / 2 * (Ioc (2 : ℝ) 3).indicator J x) :=
      (hi' 2 3 (by norm_num) le_rfl).const_mul _
    rw [e, integral_add i1 i2, integral_sub i0 (hi' 1 2 (by norm_num) (by norm_num)),
      integral_const_mul, integral_const_mul, integral_indicator measurableSet_Ioc,
      integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]
    change _ = 2 * (∫ y, J y ∂(mix3 (3 / 4) 0 (1 / 4) _ _ _) -
      ∫ y, J y ∂(mix3 (1 / 2) (1 / 2) 0 _ _ _))
    rw [integral_mix3 (by norm_num) le_rfl (by norm_num) (integrable_unifM h01 (hi 0 1 le_rfl
        (by norm_num))) (integrable_unifM h12 (hi 1 2 (by norm_num) (by norm_num)))
        (integrable_unifM h23 (hi 2 3 (by norm_num) le_rfl)),
      integral_mix3 (by norm_num) (by norm_num) le_rfl (integrable_unifM h01 (hi 0 1 le_rfl
        (by norm_num))) (integrable_unifM h12 (hi 1 2 (by norm_num) (by norm_num)))
        (integrable_unifM h23 (hi 2 3 (by norm_num) le_rfl)),
      integral_unifM, integral_unifM, integral_unifM]
    rw [quad_integral_Ioc_eq_average J (by norm_num : (1 : ℝ) - 0 = 1),
      quad_integral_Ioc_eq_average J (by norm_num : (2 : ℝ) - 1 = 1),
      quad_integral_Ioc_eq_average J (by norm_num : (3 : ℝ) - 2 = 1)]
    ring

end

end PGM
