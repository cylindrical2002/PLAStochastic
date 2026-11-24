import PLAStochastic.Index.KEP.StoppedExponential

/-!
# The normalized stopped output has a fixed exponential moment

The compensated stopped exponential and the geometric stopping tail are
combined by the arithmetic-geometric mean inequality. This argument allows
dependent nonhomogeneous gaps and preserves the original stopped readout.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

theorem integral_normalized_stopSum_exp_le_73
    (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] (eps theta C d : ℝ)
    {M : ℕ} (hM : 1 ≤ M) (hd : 0 ≤ d) (hdM : d * M ≤ 1 / 144)
    (hcomp : ∫⁻ g, ENNReal.ofReal (Real.exp ((2 * theta / C) * stopSum eps g -
      d * ((gapSegLen eps g).toNat : ℝ))) ∂P ≤ 1)
    (htail : ∀ k : ℕ, P.real {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps g} ≤
      (71 / 72 : ℝ) ^ k) :
    Integrable (fun g => Real.exp (theta * (stopSum eps g / C))) P ∧
      ∫ g, Real.exp (theta * (stopSum eps g / C)) ∂P ≤ 73 := by
  have hT := (isStoppingRule_gapSegLen eps).measurable
  have hTe := lintegral_exp_toNat_le_145 hT hM hd hdM htail
  have hTn : Measurable (fun g : ℕ → ℝ => ((gapSegLen eps g).toNat : ℝ)) :=
    (Measurable.of_discrete (f := fun k : ℕ∞ => (k.toNat : ℝ))).comp hT
  have hpt (g : ℕ → ℝ) : Real.exp (theta * (stopSum eps g / C)) ≤
      (Real.exp ((2 * theta / C) * stopSum eps g - d * ((gapSegLen eps g).toNat : ℝ)) +
        Real.exp (d * ((gapSegLen eps g).toNat : ℝ))) / 2 := by
    calc
      _ = Real.exp (((2 * theta / C) * stopSum eps g - d * ((gapSegLen eps g).toNat : ℝ) +
          d * ((gapSegLen eps g).toNat : ℝ)) / 2) := by congr 1; ring
      _ ≤ _ := exp_half_add_le _ _
  have hlin : ∫⁻ g, ENNReal.ofReal (Real.exp (theta * (stopSum eps g / C))) ∂P ≤
      ENNReal.ofReal 73 := by
    calc
      _ ≤ ∫⁻ g, ENNReal.ofReal (1 / 2) *
          ENNReal.ofReal (Real.exp ((2 * theta / C) * stopSum eps g -
            d * ((gapSegLen eps g).toNat : ℝ))) +
          ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Real.exp (d * ((gapSegLen eps g).toNat : ℝ))) ∂P := by
        apply lintegral_mono
        intro g
        dsimp only
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith [hpt g])
      _ = ENNReal.ofReal (1 / 2) * (∫⁻ g, ENNReal.ofReal
          (Real.exp ((2 * theta / C) * stopSum eps g - d * ((gapSegLen eps g).toNat : ℝ))) ∂P) +
          ENNReal.ofReal (1 / 2) * (∫⁻ g, ENNReal.ofReal
            (Real.exp (d * ((gapSegLen eps g).toNat : ℝ))) ∂P) := by
        rw [lintegral_add_right _ ((hTn.const_mul d).exp.ennreal_ofReal.const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (1 / 2) * 1 + ENNReal.ofReal (1 / 2) * ENNReal.ofReal 145 := by
        gcongr
      _ = ENNReal.ofReal 73 := by
        rw [mul_one, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
  have hi : Integrable (fun g => Real.exp (theta * (stopSum eps g / C))) P :=
    (lintegral_ofReal_ne_top_iff_integrable
      (((measurable_stopSum eps).div_const C).const_mul theta).exp.aestronglyMeasurable
      (Eventually.of_forall fun _ => Real.exp_nonneg _)).mp
      ((hlin.trans_lt ENNReal.ofReal_lt_top).ne)
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun _ => Real.exp_nonneg _)] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 73)).mp hlin

end

end PGM
