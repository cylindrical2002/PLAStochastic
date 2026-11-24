import PLAStochastic.Affine.Moments.Optimal.FirstFourMoments
import PLAStochastic.Affine.Moments.Optimal.Survival.Image.Decay
import PLAStochastic.Index.GEP.LayerLaw.Defs
import PLAStochastic.ForMathlib.Probability.DensityOfSmoothCDF

/-!
# The actual normalized Brownian reference law

`cepsLambda` is the law of the canonical optimal unit lifetime divided by its
proved mean. Its mean and variance are exact, without density hypotheses.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped ENNReal NNReal

/-- The reference law `Law(τ_opt / κ)` on the actual canonical Brownian space. -/
def cepsLambda : ProbabilityMeasure ℝ :=
  ⟨canonicalPreBrownianMeasure.map (fun ω => optimalUnitLifetime canonicalBrownian ω / optimalMeanConstant),
    Measure.isProbabilityMeasure_map
      ((aemeasurable_optimalUnitLifetime isBrownianReal_canonicalBrownian).div_const _)⟩

theorem lawMean_cepsLambda : lawMean cepsLambda = 1 := by
  change (∫ x, x ∂(canonicalPreBrownianMeasure.map
    (fun ω => optimalUnitLifetime canonicalBrownian ω / optimalMeanConstant))) = 1
  rw [integral_map ((aemeasurable_optimalUnitLifetime isBrownianReal_canonicalBrownian).div_const _)
    (by fun_prop), integral_div, optimalUnitLifetime_mean_eq_constant isBrownianReal_canonicalBrownian,
    div_self optimalMeanConstant_pos.ne']

theorem lawVar_cepsLambda : lawVar cepsLambda = optimalDispersionConstant := by
  rw [lawVar, lawMean_cepsLambda]
  change (∫ x, (x - 1) ^ 2 ∂(canonicalPreBrownianMeasure.map
    (fun ω => optimalUnitLifetime canonicalBrownian ω / optimalMeanConstant))) = optimalDispersionConstant
  rw [integral_map ((aemeasurable_optimalUnitLifetime isBrownianReal_canonicalBrownian).div_const _)
    (by fun_prop)]
  have heq (x : ℝ) : (x / optimalMeanConstant - 1) ^ 2 =
      (x - optimalMeanConstant) ^ 2 / optimalMeanConstant ^ 2 := by
    field_simp [optimalMeanConstant_pos.ne']
  simp_rw [heq]
  rw [integral_div]
  have hv := variance_eq_integral (aemeasurable_optimalUnitLifetime isBrownianReal_canonicalBrownian)
  rw [optimalUnitLifetime_mean_eq_constant isBrownianReal_canonicalBrownian,
    optimalUnitLifetime_variance_eq_constant isBrownianReal_canonicalBrownian] at hv
  rw [← hv]
  rfl

theorem lawVar_cepsLambda_pos : 0 < lawVar cepsLambda := by
  rw [lawVar_cepsLambda]
  exact optimalDispersionConstant_pos

theorem cepsLambda_positive_ae : ∀ᵐ x ∂(cepsLambda : Measure ℝ), 0 < x := by
  change ∀ᵐ x ∂(canonicalPreBrownianMeasure.map
    (fun ω => optimalUnitLifetime canonicalBrownian ω / optimalMeanConstant)), 0 < x
  apply (ae_map_iff ((aemeasurable_optimalUnitLifetime isBrownianReal_canonicalBrownian).div_const _)
    measurableSet_Ioi).mpr
  filter_upwards [optimalUnitLifetime_positive_ae isBrownianReal_canonicalBrownian] with ω hω
  exact div_pos hω optimalMeanConstant_pos

theorem cepsLambda_memLp (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x : ℝ => x) p (cepsLambda : Measure ℝ) := by
  change MemLp (fun x : ℝ => x) p (canonicalPreBrownianMeasure.map
    (fun ω => optimalUnitLifetime canonicalBrownian ω / optimalMeanConstant))
  apply (memLp_map_measure_iff (by fun_prop)
    ((aemeasurable_optimalUnitLifetime isBrownianReal_canonicalBrownian).div_const _)).mpr
  simpa only [Function.comp_def, div_eq_mul_inv] using
    (optimalUnitLifetime_memLp isBrownianReal_canonicalBrownian p hp).mul_const optimalMeanConstant⁻¹

theorem cepsLambda_exp_integrable : ∃ η : ℝ, 0 < η ∧
    Integrable (fun x : ℝ => Real.exp (η * x)) (cepsLambda : Measure ℝ) := by
  obtain ⟨θ, hθ, hint⟩ := optimalUnitLifetime_exp_neighborhood isBrownianReal_canonicalBrownian
  refine ⟨θ * optimalMeanConstant, mul_pos hθ optimalMeanConstant_pos, ?_⟩
  change Integrable (fun x : ℝ => Real.exp (θ * optimalMeanConstant * x))
    (canonicalPreBrownianMeasure.map
      (fun ω => optimalUnitLifetime canonicalBrownian ω / optimalMeanConstant))
  apply (integrable_map_measure (by fun_prop)
    ((aemeasurable_optimalUnitLifetime isBrownianReal_canonicalBrownian).div_const _)).mpr
  convert hint θ (by rw [abs_of_pos hθ]) using 1
  funext ω
  dsimp [Function.comp_def]
  congr 1
  field_simp [optimalMeanConstant_pos.ne']

end

end PGM
