import PLAStochastic.Affine.Moments.Optimal.Spatial.IntegralDerivative
import PLAStochastic.Affine.Moments.Optimal.Laplace.KernelIdentification

/-! # The genuine nonnegative spatial integrals equal the four real L-integrands -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Compact integrability justifies converting a nonnegative spatial integral to a real one. -/
theorem lintegral_ofReal_weighted_spatial {H : ℝ → ℝ → ℝ}
    (hH : Continuous (fun p : ℝ×ℝ => H p.1 p.2))
    (hpos : ∀ a ∈ Ioo (0:ℝ) 1, ∀ b ∈ Ioo (0:ℝ) 1, 0 ≤ H a b) (k : ℝ) :
    (∫⁻ b : ℝ in Ioo 0 1, ∫⁻ a : ℝ in Ioo 0 1,
      ENNReal.ofReal (Real.cosh (k*(b-a))*H a b)) =
      ENNReal.ofReal (∫ b : ℝ in Ioo 0 1, ∫ a : ℝ in Ioo 0 1,
        Real.cosh (k*(b-a))*H a b) := by
  let F : ℝ×ℝ → ℝ := fun p => Real.cosh (k*(p.1-p.2))*H p.2 p.1
  have hc : Continuous F :=
    (by fun_prop : Continuous (fun p : ℝ×ℝ => Real.cosh (k*(p.1-p.2)))).mul
      (hH.comp continuous_swap)
  have hi : IntegrableOn F (Ioo 0 1 ×ˢ Ioo 0 1) ((volume : Measure ℝ).prod volume) :=
    (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hn : 0 ≤ᵐ[((volume : Measure ℝ).prod volume).restrict (Ioo 0 1 ×ˢ Ioo 0 1)] F := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    exact mul_nonneg (Real.cosh_pos _).le (hpos p.2 hp.2 p.1 hp.1)
  rw [← setLIntegral_prod (fun p : ℝ×ℝ => ENNReal.ofReal (F p))
    (hc.measurable.ennreal_ofReal.aemeasurable)]
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, setIntegral_prod F hi]

theorem spatialLaplaceFormula0_nonneg {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) :
    0≤spatialLaplaceFormula0 k a b := by
  rw [← optimalMomentTimeTransform_eq_spatial0 ha hb hk]
  exact optimalMomentTimeTransform_nonneg ha hb 0 k

theorem spatialLaplaceFormula1_nonneg {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) :
    0≤spatialLaplaceFormula1 k a b := by
  rw [← optimalMomentTimeTransform_eq_spatial1 ha hb hk]
  exact optimalMomentTimeTransform_nonneg ha hb 1 k

theorem spatialLaplaceFormula2_nonneg {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) :
    0≤spatialLaplaceFormula2 k a b := by
  rw [← optimalMomentTimeTransform_eq_spatial2 ha hb hk]
  exact optimalMomentTimeTransform_nonneg ha hb 2 k

theorem spatialLaplaceFormula3_nonneg {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) :
    0≤spatialLaplaceFormula3 k a b := by
  rw [← optimalMomentTimeTransform_eq_spatial3 ha hb hk]
  exact optimalMomentTimeTransform_nonneg ha hb 3 k

theorem lintegral_spatialLaplaceFormula0_diagonal {k : ℝ} (hk : 0 < k) :
    (∫⁻ b : ℝ in Ioo 0 1, ∫⁻ a : ℝ in Ioo 0 1,
      ENNReal.ofReal (Real.cosh (k*(b-a))*spatialLaplaceFormula0 k a b)) =
      ENNReal.ofReal (optimalRawIntegrandOne k) := by
  rw [lintegral_ofReal_weighted_spatial (continuous_spatialLaplaceFormula0 k)
    (fun a ha b hb => spatialLaplaceFormula0_nonneg ha hb hk),
    integral_spatialLaplaceFormula0_diagonal hk]

theorem optimalRawIntegrandOne_nonneg {k : ℝ} (hk : 0 < k) :
    0 ≤ optimalRawIntegrandOne k := by
  rw [← integral_spatialLaplaceFormula0_diagonal hk]
  apply setIntegral_nonneg measurableSet_Ioo
  intro b hb
  apply setIntegral_nonneg measurableSet_Ioo
  intro a ha
  exact mul_nonneg (Real.cosh_pos _).le (spatialLaplaceFormula0_nonneg ha hb hk)

theorem lintegral_spatialLaplaceFormula1_diagonal {k : ℝ} (hk : 0 < k) :
    (∫⁻ b : ℝ in Ioo 0 1, ∫⁻ a : ℝ in Ioo 0 1,
      ENNReal.ofReal (Real.cosh (k*(b-a))*spatialLaplaceFormula1 k a b)) =
      ENNReal.ofReal (optimalRawIntegrandTwo k) := by
  rw [lintegral_ofReal_weighted_spatial (continuous_spatialLaplaceFormula1 k)
    (fun a ha b hb => spatialLaplaceFormula1_nonneg ha hb hk),
    integral_spatialLaplaceFormula1_diagonal hk]

theorem optimalRawIntegrandTwo_nonneg {k : ℝ} (hk : 0 < k) :
    0 ≤ optimalRawIntegrandTwo k := by
  rw [← integral_spatialLaplaceFormula1_diagonal hk]
  apply setIntegral_nonneg measurableSet_Ioo
  intro b hb
  apply setIntegral_nonneg measurableSet_Ioo
  intro a ha
  exact mul_nonneg (Real.cosh_pos _).le (spatialLaplaceFormula1_nonneg ha hb hk)

theorem lintegral_spatialLaplaceFormula2_diagonal {k : ℝ} (hk : 0 < k) :
    (∫⁻ b : ℝ in Ioo 0 1, ∫⁻ a : ℝ in Ioo 0 1,
      ENNReal.ofReal (Real.cosh (k*(b-a))*spatialLaplaceFormula2 k a b)) =
      ENNReal.ofReal (optimalRawIntegrandThree k) := by
  rw [lintegral_ofReal_weighted_spatial (continuous_spatialLaplaceFormula2 k)
    (fun a ha b hb => spatialLaplaceFormula2_nonneg ha hb hk),
    integral_spatialLaplaceFormula2_diagonal hk]

theorem optimalRawIntegrandThree_nonneg {k : ℝ} (hk : 0 < k) :
    0 ≤ optimalRawIntegrandThree k := by
  rw [← integral_spatialLaplaceFormula2_diagonal hk]
  apply setIntegral_nonneg measurableSet_Ioo
  intro b hb
  apply setIntegral_nonneg measurableSet_Ioo
  intro a ha
  exact mul_nonneg (Real.cosh_pos _).le (spatialLaplaceFormula2_nonneg ha hb hk)

theorem lintegral_spatialLaplaceFormula3_diagonal {k : ℝ} (hk : 0 < k) :
    (∫⁻ b : ℝ in Ioo 0 1, ∫⁻ a : ℝ in Ioo 0 1,
      ENNReal.ofReal (Real.cosh (k*(b-a))*spatialLaplaceFormula3 k a b)) =
      ENNReal.ofReal (optimalRawIntegrandFour k) := by
  rw [lintegral_ofReal_weighted_spatial (continuous_spatialLaplaceFormula3 k)
    (fun a ha b hb => spatialLaplaceFormula3_nonneg ha hb hk),
    integral_spatialLaplaceFormula3_diagonal hk]

theorem optimalRawIntegrandFour_nonneg {k : ℝ} (hk : 0 < k) :
    0 ≤ optimalRawIntegrandFour k := by
  rw [← integral_spatialLaplaceFormula3_diagonal hk]
  apply setIntegral_nonneg measurableSet_Ioo
  intro b hb
  apply setIntegral_nonneg measurableSet_Ioo
  intro a ha
  exact mul_nonneg (Real.cosh_pos _).le (spatialLaplaceFormula3_nonneg ha hb hk)

end BrownianAffine
