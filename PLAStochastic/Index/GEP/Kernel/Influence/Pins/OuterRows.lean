import PLAStochastic.Index.GEP.Kernel.Influence.Pins.OuterSurvival

/-! # The actual two outside rows in the scalar influence formula -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1000000

theorem kernel_IF_outer_lintegral (ν : ProbabilityMeasure ℝ) (eps a : ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (hrt : (q.1 : ℕ) ≤ q.2.2.1) :
    (∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) ∂iidLaw ν) =
      ENNReal.ofReal (krSurv (Icc 0 (2*eps)) (ν : Measure ℝ) (-1) (-a) q.1 (eps-fluxFacetSign q*eps) *
        krSurv (Icc 0 (2*eps)) (ν : Measure ℝ) 1 a (k-q.2.2.1) (eps-fluxFacetSign q*eps)) := by
  let J := Icc 0 (2*eps)
  let b := eps-fluxFacetSign q*eps
  let r : ℕ := q.1
  let t : ℕ := q.2.2.1
  have hm : Measurable (kernelIFOuterSurvival eps a q) :=
    (measurable_kernelIFOuterSurvival_coords eps a q).mono (kCoordSigma_le _) le_rfl
  have hi : Integrable (kernelIFOuterSurvival eps a q) (iidLaw ν) := by
    apply kr_integrable_of_bdd hm (M := 1)
    intro g
    rw [kernelIFOuterSurvival, abs_mul]
    exact (mul_le_mul (abs_krAlive_le_one _ _ _) (abs_krAlive_le_one _ _ _)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun g => kernel_IF_outer_survival_nonneg eps a q g)]
  congr 1
  have h₀ : Measurable[kCoordSigma (Iio r)] (fun g : ℕ → ℝ =>
      krAlive J (-1) (-a) r b (kernelReversePrefix g r)) := by
    have hh := kernel_blockTest_coord_measurable (J := J) measurableSet_Icc (-1) (-a) r b
      (φ := fun _ => (1 : ℝ)) measurable_const (c := fun j => r-1-j) (S := Iio r)
      (by intro j hj; change r-1-j < r; omega)
    unfold kernelReversePrefix
    simpa only [kernelBlockTest, mul_one] using hh
  have h₃ : Measurable[kCoordSigma (Ici t)] (fun g : ℕ → ℝ =>
      krAlive J 1 a (k-t) b (fun j => g (j+t))) := by
    simpa only [kernelBlockTest, mul_one] using
      kernel_blockTest_coord_measurable (J := J) measurableSet_Icc 1 a (k-t) b
        (φ := fun _ => (1 : ℝ)) measurable_const (c := fun j => j+t) (S := Ici t)
        (by intro j _; change t ≤ j+t; omega)
  rw [show kernelIFOuterSurvival eps a q = fun g =>
      krAlive J (-1) (-a) r b (kernelReversePrefix g r) *
        krAlive J 1 a (k-t) b (fun j => g (j+t)) from rfl,
    kernel_iid_integral_mul_coords ν (S := Iio r) (T := Ici t)
      (Set.disjoint_left.mpr (by intro j hj ht; change j < r at hj; change t ≤ j at ht; omega)) h₀ h₃]
  have hrev : (∫ g, krAlive J (-1) (-a) r b (kernelReversePrefix g r) ∂iidLaw ν) =
      ∫ g, krAlive J (-1) (-a) r b g ∂iidLaw ν := by
    calc
      _ = ∫ g, krAlive J (-1) (-a) r b (fun j => g (kernelReverseIndex r j)) ∂iidLaw ν := by
        apply integral_congr_ae
        exact Eventually.of_forall fun g => kernel_krAlive_congr _ _ _ _ _ (by
          intro j hj
          simp only [kernelReversePrefix, kernelReverseIndex, if_pos hj])
      _ = _ := kernel_iid_integral_reindex ν (kernelReverseIndex_injective r)
        (measurable_krAlive_right measurableSet_Icc (-1) (-a) r b)
  rw [hrev, kernel_iid_integral_reindex ν (fun _ _ h => Nat.add_right_cancel h)
    (measurable_krAlive_right measurableSet_Icc 1 a (k-t) b),
    ← krSurv_eq_integral measurableSet_Icc ν (-1) (-a) r b,
    ← krSurv_eq_integral measurableSet_Icc ν 1 a (k-t) b]

end
end PGM
