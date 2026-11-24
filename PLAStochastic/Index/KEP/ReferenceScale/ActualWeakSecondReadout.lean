import PLAStochastic.Index.KEP.ReferenceScale.WeightedSecondDuality
import PLAStochastic.Index.KEP.ReferenceScale.IntegrableRadialTransfer

/-!
# Weak second tests read the genuine next reference density

Two genuine global integrations by parts identify the second test under the
actual probability law with a test of its actual classical second density.
The weighted duality lemma then reads the original weighted second norm.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepReference_compact_second_weak_identity {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    {phi : ℝ → ℝ} (hphi : ContDiff ℝ 2 phi) (hsupp : HasCompactSupport phi) :
    (∫ x, deriv (deriv phi) x ∂(kepReferenceLaw eps j : Measure ℝ)) =
      ∫ x, phi x * gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j) x := by
  let p := kepReferenceDensity heps hj
  let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  have hp := kepReferenceDensity_classical heps hj
  have hc1 : ContDiff ℝ 1 (deriv phi) := hphi.deriv'
  have hc2 : Continuous (deriv (deriv phi)) := hc1.continuous_deriv (by norm_num)
  have hd : ∀ x, HasDerivAt phi (deriv phi x) x := fun x =>
    (hphi.differentiable (by norm_num) x).hasDerivAt
  have hdd : ∀ x, HasDerivAt (deriv phi) (deriv (deriv phi) x) x := fun x =>
    (hc1.differentiable (by norm_num) x).hasDerivAt
  obtain ⟨M, hb⟩ := kep_C2_compact_bounded_test hd hdd hc2 hsupp
  have hi (psi F : ℝ → ℝ) (hpsi : Continuous psi) (hF : Integrable F)
      (hbound : ∀ t, |psi t| ≤ M) : Integrable (fun t => psi t * F t) :=
    hF.bdd_mul hpsi.aestronglyMeasurable (ae_of_all _ fun t => by
      simpa only [Real.norm_eq_abs] using hbound t)
  have hi0 := hi (deriv phi) p.density hc1.continuous p.integrable (fun t => (hb t).2.1)
  have hi1 := hi (deriv (deriv phi)) p.density hc2 p.integrable (fun t => (hb t).2.2)
  have hi2 := hi (deriv phi) f' hc1.continuous hp.2.2.2.2.1 (fun t => (hb t).2.1)
  have hiF := hi phi f' hphi.continuous hp.2.2.2.2.1 (fun t => (hb t).1)
  have hiFF := hi phi f'' hphi.continuous hp.2.2.2.2.2.1 (fun t => (hb t).1)
  have h1 := kep_integrable_first_weak_transfer hdd hp.2.1 hi0 hi1 hi2
  have h2 := kep_integrable_first_weak_transfer hd hp.2.2.1 hiF hi2 hiFF
  rw [← kepReferenceDensity_toMeasure heps hj, p.integral_toMeasure]
  calc
    _ = ∫ x, deriv (deriv phi) x * p.density x := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => mul_comm _ _
    _ = -(∫ x, deriv phi x * f' x) := h1
    _ = _ := by rw [h2, neg_neg]

theorem kepReference_weighted_norm_of_compact_second_tests {eps theta K : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) (he3 : 3 ≤ eps)
    {j : ℕ} (hj : 1 ≤ j)
    (hi : Integrable (fun x => Real.exp (theta * x) *
      gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j) x))
    (hbudget : ∀ phi : ℝ → ℝ, ContDiff ℝ 2 phi → HasCompactSupport phi →
      (∀ x, |phi x| ≤ Real.exp (theta * x)) →
      |∫ x, deriv (deriv phi) x ∂(kepReferenceLaw eps j : Measure ℝ)| ≤ K) :
    kepReferenceWeightedSecondNorm theta eps j ≤ K := by
  apply kep_weighted_second_norm_le_of_C2_tests
    (kepReference_second_density_C2 heps he3 hj) theta K
  · simpa only [abs_mul, abs_of_pos (Real.exp_pos _)] using hi.abs
  · intro phi hphi hsupp hb
    rw [← kepReference_compact_second_weak_identity heps hj hphi hsupp]
    exact hbudget phi hphi hsupp hb

end

end PGM
