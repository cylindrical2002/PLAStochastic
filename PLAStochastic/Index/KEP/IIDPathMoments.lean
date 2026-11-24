import PLAStochastic.Index.KEP.IIDStoppedPrefixLaws
import PLAStochastic.ForMathlib.Probability.Moments.ExponentialPolynomial

/-!
# Actual iid reference path moments and their prefix-state laws

The canonical iid sequence is used, rather than an assumed path certificate.
Its fixed exponential moment pays every integer cumulative moment and the
same moment under the proved finite-prefix kernel iteration.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepGapPrefix_gapKeys (i : ℕ) (g : ℕ → ℝ) :
    gapKeys (kepGapPrefix i g) i = gapKeys g i :=
  gapKeys_congr (fun _k hk => if_pos hk) i le_rfl

theorem iid_gapKeys_power_budget (nu : ProbabilityMeasure ℝ)
    {theta B : ℝ} (htheta : 0 < theta)
    (hpos : ∀ᵐ z ∂(nu : Measure ℝ), 0 ≤ z)
    (hi : Integrable (fun z => Real.exp (theta * z)) (nu : Measure ℝ))
    (hb : ∫ z, Real.exp (theta * z) ∂(nu : Measure ℝ) ≤ B) (N k : ℕ) :
    Integrable (fun g => gapKeys g N ^ (k + 1)) (iidLaw nu) ∧
      ∫ g, gapKeys g N ^ (k + 1) ∂iidLaw nu ≤
        (N : ℝ) ^ (k + 1) * ((k + 1).factorial / theta ^ (k + 1) * B) := by
  have hmoment := polynomial_moment_of_exponential measurable_id htheta hpos hi hb (k + 1)
  have hpres (i : ℕ) :
      MeasurePreserving (fun g : ℕ → ℝ => g i) (iidLaw nu) (nu : Measure ℝ) :=
    measurePreserving_eval_infinitePi (fun _ : ℕ => (nu : Measure ℝ)) i
  have hcoordI (i : ℕ) : Integrable (fun g : ℕ → ℝ => g i ^ (k + 1)) (iidLaw nu) :=
    (hpres i).integrable_comp_of_integrable hmoment.1
  have hcoordB (i : ℕ) :
      ∫ g : ℕ → ℝ, g i ^ (k + 1) ∂iidLaw nu ≤
        (k + 1).factorial / theta ^ (k + 1) * B := by
    have hF : Measurable (fun z : ℝ => z ^ (k + 1)) := by fun_prop
    have he := integral_map (μ := iidLaw nu) (hpres i).measurable.aemeasurable
      hF.aestronglyMeasurable
    rw [(hpres i).map_eq] at he
    rw [← he]
    exact hmoment.2
  exact ⟨integrable_finite_sum_pow N k (fun i _ => measurable_pi_apply i)
      (fun i _ => (hpres i).quasiMeasurePreserving.ae hpos) (fun i _ => hcoordI i),
    integral_finite_sum_pow_le N k (fun i _ => measurable_pi_apply i)
      (fun i _ => (hpres i).quasiMeasurePreserving.ae hpos) (fun i _ => hcoordI i)
      (fun i _ => hcoordB i)⟩

theorem iid_prefix_state_power_budget (nu : ProbabilityMeasure ℝ)
    {theta B : ℝ} (htheta : 0 < theta)
    (hpos : ∀ᵐ z ∂(nu : Measure ℝ), 0 ≤ z)
    (hi : Integrable (fun z => Real.exp (theta * z)) (nu : Measure ℝ))
    (hb : ∫ z, Real.exp (theta * z) ∂(nu : Measure ℝ) ≤ B) (N k : ℕ) :
    Integrable (fun g => gapKeys g N ^ (k + 1))
      (kernelIterateLaw (kepReferencePrefixKernel nu) (Measure.dirac (fun _ => 0)) N) ∧
      ∫ g, gapKeys g N ^ (k + 1)
        ∂kernelIterateLaw (kepReferencePrefixKernel nu) (Measure.dirac (fun _ => 0)) N ≤
        (N : ℝ) ^ (k + 1) * ((k + 1).factorial / theta ^ (k + 1) * B) := by
  have h := iid_gapKeys_power_budget nu htheta hpos hi hb N k
  rw [← iid_kepGapPrefix_law]
  have hF : Measurable (fun g : ℕ → ℝ => gapKeys g N ^ (k + 1)) :=
    ((measurable_pi_apply N).comp measurable_gapKeys).pow_const _
  refine ⟨?_, ?_⟩
  · apply (integrable_map_measure hF.aestronglyMeasurable
      (measurable_kepGapPrefix N).aemeasurable).mpr
    simpa only [Function.comp_def, kepGapPrefix_gapKeys] using h.1
  · rw [integral_map (measurable_kepGapPrefix N).aemeasurable hF.aestronglyMeasurable]
    simpa only [kepGapPrefix_gapKeys] using h.2

end

end PGM
