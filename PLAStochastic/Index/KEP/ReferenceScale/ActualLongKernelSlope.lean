import PLAStochastic.Index.KEP.ReferenceScale.LongKernelSlope
import PLAStochastic.Index.KEP.ReferenceScale.ReferenceBand
import PLAStochastic.ForMathlib.Probability.Hellinger.DerivativeInterpolation

/-!
# Actual reference long kernels after the physical slope average

The common orbit class supplies every band hypothesis. The actual Gamma density
supplies its classical derivatives and their integrability. The endpoint slope
average then pays a square root of the input second-derivative norm; its linear
term retains the extra geometric decay of the long-row remainder.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepReferenceSecondNorm (eps : ℝ) (j : ℕ) : ℝ :=
  ∫ t, |gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j) t|

theorem kepReferenceSecondNorm_nonneg (eps : ℝ) (j : ℕ) :
    0 ≤ kepReferenceSecondNorm eps j := integral_nonneg fun _ => abs_nonneg _

theorem kepReferenceFirstNorm_le_sqrt {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j) :
    (∫ t, |gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j) t|) ≤
      3 * Real.sqrt (1 + kepReferenceSecondNorm eps j) := by
  have hc := kepReferenceDensity_classical heps hj
  exact (kepReferenceDensity heps hj).integral_abs_derivative_le_three_sqrt
    hc.2.1 hc.2.2.1
    (continuous_iff_continuousAt.mpr fun t => (hc.2.2.1 t).continuousAt).measurable
    hc.2.2.2.1.measurable hc.2.2.2.2.1 hc.2.2.2.2.2.1
    (by linarith [kepReferenceSecondNorm_nonneg eps j]) (by
      change kepReferenceSecondNorm eps j ≤ 1 + kepReferenceSecondNorm eps j
      linarith)

/-- Both endpoint orientations, every reference layer and every compact slope
are covered by one choice of constants. This remains a kernel theorem rather
than a bound on the full greedy output derivative. -/
theorem kepReference_second_long_slope_uniform :
    ∃ D vlo vhi eps0 : ℝ, 0 < D ∧ 0 < vlo ∧ vlo ≤ vhi ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ w σ : ℝ, 2 ≤ w → (σ = 1 ∨ σ = -1) →
        ∀ m k : ℕ, 8 ≤ k → ∀ x y : ℝ, (y = 0 ∨ y = w) →
        let f := (kepReferenceDensity heps hj).density
        let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        let F := fun a => truncatedConvolution 0 w (kepStepSpatialSecond f'' σ (σ * a))
          (fun z => krDens (Icc 0 w) (kepReferenceLaw eps j) f σ (σ * a)
            (m + k + 2) x z) y
        (∀ a ∈ Icc (1 / 2 : ℝ) 2,
          HasDerivAt (truncatedConvolution 0 w (kepStepSpatialFirst f' σ (σ * a))
            (fun z => krDens (Icc 0 w) (kepReferenceLaw eps j) f σ (σ * a)
              (m + k + 2) x z)) (F a) y) ∧
        IntegrableOn (fun a => |F a|) (Icc (1 / 2 : ℝ) 2) ∧
        (∫ a in Icc (1 / 2 : ℝ) 2, |F a|) ≤
          kepLongSecondSlopeBudget D vlo vhi w k
            (3 * Real.sqrt (1 + kepReferenceSecondNorm eps j))
            (kepReferenceSecondNorm eps j) := by
  obtain ⟨D, θ, vlo, vhi, K, L, e0, hD, -, hvlo, hvhi, -, -, he0, hband⟩ :=
    kepReferenceBand_uniform
  refine ⟨D, vlo, vhi, e0, hD, hvlo, hvhi, he0, ?_⟩
  intro eps he heps j hj w σ hw hσ m k hk x y hy
  dsimp only
  let p := kepReferenceDensity heps hj
  let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  have hc := kepReferenceDensity_classical heps hj
  have hH (a : ℝ) (ha : a ∈ Icc (1 / 2 : ℝ) 2) :
      KrBand D θ vlo vhi K L (kepReferenceLaw eps j) p.density w w a σ (σ * a) := by
    obtain ⟨hf, hr⟩ := hband eps he heps j hj w a (by linarith) ha.1 ha.2
    rcases hσ with rfl | rfl
    · simpa only [one_mul] using hf
    · simpa only [neg_one_mul] using hr
  have hz (t : ℝ) (ht : t ≤ 0) : f' t = 0 := by
    have hmt := mul_nonpos_of_nonneg_of_nonpos (kepReferenceSpan_pos heps j).le ht
    dsimp [f', gammaScaledFirst, gammaMixtureFirst]
    rw [gammaMixtureDensity_succ_of_nonpos _ 1 hmt,
      gammaMixtureDensity_succ_of_nonpos _ 2 hmt, sub_self, mul_zero]
  obtain ⟨hi, hb⟩ := krDens_second_long_slope_budget p (kepReferenceLaw eps j) hH
    (continuous_iff_continuousAt.mpr fun t => (hc.2.1 t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t => (hc.2.2.1 t).continuousAt)
    hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.1 hc.2.2.1 hz hw hσ m k hk x hy
  refine ⟨?_, hi, hb.trans ?_⟩
  · intro a ha
    have H := hH a ha
    convert hasDerivAt_kepFinalConvolutionFirst (kepReferenceLaw eps j)
      (w := w) (β := σ) (a := σ * a) p.measurable
      (continuous_iff_continuousAt.mpr fun t => (hc.2.2.1 t).continuousAt)
      hc.2.2.2.1 hc.2.2.1 p.nonneg H.hfD (m + k + 1) x y using 1
  · unfold kepLongSecondSlopeBudget
    apply add_le_add _ le_rfl
    have hV := kepLongUniformVariation_nonneg (w := w) k hD hvlo hvhi
    have hcoef : 0 ≤ 2 * D * kepLongUniformVariation D vlo vhi w k * (3 + 2 * w) := by
      positivity
    exact mul_le_mul_of_nonneg_left (kepReferenceFirstNorm_le_sqrt heps hj) hcoef

end

end PGM
