import PLAStochastic.Index.KEP.ReferenceScale.ActualFiniteGraphPolynomial
import PLAStochastic.Index.KEP.ReferenceScale.ActualLongKernelQuantitative

/-!
# The original second graph kernel inherits the physical long-series budget

The bridge index is the number of preceding killed steps. The final spatial
derivative adds one step; its logarithmic-slope norm costs at most a factor two.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepLogBridgeRight_second_physical_average (ν : ProbabilityMeasure ℝ)
    {f g : ℝ → ℝ} {D w σ : ℝ} (hcf : Continuous f) (hcg : Continuous g)
    (hf0 : ∀ t, 0 ≤ f t) (hfD : ∀ t, f t ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (f t)))
    (hσ : σ = 1 ∨ σ = -1) (n : ℕ) {x : ℝ} (hx : x ∈ Icc 0 w) (y : ℝ) :
    kepLogSlopeNorm (fun s => kepFixedBridgeRight (kepLogStep f σ)
      (kepLogStepSecond g σ) w s (n + 1) x y) ≤
      2 * ∫ a in Icc (1 / 2 : ℝ) 2,
        |truncatedConvolution 0 w (kepStepSpatialSecond g σ (σ * a))
          (fun z => krDens (Icc 0 w) ν f σ (σ * a) (n + 1) x z) y| := by
  have hG : Continuous (fun s => kepFixedBridgeRight (kepLogStep f σ)
      (kepLogStepSecond g σ) w s (n + 1) x y) :=
    (continuous_kepFixedBridgeRight (continuous_kepLogStep hcf σ)
      (continuous_kepLogStepSecond hcg σ) w (n + 1)).comp
        (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hh := kep_setIntegral_abs_logSlope_le hG
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 2)
  have heq : (fun a => |kepFixedBridgeRight (kepLogStep f σ)
      (kepLogStepSecond g σ) w (Real.log a) (n + 1) x y|) =ᵐ[
      volume.restrict (Icc (1 / 2 : ℝ) 2)]
      (fun a => |truncatedConvolution 0 w (kepStepSpatialSecond g σ (σ * a))
        (fun z => krDens (Icc 0 w) ν f σ (σ * a) (n + 1) x z) y|) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    rw [kepLogBridgeRight_eq_second_convolution ν hcf.measurable hf0 hfD hν hσ
      (Real.log a) n hx y, Real.exp_log (by linarith [ha.1] : 0 < a)]
  rw [integral_congr_ae heq] at hh
  simpa only [one_div, inv_inv, kepLogSlopeNorm] using hh

theorem kepReference_second_graph_kernel_polynomial_budget :
    ∃ theta c eps0 : ℝ, 0 < theta ∧ 0 < c ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ p : ℕ, ∃ K : ℝ, 0 < K ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
          ∀ m N : ℕ, 8 ≤ N → eps ≤ (N / 2 : ℕ) →
          ∀ x y : ℝ, (x = 0 ∨ x = 2 * eps) → (y = 0 ∨ y = 2 * eps) →
          let f := (kepReferenceDensity heps hj).density
          let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
          let C := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
          let F := fun k : ℕ => (k + N + 1 : ℝ) ^ p *
            Real.exp (2 * theta * (k + N) / C) *
            kepLogSlopeNorm (fun s => kepFixedBridgeRight (kepLogStep f σ)
              (kepLogStepSecond f'' σ) (2 * eps) s (m + k + N + 2) x y)
          Summable F ∧ (∑' k : ℕ, F k) ≤
            K * eps ^ (2 * p + 4) *
              (1 + Real.sqrt (kepReferenceSecondNorm eps j) +
                Real.exp (-c * eps) * kepReferenceSecondNorm eps j) := by
  obtain ⟨theta, c, e0, ht, hc, he0, hlong⟩ := kepReference_second_long_slope_polynomial_budget
  obtain ⟨D, θ, vlo, vhi, KB, LB, e1, hD, _, hvlo, hvhi, _, _, he1, hband⟩ :=
    kepReferenceBand_uniform
  refine ⟨theta, c, max e0 e1, ht, hc, he0.trans (le_max_left _ _), ?_⟩
  intro p
  obtain ⟨K, hK, hlongp⟩ := hlong p
  refine ⟨2 * K, by positivity, ?_⟩
  intro eps he heps j hj σ hσ m N hN hcut x y hx hy
  dsimp only
  let f := (kepReferenceDensity heps hj).density
  let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let C := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
  let F := fun k : ℕ => (k + N + 1 : ℝ) ^ p * Real.exp (2 * theta * (k + N) / C) *
    (∫ a in Icc (1 / 2 : ℝ) 2,
      |truncatedConvolution 0 (2 * eps) (kepStepSpatialSecond f'' σ (σ * a))
        (fun z => krDens (Icc 0 (2 * eps)) (kepReferenceLaw eps j) f σ (σ * a)
          (m + k + N + 2) x z) y|)
  let G := fun k : ℕ => (k + N + 1 : ℝ) ^ p * Real.exp (2 * theta * (k + N) / C) *
    kepLogSlopeNorm (fun s => kepFixedBridgeRight (kepLogStep f σ)
      (kepLogStepSecond f'' σ) (2 * eps) s (m + k + N + 2) x y)
  obtain ⟨hsF, hbF⟩ := hlongp eps ((le_max_left _ _).trans he) heps j hj σ hσ m N hN hcut x y hy
  have H := (hband eps ((le_max_right _ _).trans he) heps j hj (2 * eps) 1
    (by linarith [(le_max_left _ _).trans heps] : 1 ≤ 2 * eps)
    (by norm_num) (by norm_num)).1
  have hclass := kepReferenceDensity_classical heps hj
  have hxband : x ∈ Icc 0 (2 * eps) := by
    have he2 : 2 ≤ eps := (le_max_left _ _).trans heps
    rcases hx with rfl | rfl <;> constructor <;> linarith
  have hb (k : ℕ) : G k ≤ 2 * F k := by
    have hcf : Continuous f := continuous_iff_continuousAt.mpr
      (fun t => (hclass.2.1 t).continuousAt)
    have hh := kepLogBridgeRight_second_physical_average (kepReferenceLaw eps j)
      hcf hclass.2.2.2.1 H.hf0 H.hfD H.hνf hσ (m + k + N + 1) hxband y
    have hn : m + k + N + 1 + 1 = m + k + N + 2 := by omega
    rw [hn] at hh
    have hm := mul_le_mul_of_nonneg_left hh (by positivity :
      0 ≤ (k + N + 1 : ℝ) ^ p * Real.exp (2 * theta * (k + N) / C))
    exact hm.trans_eq (by dsimp [G, F]; ring)
  have hs2 : Summable (fun k => 2 * F k) := hsF.mul_left 2
  have hsG := hs2.of_nonneg_of_le (fun k =>
    mul_nonneg (by positivity) (kepLogSlopeNorm_nonneg _)) hb
  refine ⟨hsG, ?_⟩
  calc
    _ ≤ ∑' k : ℕ, 2 * F k := hsG.tsum_le_tsum hb hs2
    _ = 2 * ∑' k : ℕ, F k := tsum_mul_left
    _ ≤ 2 * (K * eps ^ (2 * p + 4) *
        (1 + Real.sqrt (kepReferenceSecondNorm eps j) +
          Real.exp (-c * eps) * kepReferenceSecondNorm eps j)) :=
      mul_le_mul_of_nonneg_left hbF (by norm_num)
    _ = _ := by ring

end

end PGM
