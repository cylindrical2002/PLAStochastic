import PLAStochastic.ForMathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # Removing a second-order zero over the square of a simple zero -/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

theorem tendsto_doubleZeroQuotient {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hg : DifferentiableOn ℂ g (ball 0 R))
    (hf0 : f 0 = 0) (hdf0 : deriv f 0 = 0) (hg0 : g 0 = 0) (hdg0 : deriv g 0 ≠ 0) :
    Tendsto (fun z => f z / g z ^ 2) (𝓝[≠] 0)
      (𝓝 (deriv (deriv f) 0 / (2 * deriv g 0 ^ 2))) := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hcF : ContinuousAt (fun z : ℂ => hadamard2 f 0 z) 0 := by
    have hH := differentiableOn_hadamard2 hf
    have hmem : ((0 : ℂ), (0 : ℂ)) ∈ {x : ℂ × ℂ | ‖x.1‖ + ‖x.2‖ < R} := by simpa using hR
    have hU : IsOpen {x : ℂ × ℂ | ‖x.1‖ + ‖x.2‖ < R} :=
      isOpen_lt (continuous_fst.norm.add continuous_snd.norm) continuous_const
    exact (((hH _ hmem).differentiableAt (hU.mem_nhds hmem)).continuousAt).comp
      (f := fun z : ℂ => (0, z)) (by fun_prop)
  have hcG : ContinuousAt (dslope g 0) 0 :=
    continuousAt_dslope_same.mpr ((hg _ h0).differentiableAt (isOpen_ball.mem_nhds h0))
  have hdS : dslope g 0 0 ≠ 0 := by rwa [dslope_same]
  have hc := hcF.div (hcG.pow 2) (pow_ne_zero 2 hdS)
  have hval : hadamard2 f 0 0 / dslope g 0 0 ^ 2 =
      deriv (deriv f) 0 / (2 * deriv g 0 ^ 2) := by
    rw [hadamard2_zero, dslope_same]
    ring
  have ht := hc.tendsto
  change Tendsto (fun z => hadamard2 f 0 z / dslope g 0 z ^ 2) (𝓝 0)
    (𝓝 (hadamard2 f 0 0 / dslope g 0 0 ^ 2)) at ht
  rw [hval] at ht
  have he : (fun z => f z / g z ^ 2) =ᶠ[𝓝[≠] 0]
      (fun z => hadamard2 f 0 z / dslope g 0 z ^ 2) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) hR)]
      with z hz hzR
    have hzne : z ≠ 0 := hz
    have hseg : ∀ t ∈ Icc (0 : ℝ) 1, (0 : ℂ) + t * z ∈ ball (0 : ℂ) R := by
      intro t ht
      rw [mem_ball, dist_zero_right] at hzR ⊢
      simp only [zero_add, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hzR
    have hF := hadamard2_spec isOpen_ball hf hseg
    simp only [zero_add, hf0, hdf0, zero_mul] at hF
    have hG := sub_smul_dslope g 0 z
    simp only [sub_zero, smul_eq_mul, hg0] at hG
    rw [hF, ← hG, mul_pow, mul_div_mul_left _ _ (pow_ne_zero 2 hzne)]
  exact ht.mono_left nhdsWithin_le_nhds |>.congr' he.symm

theorem tendsto_doubleZeroQuotient_of_analyticAt {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hf0 : f 0 = 0) (hdf0 : deriv f 0 = 0) (hg0 : g 0 = 0) (hdg0 : deriv g 0 ≠ 0) :
    Tendsto (fun z => f z / g z ^ 2) (𝓝[≠] 0)
      (𝓝 (deriv (deriv f) 0 / (2 * deriv g 0 ^ 2))) := by
  have he : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ f z ∧ DifferentiableAt ℂ g z :=
    (analyticAt_iff_eventually_differentiableAt.mp hf).and
      (analyticAt_iff_eventually_differentiableAt.mp hg)
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp he
  exact tendsto_doubleZeroQuotient hR
    (fun z hz => (hsub hz).1.differentiableWithinAt)
    (fun z hz => (hsub hz).2.differentiableWithinAt) hf0 hdf0 hg0 hdg0

end PGM
