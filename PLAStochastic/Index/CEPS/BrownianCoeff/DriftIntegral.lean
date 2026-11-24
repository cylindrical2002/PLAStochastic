import PLAStochastic.Index.CEPS.BrownianCoeff.DriftMeasurable
import PLAStochastic.Index.CEPS.BrownianCoeff.UpperDrift

/-!
# The Brownian full-drift integral

The variance-disc envelope is used before taking the real drift integral.
The derivative is the integral of actual variance derivatives, each integrable.
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace PGM

def cepsBrownianDriftIntegral (v z : ℂ) : ℂ :=
  ∫ lam : ℝ, cepsBrownianKernel v lam z

/-- Dominated variance differentiation of the actual Brownian kernel. -/
theorem cepsBrownianDriftIntegral_hasDerivAt_of_envelope {v₀ : ℝ} {v z : ℂ}
    {B : ℝ → ℝ} (hv₀ : 0 < v₀)
    (hv : ‖v - (v₀ : ℂ)‖ < cepsBrownianRadius v₀) (hz : z.re = 0)
    (hB : Integrable B)
    (hb : ∀ u : ℂ, ‖u - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀ →
      ∀ lam : ℝ, ‖cepsBrownianKernel u lam z‖ ≤ B lam) :
    Integrable (fun lam : ℝ => cepsBrownianKernel v lam z) ∧
      Integrable (fun lam : ℝ => deriv (fun u => cepsBrownianKernel u lam z) v) ∧
      HasDerivAt (fun u => cepsBrownianDriftIntegral u z)
        (∫ lam : ℝ, deriv (fun u => cepsBrownianKernel u lam z) v) v := by
  have hvb : v ∈ ball (v₀ : ℂ) (cepsBrownianRadius v₀) := by
    simpa only [mem_ball, dist_eq_norm] using hv
  have hd (lam : ℝ) : DifferentiableOn ℂ (fun u => cepsBrownianKernel u lam z)
      (ball (v₀ : ℂ) (cepsBrownianRadius v₀)) := by
    intro u hu
    have hum : ‖u - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀ := by
      simpa only [dist_eq_norm] using (mem_ball.mp hu).le
    exact (cepsBrownianKernel_differentiableAt lam z hv₀ hum hz).differentiableWithinAt
  exact cepsBrownian_hasDerivAt_integral_of_disc_bound hvb
    (fun u => (cepsBrownianKernel_measurable_drift u z).aestronglyMeasurable) hd hB
    (fun u hu => hb u (by simpa only [dist_eq_norm] using (mem_ball.mp hu).le))

theorem cepsBrownianKernel_integrable_drift {v₀ : ℝ} {v z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hz : z.re = 0) :
    Integrable (fun lam : ℝ => cepsBrownianKernel v lam z) := by
  exact (cepsBrownian_fullEnvelope_integrable (C := cepsBrownianKernelConst v₀) 4
    (div_pos (cepsBrownianDecay_pos hv₀) (by norm_num)) z).mono'
    (cepsBrownianKernel_measurable_drift v z).aestronglyMeasurable
    (ae_of_all _ fun lam => cepsBrownianKernel_decay lam z hv₀ hv hz)

def cepsBrownianIntegralConst (v₀ : ℝ) : ℝ :=
  cepsBrownianKernelConst v₀ *
    ∫ lam : ℝ, (1 + |lam|) ^ 4 * Real.exp (-(cepsBrownianDecay v₀ / 3) * |lam|)

theorem cepsBrownianIntegralConst_nonneg {v₀ : ℝ} (hv₀ : 0 < v₀) :
    0 ≤ cepsBrownianIntegralConst v₀ := by
  exact mul_nonneg (cepsBrownianKernelConst_nonneg hv₀)
    (integral_nonneg fun lam => by positivity)

theorem cepsBrownianIntegralConst_le_explicit {v₀ : ℝ} (hv₀ : 0 < v₀) :
    cepsBrownianIntegralConst v₀ ≤ cepsBrownianKernelConst v₀ *
      (((4 : ℕ).factorial : ℝ) / ((cepsBrownianDecay v₀ / 3) / 2) ^ 4 *
        Real.exp ((cepsBrownianDecay v₀ / 3) / 2) * (4 / (cepsBrownianDecay v₀ / 3))) := by
  exact mul_le_mul_of_nonneg_left (cepsBrownian_driftEnvelope_integral_le 4
    (div_pos (cepsBrownianDecay_pos hv₀) (by norm_num))) (cepsBrownianKernelConst_nonneg hv₀)

/-- The actual real-drift integral retains stretched-exponential frequency decay. -/
theorem cepsBrownianDriftIntegral_decay {v₀ : ℝ} {v z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hz : z.re = 0) :
    ‖cepsBrownianDriftIntegral v z‖ ≤ cepsBrownianIntegralConst v₀ * (1 + ‖z‖) ^ 4 *
      Real.exp (-(cepsBrownianDecay v₀ / 3) * Real.sqrt ‖z‖) := by
  exact (cepsBrownian_integral_norm_le_of_envelope 4
    (div_pos (cepsBrownianDecay_pos hv₀) (by norm_num))
    (cepsBrownianKernelConst_nonneg hv₀) z
    (cepsBrownianKernel_measurable_drift v z).aestronglyMeasurable
    (fun lam => cepsBrownianKernel_decay lam z hv₀ hv hz)).2

theorem cepsBrownianDriftIntegral_hasDerivAt {v₀ : ℝ} {v z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ < cepsBrownianRadius v₀) (hz : z.re = 0) :
    Integrable (fun lam : ℝ => deriv (fun u => cepsBrownianKernel u lam z) v) ∧
      HasDerivAt (fun u => cepsBrownianDriftIntegral u z)
        (∫ lam : ℝ, deriv (fun u => cepsBrownianKernel u lam z) v) v := by
  exact (cepsBrownianDriftIntegral_hasDerivAt_of_envelope hv₀ hv hz
    (cepsBrownian_fullEnvelope_integrable (C := cepsBrownianKernelConst v₀) 4
      (div_pos (cepsBrownianDecay_pos hv₀) (by norm_num)) z)
    (fun u hu lam => cepsBrownianKernel_decay lam z hv₀ hu hz)).2

/-- Holomorphy on the full open disc used for the uniform kernel estimates. -/
theorem cepsBrownianDriftIntegral_analyticOnNhd {v₀ : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hz : z.re = 0) :
    AnalyticOnNhd ℂ (fun v => cepsBrownianDriftIntegral v z)
      (ball (v₀ : ℂ) (cepsBrownianRadius v₀)) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  intro v hv
  exact (cepsBrownianDriftIntegral_hasDerivAt hv₀
    (by simpa only [mem_ball, dist_eq_norm] using hv) hz).2.differentiableAt.differentiableWithinAt

/-- A closed admissible disc of radius `v₀ / 32` lies inside the holomorphy
domain, so every point has an actual open complex neighborhood. -/
theorem cepsBrownianDriftIntegral_analyticAt {v₀ : ℝ} {v z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ v₀ / 32) (hz : z.re = 0) :
    AnalyticAt ℂ (fun u => cepsBrownianDriftIntegral u z) v := by
  apply cepsBrownianDriftIntegral_analyticOnNhd hv₀ hz v
  rw [mem_ball, dist_eq_norm, cepsBrownianRadius]
  linarith

end PGM
