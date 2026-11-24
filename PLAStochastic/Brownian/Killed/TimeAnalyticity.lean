import PLAStochastic.Brownian.Killed.Semigroup
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Complex-time extension on the right half-plane. -/
def complexHeatMode (r : ℝ) (n : ℕ) (w : ℂ) (x z : ℝ) : ℂ :=
  (2 / r * (Real.sin (heatFrequency r n * x) * Real.sin (heatFrequency r n * z)) : ℝ) *
    Complex.exp (-(heatFrequency r n ^ 2 : ℝ) * w / 2)

def complexHeatKernel (r : ℝ) (w : ℂ) (x z : ℝ) : ℂ := ∑' n, complexHeatMode r n w x z

theorem norm_complexHeatMode (r : ℝ) (n : ℕ) (w : ℂ) (x z : ℝ) :
    ‖complexHeatMode r n w x z‖ = ‖heatSpatialMode r 0 0 n w.re x z‖ := by
  simp only [complexHeatMode, heatSpatialMode, Nat.cast_zero, zero_mul,
    zero_div, add_zero, pow_zero, mul_one, norm_mul, Complex.norm_real, Complex.norm_exp,
    Complex.div_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, add_zero]
  norm_num [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  left
  ring

theorem complexHeatMode_ofReal (r : ℝ) (n : ℕ) (t x z : ℝ) :
    complexHeatMode r n t x z = (heatSpatialMode r 0 0 n t x z : ℂ) := by
  simp only [complexHeatMode, heatSpatialMode, Nat.cast_zero, zero_mul,
    zero_div, add_zero, pow_zero, mul_one, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]

theorem complexHeatKernel_ofReal (r t x z : ℝ) :
    complexHeatKernel r t x z = (dirichletHeatKernel r t x z : ℂ) := by
  simp only [complexHeatKernel, complexHeatMode_ofReal, dirichletHeatKernel,
    heatSpatialSeries, Complex.ofReal_tsum]

theorem analyticOnNhd_complexHeatKernel {r : ℝ} (hr : 0 < r) (x z : ℝ) :
    AnalyticOnNhd ℂ (fun w => complexHeatKernel r w x z) {w : ℂ | 0 < w.re} := by
  intro w hw
  change 0 < w.re at hw
  let δ := w.re / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hU : IsOpen {v : ℂ | δ < v.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun v => complexHeatKernel r v x z) {v : ℂ | δ < v.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm (summable_heatSpatialBound hr hδ 0 0)
    · intro n
      dsimp only [complexHeatMode]
      fun_prop
    · exact hU
    · intro n v hv
      rw [norm_complexHeatMode]
      exact heatSpatialMode_bound hr hδ.le hv.le 0 0 n x z
  exact hd.analyticAt (hU.mem_nhds (by change δ < w.re; dsimp only [δ]; linarith))

theorem analyticOnNhd_dirichletHeatKernel_time {r : ℝ} (hr : 0 < r) (x z : ℝ) :
    AnalyticOnNhd ℝ (fun t => dirichletHeatKernel r t x z) (Ioi 0) := by
  intro t ht
  have hc := (analyticOnNhd_complexHeatKernel hr x z (t : ℂ) ht).restrictScalars (𝕜 := ℝ)
  have hd := Complex.reCLM.analyticAt (complexHeatKernel r t x z)
  have he := hc.comp (Complex.ofRealCLM.analyticAt t)
  have hf := hd.comp (f := fun v : ℝ => complexHeatKernel r v x z) he
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.reCLM_apply,
    complexHeatKernel_ofReal, Complex.ofReal_re] using hf

end BrownianAffine
