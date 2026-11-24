import PLAStochastic.Index.CEPS.BrownianCoeff.Holomorphy
import PLAStochastic.Index.CEPS.BrownianCoeff.Removable
import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound
import PLAStochastic.ForMathlib.Analysis.Fourier.WeightedRemainder
import PLAStochastic.ForMathlib.Analysis.Calculus.ExponentialDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Integrable drift envelopes and genuine variance differentiation

The bounds in this file apply to the full real drift integral. Holomorphy
uses a common integrable envelope on a variance disc and Cauchy estimates;
pointwise holomorphy alone is not an input sufficient for the conclusion.
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace PGM

theorem cepsBrownian_integral_exp_neg_abs {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, Real.exp (-a * |x|)) = 2 / a := by
  have hn : (∫ x : ℝ in Iic 0, Real.exp (-a * |x|)) = 1 / a := by
    calc
      _ = ∫ x : ℝ in Iic 0, Real.exp (a * x) :=
        setIntegral_congr_fun measurableSet_Iic fun x hx => by
          rw [abs_of_nonpos hx]; congr 1; ring
      _ = _ := by rw [integral_exp_mul_Iic ha]; simp
  have hp : (∫ x : ℝ in Ioi 0, Real.exp (-a * |x|)) = 1 / a := by
    calc
      _ = ∫ x : ℝ in Ioi 0, Real.exp (-a * x) :=
        setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [abs_of_pos hx]
      _ = _ := by rw [integral_exp_mul_Ioi (show -a < 0 by linarith)]; simp
  rw [← integral_add_compl measurableSet_Iic (integrable_exp_neg_abs ha), compl_Iic, hn, hp]
  ring

theorem cepsBrownian_driftEnvelope_integrable (d : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => (1 + |x|) ^ d * Real.exp (-c * |x|)) := by
  let B : ℝ := (d.factorial : ℝ) / (c / 2) ^ d * Real.exp (c / 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (x : ℝ) : (1 + |x|) ^ d * Real.exp (-c * |x|) ≤
      B * Real.exp (-(c / 2) * |x|) := by
    have hp := Real.pow_le_factorial_inv_mul_exp d (half_pos hc)
      (show 0 ≤ 1 + |x| by positivity)
    calc
      _ ≤ ((d.factorial : ℝ) / (c / 2) ^ d *
          Real.exp ((c / 2) * (1 + |x|))) * Real.exp (-c * |x|) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = _ := by
        dsimp [B]
        rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
        congr 2
        ring
  refine ((integrable_exp_neg_abs (half_pos hc)).const_mul B).mono'
    (by fun_prop) (ae_of_all _ fun x => ?_)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ (1 + |x|) ^ d * Real.exp (-c * |x|))] using hb x

/-- An explicit bound for the only remaining drift-envelope integral. -/
theorem cepsBrownian_driftEnvelope_integral_le (d : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ, (1 + |x|) ^ d * Real.exp (-c * |x|)) ≤
      ((d.factorial : ℝ) / (c / 2) ^ d * Real.exp (c / 2)) * (4 / c) := by
  let B : ℝ := (d.factorial : ℝ) / (c / 2) ^ d * Real.exp (c / 2)
  have hb (x : ℝ) : (1 + |x|) ^ d * Real.exp (-c * |x|) ≤
      B * Real.exp (-(c / 2) * |x|) := by
    have hp := Real.pow_le_factorial_inv_mul_exp d (half_pos hc)
      (show 0 ≤ 1 + |x| by positivity)
    calc
      _ ≤ ((d.factorial : ℝ) / (c / 2) ^ d *
          Real.exp ((c / 2) * (1 + |x|))) * Real.exp (-c * |x|) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = _ := by
        dsimp [B]
        rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
        congr 2
        ring
  calc
    _ ≤ ∫ x : ℝ, B * Real.exp (-(c / 2) * |x|) :=
      integral_mono (cepsBrownian_driftEnvelope_integrable d hc)
        ((integrable_exp_neg_abs (half_pos hc)).const_mul B) hb
    _ = _ := by
      rw [integral_const_mul, cepsBrownian_integral_exp_neg_abs (half_pos hc)]
      dsimp [B]
      congr 1
      ring

theorem cepsBrownian_fullEnvelope_integrable (d : ℕ) {c C : ℝ} (hc : 0 < c)
    (z : ℂ) :
    Integrable (fun x : ℝ => C * (1 + |x| + ‖z‖) ^ d *
      Real.exp (-c * (|x| + Real.sqrt ‖z‖))) := by
  have hi := (cepsBrownian_driftEnvelope_integrable d hc).const_mul
    (|C| * (1 + ‖z‖) ^ d * Real.exp (-c * Real.sqrt ‖z‖))
  refine hi.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (1 + |x| + ‖z‖) ^ d),
    abs_of_pos (Real.exp_pos _)]
  have hp : 1 + |x| + ‖z‖ ≤ (1 + |x|) * (1 + ‖z‖) := by
    nlinarith [mul_nonneg (abs_nonneg x) (norm_nonneg z)]
  calc
    _ ≤ |C| * ((1 + |x|) * (1 + ‖z‖)) ^ d *
        Real.exp (-c * (|x| + Real.sqrt ‖z‖)) := by gcongr
    _ = _ := by rw [mul_pow, show -c * (|x| + Real.sqrt ‖z‖) =
      -c * |x| + -c * Real.sqrt ‖z‖ by ring, Real.exp_add]; ring

/-- The integrated envelope preserves the frequency decay and a finite
polynomial budget. All integrals in this estimate are genuinely integrable. -/
theorem cepsBrownian_integral_norm_le_of_envelope {F : ℝ → ℂ} {C c : ℝ}
    (d : ℕ) (hc : 0 < c) (hC : 0 ≤ C) (z : ℂ)
    (hm : AEStronglyMeasurable F)
    (hb : ∀ x, ‖F x‖ ≤ C * (1 + |x| + ‖z‖) ^ d *
      Real.exp (-c * (|x| + Real.sqrt ‖z‖))) :
    Integrable F ∧ ‖∫ x, F x‖ ≤
      (C * ∫ x : ℝ, (1 + |x|) ^ d * Real.exp (-c * |x|)) *
        (1 + ‖z‖) ^ d * Real.exp (-c * Real.sqrt ‖z‖) := by
  have he := cepsBrownian_fullEnvelope_integrable (C := C) d hc z
  have hi : Integrable F := he.mono' hm (ae_of_all _ hb)
  have hmajor (x : ℝ) : C * (1 + |x| + ‖z‖) ^ d *
      Real.exp (-c * (|x| + Real.sqrt ‖z‖)) ≤
      (C * (1 + ‖z‖) ^ d * Real.exp (-c * Real.sqrt ‖z‖)) *
        ((1 + |x|) ^ d * Real.exp (-c * |x|)) := by
    have hp : 1 + |x| + ‖z‖ ≤ (1 + |x|) * (1 + ‖z‖) := by
      nlinarith [mul_nonneg (abs_nonneg x) (norm_nonneg z)]
    calc
      _ ≤ C * ((1 + |x|) * (1 + ‖z‖)) ^ d *
          Real.exp (-c * (|x| + Real.sqrt ‖z‖)) := by gcongr
      _ = _ := by rw [mul_pow, show -c * (|x| + Real.sqrt ‖z‖) =
        -c * |x| + -c * Real.sqrt ‖z‖ by ring, Real.exp_add]; ring
  have hmi := (cepsBrownian_driftEnvelope_integrable d hc).const_mul
    (C * (1 + ‖z‖) ^ d * Real.exp (-c * Real.sqrt ‖z‖))
  refine ⟨hi, (norm_integral_le_integral_norm F).trans ?_⟩
  calc
    _ ≤ ∫ x : ℝ, (C * (1 + ‖z‖) ^ d * Real.exp (-c * Real.sqrt ‖z‖)) *
        ((1 + |x|) ^ d * Real.exp (-c * |x|)) :=
      integral_mono hi.norm hmi (fun x => (hb x).trans (hmajor x))
    _ = _ := by rw [integral_const_mul]; ring

/-- Measurability of variance derivatives comes from measurable difference quotients. -/
theorem cepsBrownian_parameterDeriv_aestronglyMeasurable {F : ℂ → ℝ → ℂ} {v : ℂ}
    (hm : ∀ u, AEStronglyMeasurable (F u))
    (hd : ∀ x, DifferentiableAt ℂ (fun u => F u x) v) :
    AEStronglyMeasurable (fun x => deriv (fun u => F u x) v) := by
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] v)
    (f := fun u x => slope (fun w => F w x) v u)
  · intro u
    simpa only [slope_def_field, div_eq_mul_inv, Pi.sub_apply] using
      ((hm u).sub (hm v)).mul_const (u - v)⁻¹
  · exact ae_of_all _ fun x => (hd x).hasDerivAt.tendsto_slope

/-- A common integrable bound on a complex disc pays genuine differentiation
under the drift integral at each interior variance point. -/
theorem cepsBrownian_hasDerivAt_integral_of_disc_bound {F : ℂ → ℝ → ℂ}
    {v center : ℂ} {r : ℝ} {B : ℝ → ℝ}
    (hv : v ∈ ball center r)
    (hm : ∀ u, AEStronglyMeasurable (F u))
    (hd : ∀ x, DifferentiableOn ℂ (fun u => F u x) (ball center r))
    (hB : Integrable B)
    (hb : ∀ u ∈ ball center r, ∀ x, ‖F u x‖ ≤ B x) :
    Integrable (F v) ∧
      Integrable (fun x => deriv (fun u => F u x) v) ∧
      HasDerivAt (fun u => ∫ x, F u x) (∫ x, deriv (fun u => F u x) v) v := by
  let rho : ℝ := r - dist v center
  have hrho : 0 < rho := by dsimp [rho]; exact sub_pos.mpr hv
  have hsub : ball v rho ⊆ ball center r := by
    intro u hu
    change dist u center < r
    calc
      dist u center ≤ dist u v + dist v center := dist_triangle _ _ _
      _ < rho + dist v center := by linarith [mem_ball.mp hu]
      _ = r := by dsimp [rho]; ring
  have hdv (x : ℝ) : DifferentiableAt ℂ (fun u => F u x) v :=
    (hd x v hv).differentiableAt (isOpen_ball.mem_nhds hv)
  have hi : Integrable (F v) := hB.mono' (hm v) (ae_of_all _ (hb v hv))
  have hdm := cepsBrownian_parameterDeriv_aestronglyMeasurable hm hdv
  have hlip : ∀ᵐ x : ℝ, LipschitzOnWith (Real.nnabs (4 * B x / rho))
      (fun u => F u x) (ball v (rho / 2)) := by
    apply ae_of_all
    intro x
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu w hw
    rw [Real.coe_nnabs, dist_eq_norm, dist_eq_norm]
    exact (norm_sub_le_of_ball_half hrho ((hd x).mono hsub)
      (fun t ht => hb t (hsub ht) x) hu hw).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have hboundI : Integrable (fun x => 4 * B x / rho) := by
    convert hB.const_mul (4 / rho) using 1
    ext x
    ring
  have h := hasDerivAt_integral_of_dominated_loc_of_lip
    (ball_mem_nhds v (half_pos hrho)) (Eventually.of_forall hm) hi hdm hlip
    hboundI (ae_of_all _ fun x => (hdv x).hasDerivAt)
  exact ⟨hi, h.1, h.2⟩

end PGM
