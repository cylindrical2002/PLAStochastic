import PLAStochastic.Index.CEPS.BrownianCoeff.Root

/-!
# The Brownian endpoint coefficient

The factor `ξ₊ / z` is rationalized before defining the endpoint. In particular
`cepsBrownianEndpoint v 0 = 1` is an analytic value, not a total-division convention.
-/

noncomputable section

open Complex

namespace PGM

/-- The analytic Brownian endpoint coefficient `𝓔₀`. -/
def cepsBrownianEndpoint (v z : ℂ) : ℂ :=
  2 * cepsBrownianR v 1 z / (1 + cepsBrownianR v 1 z) *
    Complex.exp (-cepsBrownianXiPlus v 1 z)

@[simp] theorem cepsBrownianEndpoint_zero (v : ℂ) : cepsBrownianEndpoint v 0 = 1 := by
  norm_num [cepsBrownianEndpoint, cepsBrownianR, cepsBrownianXiPlus]

theorem cepsBrownian_one_add_R_ne (v : ℂ) (lam : ℝ) (z : ℂ) :
    1 + cepsBrownianR v lam z ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [add_re, one_re, zero_re] at this
  linarith [cepsBrownianR_re_nonneg v lam z]

/-- Agreement with blueprint §3.8 away from the displayed `0/0`. -/
theorem cepsBrownianEndpoint_eq {v z : ℂ} (hv : v ≠ 0) (hz : z ≠ 0) :
    cepsBrownianEndpoint v z = cepsBrownianXiPlus v 1 z * cepsBrownianR v 1 z *
      Complex.exp (-cepsBrownianXiPlus v 1 z) / z := by
  have hs := cepsBrownianR_sq v 1 z
  norm_num at hs
  have hx : cepsBrownianXiPlus v 1 z / z = 2 / (1 + cepsBrownianR v 1 z) := by
    unfold cepsBrownianXiPlus
    norm_num
    field_simp [hv, hz, cepsBrownian_one_add_R_ne v 1 z]
    linear_combination hs
  unfold cepsBrownianEndpoint
  rw [show cepsBrownianXiPlus v 1 z * cepsBrownianR v 1 z *
      Complex.exp (-cepsBrownianXiPlus v 1 z) / z =
      (cepsBrownianXiPlus v 1 z / z) * cepsBrownianR v 1 z *
        Complex.exp (-cepsBrownianXiPlus v 1 z) by ring, hx]
  ring

theorem cepsBrownianEndpoint_differentiableAt {v z : ℂ} (hv : 0 < v.re) (hz : z.re = 0) :
    DifferentiableAt ℂ (fun u => cepsBrownianEndpoint u z) v := by
  have hvne : v ≠ 0 := by intro h; simp [h] at hv
  have hr := cepsBrownianR_differentiableAt (lam := (1 : ℝ)) hv hz
  have hxi : DifferentiableAt ℂ (fun u => cepsBrownianXiPlus u 1 z) v := by
    exact (differentiableAt_const _ |>.add hr).div differentiableAt_id hvne
  exact ((hr.const_mul 2).div (differentiableAt_const _ |>.add hr)
    (cepsBrownian_one_add_R_ne v 1 z)).mul hxi.neg.cexp

/-- Explicit endpoint-envelope amplitude. -/
def cepsBrownianEndpointConst (v₀ : ℝ) : ℝ :=
  2 * (1 + 2 * Real.sqrt v₀) * Real.exp (2 / v₀)

theorem cepsBrownianEndpoint_decay {v₀ : ℝ} {v z : ℂ} (hv₀ : 0 < v₀)
    (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hz : z.re = 0) :
    ‖cepsBrownianEndpoint v z‖ ≤ cepsBrownianEndpointConst v₀ * (1 + ‖z‖) *
      Real.exp (-cepsBrownianDecay v₀ * Real.sqrt ‖z‖) := by
  have hvnorm := (cepsBrownian_variance_bounds hv₀ hv).2.1
  have hden : 1 ≤ ‖1 + cepsBrownianR v 1 z‖ := by
    have := Complex.re_le_norm (1 + cepsBrownianR v 1 z)
    simp only [add_re, one_re] at this
    linarith [cepsBrownianR_re_nonneg v 1 z]
  have hroot := cepsBrownianR_norm_le hv₀ hv 1 z
  norm_num at hroot
  have hsqrt : Real.sqrt ‖z‖ ≤ 1 + ‖z‖ := by
    nlinarith [Real.sqrt_nonneg ‖z‖, Real.sq_sqrt (norm_nonneg z), norm_nonneg z,
      sq_nonneg (Real.sqrt ‖z‖ - 1)]
  have hroot' : ‖cepsBrownianR v 1 z‖ ≤ (1 + 2 * Real.sqrt v₀) * (1 + ‖z‖) := by
    nlinarith [Real.sqrt_nonneg v₀, norm_nonneg z]
  have hinv : (1 / v : ℂ).re ≤ 2 / v₀ := by
    calc
      (1 / v : ℂ).re ≤ ‖(1 / v : ℂ)‖ := Complex.re_le_norm _
      _ = 1 / ‖v‖ := by simp
      _ ≤ 2 / v₀ := by
        have := div_le_div_of_nonneg_left zero_le_one (by positivity : 0 < v₀ / 2) hvnorm
        simpa using this
  have hq := cepsBrownian_quotient_re (lam := (1 : ℝ)) hv₀ hv hz
  norm_num at hq
  have hexp : ‖Complex.exp (-cepsBrownianXiPlus v 1 z)‖ ≤
      Real.exp (2 / v₀) * Real.exp (-cepsBrownianDecay v₀ * Real.sqrt ‖z‖) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have heq : (-cepsBrownianXiPlus v 1 z).re =
        (1 / v : ℂ).re - (cepsBrownianR v 1 z / v).re := by
      have he : -cepsBrownianXiPlus v 1 z = 1 / v - cepsBrownianR v 1 z / v := by
        unfold cepsBrownianXiPlus
        norm_num
        ring
      simpa using congrArg Complex.re he
    rw [heq]
    have hc := (cepsBrownianDecay_pos hv₀).le
    nlinarith
  unfold cepsBrownianEndpoint
  rw [norm_mul, norm_div, norm_mul, Complex.norm_ofNat]
  calc
    2 * ‖cepsBrownianR v 1 z‖ / ‖1 + cepsBrownianR v 1 z‖ *
        ‖Complex.exp (-cepsBrownianXiPlus v 1 z)‖ ≤
        (2 * ((1 + 2 * Real.sqrt v₀) * (1 + ‖z‖))) *
          (Real.exp (2 / v₀) * Real.exp (-cepsBrownianDecay v₀ * Real.sqrt ‖z‖)) := by
      gcongr
      · calc
          2 * ‖cepsBrownianR v 1 z‖ / ‖1 + cepsBrownianR v 1 z‖ ≤
              2 * ‖cepsBrownianR v 1 z‖ / 1 := by gcongr
          _ ≤ 2 * ((1 + 2 * Real.sqrt v₀) * (1 + ‖z‖)) := by simpa using mul_le_mul_of_nonneg_left hroot' (by norm_num : (0 : ℝ) ≤ 2)
    _ = _ := by unfold cepsBrownianEndpointConst; ring

end PGM
