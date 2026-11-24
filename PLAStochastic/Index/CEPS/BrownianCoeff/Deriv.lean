import PLAStochastic.Index.CEPS.BrownianCoeff.Formula

/-!
# Actual frequency derivatives of the Brownian bridges

These derivatives justify the `∂z` symbols in the definition of `I₀`. The strip
bridge is differentiated through an entire function, including at the joint zero.
-/

noncomputable section

open Complex

namespace PGM

theorem cepsBrownianU_hasDerivAt {v : ℂ} (lam : ℝ) (z : ℂ) (hv : v ≠ 0)
    (hs : cepsBrownianSinhc (cepsBrownianSquare v lam z) ≠ 0) :
    HasDerivAt (fun u => cepsBrownianU v lam u)
      (-Complex.exp ((lam : ℂ) / v) * deriv cepsBrownianSinhc (cepsBrownianSquare v lam z) /
        cepsBrownianSinhc (cepsBrownianSquare v lam z) ^ 2) z := by
  have hu : HasDerivAt (fun u => cepsBrownianSquare v lam u) (2 / v) z := by
    simpa [cepsBrownianSquare] using
      ((hasDerivAt_id z).const_mul 2 |>.div_const v).const_add (((lam : ℂ) / v) ^ 2)
  have hS := (cepsBrownianSinhc_differentiable _).hasDerivAt.comp z hu
  have h := (hasDerivAt_const z (v / 2 * Complex.exp ((lam : ℂ) / v))).div hS hs
  apply h.congr_deriv
  simp only [Function.comp_apply, zero_mul, zero_sub]
  field_simp

theorem cepsBrownianR_hasDerivAt {v : ℂ} (lam : ℝ) (z : ℂ) (hv : 0 < v.re)
    (hz : z.re = 0) (hne : lam ≠ 0 ∨ z ≠ 0) (hRne : cepsBrownianR v lam z ≠ 0) :
    HasDerivAt (fun u => cepsBrownianR v lam u) (v / cepsBrownianR v lam z) z := by
  have hslit : (lam : ℂ) ^ 2 + 2 * v * z ∈ Complex.slitPlane := by
    by_cases hz0 : z = 0
    · have hlam : lam ≠ 0 := hne.resolve_right (by simp [hz0])
      left
      simpa [hz0, pow_two, mul_re] using (sq_pos_of_ne_zero hlam)
    · have hzim : z.im ≠ 0 := by intro him; exact hz0 (Complex.ext hz him)
      right
      simpa [pow_two, add_im, mul_im, hz] using
        mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hv.ne') hzim
  have hdiff : DifferentiableAt ℂ (fun u => cepsBrownianR v lam u) z :=
    (Complex.differentiableAt_sqrt hslit).comp z
      ((differentiableAt_id.const_mul (2 * v)).const_add ((lam : ℂ) ^ 2))
  have hR := hdiff.hasDerivAt
  have hsq := hR.pow 2
  have hfun : (fun u => cepsBrownianR v lam u) ^ 2 =
      fun u => (lam : ℂ) ^ 2 + 2 * v * u := by
    ext u
    simpa only [Pi.pow_apply] using cepsBrownianR_sq v lam u
  rw [hfun] at hsq
  have hlin : HasDerivAt (fun u => (lam : ℂ) ^ 2 + 2 * v * u) (2 * v) z := by
    simpa using ((hasDerivAt_id z).const_mul (2 * v)).const_add ((lam : ℂ) ^ 2)
  have he := hsq.unique hlin
  have hd : deriv (fun u => cepsBrownianR v lam u) z = v / cepsBrownianR v lam z := by
    field_simp
    norm_num at he
    linear_combination he / 2
  exact hR.congr_deriv hd

theorem cepsBrownianUInf_hasDerivAt {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hne : lam ≠ 0 ∨ z ≠ 0) :
    HasDerivAt (fun u => cepsBrownianUInf v lam u)
      (Complex.exp (-cepsBrownianXiPlus v lam z) * (v / cepsBrownianR v lam z - 1)) z := by
  obtain ⟨hvre, -, -, hvne⟩ := cepsBrownian_variance_bounds hv₀ hv
  have hvpos : 0 < v.re := by linarith
  have hRne : cepsBrownianR v lam z ≠ 0 := by
    intro heq
    have hp := cepsBrownian_quotient_re_pos hv₀ hv hz hne
    simp [heq] at hp
  have hR := cepsBrownianR_hasDerivAt lam z hvpos hz hne hRne
  have hxi : HasDerivAt (fun u => cepsBrownianXiPlus v lam u) (1 / cepsBrownianR v lam z) z := by
    have h := (hR.const_add (-(lam : ℂ))).div_const v
    apply h.congr_deriv
    field_simp
  have h := hR.mul hxi.neg.cexp
  apply h.congr_deriv
  simp only [Pi.neg_apply]
  field_simp
  ring

/-- The full kernel is exactly the differentiated Brownian expression away from
the displayed zero-frequency fractions. -/
theorem cepsBrownianKernel_blueprint {v₀ : ℝ} {v : ℂ} (lam : ℝ) {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hz0 : z ≠ 0) :
    cepsBrownianKernel v lam z = -(cepsBrownianH v lam z ^ 2) *
        deriv (fun u => cepsBrownianU v lam u) z +
      if 1 ≤ lam then (cepsBrownianXiPlus v lam z / z) ^ 2 *
        deriv (fun u => cepsBrownianUInf v lam u) z else 0 := by
  have hvne := (cepsBrownian_variance_bounds hv₀ hv).2.2.2
  have hs := cepsBrownianSinhc_ne (lam := lam) hv₀ hv hz
  rw [(cepsBrownianU_hasDerivAt lam z hvne hs).deriv]
  have hUinf := (cepsBrownianUInf_hasDerivAt (lam := lam) hv₀ hv hz (Or.inr hz0)).deriv
  unfold cepsBrownianKernel
  by_cases hlam : 1 ≤ lam
  · rw [if_pos hlam, if_pos hlam, hUinf, cepsBrownianHInf_blueprint hvne hz0 (by linarith)]
    ring
  · rw [if_neg hlam, if_neg hlam]
    ring

end PGM
