import PLAStochastic.Index.CEPS.BrownianCoeff.Defs

/-!
# Agreement with the Brownian formulas in blueprint section 3.8

The identities here relate the analytic definitions to the displayed exponential
fractions. The fractions are used only where their denominators are nonzero.
-/

noncomputable section

open Complex

namespace PGM

private theorem brownian_numerator (a s : ℂ) :
    (s - a) - (-a - s) * Complex.exp (-2 * s) - 2 * s * Complex.exp (-a - s) =
      2 * Complex.exp (-s) * (s * Complex.cosh s - a * Complex.sinh s - s * Complex.exp (-a)) := by
  have he2 : Complex.exp (-2 * s) = Complex.exp (-s) ^ 2 := by
    rw [show -2 * s = -s + -s by ring, Complex.exp_add, pow_two]
  have hea : Complex.exp (-a - s) = Complex.exp (-a) * Complex.exp (-s) := by
    rw [sub_eq_add_neg, Complex.exp_add]
  have hc : 2 * Complex.exp (-s) * Complex.cosh s = 1 + Complex.exp (-s) ^ 2 := by
    calc
      2 * Complex.exp (-s) * Complex.cosh s = Complex.exp (-s) * (2 * Complex.cosh s) := by ring
      _ = Complex.exp (-s) * (Complex.exp s + Complex.exp (-s)) := by rw [Complex.two_cosh]
      _ = _ := by rw [mul_add, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]; ring
  have hs : 2 * Complex.exp (-s) * Complex.sinh s = 1 - Complex.exp (-s) ^ 2 := by
    calc
      2 * Complex.exp (-s) * Complex.sinh s = Complex.exp (-s) * (2 * Complex.sinh s) := by ring
      _ = Complex.exp (-s) * (Complex.exp s - Complex.exp (-s)) := by rw [Complex.two_sinh]
      _ = _ := by rw [mul_sub, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]; ring
  rw [he2, hea]
  linear_combination -s * hc + a * hs

theorem cepsBrownianH_blueprint {v₀ : ℝ} {v : ℂ} (lam : ℝ) {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hz0 : z ≠ 0) :
    cepsBrownianH v lam z =
      (cepsBrownianXiPlus v lam z - cepsBrownianXiMinus v lam z *
          Complex.exp (-2 * cepsBrownianR v lam z / v) -
        (cepsBrownianXiPlus v lam z - cepsBrownianXiMinus v lam z) *
          Complex.exp (cepsBrownianXiMinus v lam z)) / (z * cepsBrownianDelta v lam z) := by
  have hvne := (cepsBrownian_variance_bounds hv₀ hv).2.2.2
  have hS := cepsBrownianSinhc_ne (lam := lam) hv₀ hv hz
  have hDelta := cepsBrownianDelta_ne_zero (lam := lam) hv₀ hv hz (Or.inr hz0)
  set a := (lam : ℂ) / v
  set s := cepsBrownianR v lam z / v
  set u := cepsBrownianSquare v lam z
  have hs : s ^ 2 = u := cepsBrownian_normalized_sq hvne lam z
  have hC : cepsBrownianCosh u = Complex.cosh s := by rw [← hs, cepsBrownianCosh_sq]
  have hS' : s * cepsBrownianSinhc u = Complex.sinh s := by rw [← hs, cepsBrownianSinhc_mul]
  have hxp : cepsBrownianXiPlus v lam z = s - a := by unfold cepsBrownianXiPlus; dsimp [s, a]; ring
  have hxm : cepsBrownianXiMinus v lam z = -a - s := by unfold cepsBrownianXiMinus; dsimp [s, a]; ring
  have hsne : s ≠ 0 := by
    intro heq
    have hp := cepsBrownian_quotient_re_pos (lam := lam) hv₀ hv hz (Or.inr hz0)
    change 0 < s.re at hp
    simp [heq] at hp
  have hDeltaEq : cepsBrownianDelta v lam z = 2 * Complex.exp (-s) * s * cepsBrownianSinhc u :=
    cepsBrownianDelta_eq_sinhc hvne lam z
  rw [cepsBrownianH_eq hvne lam hz0, hxp, hxm,
    show -2 * cepsBrownianR v lam z / v = -2 * s by dsimp [s]; ring,
    show s - a - (-a - s) = 2 * s by ring, brownian_numerator]
  rw [← hC, ← hS', hDeltaEq]
  rw [neg_div]
  change (cepsBrownianCosh u - a * cepsBrownianSinhc u - Complex.exp (-a)) / z /
      cepsBrownianSinhc u = _
  field_simp

theorem cepsBrownianU_blueprint {v₀ : ℝ} {v : ℂ} (lam : ℝ) {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hne : lam ≠ 0 ∨ z ≠ 0) :
    cepsBrownianU v lam z = cepsBrownianR v lam z *
      Complex.exp (-cepsBrownianXiPlus v lam z) / cepsBrownianDelta v lam z := by
  have hvne := (cepsBrownian_variance_bounds hv₀ hv).2.2.2
  have hS := cepsBrownianSinhc_ne (lam := lam) hv₀ hv hz
  set a := (lam : ℂ) / v
  set s := cepsBrownianR v lam z / v
  set u := cepsBrownianSquare v lam z
  have hsne : s ≠ 0 := by
    intro heq
    have hp := cepsBrownian_quotient_re_pos hv₀ hv hz hne
    change 0 < s.re at hp
    simp [heq] at hp
  have hR : cepsBrownianR v lam z = v * s := by dsimp [s]; field_simp
  have hxi : -cepsBrownianXiPlus v lam z = a - s := by unfold cepsBrownianXiPlus; dsimp [a, s]; ring
  rw [cepsBrownianU, hxi, show a - s = a + -s by ring, Complex.exp_add,
    cepsBrownianDelta_eq_sinhc hvne lam z, hR]
  simp only [mul_div_cancel_left₀ _ hvne]
  change v / 2 * Complex.exp a / cepsBrownianSinhc u =
    v * s * (Complex.exp a * Complex.exp (-s)) /
      (2 * Complex.exp (-s) * s * cepsBrownianSinhc u)
  field_simp

theorem cepsBrownianHInf_blueprint {v : ℂ} {z : ℂ} {lam : ℝ}
    (hv : v ≠ 0) (hz : z ≠ 0) (hlam : 0 < lam) :
    cepsBrownianHInf v lam z = cepsBrownianXiPlus v lam z / z := by
  have hden : (lam : ℂ) + cepsBrownianR v lam z ≠ 0 := by
    intro heq
    have := congrArg Complex.re heq
    simp only [add_re, ofReal_re, zero_re] at this
    linarith [cepsBrownianR_re_nonneg v lam z]
  have hs := cepsBrownianR_sq v lam z
  unfold cepsBrownianHInf cepsBrownianXiPlus
  field_simp
  linear_combination -hs

end PGM
