import PLAStochastic.Index.CEPS.BrownianCoeff.BridgeBounds
import PLAStochastic.Index.CEPS.BrownianCoeff.PositiveRoot

/-!
# Frequency-derivative cancellation of the strip and full-line bridges

The formula is proved using actual derivatives and is valid at zero frequency.
-/

noncomputable section

open Complex Filter Topology

namespace PGM

private theorem brownianU_eq_full_line {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv : v ≠ 0) (hR : cepsBrownianR v lam z ≠ 0)
    (hS : cepsBrownianSinhc (cepsBrownianSquare v lam z) ≠ 0) :
    cepsBrownianU v lam z = cepsBrownianUInf v lam z / cepsBrownianDelta v lam z := by
  set a := (lam : ℂ) / v
  set s := cepsBrownianR v lam z / v
  have hs : s ≠ 0 := div_ne_zero hR hv
  have hR' : cepsBrownianR v lam z = v * s := by dsimp [s]; field_simp
  have hxi : -cepsBrownianXiPlus v lam z = a - s := by
    dsimp [cepsBrownianXiPlus, a, s]
    ring
  rw [cepsBrownianU, cepsBrownianUInf, hxi, show a - s = a + -s by ring,
    Complex.exp_add, cepsBrownianDelta_eq_sinhc hv lam z, hR']
  simp only [mul_div_cancel_left₀ _ hv]
  change v / 2 * Complex.exp a / cepsBrownianSinhc (cepsBrownianSquare v lam z) =
    v * s * (Complex.exp a * Complex.exp (-s)) /
      (2 * Complex.exp (-s) * s * cepsBrownianSinhc (cepsBrownianSquare v lam z))
  field_simp

theorem cepsBrownianU_deriv_sub_UInf_deriv {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hlam : 0 < lam) :
    deriv (fun u => cepsBrownianU v lam u) z - deriv (fun u => cepsBrownianUInf v lam u) z =
      Complex.exp (-cepsBrownianXiPlus v lam z) *
        Complex.exp (-2 * cepsBrownianR v lam z / v) *
          ((v / cepsBrownianR v lam z - 1) / cepsBrownianDelta v lam z -
            2 / cepsBrownianDelta v lam z ^ 2) := by
  obtain ⟨hvre, -, -, hvne⟩ := cepsBrownian_variance_bounds hv₀ hv
  have hvpos : 0 < v.re := by linarith
  have hRne : cepsBrownianR v lam z ≠ 0 := by
    exact ne_of_apply_ne Complex.re (ne_of_gt (cepsBrownianR_re_pos hvpos hlam hz))
  have hS := cepsBrownianSinhc_ne (lam := lam) hv₀ hv hz
  have hDelta := cepsBrownianDelta_ne_zero hv₀ hv hz (Or.inl hlam.ne')
  have hR := cepsBrownianR_hasDerivAt lam z hvpos hz (Or.inl hlam.ne') hRne
  have hE : HasDerivAt (fun u => Complex.exp (-2 * cepsBrownianR v lam u / v))
      (-2 / cepsBrownianR v lam z * Complex.exp (-2 * cepsBrownianR v lam z / v)) z := by
    have h := ((hR.const_mul (-2)).div_const v).cexp
    apply h.congr_deriv
    field_simp
  have hD : HasDerivAt (fun u => cepsBrownianDelta v lam u)
      (2 / cepsBrownianR v lam z * Complex.exp (-2 * cepsBrownianR v lam z / v)) z := by
    exact (hE.const_sub 1).congr_deriv (by ring)
  have hInf := cepsBrownianUInf_hasDerivAt hv₀ hv hz (Or.inl hlam.ne')
  have hU := hInf.div hD hDelta
  have heq : (fun u => cepsBrownianU v lam u) =ᶠ[𝓝 z]
      fun u => cepsBrownianUInf v lam u / cepsBrownianDelta v lam u := by
    have hScont : ContinuousAt (fun u => cepsBrownianSinhc (cepsBrownianSquare v lam u)) z := by
      have h := cepsBrownianSinhc_differentiable.continuous
      have hsq : Continuous (fun u : ℂ => cepsBrownianSquare v lam u) := by
        unfold cepsBrownianSquare
        fun_prop
      exact h.continuousAt.comp hsq.continuousAt
    filter_upwards [hR.continuousAt.eventually_ne hRne, hScont.eventually_ne hS] with u huR huS
    exact brownianU_eq_full_line hvne huR huS
  have hU' := hU.congr_of_eventuallyEq heq
  rw [hU'.deriv, hInf.deriv]
  unfold cepsBrownianUInf
  have hDe : cepsBrownianDelta v lam z = 1 - Complex.exp (-2 * cepsBrownianR v lam z / v) := rfl
  field_simp
  rw [hDe]
  ring_nf

end PGM
