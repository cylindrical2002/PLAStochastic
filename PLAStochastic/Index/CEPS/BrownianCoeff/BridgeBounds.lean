import PLAStochastic.Index.CEPS.BrownianCoeff.Deriv
import PLAStochastic.Index.CEPS.BrownianCoeff.SinhcInverse
import PLAStochastic.Index.CEPS.BrownianCoeff.Sector

/-!
# Brownian bridge derivative and polynomial budgets
-/

noncomputable section

open Complex

namespace PGM

def cepsBrownianBridgeDerivConst : ℝ := 2 * Real.exp 1 * cepsBrownianSinhcConst ^ 2

theorem cepsBrownianSinhc_ratio {s : ℂ} (hs : ‖s‖ ≤ 3 * s.re) :
    ‖deriv cepsBrownianSinhc (s ^ 2) / cepsBrownianSinhc (s ^ 2) ^ 2‖ ≤
      cepsBrownianBridgeDerivConst * (1 + ‖s‖) ^ 2 * Real.exp (-s.re) := by
  have hsre : 0 ≤ s.re := by linarith [norm_nonneg s]
  have hD := cepsBrownianSinhc_deriv_norm s
  rw [abs_of_nonneg hsre] at hD
  have hI := cepsBrownianSinhc_inverse hs
  have hC : 0 ≤ cepsBrownianSinhcConst := by linarith [cepsBrownianSinhcConst_bounds.1]
  rw [norm_div, norm_pow, div_eq_mul_inv, ← inv_pow]
  calc
    ‖deriv cepsBrownianSinhc (s ^ 2)‖ * ‖cepsBrownianSinhc (s ^ 2)‖⁻¹ ^ 2 ≤
        (2 * Real.exp (s.re + 1)) *
          (cepsBrownianSinhcConst * (1 + ‖s‖) * Real.exp (-s.re)) ^ 2 := by gcongr
    _ = cepsBrownianBridgeDerivConst * (1 + ‖s‖) ^ 2 * Real.exp (-s.re) := by
      unfold cepsBrownianBridgeDerivConst
      rw [Real.exp_add]
      have he : Real.exp s.re * Real.exp (-s.re) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      calc
        _ = 2 * Real.exp 1 * cepsBrownianSinhcConst ^ 2 * (1 + ‖s‖) ^ 2 *
          Real.exp (-s.re) * (Real.exp s.re * Real.exp (-s.re)) := by ring
        _ = _ := by rw [he, mul_one]

theorem cepsBrownianU_deriv_norm {v₀ : ℝ} {v : ℂ} (lam : ℝ) (z : ℂ) (hv₀ : 0 < v₀)
    (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hz : z.re = 0) :
    ‖deriv (fun u => cepsBrownianU v lam u) z‖ ≤ cepsBrownianBridgeDerivConst *
      (1 + ‖cepsBrownianR v lam z / v‖) ^ 2 *
        Real.exp (((lam : ℂ) / v).re - (cepsBrownianR v lam z / v).re) := by
  set a := (lam : ℂ) / v
  set s := cepsBrownianR v lam z / v
  have hvne := (cepsBrownian_variance_bounds hv₀ hv).2.2.2
  have hS := cepsBrownianSinhc_ne (lam := lam) hv₀ hv hz
  have hderiv := (cepsBrownianU_hasDerivAt lam z hvne hS).deriv
  rw [hderiv, ← cepsBrownian_normalized_sq hvne]
  change ‖-Complex.exp a * deriv cepsBrownianSinhc (s ^ 2) / cepsBrownianSinhc (s ^ 2) ^ 2‖ ≤ _
  rw [show -Complex.exp a * deriv cepsBrownianSinhc (s ^ 2) / cepsBrownianSinhc (s ^ 2) ^ 2 =
    -Complex.exp a * (deriv cepsBrownianSinhc (s ^ 2) / cepsBrownianSinhc (s ^ 2) ^ 2) by ring,
    norm_mul, norm_neg, Complex.norm_exp]
  have hratio := cepsBrownianSinhc_ratio (cepsBrownian_quotient_sector (lam := lam) hv₀ hv hz)
  calc
    Real.exp a.re * ‖deriv cepsBrownianSinhc (s ^ 2) / cepsBrownianSinhc (s ^ 2) ^ 2‖ ≤
        Real.exp a.re * (cepsBrownianBridgeDerivConst * (1 + ‖s‖) ^ 2 * Real.exp (-s.re)) := by gcongr
    _ = cepsBrownianBridgeDerivConst * (1 + ‖s‖) ^ 2 * Real.exp (a.re - s.re) := by
      rw [Real.exp_sub, Real.exp_neg]
      ring

def cepsBrownianRootBudget (v₀ : ℝ) : ℝ := 1 + 2 / v₀ + 4 * Real.sqrt v₀ / v₀

theorem cepsBrownianRootBudget_pos {v₀ : ℝ} (hv₀ : 0 < v₀) : 0 < cepsBrownianRootBudget v₀ := by
  unfold cepsBrownianRootBudget
  positivity

theorem cepsBrownian_root_polynomial {v₀ : ℝ} {v : ℂ} (lam : ℝ) (z : ℂ) (hv₀ : 0 < v₀)
    (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) :
    1 + ‖cepsBrownianR v lam z / v‖ ≤ cepsBrownianRootBudget v₀ * (1 + |lam| + ‖z‖) := by
  have hvnorm := (cepsBrownian_variance_bounds hv₀ hv).2.1
  have hR := cepsBrownianR_norm_le hv₀ hv lam z
  have hsqrt : Real.sqrt ‖z‖ ≤ 1 + ‖z‖ := by
    nlinarith [Real.sq_sqrt (norm_nonneg z), Real.sqrt_nonneg ‖z‖, norm_nonneg z,
      sq_nonneg (Real.sqrt ‖z‖ - 1)]
  have hn : ‖cepsBrownianR v lam z / v‖ ≤ 2 / v₀ * |lam| +
      (4 * Real.sqrt v₀ / v₀) * (1 + ‖z‖) := by
    rw [norm_div]
    calc
      ‖cepsBrownianR v lam z‖ / ‖v‖ ≤ (|lam| + 2 * Real.sqrt v₀ * Real.sqrt ‖z‖) / (v₀ / 2) := by gcongr
      _ ≤ (|lam| + 2 * Real.sqrt v₀ * (1 + ‖z‖)) / (v₀ / 2) := by gcongr
      _ = _ := by field_simp; ring
  unfold cepsBrownianRootBudget
  have ha : 0 ≤ 2 / v₀ := by positivity
  have hb : 0 ≤ 4 * Real.sqrt v₀ / v₀ := by positivity
  nlinarith [abs_nonneg lam, norm_nonneg z]

end PGM
