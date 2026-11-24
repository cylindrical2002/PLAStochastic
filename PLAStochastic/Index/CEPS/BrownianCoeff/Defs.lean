import PLAStochastic.Index.CEPS.BrownianCoeff.Root
import PLAStochastic.Index.CEPS.BrownianCoeff.Entire

/-!
# Analytic definitions of the Brownian strip coefficients

The squared normalized root is used inside entire functions. Divided differences
remove the zero in the displayed formula for the entrance coefficient at `z = 0`.
-/

noncomputable section

open Complex Filter Topology

namespace PGM

def cepsBrownianSquare (v : ℂ) (lam : ℝ) (z : ℂ) : ℂ :=
  ((lam : ℂ) / v) ^ 2 + 2 * z / v

/-- The analytically extended Brownian entrance coefficient `Hᴮ`. -/
def cepsBrownianH (v : ℂ) (lam : ℝ) (z : ℂ) : ℂ :=
  2 / v * (dslope cepsBrownianCosh (((lam : ℂ) / v) ^ 2) (cepsBrownianSquare v lam z) -
    ((lam : ℂ) / v) * dslope cepsBrownianSinhc (((lam : ℂ) / v) ^ 2)
      (cepsBrownianSquare v lam z)) / cepsBrownianSinhc (cepsBrownianSquare v lam z)

/-- The analytically extended Brownian bridge coefficient `Ûᴮ`. -/
def cepsBrownianU (v : ℂ) (lam : ℝ) (z : ℂ) : ℂ :=
  v / 2 * Complex.exp ((lam : ℂ) / v) / cepsBrownianSinhc (cepsBrownianSquare v lam z)

/-- The half-line entrance, rationalized where `lam ≥ 1`. -/
def cepsBrownianHInf (v : ℂ) (lam : ℝ) (z : ℂ) : ℂ :=
  2 / ((lam : ℂ) + cepsBrownianR v lam z)

/-- The full-line Brownian bridge. -/
def cepsBrownianUInf (v : ℂ) (lam : ℝ) (z : ℂ) : ℂ :=
  cepsBrownianR v lam z * Complex.exp (-cepsBrownianXiPlus v lam z)

/-- The Brownian kernel coefficient `I₀`, including its analytic values at zero. -/
def cepsBrownianKernel (v : ℂ) (lam : ℝ) (z : ℂ) : ℂ :=
  cepsBrownianH v lam z ^ 2 * Complex.exp ((lam : ℂ) / v) *
      deriv cepsBrownianSinhc (cepsBrownianSquare v lam z) /
        cepsBrownianSinhc (cepsBrownianSquare v lam z) ^ 2 +
    if 1 ≤ lam then cepsBrownianHInf v lam z ^ 2 *
      Complex.exp (-cepsBrownianXiPlus v lam z) * (v / cepsBrownianR v lam z - 1) else 0

theorem cepsBrownian_normalized_sq {v : ℂ} (hv : v ≠ 0) (lam : ℝ) (z : ℂ) :
    (cepsBrownianR v lam z / v) ^ 2 = cepsBrownianSquare v lam z := by
  rw [div_pow, cepsBrownianR_sq]
  unfold cepsBrownianSquare
  field_simp

theorem cepsBrownianDelta_eq_sinhc {v : ℂ} (hv : v ≠ 0) (lam : ℝ) (z : ℂ) :
    cepsBrownianDelta v lam z = 2 * Complex.exp (-(cepsBrownianR v lam z / v)) *
      (cepsBrownianR v lam z / v) * cepsBrownianSinhc (cepsBrownianSquare v lam z) := by
  set s := cepsBrownianR v lam z / v
  have hs : s ^ 2 = cepsBrownianSquare v lam z := cepsBrownian_normalized_sq hv lam z
  rw [← hs, show 2 * Complex.exp (-s) * s * cepsBrownianSinhc (s ^ 2) =
    2 * Complex.exp (-s) * (s * cepsBrownianSinhc (s ^ 2)) by ring,
    cepsBrownianSinhc_mul]
  have he : 2 * Complex.exp (-s) * Complex.sinh s = 1 - Complex.exp (-2 * s) := by
    calc
      2 * Complex.exp (-s) * Complex.sinh s =
          Complex.exp (-s) * (Complex.exp s - Complex.exp (-s)) := by
        rw [← Complex.two_sinh]
        ring
      _ = 1 - Complex.exp (-2 * s) := by
        rw [mul_sub, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, ← Complex.exp_add]
        congr 2
        ring
  rw [he]
  unfold cepsBrownianDelta
  congr 2
  dsimp [s]
  ring

theorem cepsBrownianSinhc_ne {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ} (hv₀ : 0 < v₀)
    (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hz : z.re = 0) :
    cepsBrownianSinhc (cepsBrownianSquare v lam z) ≠ 0 := by
  by_cases hne : lam ≠ 0 ∨ z ≠ 0
  · have hDelta := cepsBrownianDelta_ne_zero hv₀ hv hz hne
    have hvne := (cepsBrownian_variance_bounds hv₀ hv).2.2.2
    rw [cepsBrownianDelta_eq_sinhc hvne] at hDelta
    exact fun h => hDelta (by rw [h, mul_zero])
  · push Not at hne
    simp [cepsBrownianSquare, hne.1, hne.2]

/-- The usual entrance formula in entire functions, away from its displayed zero. -/
theorem cepsBrownianH_eq {v : ℂ} (hv : v ≠ 0) (lam : ℝ) {z : ℂ} (hz : z ≠ 0) :
    cepsBrownianH v lam z =
      (cepsBrownianCosh (cepsBrownianSquare v lam z) - (lam : ℂ) / v *
          cepsBrownianSinhc (cepsBrownianSquare v lam z) - Complex.exp (-(lam : ℂ) / v)) /
        z / cepsBrownianSinhc (cepsBrownianSquare v lam z) := by
  set a := (lam : ℂ) / v
  set u := cepsBrownianSquare v lam z
  have hdiff : u - a ^ 2 = 2 * z / v := by dsimp [u, a, cepsBrownianSquare]; ring
  have hne : u ≠ a ^ 2 := by
    apply sub_ne_zero.mp
    rw [hdiff]
    exact div_ne_zero (mul_ne_zero (by norm_num) hz) hv
  have hc := cepsBrownianCosh_sub_mul_sinhc a
  unfold cepsBrownianH
  change (2 / v * (dslope cepsBrownianCosh (a ^ 2) u -
    a * dslope cepsBrownianSinhc (a ^ 2) u)) / cepsBrownianSinhc u = _
  rw [dslope_of_ne _ hne, dslope_of_ne _ hne, slope_def_field, slope_def_field, hdiff]
  congr 1
  change 2 / v * ((cepsBrownianCosh u - cepsBrownianCosh (a ^ 2)) / (2 * z / v) -
    a * ((cepsBrownianSinhc u - cepsBrownianSinhc (a ^ 2)) / (2 * z / v))) = _
  rw [show -(lam : ℂ) / v = -a by dsimp [a]; ring, ← hc]
  field_simp
  ring

end PGM
