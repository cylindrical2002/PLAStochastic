import PLAStochastic.Affine.Moments.Optimal.AllOrders.ImageMellinTerms
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! # Mellin transform of the optimal image series

For `re q < -3/2`, the Mellin integral of the explicit image series `S(t) - 1`
is absolutely convergent term by term. Summing the spectral form of each
image-mode integral gives

  `q ∫₀^∞ t^(q-1) (S(t) - 1) dt = 8^q Γ(-q) / (3 (q + 1)) * 𝓑(q)`,

  `𝓑(q) = 4 (2q+1)(2q+3) [D(-q-1) - ζ(-2q-2)] + 4q(2q+1) [D(-q) - ζ(-2q)]
    + q(q-1) D(1-q)`,

where `D(s) = ∑_{m ≥ 1} (m (m + 1))^(-s)` is the quadratic Dirichlet series
and `ζ` is Mathlib's `riemannZeta`. All series are in their region of absolute
convergence.
-/
noncomputable section
open MeasureTheory Set Complex
namespace BrownianAffine

/-- The quadratic Dirichlet series `D(s) = ∑_{m ≥ 1} (m (m + 1))^(-s)`, indexed from zero. -/
def quadraticDirichletSum (s : ℂ) : ℂ :=
  ∑' m : ℕ, ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ (-s)

theorem summable_imageIndex_cpow {s : ℂ} (hs : s.re < -1) :
    Summable (fun n : ℕ => ((n : ℂ) + 1) ^ s) := by
  refine Summable.of_norm ((summable_imageIndex_rpow hs).congr fun n => ?_)
  rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
    norm_cpow_eq_rpow_re_of_pos (by positivity)]

theorem summable_quadraticDirichlet_cpow {s : ℂ} (hs : s.re < -1 / 2) :
    Summable (fun n : ℕ => ((((n + 1) * (n + 2) : ℕ) : ℂ)) ^ s) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => ((n : ℝ) + 1) ^ (2 * s.re))
    (summable_imageIndex_rpow (by linarith)) (fun n => ?_)
  rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (by positivity),
    show 2 * s.re = ((2 : ℕ) : ℝ) * s.re by norm_num,
    Real.rpow_natCast_mul (by positivity)]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  push_cast
  nlinarith

theorem riemannZeta_neg_eq_tsum_imageIndex_cpow {s : ℂ} (hs : s.re < -1) :
    riemannZeta (-s) = ∑' n : ℕ, ((n : ℂ) + 1) ^ s := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp only [neg_re]; linarith)]
  congr 1
  funext n
  rw [cpow_neg, one_div, inv_inv]

theorem quadraticDirichletSum_neg_eq_tsum (s : ℂ) :
    quadraticDirichletSum (-s) = ∑' n : ℕ, ((((n + 1) * (n + 2) : ℕ) : ℂ)) ^ s := by
  simp only [quadraticDirichletSum, neg_neg]

/-- The Mellin transform of the optimal image series in the region `re q < -3/2`. -/
theorem optimalImageSeries_mellin {q : ℂ} (hq : q.re < -3 / 2) :
    q * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (q - 1) * ((optimalImageSeries t : ℂ) - 1) =
      8 ^ q * Complex.Gamma (-q) / (3 * (q + 1)) *
        (4 * (2 * q + 1) * (2 * q + 3) *
            (quadraticDirichletSum (-q - 1) - riemannZeta (-2 * q - 2)) +
          4 * q * (2 * q + 1) * (quadraticDirichletSum (-q) - riemannZeta (-2 * q)) +
          q * (q - 1) * quadraticDirichletSum (1 - q)) := by
  have hq1 : q.re < -1 := by linarith
  have hpt : (fun t : ℝ => (t : ℂ) ^ (q - 1) * ((optimalImageSeries t : ℂ) - 1)) =
      fun t : ℝ => ∑' n : ℕ, (t : ℂ) ^ (q - 1) * ((optimalImageMode n t : ℝ) : ℂ) := by
    funext t
    rw [optimalImageSeries, ofReal_add, ofReal_one, add_sub_cancel_left, ofReal_tsum,
      tsum_mul_left]
  rw [hpt, ← integral_tsum_of_summable_integral_norm
    (F := fun (n : ℕ) (t : ℝ) => (t : ℂ) ^ (q - 1) * ((optimalImageMode n t : ℝ) : ℂ))
    (fun n => integrableOn_mellin_optimalImageMode hq1 n)
    (summable_integral_norm_mellin_optimalImageMode hq), ← tsum_mul_left]
  simp only [mul_integral_mellin_optimalImageMode hq1]
  rw [tsum_mul_left]
  congr 1
  have hz1 : Summable (fun n : ℕ => ((n : ℂ) + 1) ^ (2 * q + 2)) :=
    summable_imageIndex_cpow (by simp; linarith)
  have hz0 : Summable (fun n : ℕ => ((n : ℂ) + 1) ^ (2 * q)) :=
    summable_imageIndex_cpow (by simp; linarith)
  have hd1 : Summable (fun n : ℕ => ((((n + 1) * (n + 2) : ℕ) : ℂ)) ^ (q + 1)) :=
    summable_quadraticDirichlet_cpow (by simp; linarith)
  have hd0 : Summable (fun n : ℕ => ((((n + 1) * (n + 2) : ℕ) : ℂ)) ^ q) :=
    summable_quadraticDirichlet_cpow (by linarith)
  have hdm : Summable (fun n : ℕ => ((((n + 1) * (n + 2) : ℕ) : ℂ)) ^ (q - 1)) :=
    summable_quadraticDirichlet_cpow (by simp; linarith)
  rw [Summable.tsum_add (((hd1.sub hz1).mul_left _).add ((hd0.sub hz0).mul_left _))
      (hdm.mul_left _),
    Summable.tsum_add ((hd1.sub hz1).mul_left _) ((hd0.sub hz0).mul_left _),
    tsum_mul_left, tsum_mul_left, tsum_mul_left, Summable.tsum_sub hd1 hz1,
    Summable.tsum_sub hd0 hz0]
  rw [show -q - 1 = -(q + 1) by ring, show 1 - q = -(q - 1) by ring,
    show -2 * q - 2 = -(2 * q + 2) by ring, show -2 * q = -(2 * q) by ring,
    quadraticDirichletSum_neg_eq_tsum, quadraticDirichletSum_neg_eq_tsum,
    quadraticDirichletSum_neg_eq_tsum,
    riemannZeta_neg_eq_tsum_imageIndex_cpow (by simp; linarith),
    riemannZeta_neg_eq_tsum_imageIndex_cpow (by simp; linarith)]

end BrownianAffine
