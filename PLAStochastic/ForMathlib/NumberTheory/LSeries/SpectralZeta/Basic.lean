import PLAStochastic.ForMathlib.NumberTheory.LSeries.SpectralZeta.HurwitzSeries
import PLAStochastic.ForMathlib.NumberTheory.LSeries.SpectralZeta.Binomial

/-! # The quadratic spectral zeta function

The quadratic spectral zeta function is

`D(s) = ∑_{m ≥ 1} (m(m+1))^{-s}`,   `re s > 1/2`.

Centering at `u = m + 1/2` gives `m(m+1) = u^2 (1 - 1/(4u^2))`, and the binomial series yields
the continuation (T4)

`D(s) = ∑_{r ≥ 0} (s)_r / (4^r r!) ζ(2s + 2r, 3/2)`,

which we take as the definition of `spectralZeta` on all of `ℂ`. On every ball, the tail
terms are bounded by `C (8/9)^r` (`HurwitzSeries`), which gives convergence everywhere and
holomorphy away from the poles of the finitely many head terms.

* `spectralZeta_eq_tsum`: the Dirichlet series in `re s > 1/2`.
* `differentiableAt_spectralZeta`: holomorphy away from `1/2, -1/2, -3/2, …`.
-/

noncomputable section

open Complex Polynomial

namespace BrownianAffine

/-- The quadratic spectral zeta function `D(s) = ∑_{m ≥ 1} (m(m+1))^{-s}`, defined on all of `ℂ`
by its Hurwitz expansion `D(s) = ∑_{r ≥ 0} (s)_r / (4^r r!) ζ(2s + 2r, 3/2)`. -/
def spectralZeta (s : ℂ) : ℂ :=
  ∑' r : ℕ, (ascPochhammer ℂ r).eval s / (4 ^ r * r.factorial) *
    SpectralZeta.hurwitzZetaThreeHalves (2 * s + 2 * r)

namespace SpectralZeta

/-- The coefficient `(s)_r / (4^r r!)` of the Hurwitz expansion. -/
def spectralCoeff (r : ℕ) (s : ℂ) : ℂ := pochCoeff s r / 4 ^ r

theorem spectralZeta_eq_hzSeries : spectralZeta = hzSeries spectralCoeff 0 := by
  funext s
  unfold spectralZeta hzSeries spectralCoeff pochCoeff
  congr 1
  funext r
  rw [add_zero, div_div, mul_comm ((r.factorial : ℂ))]

theorem norm_spectralCoeff_le {s : ℂ} {R : ℝ} (hs : ‖s‖ ≤ R) (r : ℕ) :
    ‖spectralCoeff r s‖ ≤ 2 ^ R * 2 ^ r := by
  rw [spectralCoeff, norm_div, norm_pow, Complex.norm_ofNat]
  calc ‖pochCoeff s r‖ / 4 ^ r ≤ ‖pochCoeff s r‖ :=
        div_le_self (norm_nonneg _) (one_le_pow₀ (by norm_num))
    _ ≤ _ := norm_pochCoeff_le_of_norm_le hs r

theorem geomBounded_spectralCoeff : GeomBounded spectralCoeff :=
  fun R => ⟨2 ^ R, fun k _ hz => norm_spectralCoeff_le hz k⟩

theorem differentiable_spectralCoeff (r : ℕ) : Differentiable ℂ (spectralCoeff r) :=
  show Differentiable ℂ (fun s => pochCoeff s r / 4 ^ r) from
    (differentiable_pochCoeff r).div_const _

/-- `u^{-(w + 2k)} = u^{-w} / u^{2k}` for `u > 0`. -/
theorem ofReal_cpow_neg_add_two_mul {u : ℝ} (hu : 0 < u) (w : ℂ) (k : ℕ) :
    (u : ℂ) ^ (-(w + 2 * k)) = (u : ℂ) ^ (-w) / (u : ℂ) ^ (2 * k) := by
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.2 hu.ne'
  rw [neg_add, cpow_add _ _ hu0, cpow_neg (u : ℂ) (2 * (k : ℂ)),
    show (2 * (k : ℂ)) = ((2 * k : ℕ) : ℂ) by push_cast; ring, cpow_natCast, div_eq_mul_inv]

/-- `u^{-2w} = u^{-w} u^{-w}` for `u > 0`. -/
theorem ofReal_cpow_neg_two_mul {u : ℝ} (hu : 0 < u) (w : ℂ) :
    (u : ℂ) ^ (-(2 * w)) = (u : ℂ) ^ (-w) * (u : ℂ) ^ (-w) := by
  rw [← cpow_add _ _ (ofReal_ne_zero.2 hu.ne')]
  ring_nf

/-- The binomial expansion of one Dirichlet term around `u = m + 3/2`. -/
theorem natCast_mul_cpow_neg_eq_tsum (s : ℂ) (m : ℕ) :
    ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ (-s) =
      ∑' k : ℕ, spectralCoeff k s * ((m : ℂ) + 3 / 2) ^ (-(2 * s + 0 + 2 * k)) := by
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = m + 3 / 2 := ⟨_, rfl⟩
  have hu : 0 < u := by rw [hu_def]; positivity
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.2 hu.ne'
  obtain ⟨y, hy_def⟩ : ∃ y : ℝ, y = 1 / (4 * u ^ 2) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy_def]; positivity
  have hy1 : y < 1 := by
    rw [hy_def, div_lt_one (by positivity)]
    have : (3 / 2 : ℝ) ≤ u := by rw [hu_def]; linarith [m.cast_nonneg (α := ℝ)]
    nlinarith
  have hfacR : (((m + 1) * (m + 2) : ℕ) : ℝ) = (u * u) * (1 - y) := by
    rw [hy_def]
    field_simp
    rw [hu_def]
    push_cast
    ring
  have hfac : ((((m + 1) * (m + 2) : ℕ) : ℂ)) = ((u * u : ℝ) : ℂ) * ((1 - y : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← hfacR, Complex.ofReal_natCast]
  have hmu : ((m : ℂ) + 3 / 2) = (u : ℂ) := by rw [hu_def]; push_cast; ring
  rw [hfac, mul_cpow_ofReal_nonneg (by positivity) (by linarith), Complex.ofReal_mul,
    mul_cpow_ofReal_nonneg hu.le hu.le]
  have hbin := hasSum_pochCoeff_mul_pow s (y := (y : ℂ))
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0]; exact hy1)
  rw [show ((1 - y : ℝ) : ℂ) = 1 - (y : ℂ) by push_cast; ring, ← hbin.tsum_eq, ← tsum_mul_left]
  congr 1
  funext k
  rw [hmu, add_zero, ofReal_cpow_neg_add_two_mul hu (2 * s) k, spectralCoeff,
    ofReal_cpow_neg_two_mul hu s, hy_def]
  push_cast
  rw [div_pow, one_pow, mul_pow, ← pow_mul]
  field_simp

end SpectralZeta

open SpectralZeta

/-- The Dirichlet series of the spectral zeta function, as a `HasSum`. -/
theorem hasSum_spectralZeta {s : ℂ} (hs : 1 / 2 < s.re) :
    HasSum (fun m : ℕ => ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ (-s)) (spectralZeta s) := by
  rw [spectralZeta_eq_hzSeries]
  have h := hasSum_hzSeries (a := spectralCoeff) (b := 0) (z := s) (C := 2 ^ ‖s‖)
    (by simp; linarith) (fun k => norm_spectralCoeff_le le_rfl k)
  convert h using 1
  funext m
  exact natCast_mul_cpow_neg_eq_tsum s m

/-- **Dirichlet series.** For `re s > 1/2`, `D(s) = ∑_{m ≥ 1} (m(m+1))^{-s}`. -/
theorem spectralZeta_eq_tsum {s : ℂ} (hs : 1 / 2 < s.re) :
    spectralZeta s = ∑' m : ℕ, ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ (-s) :=
  (hasSum_spectralZeta hs).tsum_eq.symm

/-- **Holomorphy.** `D` is holomorphic away from the half-integers `1/2 - r`, `r ∈ ℕ`. -/
theorem differentiableAt_spectralZeta {s : ℂ} (hs : ∀ r : ℕ, s ≠ 1 / 2 - r) :
    DifferentiableAt ℂ spectralZeta s := by
  rw [spectralZeta_eq_hzSeries]
  refine differentiableAt_hzSeries differentiable_spectralCoeff geomBounded_spectralCoeff 0
    fun k hk => hs k ?_
  linear_combination hk / 2

end BrownianAffine
