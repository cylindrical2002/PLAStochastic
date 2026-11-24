import PLAStochastic.Affine.Moments.Optimal.AllOrders.BracketLimit
import PLAStochastic.Affine.Moments.Optimal.AllOrders.ComplexMoment
import PLAStochastic.Affine.Moments.Optimal.AllOrders.ImageMellin
import PLAStochastic.Affine.Moments.Optimal.AllOrders.Recurrence
import PLAStochastic.ForMathlib.NumberTheory.LSeries.SpectralZeta.NegNat

/-!
# Every positive integer moment of the optimal Brownian lifetime

The complex moment `q ↦ E τ^q` of the actual optimal lifetime is entire. On `Re q < -3/2`
the Mellin transform of the proved survival image series gives
`E τ^q = 8^q Γ(-q) / (3(q+1)) · 𝓑(q)`, with the quadratic spectral zeta `D` and the
Riemann zeta function. Continuing this identity and taking the limit at a positive integer,
where the pole of `Γ(-q)` meets the zero of `𝓑`, expresses every integer moment through
`D'(-N)` and `ζ'(-2k)`. With the finite forms of these derivatives this is the readout of
the coefficient recurrence: for `q ≥ 2` the moment equals `optimalMomentReadout q`, and for
`q = 1` the boundary value `D(0) = -1` gives `40 ζ(3)/π² - 4/3`.
-/

open MeasureTheory ProbabilityTheory Complex Set
open scoped NNReal Real

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The Mellin identity (T5) with the continued quadratic spectral zeta. -/
theorem optimalComplexMoment_eq_mellinBracket (hB : IsBrownianReal B μ) {q : ℂ}
    (hq : q.re < -3 / 2) :
    optimalComplexMoment B μ q = mellinPrefactor q * Gamma (-q) * mellinBracket spectralZeta q := by
  rw [optimalComplexMoment_eq_mellin_imageSeries hB (by linarith), optimalImageSeries_mellin hq]
  have h1 : quadraticDirichletSum (-q - 1) = spectralZeta (-q - 1) :=
    (spectralZeta_eq_tsum (by simp; linarith)).symm
  have h2 : quadraticDirichletSum (-q) = spectralZeta (-q) :=
    (spectralZeta_eq_tsum (by simp; linarith)).symm
  have h3 : quadraticDirichletSum (1 - q) = spectralZeta (1 - q) :=
    (spectralZeta_eq_tsum (by simp; linarith)).symm
  rw [h1, h2, h3]
  unfold mellinPrefactor mellinBracket
  ring

/-- The complex moment at a positive integer, from the continued Mellin identity. -/
theorem optimalComplexMoment_natCast_eq_bracket (hB : IsBrownianReal B μ) {n : ℕ} (hn : 1 ≤ n) :
    optimalComplexMoment B μ n = (8 : ℂ) ^ n * (-1) ^ (n + 1) / (3 * (n + 1) * n.factorial) *
      (4 * (2 * n + 1) * (2 * n + 3) *
          (-deriv spectralZeta (-((n + 1 : ℕ) : ℂ)) + 2 * deriv riemannZeta (-2 * n - 2)) +
        4 * n * (2 * n + 1) * (-deriv spectralZeta (-(n : ℂ)) + 2 * deriv riemannZeta (-2 * n)) +
        (2 * n - 1) * spectralZeta (1 - n) - n * (n - 1) * deriv spectralZeta (1 - n)) :=
  eq_at_nat_of_mellin (fun _ hs => differentiableAt_spectralZeta hs) spectralZeta_neg_nat
    (differentiable_optimalComplexMoment hB) (fun _ hq => optimalComplexMoment_eq_mellinBracket hB hq) hn

theorem deriv_spectralZeta_eq_optimalZetaDerivSum (N : ℕ) :
    deriv spectralZeta (-(N : ℂ)) = optimalZetaDerivSum N := by
  rw [deriv_spectralZeta_neg_nat]
  rfl

/-- Every integer moment of order at least two is the coefficient-recurrence readout (O7). -/
theorem optimalUnitLifetime_moment_eq_readout (hB : IsBrownianReal B μ) {q : ℕ} (hq : 2 ≤ q) :
    (∫ ω, optimalUnitLifetime B ω ^ q ∂μ) = optimalMomentReadout q := by
  have h := optimalComplexMoment_natCast_eq_bracket hB (by omega : 1 ≤ q)
  rw [optimalComplexMoment_natCast] at h
  have e3 : (1 : ℂ) - q = -((q - 1 : ℕ) : ℂ) := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [e3, spectralZeta_neg_nat, if_neg (by omega), deriv_spectralZeta_eq_optimalZetaDerivSum,
    deriv_spectralZeta_eq_optimalZetaDerivSum, deriv_spectralZeta_eq_optimalZetaDerivSum] at h
  apply Complex.ofReal_injective
  rw [h, ← optimalMomentReadout_eq_zetaDeriv hq]
  ring

/-- The mean from the same identity: the boundary value `D(0) = -1` gives `-4/3`. -/
theorem optimalUnitLifetime_mean_eq_boundary_readout (hB : IsBrownianReal B μ) :
    (∫ ω, optimalUnitLifetime B ω ∂μ) = 40 * (riemannZeta 3).re / π ^ 2 - 4 / 3 := by
  have h := optimalComplexMoment_natCast_eq_bracket hB (le_refl 1)
  rw [optimalComplexMoment_natCast] at h
  have e0 : (1 : ℂ) - ((1 : ℕ) : ℂ) = -((0 : ℕ) : ℂ) := by push_cast; ring
  rw [e0, spectralZeta_neg_nat, if_pos rfl, deriv_spectralZeta_eq_optimalZetaDerivSum,
    deriv_spectralZeta_eq_optimalZetaDerivSum] at h
  apply Complex.ofReal_injective
  rw [show (∫ ω, optimalUnitLifetime B ω ∂μ) = ∫ ω, optimalUnitLifetime B ω ^ (1 : ℕ) ∂μ by simp, h,
    ← optimalMomentReadout_boundary_one_eq_zetaDeriv]
  push_cast
  ring_nf

/-- All positive integer moments of the optimal lifetime in one statement. -/
theorem optimalUnitLifetime_moment_eq (hB : IsBrownianReal B μ) {q : ℕ} (hq : 1 ≤ q) :
    (∫ ω, optimalUnitLifetime B ω ^ q ∂μ) =
      if q = 1 then 40 * (riemannZeta 3).re / π ^ 2 - 4 / 3 else optimalMomentReadout q := by
  split_ifs with h
  · subst h
    simpa using optimalUnitLifetime_mean_eq_boundary_readout hB
  · exact optimalUnitLifetime_moment_eq_readout hB (by omega)

end BrownianAffine
