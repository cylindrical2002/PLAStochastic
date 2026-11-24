import PLAStochastic.Index.GEP.StrongApprox.Main
import PLAStochastic.Index.GEP.Universality.BrownianSide
import PLAStochastic.Index.GEP.PointwiseSmall.RealAxis
import PLAStochastic.Index.CEPS.Reference.Basic

/-!
# Actual one-layer convergence to the Brownian lifetime

The existing strong approximation and Brownian comparison discharge every
input of the single-law estimate. The estimate is uniform on a regular class.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory BrownianAffine Filter Topology Set
open scoped ENNReal

/-- The actual unnormalized optimal lifetime as a probability law. -/
def cepsTau : ProbabilityMeasure ℝ :=
  ⟨brownianLifetimeLaw, by
    unfold brownianLifetimeLaw
    exact Measure.isProbabilityMeasure_map
      (aemeasurable_optimalUnitLifetime isBrownianReal_canonicalBrownian)⟩

theorem cepsTau_nonneg : (cepsTau : Measure ℝ) (Iio 0) = 0 := by
  obtain ⟨θτ, Eτ, hL⟩ := brownian_lifetimeSide
  exact hL.nonneg

theorem integral_cepsTau : (∫ x, x ∂(cepsTau : Measure ℝ)) = optimalMeanConstant := by
  change (∫ x, x ∂(canonicalPreBrownianMeasure.map
    (optimalUnitLifetime canonicalBrownian))) = _
  rw [integral_map (f := fun x : ℝ => x)
    (aemeasurable_optimalUnitLifetime isBrownianReal_canonicalBrownian) (by fun_prop)]
  exact optimalUnitLifetime_mean_eq_constant isBrownianReal_canonicalBrownian

theorem integral_sq_cepsTau : (∫ x, x ^ 2 ∂(cepsTau : Measure ℝ)) =
    optimalSecondMomentConstant := by
  change (∫ x, x ^ 2 ∂(canonicalPreBrownianMeasure.map
    (optimalUnitLifetime canonicalBrownian))) = _
  rw [integral_map (aemeasurable_optimalUnitLifetime isBrownianReal_canonicalBrownian)
    (by fun_prop)]
  exact optimalUnitLifetime_second_eq_constant isBrownianReal_canonicalBrownian

/-- No strong approximation or lifetime comparison remains as an input. -/
theorem ceps_rawLaw_distance_on_regular_class {D θ vlo vhi : ℝ}
    (_hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ γ K : ℝ, 0 < γ ∧ 0 ≤ K ∧ ∀ᶠ eps : ℝ in atTop,
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
        dEtaL γ (rawLaw eps ν) cepsTau ≤ ENNReal.ofReal (K * eps ^ (-(17 / 32 : ℝ))) := by
  let b := regB vhi
  let β := regBeta D θ vlo
  let vmin := regV vlo
  let B := 2 * D / θ
  let κ₃ := β * Real.sqrt b ^ 3
  have hvm : 0 < vmin := regV_pos hvlo
  have hvmb : vmin ≤ b := regV_le_regB hv
  have hνU : ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      UnivClass vmin b κ₃ B (θ / 2) ν := fun ν hν =>
    pw_univClass_of_momClass (by dsimp [β]; linarith [one_le_regBeta D θ vlo])
      (hν.momClass hθ hvlo) (hν.expMom hθ)
  have hνS : ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν → SmoothPart D (1 / 2) ν := by
    intro ν hν
    simpa only [mixPM_zero] using
      pw_smoothPart_mix (σ := ν) (t := 0) hν hθ le_rfl (by norm_num)
  obtain ⟨KSA, n₀, hKSA, hn₀, hSA⟩ :=
    strongApproxClass vmin b κ₃ B (θ / 2) D (1 / 2) hvm hvmb (half_pos hθ) (by norm_num)
  obtain ⟨θτ, Eτ, hL⟩ := brownian_lifetimeSide
  let γ := saGamma vmin b θτ
  let K := max (saK vmin b θτ Eτ KSA (bernsteinRate (θ / 2) B)) 0
  have hb : 0 < b := hvm.trans_le hvmb
  refine ⟨γ, K, saGamma_pos hvm hb hL.θpos, le_max_right _ _, ?_⟩
  have hsquare : Tendsto (fun eps : ℝ => eps ^ 2) atTop atTop := tendsto_pow_atTop (by decide)
  filter_upwards [eventually_ge_atTop (epsZero b (univBeta vmin κ₃)),
    eventually_ge_atTop (Real.exp 1),
    hsquare.eventually (eventually_ge_atTop ((n₀ : ℝ) * b / saL vmin b θτ)),
    eventually_ge_atTop (2 * b / saL vmin b θτ),
    eventually_ge_atTop ((4 * saA vmin b θτ) ^ 4), eventually_ge_atTop (2 * b),
    eventually_ge_atTop ((4 * saKchi KSA (bernsteinRate (θ / 2) B) b) ^ 2),
    eventually_ge_atTop ((1215 / bernsteinRate (θ / 2) B) ^ 2),
    eventually_ge_atTop (2 * γ * b / min ((θ / 2) / 4) ((θ / 2) ^ 2 / (16 * B)))]
    with eps h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
  intro ν hν
  have hbound := single_law_bound (hνU ν hν) hvm (half_pos hθ) hL hKSA hn₀
    (hSA ν (hνU ν hν) (hνS ν hν)) h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg ((Real.exp_pos 1).le.trans h₂) _)

end

end PGM
