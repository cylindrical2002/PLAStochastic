import PLAStochastic.Index.KEP.Poisson.UniformComparison
import PLAStochastic.Index.KEP.SpatialPolynomialCutoff

/-!
# Actual Poisson comparison above an integer polynomial cutoff

The intensity cutoff is expressed with the integer epsilon power 153. The
exponential parameter and spatial error constant are fixed first; every
prescribed positive Hellinger tolerance is then paid by a fixed cutoff
constant, uniformly in epsilon, intensity, anchor and layer.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepPoisson_polynomial_comparison {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) :
    ∃ theta D : ℝ, 0 < theta ∧ 0 < D ∧
      ∀ eta : ℝ, 0 < eta → ∃ R E : ℝ, 1 ≤ R ∧
        kepReferenceClassicalThreshold ≤ E ∧ 1 ≤ E ∧
        ∀ eps, E ≤ eps → ∀ n : ℝ, ∀ j : ℕ,
          R * eps ^ 153 * kepReferenceSpan eps j ≤ n →
          (∀ x, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x j 1 g ≠ ⊤) ∧
          (∀ x, Integrable (fun z => Real.exp (theta * z))
              (kepPoissonLayerMeasure hf eps n x j) ∧
            ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n x j ≤ 73) ∧
          ∀ x, measureHellinger (kepPoissonLayerMeasure hf eps n x j)
              (kepReferenceLaw eps j) ≤ kepSpatialError D eps n j ∧
            measureHellinger (kepPoissonLayerMeasure hf eps n x j)
              (kepReferenceLaw eps j) ≤ eta := by
  obtain ⟨theta, D, delta, E0, htheta, hD, hdelta, hdelta1, hclass, hE01, hcomp⟩ :=
    kepPoisson_uniform_comparison hf
  obtain ⟨eSpan, _, _, _, hspan⟩ := kepReferenceSpan_budget
  refine ⟨theta, D, htheta, hD, ?_⟩
  intro eta heta
  let d := min delta (eta / D)
  have hd : 0 < d := lt_min hdelta (div_pos heta hD)
  have hdDelta : d ≤ delta := min_le_left _ _
  have hd1 : d ≤ 1 := hdDelta.trans hdelta1
  let R := (1 / d) ^ 3
  have hR : 1 ≤ R := one_le_pow₀ ((le_div_iff₀ hd).mpr (by simpa using hd1))
  let E := max E0 eSpan
  have hE0 : E0 ≤ E := le_max_left _ _
  refine ⟨R, E, hR, hclass.trans hE0, hE01.trans hE0, ?_⟩
  intro eps heps n j hn
  have he0 : E0 ≤ eps := hE0.trans heps
  have he1 : 1 ≤ eps := hE01.trans he0
  have hs := hspan eps ((le_max_right _ _).trans heps)
  have hm1 (k : ℕ) : 1 ≤ kepReferenceSpan eps k := by
    induction k with
    | zero => rw [hs.1]
    | succ k ih =>
      have hp := (hs.2.1 k).le
      linarith [hs.2.2.1 k]
  obtain ⟨hn1, hcut⟩ := kep_spatial_cutoff_of_polynomial_intensity he1 (hm1 j) hd hd1 hn
  have h := hcomp eps he0 n hn1 j (hcut.trans hdDelta)
  refine ⟨h.1, h.2.1, ?_⟩
  intro x
  refine ⟨h.2.2 x, (h.2.2 x).trans ?_⟩
  have h100 := kep_spatial_cutoff_lower_powers he1
    (Real.rpow_nonneg (div_nonneg (hs.2.1 j).le (zero_lt_one.trans_le hn1).le) _) hcut 100 (by omega)
  change D * eps ^ 100 * (kepReferenceSpan eps j / n) ^ (2 / 3 : ℝ) ≤ eta
  calc
    _ ≤ D * d := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h100 hD.le
    _ ≤ D * (eta / D) := mul_le_mul_of_nonneg_left (min_le_right _ _) hD.le
    _ = eta := by field_simp

end

end PGM
