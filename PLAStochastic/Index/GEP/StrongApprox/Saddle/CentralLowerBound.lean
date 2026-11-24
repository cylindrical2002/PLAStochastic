import PLAStochastic.Index.GEP.StrongApprox.Saddle.SumDensityBounds

/-! # WP5: a uniform central lower bound for actual tilted and saddle densities -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Real ENNReal NNReal

/-- A class-uniform upper bound for the Gaussian center normalization. -/
def saCenterNormalizer (vhi : ℝ) : ℝ := Real.sqrt (2 * π * (5 / 4 * vhi + 1))

theorem saCenterNormalizer_pos {vhi : ℝ} (hvhi : 0 < vhi) : 0 < saCenterNormalizer vhi := by
  unfold saCenterNormalizer
  positivity

/-- For sufficiently long blocks, every admissible recentered tilted density is
bounded below at zero by one common positive constant. -/
theorem exists_uniform_saTiltedCenterDensity_lower
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ lam : ℝ, |lam| ≤ saTiltRadius vlo B θ →
      ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ l : ℕ, 2 ≤ l →
      1 / s ≤ (l : ℝ) ^ 8 → 2 * C ≤ Real.sqrt l →
        1 / (2 * saCenterNormalizer vhi) ≤ saTiltedCenterDensity ν s l lam := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_saTiltCentralFactor vlo vhi κ₃ B θ D c
    hvlo hvhi hB hθ hD hc
  refine ⟨C, hC, ?_⟩
  intro ν hν hsm lam hlam s hs hs1 l hl hscale hlarge
  have hroot : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < l by omega))
  have herror := hb ν hν hsm lam hlam s hs hs1 l hl hscale
  have hhalf : C / Real.sqrt l ≤ 1 / 2 := by rw [div_le_iff₀ hroot]; linarith
  have hfac : 1 / 2 ≤ saTiltCentralFactor ν lam s l := by
    linarith [(abs_le.mp herror).1]
  have hv := (hν.centered_cgf_variance_bracket hvlo hθ hlam).2
  have hnorm : Real.sqrt (2 * π *
      (iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam + s ^ 2)) ≤
      saCenterNormalizer vhi := by
    apply Real.sqrt_le_sqrt
    have hs2 : s ^ 2 ≤ 1 := by nlinarith
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [hν.var_le]
  have hq : 0 ≤ saTiltedCenterDensity ν s l lam := saGaussianDensity_nonneg _ _ _
  have hfac' : saTiltCentralFactor ν lam s l ≤
      saCenterNormalizer vhi * saTiltedCenterDensity ν s l lam :=
    mul_le_mul_of_nonneg_right hnorm hq
  rw [div_le_iff₀ (mul_pos (by norm_num) (saCenterNormalizer_pos hvhi))]
  nlinarith

/-- The saddle density lower bound used to normalize the actual conditional
split. Its constants are chosen before the input law. -/
theorem exists_uniform_saCenteredSumDensity_lower
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ l : ℕ, 2 ≤ l →
      1 / s ≤ (l : ℝ) ^ 8 → 2 * C ≤ Real.sqrt l →
      ∀ w : ℝ, |w| ≤ saMeanRadius vlo B θ →
        Real.exp (-(l : ℝ) * saRate vlo B θ ν s w) /
            (2 * saCenterNormalizer vhi * Real.sqrt l) ≤
          saCenteredSumDensity ν s l (l * w) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_saTiltedCenterDensity_lower vlo vhi κ₃ B θ D c
    hvlo hvhi hB hθ hD hc
  refine ⟨C, hC, ?_⟩
  intro ν hν hsm s hs hs1 l hl hscale hlarge w hw
  have hmem := (hν.saSaddle_spec hvlo hθ s (hw.trans (saMeanRadius_lt_full hvlo hθ).le)).1
  have hcenter := hb ν hν hsm _ (abs_le.mpr hmem) s hs hs1 l hl hscale hlarge
  rw [hν.saCenteredSumDensity_saddle hvlo hθ hs (by omega) hw]
  convert mul_le_mul_of_nonneg_left hcenter
    (show 0 ≤ Real.exp (-(l : ℝ) * saRate vlo B θ ν s w) / Real.sqrt l by positivity) using 1 <;> first | rfl | ring

end

end PGM
