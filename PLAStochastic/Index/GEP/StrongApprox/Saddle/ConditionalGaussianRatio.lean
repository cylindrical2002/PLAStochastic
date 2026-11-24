import PLAStochastic.Index.GEP.StrongApprox.Saddle.GaussianRatio

/-! # WP5: conditional Gaussian density ratios for the actual sum kernels -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Real ENNReal NNReal

/-- Gaussian normalization for the midpoint split of two blocks of size `l`. -/
theorem sa_log_gaussianPDFReal_split {V : ℝ} (hV : 0 < V) {l : ℕ} (hl : 0 < l) (t : ℝ) :
    Real.log (gaussianPDFReal 0 (Real.toNNReal ((l : ℝ) * V / 2)) ((l : ℝ) * t)) =
      -(2 * Real.log (Real.sqrt l) - Real.log (Real.sqrt (2 * (l : ℝ))) +
          Real.log (Real.sqrt (2 * π * V))) - (l : ℝ) * (t ^ 2 / V) := by
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl
  rw [sa_log_gaussianPDFReal (by positivity)]
  have hn : Real.log (Real.sqrt (2 * π * ((l : ℝ) * V / 2))) =
      2 * Real.log (Real.sqrt l) - Real.log (Real.sqrt (2 * (l : ℝ))) +
        Real.log (Real.sqrt (2 * π * V)) := by
    simp (disch := positivity) only [Real.log_sqrt, Real.log_mul, Real.log_div]
    ring
  rw [hn]
  field_simp

/-- The actual quotient kernel, with the parent sum fixed at `2 l u`, has the
Gaussian midpoint density up to a uniform cubic logarithmic error. -/
theorem exists_uniform_saConditionalDensity_gaussian_ratio
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ l : ℕ, 2 ≤ l →
      1 / s ≤ (l : ℝ) ^ 8 → 2 * C ≤ Real.sqrt l →
      ∀ u t : ℝ, |u| + |t| ≤ saMeanRadius vlo B θ →
        |Real.log ((saCenteredSumDensity ν s l (l * (u + t)) *
            saCenteredSumDensity ν s l (l * (u - t)) /
            saCenteredSumDensity ν s (2 * l) (2 * l * u)) /
          gaussianPDFReal 0 (Real.toNNReal ((l : ℝ) * (lawVar ν + s ^ 2) / 2)) (l * t))| ≤
          (6 * C) / Real.sqrt l + saLogVarianceConstant vlo B θ / 2 * (3 * |u| + 2 * |t|) +
            (l : ℝ) * saRateThird vlo B θ * (|u| * t ^ 2 + |t| ^ 3 / 3) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_saCenteredSumDensity_log_correction
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  refine ⟨C, hC, ?_⟩
  intro ν hν hsm s hs hs1 l hl hscale hlarge u t hut
  have hl0 : 0 < l := by omega
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl0
  have h2l : 2 ≤ 2 * l := by omega
  have hroot : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr hlr
  have hroot2 : Real.sqrt (l : ℝ) ≤ Real.sqrt (2 * l : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show l ≤ 2 * l by omega))
  have hscale2 : 1 / s ≤ ((2 * l : ℕ) : ℝ) ^ 8 := hscale.trans
    (pow_le_pow_left₀ hlr.le (by exact_mod_cast (show l ≤ 2 * l by omega)) 8)
  have hu : |u| ≤ saMeanRadius vlo B θ := by have := abs_nonneg t; linarith
  have hup := (abs_add_le u t).trans hut
  have hum := (abs_sub u t).trans hut
  have hp := hb ν hν hsm s hs hs1 l hl hscale hlarge (u + t) hup
  have hm := hb ν hν hsm s hs hs1 l hl hscale hlarge (u - t) hum
  have h0 := hb ν hν hsm s hs hs1 (2 * l) h2l hscale2 (hlarge.trans hroot2) u hu
  have hb2 : 2 * C / Real.sqrt (2 * l : ℕ) ≤ 2 * C / Real.sqrt (l : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hroot hroot2
  have hvar : 0 < lawVar ν + s ^ 2 := by nlinarith [hν.var_ge, sq_nonneg s]
  have hposp := saCenteredSumDensity_pos ν hs hl0 ((l : ℝ) * (u + t))
  have hposm := saCenteredSumDensity_pos ν hs hl0 ((l : ℝ) * (u - t))
  have hpos0 := saCenteredSumDensity_pos ν hs (show 0 < 2 * l by omega) (2 * l * u)
  have hposg : 0 < gaussianPDFReal 0
      (Real.toNNReal ((l : ℝ) * (lawVar ν + s ^ 2) / 2)) (l * t) := by
    apply gaussianPDFReal_pos
    simp [Real.toNNReal_eq_zero, (show 0 < (l : ℝ) * (lawVar ν + s ^ 2) / 2 by positivity).not_ge]
  rw [Real.log_div (div_ne_zero (mul_ne_zero hposp.ne' hposm.ne') hpos0.ne') hposg.ne',
    Real.log_div (mul_ne_zero hposp.ne' hposm.ne') hpos0.ne',
    Real.log_mul hposp.ne' hposm.ne', sa_log_gaussianPDFReal_split hvar hl0]
  let E := fun k w => Real.log (saCenteredSumDensity ν s k (k * w)) +
    (k : ℝ) * saRate vlo B θ ν s w + Real.log (Real.sqrt k) +
    Real.log (Real.sqrt (2 * π * (lawVar ν + s ^ 2)))
  have he : Real.log (saCenteredSumDensity ν s l (l * (u + t))) +
      Real.log (saCenteredSumDensity ν s l (l * (u - t))) -
      Real.log (saCenteredSumDensity ν s (2 * l) (2 * l * u)) -
      (-(2 * Real.log (Real.sqrt l) - Real.log (Real.sqrt (2 * (l : ℝ))) +
          Real.log (Real.sqrt (2 * π * (lawVar ν + s ^ 2)))) -
        (l : ℝ) * (t ^ 2 / (lawVar ν + s ^ 2))) =
      (E l (u + t) + E l (u - t) - E (2 * l) u) -
        (l : ℝ) * (saRate vlo B θ ν s (u + t) + saRate vlo B θ ν s (u - t) -
          2 * saRate vlo B θ ν s u - t ^ 2 / (lawVar ν + s ^ 2)) := by
    dsimp [E]
    push_cast
    ring
  rw [he]
  have herr : |E l (u + t) + E l (u - t) - E (2 * l) u| ≤
      6 * C / Real.sqrt l + saLogVarianceConstant vlo B θ / 2 * (3 * |u| + 2 * |t|) := by
    have ht := (abs_sub (E l (u + t) + E l (u - t)) (E (2 * l) u)).trans
      (add_le_add (abs_add_le _ _) le_rfl)
    change |E l (u + t)| ≤ _ at hp
    change |E l (u - t)| ≤ _ at hm
    change |E (2 * l) u| ≤ _ at h0
    have hL := (saLogVarianceConstant_pos (B := B) hvlo hθ).le
    have ha := mul_le_mul_of_nonneg_left (abs_add_le u t) hL
    have hs' := mul_le_mul_of_nonneg_left (abs_sub u t) hL
    have hdiv : 6 * C / Real.sqrt l = 3 * (2 * C / Real.sqrt l) := by ring
    rw [hdiv]
    nlinarith
  have hrate := hν.saRate_three_point hvlo hθ s hut
  have hrate' : |(l : ℝ) * (saRate vlo B θ ν s (u + t) + saRate vlo B θ ν s (u - t) -
      2 * saRate vlo B θ ν s u - t ^ 2 / (lawVar ν + s ^ 2))| ≤
      (l : ℝ) * saRateThird vlo B θ * (|u| * t ^ 2 + |t| ^ 3 / 3) := by
    rw [abs_mul, abs_of_pos hlr]
    convert mul_le_mul_of_nonneg_left hrate hlr.le using 1 <;> first | rfl | ring
  exact (abs_sub _ _).trans (add_le_add herr hrate')

end

end PGM
