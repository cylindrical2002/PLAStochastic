import PLAStochastic.Index.GEP.StrongApprox.Saddle.CentralLowerBound
import PLAStochastic.Index.GEP.StrongApprox.Saddle.DyadicKernelLaws
import PLAStochastic.Index.GEP.StrongApprox.Quantile.RateEnvelopeTail

/-! # WP5: global conditional density bounds from the actual saddle normalization -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Real ENNReal NNReal

theorem sa_positive_quotient_exp_bound {p q r A K a b d : ℝ}
    (hq : 0 ≤ q) (hr : 0 < r) (hA : 0 ≤ A) (hK : 0 < K)
    (hpB : p ≤ A * Real.exp (-a)) (hqB : q ≤ A * Real.exp (-b))
    (hrB : Real.exp (-d) / K ≤ r) :
    p * q / r ≤ A ^ 2 * K * Real.exp (-(a + b - d)) := by
  have hprod := mul_le_mul hpB hqB hq (mul_nonneg hA (Real.exp_nonneg _))
  calc
    p * q / r ≤ (A * Real.exp (-a) * (A * Real.exp (-b))) / r :=
      div_le_div_of_nonneg_right hprod hr.le
    _ ≤ (A * Real.exp (-a) * (A * Real.exp (-b))) / (Real.exp (-d) / K) :=
      div_le_div_of_nonneg_left (by positivity) (div_pos (Real.exp_pos _) hK) hrB
    _ = A ^ 2 * K * (Real.exp (-a) * Real.exp (-b) / Real.exp (-d)) := by
      field_simp
    _ = A ^ 2 * K * Real.exp (-(a + b - d)) := by
      rw [← Real.exp_add, ← Real.exp_sub]
      congr 2
      ring

/-- A class-uniform global envelope for the actual conditional split density.
The explicit smoothing factor is polynomial when `1/s ≤ l⁸`. -/
theorem exists_uniform_saSplitDensity_global_upper
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ l : ℕ, 2 ≤ l →
      1 / s ≤ (l : ℝ) ^ 8 → 2 * C ≤ Real.sqrt l →
      ∀ u : ℝ, |u| ≤ saMeanRadius vlo B θ / 2 → ∀ t : ℝ,
        saSplitDensity (saCenteredSumDensity ν s l) (2 * l * u) (l * (u + t)) ≤
          (2 * saCenterNormalizer vhi * Real.sqrt (2 * (l : ℝ)) /
            (2 * π * (l : ℝ) * s ^ 2)) *
          Real.exp (-(l : ℝ) * (4 / (5 * (vhi + 1))) *
            min (t ^ 2) (saMeanRadius vlo B θ / 2 * |t|)) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_saCenteredSumDensity_lower
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  refine ⟨C, hC, ?_⟩
  intro ν hν hsm s hs hs1 l hl hscale hlarge u hu t
  have hl0 : 0 < l := by omega
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl0
  have h2l : 2 ≤ 2 * l := by omega
  have hroot2 : Real.sqrt (l : ℝ) ≤ Real.sqrt (2 * l : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show l ≤ 2 * l by omega))
  have hscale2 : 1 / s ≤ ((2 * l : ℕ) : ℝ) ^ 8 := hscale.trans
    (pow_le_pow_left₀ hlr.le (by exact_mod_cast (show l ≤ 2 * l by omega)) 8)
  have hu' : |u| ≤ saMeanRadius vlo B θ := by
    have := (saMeanRadius_pos (B := B) hvlo hθ).le
    linarith
  have hden := hb ν hν hsm s hs hs1 (2 * l) h2l hscale2 (hlarge.trans hroot2) u hu'
  have hp := hν.saCenteredSumDensity_global_upper hvlo hθ hs hl0 (u + t)
  have hm := hν.saCenteredSumDensity_global_upper hvlo hθ hs hl0 (u - t)
  rw [saSplitDensity_centeredSum ν hs hl0]
  let A := (Real.sqrt (2 * π * ((l : ℝ) * s ^ 2)))⁻¹
  let K := 2 * saCenterNormalizer vhi * Real.sqrt (2 * (l : ℝ))
  have hK : 0 < K := by
    have := saCenterNormalizer_pos hvhi
    dsimp [K]
    positivity
  have hden' : Real.exp (-((2 * (l : ℝ)) * saRate vlo B θ ν s u)) / K ≤
      saCenteredSumDensity ν s (2 * l) (2 * l * u) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, neg_mul] using hden
  have hquot := sa_positive_quotient_exp_bound
    (a := (l : ℝ) * saGlobalRate vlo B θ ν s (u + t))
    (b := (l : ℝ) * saGlobalRate vlo B θ ν s (u - t))
    (d := 2 * (l : ℝ) * saRate vlo B θ ν s u)
    (saCenteredSumDensity_pos ν hs hl0 ((l : ℝ) * (u - t))).le
    (saCenteredSumDensity_pos ν hs (show 0 < 2 * l by omega) (2 * l * u))
    (show 0 ≤ A by dsimp [A]; positivity) hK
    (by simpa only [neg_mul] using hp) (by simpa only [neg_mul] using hm) hden'
  have hexp : -((l : ℝ) * saGlobalRate vlo B θ ν s (u + t) +
      (l : ℝ) * saGlobalRate vlo B θ ν s (u - t) -
      2 * (l : ℝ) * saRate vlo B θ ν s u) ≤
      -(l : ℝ) * (4 / (5 * (vhi + 1))) * min (t ^ 2) (saMeanRadius vlo B θ / 2 * |t|) := by
    have hthree := hν.saGlobalRate_three_point_lower hvlo hθ
      (show |s| ≤ 1 by rwa [abs_of_pos hs]) hu t
    rw [hν.saGlobalRate_eq_saRate hvlo hθ s hu'] at hthree
    nlinarith [mul_le_mul_of_nonneg_left hthree hlr.le]
  have hcoef : A ^ 2 * K = 2 * saCenterNormalizer vhi * Real.sqrt (2 * (l : ℝ)) /
      (2 * π * (l : ℝ) * s ^ 2) := by
    dsimp [A, K]
    rw [inv_pow, Real.sq_sqrt (by positivity)]
    ring
  apply hquot.trans
  rw [hcoef]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)

end

end PGM
