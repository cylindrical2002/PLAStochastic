import PLAStochastic.Index.GEP.StrongApprox.Saddle.UniformEnvelope
import PLAStochastic.Index.GEP.StrongApprox.Quantile.AffineDensity

/-! # WP5: actual sum and split envelopes on the square-root block scale -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem sa_block_scale_mul {l : ℕ} (hl : 0 < l) (z : ℝ) :
    (l : ℝ) * (z / Real.sqrt l) = Real.sqrt l * z := by
  have hs : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hl)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg l)
  calc
    (l : ℝ) * (z / Real.sqrt l) = ((l : ℝ) / Real.sqrt l) * z := by ring
    _ = _ := by rw [(div_eq_iff hs.ne').mpr (show (l : ℝ) = Real.sqrt l * Real.sqrt l by nlinarith [hsq])]

theorem sa_block_scale_rate {l : ℕ} (hl : 0 < l) (r z : ℝ) :
    (l : ℝ) * min ((z / Real.sqrt l) ^ 2) (r * |z / Real.sqrt l|) =
      min (z ^ 2) (r * Real.sqrt l * |z|) := by
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl
  have hs : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr hlr
  rw [mul_min_of_nonneg _ _ hlr.le, div_pow, Real.sq_sqrt hlr.le,
    abs_div, abs_of_pos hs]
  congr 1
  · field_simp
  · calc
      (l : ℝ) * (r * (|z| / Real.sqrt l)) = r * ((l : ℝ) * (|z| / Real.sqrt l)) := by ring
      _ = _ := by rw [sa_block_scale_mul hl]; ring

/-- The root sum envelope in `sqrt(l)` coordinates. -/
theorem exists_uniform_saCenteredSumDensity_block_upper
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ l : ℕ, 2 ≤ l → 1 / s ≤ (l : ℝ) ^ 8 → ∀ z : ℝ,
        Real.sqrt l * saCenteredSumDensity ν s l (Real.sqrt l * z) ≤
          K * Real.exp (-(2 / (5 * (vhi + 1))) *
            min (z ^ 2) (saMeanRadius vlo B θ * Real.sqrt l * |z|)) := by
  obtain ⟨K, hK, hb⟩ := exists_uniform_saCenteredSumDensity_global_upper
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  refine ⟨K, hK, ?_⟩
  intro ν hν hsm s hs hs1 l hl hscale z
  have hl0 : 0 < l := by omega
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl0
  have hroot : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr hlr
  have he := hb ν hν hsm s hs l hl hscale (z / Real.sqrt l)
  rw [sa_block_scale_mul hl0] at he
  have hrate := hν.saGlobalRate_lower hvlo hθ (show |s| ≤ 1 by rwa [abs_of_pos hs])
    (z / Real.sqrt l)
  have hr := mul_le_mul_of_nonneg_left hrate hlr.le
  have hid : (l : ℝ) * (2 / (5 * (vhi + 1)) *
      min ((z / Real.sqrt l) ^ 2) (saMeanRadius vlo B θ * |z / Real.sqrt l|)) =
      (2 / (5 * (vhi + 1))) * min (z ^ 2) (saMeanRadius vlo B θ * Real.sqrt l * |z|) := by
    rw [mul_left_comm, sa_block_scale_rate hl0]
  rw [hid] at hr
  calc
    _ ≤ Real.sqrt l * (K / Real.sqrt l *
        Real.exp (-(l : ℝ) * saGlobalRate vlo B θ ν s (z / Real.sqrt l))) :=
      mul_le_mul_of_nonneg_left he hroot.le
    _ = K * Real.exp (-(l : ℝ) * saGlobalRate vlo B θ ν s (z / Real.sqrt l)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hK.le

/-- The conditional envelope uses the same square-root block coordinates. -/
theorem exists_uniform_saSplitDensity_block_upper
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ l : ℕ, 2 ≤ l →
      1 / s ≤ (l : ℝ) ^ 8 → 2 * C ≤ Real.sqrt l →
      ∀ u : ℝ, |u| ≤ saMeanRadius vlo B θ / 2 → ∀ z : ℝ,
        Real.sqrt l * saSplitDensity (saCenteredSumDensity ν s l) (2 * l * u)
          ((l : ℝ) * u + Real.sqrt l * z) ≤
          K * Real.exp (-(4 / (5 * (vhi + 1))) *
            min (z ^ 2) (saMeanRadius vlo B θ / 2 * Real.sqrt l * |z|)) := by
  obtain ⟨C, K, hC, hK, hb⟩ := exists_uniform_saSplitDensity_rate_upper
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  refine ⟨C, K, hC, hK, ?_⟩
  intro ν hν hsm s hs hs1 l hl hscale hlarge u hu z
  have hl0 : 0 < l := by omega
  have hroot : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hl0)
  have hb' := hb ν hν hsm s hs hs1 l hl hscale hlarge u hu (z / Real.sqrt l)
  rw [mul_add, sa_block_scale_mul hl0] at hb'
  have hexp : -(l : ℝ) * (4 / (5 * (vhi + 1))) *
      min ((z / Real.sqrt l) ^ 2) (saMeanRadius vlo B θ / 2 * |z / Real.sqrt l|) =
      -(4 / (5 * (vhi + 1))) *
        min (z ^ 2) (saMeanRadius vlo B θ / 2 * Real.sqrt l * |z|) := by
    calc
      _ = -(4 / (5 * (vhi + 1))) * ((l : ℝ) *
        min ((z / Real.sqrt l) ^ 2) (saMeanRadius vlo B θ / 2 * |z / Real.sqrt l|)) := by ring
      _ = _ := by rw [sa_block_scale_rate hl0]
  rw [hexp] at hb'
  calc
    _ ≤ Real.sqrt l * (K / Real.sqrt l * Real.exp (-(4 / (5 * (vhi + 1))) *
        min (z ^ 2) (saMeanRadius vlo B θ / 2 * Real.sqrt l * |z|))) :=
      mul_le_mul_of_nonneg_left hb' hroot.le
    _ = _ := by field_simp

/-- Quantitative left and right tails at a square-root block cutoff. -/
theorem exists_uniform_saSplitDensity_block_tails
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ s : ℝ, ∀ hs : 0 < s, s ≤ 1 → ∀ l : ℕ, ∀ hl : 2 ≤ l,
      1 / s ≤ (l : ℝ) ^ 8 → 2 * C ≤ Real.sqrt l →
      ∀ u : ℝ, |u| ≤ saMeanRadius vlo B θ / 2 →
      ∀ Y : ℝ, 0 < Y → Y ≤ saMeanRadius vlo B θ / 2 * Real.sqrt l →
      let hp := (saDensity_centeredSum ν hs (show 0 < l by omega)).splitDensity (2 * l * u)
      let b := 4 / (5 * (vhi + 1))
      cdf (hp.law : Measure ℝ) ((l : ℝ) * u - Real.sqrt l * Y) ≤ K * Real.exp (-b * Y ^ 2) / (b * Y) ∧
        1 - cdf (hp.law : Measure ℝ) ((l : ℝ) * u + Real.sqrt l * Y) ≤ K * Real.exp (-b * Y ^ 2) / (b * Y) := by
  obtain ⟨C, K, hC, hK, hb⟩ := exists_uniform_saSplitDensity_block_upper
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  refine ⟨C, K, hC, hK, ?_⟩
  intro ν hν hsm s hs hs1 l hl hscale hlarge u hu Y hY hYR
  dsimp only
  have hl0 : 0 < l := by omega
  have hroot : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hl0)
  have hr := saMeanRadius_pos (B := B) hvlo hθ
  have htail := ((saDensity_centeredSum ν hs hl0).splitDensity (2 * l * u)).affine_tails_le_rateEnvelope
    ((l : ℝ) * u) hroot hK.le (show 0 < 4 / (5 * (vhi + 1)) by positivity)
    (show 0 < saMeanRadius vlo B θ / 2 * Real.sqrt l by positivity) hY
    (fun x _ => hb ν hν hsm s hs hs1 l hl hscale hlarge u hu x)
  rw [min_eq_left hYR, min_eq_left (by nlinarith :
    Y ^ 2 ≤ saMeanRadius vlo B θ / 2 * Real.sqrt l * Y)] at htail
  exact htail

/-- Root-sum tails in the same coordinates. -/
theorem exists_uniform_saCenteredSumDensity_block_tails
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ s : ℝ, ∀ hs : 0 < s, s ≤ 1 → ∀ l : ℕ, ∀ hl : 2 ≤ l,
      1 / s ≤ (l : ℝ) ^ 8 →
      ∀ Y : ℝ, 0 < Y → Y ≤ saMeanRadius vlo B θ * Real.sqrt l →
      let hp := saDensity_centeredSum ν hs (show 0 < l by omega)
      let b := 2 / (5 * (vhi + 1))
      cdf (hp.law : Measure ℝ) (-Real.sqrt l * Y) ≤ K * Real.exp (-b * Y ^ 2) / (b * Y) ∧
        1 - cdf (hp.law : Measure ℝ) (Real.sqrt l * Y) ≤ K * Real.exp (-b * Y ^ 2) / (b * Y) := by
  obtain ⟨K, hK, hb⟩ := exists_uniform_saCenteredSumDensity_block_upper
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  refine ⟨K, hK, ?_⟩
  intro ν hν hsm s hs hs1 l hl hscale Y hY hYR
  dsimp only
  have hl0 : 0 < l := by omega
  have hroot : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hl0)
  have hr := saMeanRadius_pos (B := B) hvlo hθ
  have htail := (saDensity_centeredSum ν hs hl0).affine_tails_le_rateEnvelope
    0 hroot hK.le (show 0 < 2 / (5 * (vhi + 1)) by positivity)
    (show 0 < saMeanRadius vlo B θ * Real.sqrt l by positivity) hY
    (fun x _ => by simpa only [zero_add] using hb ν hν hsm s hs hs1 l hl hscale x)
  rw [min_eq_left hYR, min_eq_left (by nlinarith :
    Y ^ 2 ≤ saMeanRadius vlo B θ * Real.sqrt l * Y)] at htail
  simpa only [zero_sub, zero_add, neg_mul] using htail

end

end PGM
