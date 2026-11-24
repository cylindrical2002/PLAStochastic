import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Closure of the layer class: the real-number arithmetic

This file contains only inequalities between real numbers.  The one-layer bracket
(`PLAStochastic.Index.OneLayer.Bracket`) and the next-layer moment identities (`PLAStochastic.Index.Endpoint.NextLayerMoments`)
produce the hypotheses below; the conclusions say that the next layer again has
relative variance in a fixed interval `[δ/2, bAbs]` and normalised third moment at
most `βAbs`.  All constants are absolute: they do not depend on the layer, on the
input law or on `eps`, which is what makes the layer induction close.

Notation: `μ, σ, κ` are the current gap mean, standard deviation and centred third
moment; `G = μ² eps² / σ²`; `C = E T`; `VarT = Var T`; `S2` and `K3'` are the
next-layer centred second and third absolute moments.
-/

namespace PGM

/-- Next-layer relative variance: lower and upper bounds. -/
theorem class_variance_bounds {μ σ eps G C VarT S2 δ cP K2 : ℝ}
    (hμ : 0 < μ) (hσ : 0 < σ) (heps : 0 < eps) (hG : G = μ ^ 2 * eps ^ 2 / σ ^ 2)
    (hδ : 0 < δ)
    (hC1 : G / 128 ≤ C) (hC2 : C ≤ cP * G)
    (hV1 : δ * (cP * G) ^ 2 ≤ VarT) (hV2 : VarT ≤ K2 * G ^ 2)
    (hS : |S2 - μ ^ 2 * VarT| ≤ 2 * μ * Real.sqrt VarT * Real.sqrt (σ ^ 2 * C) + σ ^ 2 * C)
    (hLE1 : 8192 * σ ^ 4 ≤ δ * μ ^ 4 * eps ^ 2) :
    δ / 2 * (μ * C) ^ 2 ≤ S2 ∧ S2 ≤ 2 * K2 * 128 ^ 2 * (μ * C) ^ 2 := by
  have hGpos : 0 < G := by rw [hG]; positivity
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) hC1
  have hVC : δ * C ^ 2 ≤ VarT := by
    have : δ * C ^ 2 ≤ δ * (cP * G) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      exact pow_le_pow_left₀ hCpos.le hC2 2
    linarith
  have hVpos : 0 < VarT := lt_of_lt_of_le (by positivity) hVC
  -- u = √(σ² C) / (μ √VarT) ≤ 1/4
  set a := Real.sqrt VarT with ha
  set b := Real.sqrt (σ ^ 2 * C) with hb
  have ha2 : a ^ 2 = VarT := Real.sq_sqrt hVpos.le
  have hb2 : b ^ 2 = σ ^ 2 * C := Real.sq_sqrt (by positivity)
  have hapos : 0 < a := Real.sqrt_pos.2 hVpos
  have hbnn : 0 ≤ b := Real.sqrt_nonneg _
  -- key: 64 b² ≤ μ² a²
  have hkey : 64 * b ^ 2 ≤ μ ^ 2 * a ^ 2 := by
    rw [ha2, hb2]
    -- σ² C ≤ σ² C² · 128/G and VarT ≥ δ C²
    have h1 : 64 * (σ ^ 2 * C) ≤ μ ^ 2 * (δ * C ^ 2) := by
      -- 16 σ² ≤ μ² δ C, using C ≥ G/128 = μ² eps²/(128 σ²)
      have hC' : μ ^ 2 * eps ^ 2 ≤ 128 * σ ^ 2 * C := by
        have := hC1; rw [hG] at this
        rw [div_div, div_le_iff₀ (by positivity)] at this
        linarith
      have h16 : 64 * σ ^ 2 ≤ μ ^ 2 * δ * C := by
        -- 2048 σ⁴ ≤ δ μ⁴ eps² ≤ δ μ² · 128 σ² C
        have : 8192 * σ ^ 4 ≤ δ * μ ^ 2 * (128 * σ ^ 2 * C) := by
          calc 8192 * σ ^ 4 ≤ δ * μ ^ 4 * eps ^ 2 := hLE1
            _ = δ * μ ^ 2 * (μ ^ 2 * eps ^ 2) := by ring
            _ ≤ δ * μ ^ 2 * (128 * σ ^ 2 * C) := by gcongr
        have hσ2 : 0 < σ ^ 2 := by positivity
        nlinarith
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hVC (sq_nonneg μ)]
  have h4b : 8 * b ≤ μ * a := by
    have : (8 * b) ^ 2 ≤ (μ * a) ^ 2 := by nlinarith
    exact (sq_le_sq₀ (by positivity) (by positivity)).1 this
  have hμa : 0 ≤ μ * a := by positivity
  have hab : μ * a * (8 * b) ≤ μ * a * (μ * a) := mul_le_mul_of_nonneg_left h4b hμa
  rcases abs_le.1 hS with ⟨hSl, hSu⟩
  constructor
  · -- S2 ≥ μ²a² - 2μab - b² ≥ μ²a²/2
    have : μ ^ 2 * VarT / 2 ≤ S2 := by
      rw [← ha2]
      have : σ ^ 2 * C = b ^ 2 := hb2.symm
      nlinarith
    calc δ / 2 * (μ * C) ^ 2 = μ ^ 2 * (δ * C ^ 2) / 2 := by ring
      _ ≤ μ ^ 2 * VarT / 2 := by gcongr
      _ ≤ S2 := this
  · have hSu' : S2 ≤ 2 * μ ^ 2 * VarT := by
      rw [← ha2]
      have : σ ^ 2 * C = b ^ 2 := hb2.symm
      nlinarith
    have hGC : G ≤ 128 * C := by linarith
    calc S2 ≤ 2 * μ ^ 2 * VarT := hSu'
      _ ≤ 2 * μ ^ 2 * (K2 * G ^ 2) := by gcongr
      _ ≤ 2 * μ ^ 2 * (K2 * (128 * C) ^ 2) := by
          have hK2 : 0 ≤ K2 := by
            have : 0 ≤ K2 * G ^ 2 := le_trans hVpos.le hV2
            exact nonneg_of_mul_nonneg_left this (by positivity)
          gcongr
      _ = 2 * K2 * 128 ^ 2 * (μ * C) ^ 2 := by ring

/-- Next-layer normalised third moment. -/
theorem class_third_bound {μ σ κ β eps G C S2 K3' M3 Bh δ K3 Kh : ℝ}
    (hμ : 0 < μ) (hσ : 0 < σ) (heps : 0 < eps) (hG : G = μ ^ 2 * eps ^ 2 / σ ^ 2)
    (hδ : 0 < δ) (hβ : κ ≤ β * σ ^ 3)
    (hC1 : G / 128 ≤ C)
    (hM3 : M3 ≤ K3 * G ^ 3) (hK3 : 0 ≤ K3) (hBh : Bh ≤ Kh * (G * Real.sqrt G))
    (hK3' : K3' ≤ 4 * μ ^ 3 * (4 * (M3 + C ^ 3)) + 4 * (3 * σ ^ 3 * Bh + κ * C))
    (hS2 : δ / 2 * (μ * C) ^ 2 ≤ S2)
    (hLE2 : 12 * 128 ^ 3 * Kh * σ ^ 6 ≤ μ ^ 6 * eps ^ 3)
    (hLE3 : 4 * 128 ^ 2 * β * σ ^ 7 ≤ μ ^ 7 * eps ^ 4) :
    K3' ≤ (16 * (128 ^ 3 * K3 + 1) + 2) / (δ / 2) ^ ((3 : ℝ) / 2) * S2 ^ ((3 : ℝ) / 2) := by
  have hGpos : 0 < G := by rw [hG]; positivity
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) hC1
  have hGC : G ≤ 128 * C := by linarith
  set D := μ * C with hD
  have hDpos : 0 < D := by positivity
  -- G√G = μ³ eps³ / σ³
  have hsqrtG : Real.sqrt G = μ * eps / σ := by
    rw [hG, show μ ^ 2 * eps ^ 2 / σ ^ 2 = (μ * eps / σ) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  -- term 1
  have t1 : 4 * μ ^ 3 * (4 * (M3 + C ^ 3)) ≤ 16 * (128 ^ 3 * K3 + 1) * D ^ 3 := by
    have : M3 ≤ K3 * (128 * C) ^ 3 := le_trans hM3 (by gcongr)
    have hD3 : D ^ 3 = μ ^ 3 * C ^ 3 := by rw [hD]; ring
    rw [hD3]
    have : 4 * μ ^ 3 * (4 * (M3 + C ^ 3)) ≤ 4 * μ ^ 3 * (4 * (K3 * (128 * C) ^ 3 + C ^ 3)) := by
      gcongr
    nlinarith
  -- term 2: 12 σ³ Bh ≤ D³
  have t2 : 4 * (3 * σ ^ 3 * Bh) ≤ D ^ 3 := by
    have hB : Bh ≤ Kh * (μ ^ 3 * eps ^ 3 / σ ^ 3) := by
      refine hBh.trans (le_of_eq ?_)
      rw [hsqrtG, hG]; field_simp
    have hC3 : (μ ^ 2 * eps ^ 2 / σ ^ 2 / 128) ^ 3 ≤ C ^ 3 := by
      rw [← hG]; exact pow_le_pow_left₀ (by positivity) hC1 3
    have : 12 * σ ^ 3 * (Kh * (μ ^ 3 * eps ^ 3 / σ ^ 3)) ≤ μ ^ 3 * (μ ^ 2 * eps ^ 2 / σ ^ 2 / 128) ^ 3 := by
      have hs : σ ^ 3 * (μ ^ 3 * eps ^ 3 / σ ^ 3) = μ ^ 3 * eps ^ 3 := by field_simp
      have lhs : 12 * σ ^ 3 * (Kh * (μ ^ 3 * eps ^ 3 / σ ^ 3)) = 12 * Kh * (μ ^ 3 * eps ^ 3) := by
        field_simp
      rw [lhs]
      have rhs : μ ^ 3 * (μ ^ 2 * eps ^ 2 / σ ^ 2 / 128) ^ 3 =
          μ ^ 9 * eps ^ 6 / (σ ^ 6 * 128 ^ 3) := by field_simp
      rw [rhs, le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hLE2 (show 0 ≤ μ ^ 3 * eps ^ 3 by positivity)
      nlinarith
    have hD3 : D ^ 3 = μ ^ 3 * C ^ 3 := by rw [hD]; ring
    rw [hD3]
    calc 4 * (3 * σ ^ 3 * Bh) = 12 * σ ^ 3 * Bh := by ring
      _ ≤ 12 * σ ^ 3 * (Kh * (μ ^ 3 * eps ^ 3 / σ ^ 3)) := by gcongr
      _ ≤ μ ^ 3 * (μ ^ 2 * eps ^ 2 / σ ^ 2 / 128) ^ 3 := this
      _ ≤ μ ^ 3 * C ^ 3 := by gcongr
  -- term 3: 4 κ C ≤ D³
  have t3 : 4 * (κ * C) ≤ D ^ 3 := by
    have hD3 : D ^ 3 = μ ^ 3 * C * C ^ 2 := by rw [hD]; ring
    rw [hD3]
    have hC2' : (μ ^ 2 * eps ^ 2 / σ ^ 2 / 128) ^ 2 ≤ C ^ 2 := by
      rw [← hG]; exact pow_le_pow_left₀ (by positivity) hC1 2
    have : 4 * κ ≤ μ ^ 3 * (μ ^ 2 * eps ^ 2 / σ ^ 2 / 128) ^ 2 := by
      have rhs : μ ^ 3 * (μ ^ 2 * eps ^ 2 / σ ^ 2 / 128) ^ 2 =
          μ ^ 7 * eps ^ 4 / (σ ^ 4 * 128 ^ 2) := by field_simp
      rw [rhs, le_div_iff₀ (by positivity)]
      have : 4 * κ * (σ ^ 4 * 128 ^ 2) ≤ 4 * (β * σ ^ 3) * (σ ^ 4 * 128 ^ 2) := by gcongr
      nlinarith
    calc 4 * (κ * C) = (4 * κ) * C := by ring
      _ ≤ (μ ^ 3 * (μ ^ 2 * eps ^ 2 / σ ^ 2 / 128) ^ 2) * C := by gcongr
      _ = μ ^ 3 * C * (μ ^ 2 * eps ^ 2 / σ ^ 2 / 128) ^ 2 := by ring
      _ ≤ μ ^ 3 * C * C ^ 2 := by gcongr
  have hsum : K3' ≤ (16 * (128 ^ 3 * K3 + 1) + 2) * D ^ 3 := by
    have : 4 * (3 * σ ^ 3 * Bh + κ * C) = 4 * (3 * σ ^ 3 * Bh) + 4 * (κ * C) := by ring
    nlinarith
  -- `S2^{3/2} ≥ (δ/2)^{3/2} D³`
  have hS2pos : 0 ≤ δ / 2 * D ^ 2 := by positivity
  have hpow : (δ / 2) ^ ((3 : ℝ) / 2) * D ^ 3 ≤ S2 ^ ((3 : ℝ) / 2) := by
    have h1 : (δ / 2 * D ^ 2) ^ ((3 : ℝ) / 2) ≤ S2 ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow hS2pos hS2 (by norm_num)
    have h2 : (δ / 2 * D ^ 2) ^ ((3 : ℝ) / 2) = (δ / 2) ^ ((3 : ℝ) / 2) * D ^ 3 := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      rw [← Real.rpow_natCast D 2, ← Real.rpow_mul hDpos.le]
      norm_num
    rw [h2] at h1; exact h1
  have hcpos : 0 < (δ / 2) ^ ((3 : ℝ) / 2) := by positivity
  calc K3' ≤ (16 * (128 ^ 3 * K3 + 1) + 2) * D ^ 3 := hsum
    _ = (16 * (128 ^ 3 * K3 + 1) + 2) / (δ / 2) ^ ((3 : ℝ) / 2) *
          ((δ / 2) ^ ((3 : ℝ) / 2) * D ^ 3) := by field_simp
    _ ≤ (16 * (128 ^ 3 * K3 + 1) + 2) / (δ / 2) ^ ((3 : ℝ) / 2) * S2 ^ ((3 : ℝ) / 2) := by
        apply mul_le_mul_of_nonneg_left hpow
        have : 0 ≤ 16 * (128 ^ 3 * K3 + 1) + 2 := by positivity
        positivity

/-- Normalised second moment of the hyper-segment counts. -/
theorem class_count_bound {m C s2 M2 s2' K2 G : ℝ} (hm : 0 < m) (hC4 : 4 ≤ C)
    (hGC : G ≤ 128 * C) (hG : 0 ≤ G) (hM2 : M2 ≤ K2 * G ^ 2) (hK2 : 0 ≤ K2)
    (hs2' : s2' ≤ 2 * s2 * C + 2 * m ^ 2 * M2) (hs2 : 0 ≤ s2) :
    s2' / (m * C) ^ 2 ≤ (s2 / m ^ 2) / 2 + 2 * K2 * 128 ^ 2 := by
  have hCpos : 0 < C := by linarith
  have hmC : 0 < (m * C) ^ 2 := by positivity
  rw [div_le_iff₀ hmC]
  have h1 : 2 * s2 * C ≤ (s2 / m ^ 2) / 2 * (m * C) ^ 2 := by
    have : (s2 / m ^ 2) / 2 * (m * C) ^ 2 = s2 * C ^ 2 / 2 := by field_simp
    rw [this]
    have : 0 ≤ s2 * C * (C - 4) := mul_nonneg (mul_nonneg hs2 hCpos.le) (by linarith)
    nlinarith
  have h2 : 2 * m ^ 2 * M2 ≤ 2 * K2 * 128 ^ 2 * (m * C) ^ 2 := by
    have : M2 ≤ K2 * (128 * C) ^ 2 := le_trans hM2 (by gcongr)
    have : 2 * m ^ 2 * M2 ≤ 2 * m ^ 2 * (K2 * (128 * C) ^ 2) := by gcongr
    have e : 2 * m ^ 2 * (K2 * (128 * C) ^ 2) = 2 * K2 * 128 ^ 2 * (m * C) ^ 2 := by ring
    linarith
  have e : ((s2 / m ^ 2) / 2 + 2 * K2 * 128 ^ 2) * (m * C) ^ 2 =
      (s2 / m ^ 2) / 2 * (m * C) ^ 2 + 2 * K2 * 128 ^ 2 * (m * C) ^ 2 := by ring
  rw [e]; linarith

end PGM
