import PLAStochastic.Index.OneLayer.Bracket
import PLAStochastic.Index.Endpoint.ClassArithmetic

/-!
# The threshold `ε₀(b, β)`

All "large `eps`" hypotheses of the one-layer bracket and of the class arithmetic
follow from the two class bounds `σ² ≤ b μ²`, `κ ≤ β σ³` once `eps` exceeds one
explicit threshold `epsZero b β`.  The threshold depends only on the class
parameters, never on the layer.
-/

namespace PGM

/-- `b₁ = max 1 b`, so that `σ ≤ b₁ μ` whenever `σ² ≤ b μ²`. -/
noncomputable def bOne (b : ℝ) : ℝ := max 1 b

noncomputable def epsZero (b β : ℝ) : ℝ :=
  1 + 10000 * bOne b + 2304 * β ^ 2 * bOne b + 8192 * bOne b ^ 2 / deltaVar +
    12 * 128 ^ 3 * Kh * bOne b ^ 6 + 4 * 128 ^ 2 * |β| * bOne b ^ 7

theorem deltaVar_pos : 0 < deltaVar := by unfold deltaVar; positivity

theorem Kh_nonneg : 0 ≤ Kh := by
  unfold Kh
  have : 0 ≤ Real.sqrt 5185 := Real.sqrt_nonneg _
  positivity

theorem one_le_bOne (b : ℝ) : 1 ≤ bOne b := le_max_left _ _

theorem le_bOne (b : ℝ) : b ≤ bOne b := le_max_right _ _

theorem largeConditions {μ σ κ b β eps : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) (hκ : 0 ≤ κ)
    (hv : σ ^ 2 ≤ b * μ ^ 2) (hβ : κ ≤ β * σ ^ 3) (heps : epsZero b β ≤ eps) :
    10000 ≤ μ ^ 2 * eps ^ 2 / σ ^ 2 ∧
      κ ^ 2 ≤ σ ^ 6 * (μ ^ 2 * eps ^ 2 / σ ^ 2 / 2304) ∧
      σ ^ 2 ≤ 1296 * eps * μ ^ 2 ∧
      σ ^ 4 ≤ 18 * eps ^ 2 * μ ^ 4 ∧
      8192 * σ ^ 4 ≤ deltaVar * μ ^ 4 * eps ^ 2 ∧
      12 * 128 ^ 3 * Kh * σ ^ 6 ≤ μ ^ 6 * eps ^ 3 ∧
      4 * 128 ^ 2 * β * σ ^ 7 ≤ μ ^ 7 * eps ^ 4 := by
  set b₁ := bOne b with hb₁
  have hb1 : 1 ≤ b₁ := one_le_bOne b
  have hbb : b ≤ b₁ := le_bOne b
  have hδ := deltaVar_pos
  have hKh := Kh_nonneg
  -- basic consequences of the threshold
  have hterms : 0 ≤ 2304 * β ^ 2 * b₁ ∧ 0 ≤ 8192 * b₁ ^ 2 / deltaVar ∧
      0 ≤ 12 * 128 ^ 3 * Kh * b₁ ^ 6 ∧ 0 ≤ 4 * 128 ^ 2 * |β| * b₁ ^ 7 := by
    refine ⟨by positivity, by positivity, by positivity, by positivity⟩
  obtain ⟨t1, t2, t3, t4⟩ := hterms
  have e0 : epsZero b β = 1 + 10000 * b₁ + 2304 * β ^ 2 * b₁ + 8192 * b₁ ^ 2 / deltaVar +
      12 * 128 ^ 3 * Kh * b₁ ^ 6 + 4 * 128 ^ 2 * |β| * b₁ ^ 7 := rfl
  rw [e0] at heps
  have heps1 : 1 ≤ eps := by linarith
  have hepspos : 0 < eps := by linarith
  have hepsA : 10000 * b₁ ≤ eps := by linarith
  have hepsB : 2304 * β ^ 2 * b₁ ≤ eps := by linarith
  have hepsC : 8192 * b₁ ^ 2 / deltaVar ≤ eps := by linarith
  have hepsD : 12 * 128 ^ 3 * Kh * b₁ ^ 6 ≤ eps := by linarith
  have hepsE : 4 * 128 ^ 2 * |β| * b₁ ^ 7 ≤ eps := by linarith
  have hb1eps : b₁ ≤ eps := by linarith
  have heps2 : eps ≤ eps ^ 2 := by simpa using pow_le_pow_right₀ heps1 (show 1 ≤ 2 by norm_num)
  have heps3 : eps ≤ eps ^ 3 := by simpa using pow_le_pow_right₀ heps1 (show 1 ≤ 3 by norm_num)
  have heps4 : eps ≤ eps ^ 4 := by simpa using pow_le_pow_right₀ heps1 (show 1 ≤ 4 by norm_num)
  -- σ² ≤ b₁ μ² and σ ≤ b₁ μ
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hv1' : σ ^ 2 ≤ b₁ * μ ^ 2 := le_trans hv (by gcongr)
  have hσμ : σ ≤ b₁ * μ := by
    have : σ ^ 2 ≤ (b₁ * μ) ^ 2 := by
      calc σ ^ 2 ≤ b₁ * μ ^ 2 := hv1'
        _ ≤ b₁ ^ 2 * μ ^ 2 := by gcongr; exact le_self_pow₀ hb1 two_ne_zero
        _ = (b₁ * μ) ^ 2 := by ring
    exact (sq_le_sq₀ hσ.le (by positivity)).1 this
  have hσ2pos : 0 < σ ^ 2 := by positivity
  -- G ≥ eps² / b₁
  have hG : eps ^ 2 / b₁ ≤ μ ^ 2 * eps ^ 2 / σ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hσ2pos]
    calc eps ^ 2 * σ ^ 2 ≤ eps ^ 2 * (b₁ * μ ^ 2) := mul_le_mul_of_nonneg_left hv1' (sq_nonneg _)
      _ = μ ^ 2 * eps ^ 2 * b₁ := by ring
  have hGeps : eps / b₁ ≤ μ ^ 2 * eps ^ 2 / σ ^ 2 := by
    refine le_trans ?_ hG
    exact div_le_div_of_nonneg_right heps2 (by positivity)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 10000 ≤ G
    refine le_trans ?_ hGeps
    rw [le_div_iff₀ (by positivity)]; linarith
  · -- κ² ≤ σ⁶ G / 2304
    have hκβ : κ ^ 2 ≤ β ^ 2 * σ ^ 6 := by
      calc κ ^ 2 ≤ (β * σ ^ 3) ^ 2 := pow_le_pow_left₀ hκ hβ 2
        _ = β ^ 2 * σ ^ 6 := by ring
    have hβG : β ^ 2 ≤ μ ^ 2 * eps ^ 2 / σ ^ 2 / 2304 := by
      have hβ1 : β ^ 2 ≤ (eps / b₁) / 2304 := by
        rw [div_div, le_div_iff₀ (by positivity)]
        linarith [hepsB, show β ^ 2 * (b₁ * 2304) = 2304 * β ^ 2 * b₁ by ring]
      exact le_trans hβ1 (div_le_div_of_nonneg_right hGeps (by norm_num))
    calc κ ^ 2 ≤ β ^ 2 * σ ^ 6 := hκβ
      _ = σ ^ 6 * β ^ 2 := by ring
      _ ≤ σ ^ 6 * (μ ^ 2 * eps ^ 2 / σ ^ 2 / 2304) := by gcongr
  · -- σ² ≤ 1296 eps μ²
    calc σ ^ 2 ≤ b₁ * μ ^ 2 := hv1'
      _ ≤ 1296 * eps * μ ^ 2 := by gcongr; linarith
  · -- σ⁴ ≤ 18 eps² μ⁴
    have : σ ^ 4 ≤ (b₁ * μ ^ 2) ^ 2 := by
      have := pow_le_pow_left₀ hσ2pos.le hv1' 2
      calc σ ^ 4 = (σ ^ 2) ^ 2 := by ring
        _ ≤ _ := this
    calc σ ^ 4 ≤ (b₁ * μ ^ 2) ^ 2 := this
      _ = b₁ ^ 2 * μ ^ 4 := by ring
      _ ≤ 18 * eps ^ 2 * μ ^ 4 := by
          gcongr
          calc b₁ ^ 2 ≤ eps ^ 2 := pow_le_pow_left₀ (by linarith) hb1eps 2
            _ ≤ 18 * eps ^ 2 := by linarith [sq_nonneg eps]
  · -- 8192 σ⁴ ≤ δ μ⁴ eps²
    have hs4 : σ ^ 4 ≤ b₁ ^ 2 * μ ^ 4 := by
      calc σ ^ 4 = (σ ^ 2) ^ 2 := by ring
        _ ≤ (b₁ * μ ^ 2) ^ 2 := pow_le_pow_left₀ hσ2pos.le hv1' 2
        _ = b₁ ^ 2 * μ ^ 4 := by ring
    have hC' : 8192 * b₁ ^ 2 ≤ deltaVar * eps := by
      have := hepsC; rw [div_le_iff₀ hδ] at this; linarith
    calc 8192 * σ ^ 4 ≤ 8192 * (b₁ ^ 2 * μ ^ 4) := by gcongr
      _ = (8192 * b₁ ^ 2) * μ ^ 4 := by ring
      _ ≤ (deltaVar * eps) * μ ^ 4 := by gcongr
      _ ≤ (deltaVar * eps ^ 2) * μ ^ 4 := by gcongr
      _ = deltaVar * μ ^ 4 * eps ^ 2 := by ring
  · -- 12·128³ Kh σ⁶ ≤ μ⁶ eps³
    have hs6 : σ ^ 6 ≤ (b₁ * μ) ^ 6 := pow_le_pow_left₀ hσ.le hσμ 6
    calc 12 * 128 ^ 3 * Kh * σ ^ 6 ≤ 12 * 128 ^ 3 * Kh * (b₁ * μ) ^ 6 := by gcongr
      _ = (12 * 128 ^ 3 * Kh * b₁ ^ 6) * μ ^ 6 := by ring
      _ ≤ eps * μ ^ 6 := by gcongr
      _ ≤ eps ^ 3 * μ ^ 6 := by gcongr
      _ = μ ^ 6 * eps ^ 3 := by ring
  · -- 4·128² β σ⁷ ≤ μ⁷ eps⁴
    have hs7 : σ ^ 7 ≤ (b₁ * μ) ^ 7 := pow_le_pow_left₀ hσ.le hσμ 7
    have hβabs : β ≤ |β| := le_abs_self β
    calc 4 * 128 ^ 2 * β * σ ^ 7 ≤ 4 * 128 ^ 2 * |β| * σ ^ 7 := by gcongr
      _ ≤ 4 * 128 ^ 2 * |β| * (b₁ * μ) ^ 7 := by gcongr
      _ = (4 * 128 ^ 2 * |β| * b₁ ^ 7) * μ ^ 7 := by ring
      _ ≤ eps * μ ^ 7 := by gcongr
      _ ≤ eps ^ 4 * μ ^ 7 := by gcongr
      _ = μ ^ 7 * eps ^ 4 := by ring

end PGM
