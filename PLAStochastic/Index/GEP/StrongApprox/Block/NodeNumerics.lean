import PLAStochastic.Index.GEP.StrongApprox.Block.WindowNumerics

/-! # WP5: choosing constants and bounding the window error polynomial -/

namespace PGM

noncomputable section

open scoped Real

def saNodeErrorConstant (C L T A Y : ℝ) : ℝ :=
  1 + 6 * C + L / 2 * (3 * A + 2 * Y) + T * (A * Y ^ 2 + Y ^ 3 / 3)

theorem saNodeErrorConstant_bounds {C L T A Y : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hT : 0 ≤ T) (hA : 0 ≤ A) (hY : 0 ≤ Y) :
    1 ≤ saNodeErrorConstant C L T A Y ∧ 2 * C ≤ saNodeErrorConstant C L T A Y := by
  unfold saNodeErrorConstant
  have hp : 0 ≤ L / 2 * (3 * A + 2 * Y) := by positivity
  have hq : 0 ≤ T * (A * Y ^ 2 + Y ^ 3 / 3) := by positivity
  constructor <;> linarith

theorem exists_saNodeWindow {b S : ℝ} (hb : 0 < b) (hS : 0 < S) :
    ∃ Y : ℝ, 0 < Y ∧ S * (Real.sqrt 10 + 1) ≤ Y ∧
      20 ≤ b * Y ^ 2 ∧ 40 * S ^ 2 ≤ Y ^ 2 := by
  let Y := 1 + S * (Real.sqrt 10 + 1) + Real.sqrt (20 / b) + Real.sqrt (40 * S ^ 2)
  have hY : 0 < Y := by dsimp [Y]; positivity
  have h1 : S * (Real.sqrt 10 + 1) ≤ Y := by
    dsimp [Y]; linarith [Real.sqrt_nonneg (20 / b), Real.sqrt_nonneg (40 * S ^ 2)]
  have h2 : Real.sqrt (20 / b) ≤ Y := by
    dsimp [Y]; nlinarith [Real.sqrt_nonneg 10, Real.sqrt_nonneg (40 * S ^ 2)]
  have h3 : Real.sqrt (40 * S ^ 2) ≤ Y := by
    dsimp [Y]; nlinarith [Real.sqrt_nonneg 10, Real.sqrt_nonneg (20 / b)]
  refine ⟨Y, hY, h1, ?_, ?_⟩
  · have he := pow_le_pow_left₀ (Real.sqrt_nonneg (20 / b)) h2 2
    rw [Real.sq_sqrt (by positivity)] at he
    simpa only [mul_comm] using (div_le_iff₀ hb).mp he
  · have he := pow_le_pow_left₀ (Real.sqrt_nonneg (40 * S ^ 2)) h3 2
    rwa [Real.sq_sqrt (by positivity)] at he

/-- The cubic local error polynomial has the advertised `H sqrt(H)` growth. -/
theorem saNodeError_polynomial {C L T A Y H : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hT : 0 ≤ T) (hA : 0 ≤ A) (hY : 0 ≤ Y) (hH : 1 ≤ H) :
    6 * C + L / 2 * (3 * (A * Real.sqrt H) + 2 * (Y * Real.sqrt H)) +
        T * ((A * Real.sqrt H) * (Y * Real.sqrt H) ^ 2 + (Y * Real.sqrt H) ^ 3 / 3) ≤
      saNodeErrorConstant C L T A Y * H * Real.sqrt H := by
  have hH0 : 0 ≤ H := by linarith
  have hs : 0 ≤ Real.sqrt H := Real.sqrt_nonneg H
  have hs1 : 1 ≤ Real.sqrt H := by rw [Real.le_sqrt (by norm_num) hH0]; simpa using hH
  have hHH : 1 ≤ H * Real.sqrt H := by nlinarith
  have hsH : Real.sqrt H ≤ H * Real.sqrt H := by nlinarith
  have hs3 : Real.sqrt H ^ 3 = H * Real.sqrt H := by rw [pow_succ, Real.sq_sqrt hH0]
  let P := L / 2 * (3 * A + 2 * Y)
  let Q := T * (A * Y ^ 2 + Y ^ 3 / 3)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  calc
    _ = 6 * C + P * Real.sqrt H + Q * Real.sqrt H ^ 3 := by dsimp [P, Q]; ring
    _ = 6 * C + P * Real.sqrt H + Q * (H * Real.sqrt H) := by rw [hs3]
    _ ≤ (6 * C) * (H * Real.sqrt H) + P * (H * Real.sqrt H) + Q * (H * Real.sqrt H) := by
      exact add_le_add (add_le_add
        (by simpa using mul_le_mul_of_nonneg_left hHH (by positivity : 0 ≤ 6 * C))
        (mul_le_mul_of_nonneg_left hsH hP)) le_rfl
    _ ≤ _ := by
      dsimp [saNodeErrorConstant, P, Q]
      nlinarith only [hHH]

theorem saNodeError_root_le_split {C L T A Y : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hT : 0 ≤ T) (hA : 0 ≤ A) (hY : 0 ≤ Y) :
    2 * C + L / 2 * Y + T * Y ^ 3 / 6 ≤
      6 * C + L / 2 * (3 * A + 2 * Y) + T * (A * Y ^ 2 + Y ^ 3 / 3) := by
  have hn : 0 ≤ 4 * C + L / 2 * (3 * A + Y) + T * (A * Y ^ 2 + Y ^ 3 / 6) := by positivity
  nlinarith only [hn]

/-- Exponential bounds on the block length imply the scalar square-root range. -/
theorem sa_sqrt_block_range {l : ℕ} (hl : 2 ≤ l) {H : ℝ}
    (hlo : Real.exp (H / 4) ≤ (l : ℝ)) (hhi : (l : ℝ) ≤ Real.exp H) :
    Real.exp (H / 8) ≤ Real.sqrt l ∧ Real.sqrt l ≤ Real.exp H := by
  have hlr : 1 ≤ (l : ℝ) := by exact_mod_cast (show 1 ≤ l by omega)
  constructor
  · rw [Real.le_sqrt (Real.exp_nonneg _) (Nat.cast_nonneg l), ← Real.exp_nat_mul]
    convert hlo using 1
    congr 1
    norm_num
    ring
  · have hsq := Real.sq_sqrt (Nat.cast_nonneg l)
    have hs := Real.sqrt_nonneg (l : ℝ)
    exact (show Real.sqrt (l : ℝ) ≤ (l : ℝ) by nlinarith).trans hhi

end

end PGM
