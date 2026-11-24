import PLAStochastic.Swing.DenseSampling.CarriedPrefix.TruncatedLogMean

/-! # Uniform scalar comparison between boundary tails and logarithmic means -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

private theorem carried_log_ratio_eq {H d : ℝ} (hH : 0 < H) (hd : 0 < d) :
    Real.log (H/(8*d)) = Real.log (H/8)-Real.log d := by
  have heq : H/(8*d) = (H/8)/d := by ring
  rw [heq, Real.log_div (by positivity) hd.ne']

/-- At logarithmic mesh scale L, the comparison is uniform over every starting
distance between exp(-L/2) and a fixed sufficiently small delta. -/
theorem exists_carried_ratio_log_cutoff {H A c β : ℝ}
    (hH : 0 < H) (hA : 0 < A) (hc : 0 < c) (hβ : 0 < β) :
    ∃ δ K : ℝ, 0 < δ ∧ 8*δ < H ∧ 0 < K ∧ ∀ L : ℝ, K ≤ L → ∀ d : ℝ,
      Real.exp (-L/2) ≤ d → d ≤ δ →
      A*(d+Real.exp (-L/2)*Real.sqrt (8*L)) ≤ β*c*d*Real.log (H/(8*d)) := by
  let B := β*c/A
  have hB : 0 < B := div_pos (mul_pos hβ hc) hA
  let δ := (H/8)*Real.exp (-2/B)
  have hδ : 0 < δ := mul_pos (by positivity) (Real.exp_pos _)
  have hδH : 8*δ < H := by
    have he : Real.exp (-2/B) < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hB)
    have hm := mul_lt_mul_of_pos_left he hH
    dsimp only [δ]
    nlinarith
  let K := 128+8*|Real.log (H/8)|+16/B+2048/B^2
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨δ, K, hδ, hδH, hK, ?_⟩
  intro L hKL d had hdδ
  have hL : 0 < L := hK.trans_le hKL
  have hd : 0 < d := (Real.exp_pos _).trans_le had
  have h128 : 128 ≤ L := by
    dsimp only [K] at hKL
    nlinarith [abs_nonneg (Real.log (H/8)),
      div_nonneg (by norm_num : (0 : ℝ) ≤ 16) hB.le,
      div_nonneg (by norm_num : (0 : ℝ) ≤ 2048) (sq_nonneg B)]
  have hlogH : -8*Real.log (H/8) ≤ L := by
    have hh := neg_le_abs (Real.log (H/8))
    dsimp only [K] at hKL
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 16) hB.le,
      div_nonneg (by norm_num : (0 : ℝ) ≤ 2048) (sq_nonneg B)]
  have h16 : 16/B ≤ L := by
    dsimp only [K] at hKL
    nlinarith [abs_nonneg (Real.log (H/8)), div_nonneg (by norm_num : (0 : ℝ) ≤ 2048) (sq_nonneg B)]
  have h2048 : 2048/B^2 ≤ L := by
    dsimp only [K] at hKL
    nlinarith [abs_nonneg (Real.log (H/8)), div_nonneg (by norm_num : (0 : ℝ) ≤ 16) hB.le]
  have hB16 : 16 ≤ B*L := by
    have hh := (div_le_iff₀ hB).mp h16
    nlinarith
  have hB2048 : 2048 ≤ B^2*L := by
    have hh := (div_le_iff₀ (sq_pos_of_pos hB)).mp h2048
    nlinarith
  have hs := Real.sqrt_nonneg (8*L)
  have hsq := Real.sq_sqrt (show 0 ≤ 8*L by positivity)
  have hsB : Real.sqrt (8*L) ≤ B*L/16 := by
    have hm := mul_le_mul_of_nonneg_right hB2048 hL.le
    nlinarith
  have hsL : Real.sqrt (8*L) ≤ L/4 := by nlinarith
  have hδlog : Real.log δ = Real.log (H/8)-2/B := by
    dsimp only [δ]
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hlower : 2/B ≤ Real.log (H/(8*d)) := by
    rw [carried_log_ratio_eq hH hd]
    have hm := Real.log_le_log hd hdδ
    rw [hδlog] at hm
    linarith
  by_cases hdcut : d ≤ Real.exp (-L/4)
  · have hsmallLog : L/8 ≤ Real.log (H/(8*d)) := by
      rw [carried_log_ratio_eq hH hd]
      have hm := Real.log_le_log hd hdcut
      rw [Real.log_exp] at hm
      linarith
    have hn : 1+Real.sqrt (8*L) ≤ B*L/8 := by linarith
    have hnum : d+Real.exp (-L/2)*Real.sqrt (8*L) ≤ d*(B*L/8) := by
      have h1 := mul_le_mul_of_nonneg_right had hs
      have h2 := mul_le_mul_of_nonneg_left hn hd.le
      nlinarith
    calc
      _ ≤ A*(d*(B*L/8)) := mul_le_mul_of_nonneg_left hnum hA.le
      _ ≤ A*(d*(B*Real.log (H/(8*d)))) := by
        apply mul_le_mul_of_nonneg_left _ hA.le
        apply mul_le_mul_of_nonneg_left _ hd.le
        nlinarith [mul_le_mul_of_nonneg_left hsmallLog hB.le]
      _ = _ := by dsimp only [B]; field_simp
  · have he : Real.sqrt (8*L) ≤ Real.exp (L/4) := by
      linarith [Real.add_one_le_exp (L/4)]
    have hρ : Real.exp (-L/2)*Real.sqrt (8*L) ≤ d := by
      calc
        _ ≤ Real.exp (-L/2)*Real.exp (L/4) := mul_le_mul_of_nonneg_left he (Real.exp_nonneg _)
        _ = Real.exp (-L/4) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ d := le_of_not_ge hdcut
    calc
      _ ≤ A*(2*d) := by nlinarith
      _ = A*(d*(B*(2/B))) := by field_simp
      _ ≤ A*(d*(B*Real.log (H/(8*d)))) := by gcongr
      _ = _ := by dsimp only [B]; field_simp

/-- Returning from L=log(1/h) gives the uniform small-mesh comparison required
for the entire range sqrt(h)≤d≤delta, including its moving lower endpoint. -/
theorem exists_carried_ratio_mesh_cutoff {H A c β : ℝ}
    (hH : 0 < H) (hA : 0 < A) (hc : 0 < c) (hβ : 0 < β) :
    ∃ δ h₀ : ℝ, 0 < δ ∧ 8*δ < H ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ d : ℝ, Real.sqrt h ≤ d → d ≤ δ →
      A*(d+brownianGridLogRadius h) ≤ β*c*d*Real.log (H/(8*d)) := by
  obtain ⟨δ, K, hδ, hδH, hK, hb⟩ := exists_carried_ratio_log_cutoff hH hA hc hβ
  refine ⟨δ, Real.exp (-K), hδ, hδH, Real.exp_pos _,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hK.le), ?_⟩
  intro h hh hhk d hsd hdδ
  let L := Real.log (1/h)
  have hLid : L = -Real.log h := by simp only [L, one_div, Real.log_inv]
  have hLK : K ≤ L := by
    have hl := Real.log_le_log hh hhk
    rw [Real.log_exp] at hl
    rw [hLid]
    linarith
  have hL0 : 0 < L := hK.trans_le hLK
  have heq : Real.exp (-L/2) = Real.sqrt h := by
    have hs : Real.exp (-L/2)^2 = h := by
      rw [pow_two, ← Real.exp_add]
      have hi : -L/2+-L/2 = Real.log h := by rw [hLid]; ring
      rw [hi, Real.exp_log hh]
    nlinarith [Real.exp_pos (-L/2), Real.sqrt_nonneg h, Real.sq_sqrt hh.le]
  have hρ : Real.exp (-L/2)*Real.sqrt (8*L) = brownianGridLogRadius h := by
    rw [heq, ← Real.sqrt_mul hh.le]
    unfold brownianGridLogRadius
    congr 1
    dsimp only [L]
    ring
  have hr := hb L hLK d (by rwa [heq]) hdδ
  rwa [hρ] at hr

end SwingRepair
