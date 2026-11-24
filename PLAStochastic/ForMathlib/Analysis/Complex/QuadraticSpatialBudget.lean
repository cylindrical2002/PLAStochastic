import PLAStochastic.ForMathlib.Analysis.Complex.QuadraticExpUnit
import Mathlib.Analysis.Asymptotics.Lemmas

/-! # Uniform finite-jet errors of quadratic spatial exponential units -/

noncomputable section
open Complex Set Metric Filter Topology Asymptotics
namespace PGM

theorem quadraticSpatialUnit_difference_budget {H P : ℂ → ℂ}
    (hH : ContinuousAt H 0) (hP : ContinuousAt P 0) (N : ℕ)
    (he : (fun s => H s - P s) =O[𝓝 (0 : ℂ)] (fun s => s ^ (N + 1)))
    (lam z : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 < B ∧ ∀ {b ξ : ℂ}, b ∈ ball (0 : ℂ) B → ξ ∈ ball 0 R →
      ‖quadraticExpUnit b (ξ ^ 2 * H (b * ξ) + lam * ξ - z * (1 + b * lam)) -
        quadraticExpUnit b (ξ ^ 2 * P (b * ξ) + lam * ξ - z * (1 + b * lam))‖ ≤
        C * ‖b‖ ^ (N + 1) := by
  obtain ⟨K, hK, hKe⟩ := he.exists_nonneg
  have hHb : ∀ᶠ s : ℂ in 𝓝 0, ‖H s‖ < ‖H 0‖ + 1 :=
    hH.norm.eventually (gt_mem_nhds (show ‖H 0‖ < ‖H 0‖ + 1 by linarith))
  have hPb : ∀ᶠ s : ℂ in 𝓝 0, ‖P s‖ < ‖P 0‖ + 1 :=
    hP.norm.eventually (gt_mem_nhds (show ‖P 0‖ < ‖P 0‖ + 1 by linarith))
  obtain ⟨δ, hδ, hδe⟩ := Metric.mem_nhds_iff.mp (hHb.and (hPb.and hKe.bound))
  let B : ℝ := min 1 (δ / (R + 1)) / 2
  let L : ℝ := max (‖H 0‖ + 1) (‖P 0‖ + 1)
  let A : ℝ := R ^ 2 * L + ‖lam‖ * R + ‖z‖ * (1 + ‖lam‖)
  refine ⟨Real.exp A * R ^ 2 * K * R ^ (N + 1), B, by positivity, by dsimp [B]; positivity, ?_⟩
  intro b ξ hb hξ
  have hbn : ‖b‖ < B := mem_ball_zero_iff.mp hb
  have hξn : ‖ξ‖ ≤ R := (mem_ball_zero_iff.mp hξ).le
  have hb1 : ‖b‖ ≤ 1 := by dsimp [B] at hbn; linarith [min_le_left 1 (δ / (R + 1))]
  have hbs : b * ξ ∈ ball (0 : ℂ) δ := by
    rw [mem_ball_zero_iff, norm_mul]
    have hBδ : B * R < δ := by
      have hh : min 1 (δ / (R + 1)) ≤ δ / (R + 1) := min_le_right _ _
      have hh' : min 1 (δ / (R + 1)) * (R + 1) ≤ δ := (le_div_iff₀ (by linarith)).mp hh
      dsimp [B]
      nlinarith [le_of_lt (show 0 < min 1 (δ / (R + 1)) by positivity)]
    exact (mul_le_mul hbn.le hξn (norm_nonneg _) (by dsimp [B]; positivity)).trans_lt hBδ
  have hedata := hδe hbs
  simp only [norm_pow] at hedata
  have hHL : ‖H (b * ξ)‖ ≤ L := hedata.1.le.trans (le_max_left _ _)
  have hPL : ‖P (b * ξ)‖ ≤ L := hedata.2.1.le.trans (le_max_right _ _)
  have hTL (J : ℂ → ℂ) (hJL : ‖J (b * ξ)‖ ≤ L) :
      ‖ξ ^ 2 * J (b * ξ) + lam * ξ - z * (1 + b * lam)‖ ≤ A := by
    calc
      _ ≤ ‖ξ ^ 2 * J (b * ξ)‖ + ‖lam * ξ‖ + ‖z * (1 + b * lam)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖ξ‖ ^ 2 * ‖J (b * ξ)‖ + ‖lam‖ * ‖ξ‖ + ‖z‖ * ‖1 + b * lam‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_pow]
      _ ≤ R ^ 2 * L + ‖lam‖ * R + ‖z‖ * (1 + ‖lam‖) := by
        gcongr
        calc
          ‖1 + b * lam‖ ≤ ‖(1 : ℂ)‖ + ‖b * lam‖ := norm_add_le _ _
          _ ≤ 1 + 1 * ‖lam‖ := by rw [norm_one, norm_mul]; gcongr
          _ = 1 + ‖lam‖ := by ring
      _ = A := rfl
  have hdiff : ‖(ξ ^ 2 * H (b * ξ) + lam * ξ - z * (1 + b * lam)) -
      (ξ ^ 2 * P (b * ξ) + lam * ξ - z * (1 + b * lam))‖ ≤
      R ^ 2 * K * R ^ (N + 1) * ‖b‖ ^ (N + 1) := by
    rw [show (ξ ^ 2 * H (b * ξ) + lam * ξ - z * (1 + b * lam)) -
      (ξ ^ 2 * P (b * ξ) + lam * ξ - z * (1 + b * lam)) = ξ ^ 2 * (H (b * ξ) - P (b * ξ)) by ring,
      norm_mul, norm_pow]
    calc
      _ ≤ R ^ 2 * (K * ‖b * ξ‖ ^ (N + 1)) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hξn 2)
          hedata.2.2 (norm_nonneg _) (by positivity)
      _ ≤ R ^ 2 * (K * (‖b‖ * R) ^ (N + 1)) := by rw [norm_mul]; gcongr
      _ = _ := by rw [mul_pow]; ring
  exact (quadraticExpUnit_lipschitz hb1 (hTL H hHL) (hTL P hPL)).trans
    ((mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le).trans_eq (by ring))

end PGM
