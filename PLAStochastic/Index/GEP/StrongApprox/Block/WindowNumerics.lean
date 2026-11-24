import PLAStochastic.Index.GEP.StrongApprox.Block.QuantileDefect
import PLAStochastic.Index.GEP.StrongApprox.Quantile.GaussianTailLower
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # WP5: uniform scalar conditions for logarithmic quantile windows -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Real

/-- The scalar conditions consumed by the proved actual block quantile estimates.
This structure is constructed below from a single eventual horizon threshold. -/
structure SABlockWindowInputs (C K r b S A₀ Y₀ E H d : ℝ) : Prop where
  horizon : 1 ≤ H
  large : 2 * C ≤ d
  local_window : (A₀ + Y₀) * Real.sqrt H ≤ r * d
  tail_window : Y₀ * Real.sqrt H ≤ r / 2 * d
  parent_window : A₀ * Real.sqrt H ≤ r / 2 * d
  error_nonneg : 0 ≤ E * H * Real.sqrt H / d
  error_small : E * H * Real.sqrt H / d ≤ 1 / 32
  quantile_window : ∀ σ : ℝ, 0 < σ → σ ≤ S * d →
    σ * (Real.sqrt (10 * H) + 1) ≤ d * (Y₀ * Real.sqrt H)
  density_tail : ∀ b' : ℝ, b ≤ b' →
    K * Real.exp (-b' * (Y₀ * Real.sqrt H) ^ 2) / (b' * (Y₀ * Real.sqrt H)) ≤
      (E * H * Real.sqrt H / d) * saGaussianTail (Real.sqrt (10 * H))
  gaussian_tail : ∀ σ : ℝ, 0 < σ → σ ≤ S * d →
    saGaussianTail (d * (Y₀ * Real.sqrt H) / σ) ≤
      (E * H * Real.sqrt H / d) * saGaussianTail (Real.sqrt (10 * H))
  defect : ∀ σ : ℝ, 0 < σ → σ ≤ S * d →
    32 * σ * (E * H * Real.sqrt H / d) ≤ 32 * S * E * H * Real.sqrt H

theorem sa_tendsto_square_exp_neg_eighth :
    Tendsto (fun H : ℝ => H ^ 2 * Real.exp (-(H / 8))) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (1 / 8) (by norm_num)
  convert h using 1
  funext H
  rw [Real.rpow_two]
  congr 1
  congr 1
  ring

theorem sa_tendsto_exp_neg_nine :
    Tendsto (fun H : ℝ => Real.exp (-(9 * H))) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 9 (by norm_num)
  simpa only [Real.rpow_zero, one_mul, neg_mul] using h

set_option maxHeartbeats 800000 in
/-- All numerical windows hold beyond one threshold, uniformly for every block
whose square-root size lies between `exp(H/8)` and `exp(H)`. -/
theorem exists_saBlockWindowInputs {C K r b S A₀ Y₀ E : ℝ}
    (hC : 0 < C) (hK : 0 < K) (hr : 0 < r) (hb : 0 < b) (hS : 0 < S)
    (hA : 0 ≤ A₀) (hY : 0 < Y₀) (hE : 1 ≤ E) (hEC : 2 * C ≤ E)
    (hwindow : S * (Real.sqrt 10 + 1) ≤ Y₀)
    (hrate : 20 ≤ b * Y₀ ^ 2) (hgaussrate : 40 * S ^ 2 ≤ Y₀ ^ 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∀ d : ℝ,
      Real.exp (H / 8) ≤ d → d ≤ Real.exp H → SABlockWindowInputs C K r b S A₀ Y₀ E H d := by
  let M := 3 * (A₀ + Y₀)
  let g := Real.exp (-1) / Real.sqrt (2 * π)
  have hM : 0 < M := by dsimp [M]; positivity
  have hg : 0 < g := by dsimp [g]; positivity
  have hevent : ∀ᶠ H : ℝ in atTop, 1 ≤ H ∧
      E * (H ^ 2 * Real.exp (-(H / 8))) ≤ 1 / 32 ∧
      M * (H ^ 2 * Real.exp (-(H / 8))) ≤ r ∧
      (K / (b * Y₀) + 1) * Real.exp (-(9 * H)) ≤ g := by
    have he0 : Tendsto (fun H : ℝ => E * (H ^ 2 * Real.exp (-(H / 8)))) atTop (𝓝 0) := by
      simpa only [mul_zero] using sa_tendsto_square_exp_neg_eighth.const_mul E
    have hw0 : Tendsto (fun H : ℝ => M * (H ^ 2 * Real.exp (-(H / 8)))) atTop (𝓝 0) := by
      simpa only [mul_zero] using sa_tendsto_square_exp_neg_eighth.const_mul M
    have ht0 : Tendsto (fun H : ℝ => (K / (b * Y₀) + 1) * Real.exp (-(9 * H))) atTop (𝓝 0) := by
      simpa only [mul_zero] using sa_tendsto_exp_neg_nine.const_mul (K / (b * Y₀) + 1)
    have he := he0.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 32)
    have hw := hw0.eventually_le_const hr
    have ht := ht0.eventually_le_const hg
    filter_upwards [eventually_ge_atTop (1 : ℝ), he, hw, ht] with H hH h1 h2 h3
    exact ⟨hH, by simpa using h1, by simpa using h2, by simpa using h3⟩
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp hevent
  refine ⟨max 1 H₀, le_max_left _ _, ?_⟩
  intro H hH d hdl hdu
  obtain ⟨hH1, he, hw, ht⟩ := hH₀ H ((le_max_right _ _).trans hH)
  have hH0 : 0 ≤ H := by linarith
  have hd : 0 < d := (Real.exp_pos _).trans_le hdl
  have hsH : 0 ≤ Real.sqrt H := Real.sqrt_nonneg H
  have hsH1 : 1 ≤ Real.sqrt H := by rw [Real.le_sqrt (by norm_num) hH0]; simpa using hH1
  have hsHsq : Real.sqrt H ^ 2 = H := Real.sq_sqrt hH0
  have hsHH : Real.sqrt H ≤ H := by nlinarith
  have hsH2 : Real.sqrt H ≤ H ^ 2 := by nlinarith
  have hHh : 1 ≤ H * Real.sqrt H := by nlinarith
  have hEH : 1 ≤ E * H * Real.sqrt H := by nlinarith
  have hpow : H * Real.sqrt H ≤ H ^ 2 := by nlinarith
  have herror : E * H * Real.sqrt H / d ≤ 1 / 32 := by
    calc
      _ ≤ E * H ^ 2 / Real.exp (H / 8) := by
        rw [mul_assoc E H]
        apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by linarith)) hd.le).trans
        exact div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hdl
      _ = E * (H ^ 2 * Real.exp (-(H / 8))) := by rw [Real.exp_neg]; ring
      _ ≤ _ := he
  have hMd : M * Real.sqrt H ≤ r * d := by
    have hm := mul_le_mul_of_nonneg_right hw (Real.exp_nonneg (H / 8))
    have hexp : Real.exp (-(H / 8)) * Real.exp (H / 8) = 1 := by rw [← Real.exp_add]; simp
    have hbound : M * H ^ 2 ≤ r * Real.exp (H / 8) := by
      calc
        _ = (M * (H ^ 2 * Real.exp (-(H / 8)))) * Real.exp (H / 8) := by
          calc
            _ = M * H ^ 2 * (Real.exp (-(H / 8)) * Real.exp (H / 8)) := by rw [hexp, mul_one]
            _ = _ := by ring
        _ ≤ _ := hm
    exact (mul_le_mul_of_nonneg_left hsH2 hM.le).trans
      (hbound.trans (mul_le_mul_of_nonneg_left hdl hr.le))
  have hlocal : (A₀ + Y₀) * Real.sqrt H ≤ r * d :=
    (mul_le_mul_of_nonneg_right (show A₀ + Y₀ ≤ M by dsimp [M]; linarith) hsH).trans hMd
  have htail : Y₀ * Real.sqrt H ≤ r / 2 * d := by
    have h1 := (mul_le_mul_of_nonneg_right (show 2 * Y₀ ≤ M by dsimp [M]; linarith) hsH).trans hMd
    nlinarith only [h1]
  have hparent : A₀ * Real.sqrt H ≤ r / 2 * d := by
    have h1 := (mul_le_mul_of_nonneg_right (show 2 * A₀ ≤ M by dsimp [M]; linarith) hsH).trans hMd
    nlinarith only [h1]
  have hlarge : 2 * C ≤ d := by
    rw [div_le_iff₀ hd] at herror
    have hEE := mul_le_mul_of_nonneg_left hHh (show 0 ≤ E by linarith)
    nlinarith only [herror, hEC, hEE, hd]
  have hepslower : Real.exp (-H) ≤ E * H * Real.sqrt H / d := by
    rw [le_div_iff₀ hd]
    have he1 : Real.exp (-H) * d ≤ 1 := by
      calc
        _ ≤ Real.exp (-H) * Real.exp H := mul_le_mul_of_nonneg_left hdu (Real.exp_nonneg _)
        _ = 1 := by rw [← Real.exp_add]; simp
    exact he1.trans hEH
  have hTlower : g * Real.exp (-(11 * H)) ≤
      (E * H * Real.sqrt H / d) * saGaussianTail (Real.sqrt (10 * H)) := by
    have ht0 := saGaussianTail_lower (Real.sqrt_nonneg (10 * H))
    rw [Real.sq_sqrt (by positivity)] at ht0
    calc
      _ = Real.exp (-H) * (g * Real.exp (-(10 * H))) := by
        have hid : Real.exp (-(11 * H)) = Real.exp (-H) * Real.exp (-(10 * H)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hid]
        ring
      _ ≤ _ := mul_le_mul hepslower ht0 (by positivity) (by positivity)
  have he20 : (K / (b * Y₀) + 1) * Real.exp (-(20 * H)) ≤ g * Real.exp (-(11 * H)) := by
    calc
      _ = ((K / (b * Y₀) + 1) * Real.exp (-(9 * H))) * Real.exp (-(11 * H)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ht (Real.exp_nonneg _)
  refine ⟨hH1, hlarge, hlocal, htail, hparent, by positivity, herror, ?_, ?_, ?_, ?_⟩
  · intro σ hσ hσd
    have hR : Real.sqrt (10 * H) + 1 ≤ (Real.sqrt 10 + 1) * Real.sqrt H := by
      rw [Real.sqrt_mul (by norm_num)]
      nlinarith
    calc
      _ ≤ (S * d) * ((Real.sqrt 10 + 1) * Real.sqrt H) := by gcongr
      _ = d * (S * (Real.sqrt 10 + 1)) * Real.sqrt H := by ring
      _ ≤ d * Y₀ * Real.sqrt H := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hwindow hd.le) hsH
      _ = _ := by ring
  · intro b' hbb
    have hb' : 0 < b' := hb.trans_le hbb
    have hden : b * Y₀ ≤ b' * (Y₀ * Real.sqrt H) := by
      calc
        _ ≤ b' * Y₀ := mul_le_mul_of_nonneg_right hbb hY.le
        _ ≤ (b' * Y₀) * Real.sqrt H := le_mul_of_one_le_right (by positivity) hsH1
        _ = _ := by ring
    have hexp : -(b' * (Y₀ * Real.sqrt H) ^ 2) ≤ -(20 * H) := by
      have hrate' : 20 ≤ b' * Y₀ ^ 2 := hrate.trans (mul_le_mul_of_nonneg_right hbb (sq_nonneg _))
      rw [mul_pow, hsHsq]
      nlinarith [mul_le_mul_of_nonneg_right hrate' hH0]
    apply le_trans _ hTlower
    apply le_trans _ he20
    calc
      _ ≤ K * Real.exp (-(20 * H)) / (b' * (Y₀ * Real.sqrt H)) := by
        gcongr
        simpa only [neg_mul] using hexp
      _ ≤ K * Real.exp (-(20 * H)) / (b * Y₀) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hb hY) hden
      _ = (K / (b * Y₀)) * Real.exp (-(20 * H)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
  · intro σ hσ hσd
    have hz : Y₀ * Real.sqrt H / S ≤ d * (Y₀ * Real.sqrt H) / σ := by
      calc
        _ = d * (Y₀ * Real.sqrt H) / (S * d) := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hσ hσd
    have hz0 : 0 ≤ Y₀ * Real.sqrt H / S := by positivity
    have hsq : 40 * H ≤ (Y₀ * Real.sqrt H / S) ^ 2 := by
      rw [div_pow, le_div_iff₀ (sq_pos_of_pos hS), mul_pow, hsHsq]
      nlinarith [mul_le_mul_of_nonneg_right hgaussrate hH0]
    have hsq' : 40 * H ≤ (d * (Y₀ * Real.sqrt H) / σ) ^ 2 :=
      hsq.trans (pow_le_pow_left₀ hz0 hz 2)
    apply (saGaussianTail_le_exp (by positivity)).trans
    apply le_trans _ hTlower
    apply le_trans _ he20
    calc
      _ ≤ Real.exp (-(20 * H)) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := le_mul_of_one_le_left (Real.exp_nonneg _)
        (by linarith [div_nonneg hK.le (mul_pos hb hY).le])
  · intro σ _ hσd
    calc
      _ ≤ 32 * (S * d) * (E * H * Real.sqrt H / d) := by gcongr
      _ = _ := by field_simp

end

end PGM
