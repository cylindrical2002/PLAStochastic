import PLAStochastic.Index.CEPS.Scaled.CanonWeight
import PLAStochastic.Index.CEPS.Scaled.QuotientCurve

/-! # A first-order root-gap budget for the canonical surrogate ratio -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledSurrogatePi {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  cepsCanonSurrogateWeight dom ρW N (b * lam) (cepsComplexScaledDiscount lam z b)
      (b * cepsScaledSignedRoot D θ ρW lam z 1 b) /
    cepsCanonSurrogateWeight dom ρW N (b * lam) (cepsComplexScaledDiscount lam z b)
      (b * cepsScaledSignedRoot D θ ρW lam z (-1) b)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsCanonSurrogateWeight_ratio_sub_one_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {μ q p n : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀ / 8) (hq : ‖q‖ < dom.q₀ / 2)
    (hp : ‖p‖ ≤ dom.c₀ / 4) (hn : ‖n‖ ≤ dom.c₀ / 4) :
    ‖cepsCanonSurrogateWeight dom ρW N μ q p /
        cepsCanonSurrogateWeight dom ρW N μ q n - 1‖ ≤
      dom.canonSurrogatePiBound N M * ‖p - n‖ := by
  let F := cepsCanonSurrogateWeight dom ρW N μ q
  let B := dom.canonDriftTaylorBound N M (dom.μ₀ / 8)
  have hd : ∀ ζ ∈ closedBall (0 : ℂ) (dom.c₀ / 4), DifferentiableAt ℂ F ζ := by
    intro ζ hζ
    have hz : ζ ∈ ball (0 : ℂ) (dom.c₀ / 2) := mem_ball_zero_iff.mpr (by
      have := mem_closedBall_zero_iff.mp hζ
      linarith [dom.c₀_pos])
    exact ((cepsCanonSurrogateWeight_differentiableOn dom hW hθ hD hf hη N hN hμ hq) ζ hz).differentiableAt
      (isOpen_ball.mem_nhds hz)
  have hdiff := (convex_closedBall (0 : ℂ) (dom.c₀ / 4)).norm_image_sub_le_of_norm_deriv_le
    (f := F) hd
    (fun ζ hζ => cepsCanonSurrogateWeight_deriv_bound dom hW hθ hD hf hη hM N hN hμ hq
      (mem_closedBall_zero_iff.mp hζ))
    (mem_closedBall_zero_iff.mpr hn) (mem_closedBall_zero_iff.mpr hp)
  have hlow := (cepsCanonSurrogateWeight_bounds dom hW hθ hD hf hη hM N hN hμ hq.le
    (show ‖n‖ ≤ dom.c₀ / 2 by linarith [dom.c₀_pos])).1
  change cepsVarLo D / 4 * Real.exp (-2 * B) ≤ ‖F n‖ at hlow
  have hlo0 : 0 < cepsVarLo D / 4 * Real.exp (-2 * B) :=
    mul_pos (div_pos (cepsVarLo_pos hD) (by norm_num)) (Real.exp_pos _)
  have hFn : F n ≠ 0 := norm_pos_iff.mp (hlo0.trans_le hlow)
  have hfactor : dom.canonSurrogatePiBound N M *
      (cepsVarLo D / 4 * Real.exp (-2 * B)) =
      16 * (v * Real.exp (2 * B)) / dom.c₀ := by
    have hexp : Real.exp (4 * B) * Real.exp (-2 * B) = Real.exp (2 * B) := by
      rw [← Real.exp_add]; congr 1; ring
    have hvl := (cepsVarLo_pos hD).ne'
    have hc := dom.c₀_pos.ne'
    unfold CepsCanonDomain.canonSurrogatePiBound
    change 64 * v / (dom.c₀ * cepsVarLo D) * Real.exp (4 * B) *
      (cepsVarLo D / 4 * Real.exp (-2 * B)) = _
    calc
      _ = (16 * v / dom.c₀) * (Real.exp (4 * B) * Real.exp (-2 * B)) := by field_simp; ring
      _ = _ := by rw [hexp]; ring
  have hmul : ‖F p / F n - 1‖ * (cepsVarLo D / 4 * Real.exp (-2 * B)) ≤
      (dom.canonSurrogatePiBound N M * ‖p - n‖) * (cepsVarLo D / 4 * Real.exp (-2 * B)) := by
    calc
      _ ≤ ‖F p / F n - 1‖ * ‖F n‖ := mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
      _ = ‖F p - F n‖ := by
        rw [div_sub_one hFn, norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hFn)]
      _ ≤ _ := hdiff
      _ = _ := by rw [mul_right_comm (dom.canonSurrogatePiBound N M), hfactor]
  exact le_of_mul_le_mul_right hmul hlo0

include hW hθ hD in
theorem cepsScaledRootCurve_norm_le (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) :
    ‖b * cepsScaledSignedRoot D θ ρW lam z 1 b‖ ≤ dom.c₀ / 4 ∧
      ‖b * cepsScaledSignedRoot D θ ρW lam z (-1) b‖ ≤ dom.c₀ / 4 := by
  obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hb
  have hμ' : ‖b * (lam : ℂ)‖ ≤ dom.μ₀ := hμ.le.trans (by linarith [dom.μ₀_pos])
  have hq' : ‖cepsComplexScaledDiscount lam z b‖ ≤ dom.q₀ := hq.le.trans (half_le_self dom.q₀_pos.le)
  have hp := dom.norm_rootPlus_le hW hθ hD hμ' hq'
  have hm := dom.norm_rootMinus_le hW hθ hD hμ' hq'
  rcases cepsScaledRootCurve_pair dom hW hθ hD lam hz hb with he | he
  · have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
    dsimp only at h1 h2
    exact ⟨by rw [h1]; exact hp, by rw [h2]; exact hm⟩
  · have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
    dsimp only at h1 h2
    exact ⟨by rw [h1]; exact hm, by rw [h2]; exact hp⟩

include hW hθ hD in
theorem cepsScaledSurrogatePi_sub_one_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) :
    ‖cepsScaledSurrogatePi dom ρW N lam z b - 1‖ ≤
      dom.canonSurrogatePiBound N M * ‖b‖ *
        ‖cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b‖ := by
  obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hb
  obtain ⟨hp, hn⟩ := cepsScaledRootCurve_norm_le dom hW hθ hD lam hz hb
  have h := cepsCanonSurrogateWeight_ratio_sub_one_le dom hW hθ hD hf hη hM N hN hμ.le hq hp hn
  simpa only [cepsScaledSurrogatePi, ← mul_sub, norm_mul, mul_assoc] using h

end PGM
