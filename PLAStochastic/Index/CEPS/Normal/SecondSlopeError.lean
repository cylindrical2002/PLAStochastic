import PLAStochastic.Index.CEPS.Normal.SecondSlopeBound
import PLAStochastic.Index.CEPS.Normal.SlopeCongr
import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound
import Mathlib.Analysis.Asymptotics.Lemmas

/-! # Cauchy error budgets for genuine removable second divided differences -/

noncomputable section
open Complex Set Metric Filter Topology Asymptotics
namespace PGM

theorem cepsNormal_norm_second_dslope_le_of_bound {f : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hbound : ∀ ξ ∈ ball (0 : ℂ) R, ‖f ξ‖ ≤ M)
    {a b t : ℂ} (ha : a ∈ ball 0 (R / 2)) (hb : b ∈ ball 0 (R / 2))
    (ht : t ∈ ball 0 (R / 2)) :
    ‖dslope (dslope f a) b t‖ ≤ 32 * M / R ^ 2 := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 0 (mem_ball_self hR))
  have hsub : ball (0 : ℂ) (R / 2) ⊆ ball 0 R := ball_subset_ball (half_le_self hR.le)
  apply cepsNormal_norm_second_dslope_le hf (convex_ball (0 : ℂ) (R / 2)) hsub
    (by positivity) ?_ ha hb ht
  intro ξ hξ
  have he := norm_iteratedDeriv_le_of_ball_half 2 hR hf hbound hξ
  rw [iteratedDeriv_succ, iteratedDeriv_one] at he
  exact he.trans_eq (by simp only [Nat.factorial, Nat.cast_mul, mul_one]; field_simp; ring)

theorem cepsNormal_norm_second_dslope_sub_le_of_bound {f g : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hg : DifferentiableOn ℂ g (ball 0 R))
    (hbound : ∀ ξ ∈ ball (0 : ℂ) R, ‖f ξ - g ξ‖ ≤ M)
    {a b t : ℂ} (ha : a ∈ ball 0 (R / 2)) (hb : b ∈ ball 0 (R / 2))
    (ht : t ∈ ball 0 (R / 2)) :
    ‖dslope (dslope f a) b t - dslope (dslope g a) b t‖ ≤ 32 * M / R ^ 2 := by
  have hsub : ball (0 : ℂ) (R / 2) ⊆ ball 0 R := ball_subset_ball (half_le_self hR.le)
  have hfa := (hf _ (hsub ha)).differentiableAt (isOpen_ball.mem_nhds (hsub ha))
  have hga := (hg _ (hsub ha)).differentiableAt (isOpen_ball.mem_nhds (hsub ha))
  have hfS := ((differentiableOn_dslope (isOpen_ball.mem_nhds (hsub ha))).mpr hf _
    (hsub hb)).differentiableAt (isOpen_ball.mem_nhds (hsub hb))
  have hgS := ((differentiableOn_dslope (isOpen_ball.mem_nhds (hsub ha))).mpr hg _
    (hsub hb)).differentiableAt (isOpen_ball.mem_nhds (hsub hb))
  rw [← cepsNormal_second_dslope_sub_of_differentiableAt hfa hga hfS hgS]
  exact cepsNormal_norm_second_dslope_le_of_bound hR (hf.sub hg) hbound ha hb ht

theorem cepsNormal_second_dslope_curve_error_isBigO {F G : ℂ → ℂ → ℂ} {R B C : ℝ}
    (hR : 0 < R) (hB : 0 < B)
    (hF : ∀ b ∈ ball (0 : ℂ) B, DifferentiableOn ℂ (F b) (ball 0 R))
    (hG : ∀ b ∈ ball (0 : ℂ) B, DifferentiableOn ℂ (G b) (ball 0 R)) (N : ℕ)
    (he : ∀ b ∈ ball (0 : ℂ) B, ∀ ξ ∈ ball (0 : ℂ) R, ‖F b ξ - G b ξ‖ ≤ C * ‖b‖ ^ (N + 1))
    {a d t : ℂ → ℂ} (ha : ContinuousAt a 0) (hd : ContinuousAt d 0) (ht : ContinuousAt t 0)
    (ha0 : a 0 ∈ ball 0 (R / 2)) (hd0 : d 0 ∈ ball 0 (R / 2))
    (ht0 : t 0 ∈ ball 0 (R / 2)) :
    (fun b => dslope (dslope (F b) (a b)) (d b) (t b) -
      dslope (dslope (G b) (a b)) (d b) (t b))
      =O[𝓝 (0 : ℂ)] (fun b => b ^ (N + 1)) := by
  apply IsBigO.of_bound (32 * C / R ^ 2)
  have hBmem : ∀ᶠ b : ℂ in 𝓝 0, b ∈ ball (0 : ℂ) B := ball_mem_nhds _ hB
  filter_upwards [hBmem, ha.eventually (isOpen_ball.mem_nhds ha0),
    hd.eventually (isOpen_ball.mem_nhds hd0), ht.eventually (isOpen_ball.mem_nhds ht0)]
    with b hb hab hdb htb
  have hh := cepsNormal_norm_second_dslope_sub_le_of_bound hR (hF b hb) (hG b hb)
    (he b hb) hab hdb htb
  exact hh.trans_eq (by rw [norm_pow]; ring)

end PGM
