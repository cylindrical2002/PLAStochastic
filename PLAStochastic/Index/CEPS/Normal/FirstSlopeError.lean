import PLAStochastic.Index.CEPS.Normal.SecondSlopeError
import PLAStochastic.Index.CEPS.Normal.DividedDifferenceSymmetry

/-! # Finite spatial-family and node errors in genuine first divided differences -/

noncomputable section
open Complex Set Metric Filter Topology Asymptotics
namespace PGM

theorem cepsNormal_norm_dslope_le_of_bound {f : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hbound : ∀ ξ ∈ ball (0 : ℂ) R, ‖f ξ‖ ≤ M)
    {a t : ℂ} (ha : a ∈ ball 0 (R / 2)) (ht : t ∈ ball 0 (R / 2)) :
    ‖dslope f a t‖ ≤ 4 * M / R := by
  by_cases hta : t = a
  · subst t; rw [dslope_same]; exact norm_deriv_le_of_ball_half hR hf hbound ha
  · rw [dslope_of_ne _ hta, slope_def_field, norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hta))).mpr
      (norm_sub_le_of_ball_half hR hf hbound ht ha)

theorem cepsNormal_norm_dslope_sub_le_of_bound {f g : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hg : DifferentiableOn ℂ g (ball 0 R))
    (hbound : ∀ ξ ∈ ball (0 : ℂ) R, ‖f ξ - g ξ‖ ≤ M)
    {a t : ℂ} (ha : a ∈ ball 0 (R / 2)) (ht : t ∈ ball 0 (R / 2)) :
    ‖dslope f a t - dslope g a t‖ ≤ 4 * M / R := by
  have hsub : ball (0 : ℂ) (R / 2) ⊆ ball 0 R := ball_subset_ball (half_le_self hR.le)
  rw [← cepsNormal_dslope_sub_of_differentiableAt
    ((hf _ (hsub ha)).differentiableAt (isOpen_ball.mem_nhds (hsub ha)))
    ((hg _ (hsub ha)).differentiableAt (isOpen_ball.mem_nhds (hsub ha)))]
  exact cepsNormal_norm_dslope_le_of_bound hR (hf.sub hg) hbound ha ht

theorem cepsNormal_dslope_nodes_lipschitz {f : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hbound : ∀ ξ ∈ ball (0 : ℂ) R, ‖f ξ‖ ≤ M)
    {a t a' t' : ℂ} (ha : a ∈ ball 0 (R / 2)) (ht : t ∈ ball 0 (R / 2))
    (ha' : a' ∈ ball 0 (R / 2)) (ht' : t' ∈ ball 0 (R / 2)) :
    ‖dslope f a t - dslope f a' t'‖ ≤ (32 * M / R ^ 2) * (‖a - a'‖ + ‖t - t'‖) := by
  have hmarker (a t t' : ℂ) (ha : a ∈ ball 0 (R / 2))
      (ht : t ∈ ball 0 (R / 2)) (ht' : t' ∈ ball 0 (R / 2)) :
      ‖dslope f a t - dslope f a t'‖ ≤ (32 * M / R ^ 2) * ‖t - t'‖ := by
    have he := sub_smul_dslope (dslope f a) t' t
    rw [smul_eq_mul] at he
    rw [← he, norm_mul]
    exact (mul_le_mul_of_nonneg_left
      (cepsNormal_norm_second_dslope_le_of_bound hR hf hbound ha ht' ht) (norm_nonneg _)).trans_eq
        (mul_comm _ _)
  have h1 : ‖dslope f a t - dslope f a' t‖ ≤ (32 * M / R ^ 2) * ‖a - a'‖ := by
    rw [cepsNormal_dslope_swap f a t, cepsNormal_dslope_swap f a' t]
    exact hmarker t a a' ht ha ha'
  calc
    _ ≤ ‖dslope f a t - dslope f a' t‖ + ‖dslope f a' t - dslope f a' t'‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (32 * M / R ^ 2) * ‖a - a'‖ + (32 * M / R ^ 2) * ‖t - t'‖ :=
      add_le_add h1 (hmarker a' t t' ha' ht ht')
    _ = _ := by ring

theorem cepsNormal_dslope_curve_error_isBigO {F G : ℂ → ℂ → ℂ} {R B C : ℝ}
    (hR : 0 < R) (hB : 0 < B)
    (hF : ∀ b ∈ ball (0 : ℂ) B, DifferentiableOn ℂ (F b) (ball 0 R))
    (hG : ∀ b ∈ ball (0 : ℂ) B, DifferentiableOn ℂ (G b) (ball 0 R)) (N : ℕ)
    (he : ∀ b ∈ ball (0 : ℂ) B, ∀ ξ ∈ ball (0 : ℂ) R, ‖F b ξ - G b ξ‖ ≤ C * ‖b‖ ^ (N + 1))
    {a t : ℂ → ℂ} (ha : ContinuousAt a 0) (ht : ContinuousAt t 0)
    (ha0 : a 0 ∈ ball 0 (R / 2)) (ht0 : t 0 ∈ ball 0 (R / 2)) :
    (fun b => dslope (F b) (a b) (t b) - dslope (G b) (a b) (t b))
      =O[𝓝 (0 : ℂ)] (fun b => b ^ (N + 1)) := by
  apply IsBigO.of_bound (4 * C / R)
  have hBmem : ∀ᶠ b : ℂ in 𝓝 0, b ∈ ball (0 : ℂ) B := ball_mem_nhds _ hB
  filter_upwards [hBmem, ha.eventually (isOpen_ball.mem_nhds ha0),
    ht.eventually (isOpen_ball.mem_nhds ht0)] with b hb hab htb
  have hh := cepsNormal_norm_dslope_sub_le_of_bound hR (hF b hb) (hG b hb) (he b hb) hab htb
  exact hh.trans_eq (by rw [norm_pow]; ring)

theorem cepsNormal_dslope_node_curves_isBigO {G : ℂ → ℂ → ℂ} {R B M : ℝ}
    (hR : 0 < R) (hB : 0 < B)
    (hG : ∀ b ∈ ball (0 : ℂ) B, DifferentiableOn ℂ (G b) (ball 0 R))
    (hbound : ∀ b ∈ ball (0 : ℂ) B, ∀ ξ ∈ ball (0 : ℂ) R, ‖G b ξ‖ ≤ M) (N : ℕ)
    {a t a' t' : ℂ → ℂ}
    (ha : ContinuousAt a 0) (ht : ContinuousAt t 0)
    (ha' : ContinuousAt a' 0) (ht' : ContinuousAt t' 0)
    (ha0 : a 0 ∈ ball 0 (R / 2)) (ht0 : t 0 ∈ ball 0 (R / 2))
    (ha'0 : a' 0 ∈ ball 0 (R / 2)) (ht'0 : t' 0 ∈ ball 0 (R / 2))
    (hae : (fun b => a b - a' b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)))
    (hte : (fun b => t b - t' b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1))) :
    (fun b => dslope (G b) (a b) (t b) - dslope (G b) (a' b) (t' b))
      =O[𝓝 (0 : ℂ)] (fun b => b ^ (N + 1)) := by
  have hBmem : ∀ᶠ b : ℂ in 𝓝 0, b ∈ ball (0 : ℂ) B := ball_mem_nhds _ hB
  have he : (fun b => dslope (G b) (a b) (t b) - dslope (G b) (a' b) (t' b)) =O[𝓝 (0 : ℂ)]
      (fun b => ‖a b - a' b‖ + ‖t b - t' b‖) := by
    apply IsBigO.of_bound (32 * M / R ^ 2)
    filter_upwards [hBmem, ha.eventually (isOpen_ball.mem_nhds ha0),
      ht.eventually (isOpen_ball.mem_nhds ht0), ha'.eventually (isOpen_ball.mem_nhds ha'0),
      ht'.eventually (isOpen_ball.mem_nhds ht'0)] with b hb hab htb hab' htb'
    simpa only [Real.norm_of_nonneg (show 0 ≤ ‖a b - a' b‖ + ‖t b - t' b‖ from by positivity)] using
      cepsNormal_dslope_nodes_lipschitz hR (hG b hb) (hbound b hb) hab htb hab' htb'
  exact he.trans (hae.norm_left.add hte.norm_left)

end PGM
