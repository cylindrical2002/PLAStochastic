import PLAStochastic.Index.CEPS.Normal.SecondSlopeError
import PLAStochastic.Index.CEPS.Normal.DividedDifferenceSymmetry

/-! # Uniform stability of all three removable second-slope nodes -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsNormal_second_dslope_marker_lipschitz {f : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hbound : ∀ ξ ∈ ball (0 : ℂ) R, ‖f ξ‖ ≤ M)
    {a b t t' : ℂ} (ha : a ∈ ball 0 (R / 4)) (hb : b ∈ ball 0 (R / 4))
    (ht : t ∈ ball 0 (R / 4)) (ht' : t' ∈ ball 0 (R / 4)) :
    ‖dslope (dslope f a) b t - dslope (dslope f a) b t'‖ ≤
      (256 * M / R ^ 3) * ‖t - t'‖ := by
  have hsmall : ball (0 : ℂ) (R / 4) ⊆ ball 0 (R / 2) := ball_subset_ball (by linarith)
  have hlarge : ball (0 : ℂ) (R / 2) ⊆ ball 0 R := ball_subset_ball (half_le_self hR.le)
  have hS : DifferentiableOn ℂ (dslope (dslope f a) b) (ball 0 R) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds (hlarge (hsmall hb)))).mpr
      ((differentiableOn_dslope (isOpen_ball.mem_nhds (hlarge (hsmall ha)))).mpr hf)
  have hSb : ∀ ξ ∈ ball (0 : ℂ) (R / 2), ‖dslope (dslope f a) b ξ‖ ≤ 32 * M / R ^ 2 :=
    fun ξ hξ => cepsNormal_norm_second_dslope_le_of_bound hR hf hbound (hsmall ha) (hsmall hb) hξ
  apply (convex_ball (0 : ℂ) (R / 4)).norm_image_sub_le_of_norm_deriv_le
    (fun ξ hξ => (hS _ (hlarge (hsmall hξ))).differentiableAt
      (isOpen_ball.mem_nhds (hlarge (hsmall hξ)))) ?_ ht' ht
  intro ξ hξ
  have he := norm_iteratedDeriv_le_of_ball_half 1 (half_pos hR) (hS.mono hlarge) hSb
    (show ξ ∈ ball (0 : ℂ) ((R / 2) / 2) from by convert hξ using 1; ring)
  rw [iteratedDeriv_one] at he
  exact he.trans_eq (by norm_num; field_simp; ring)

theorem cepsNormal_second_dslope_nodes_lipschitz {f : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hbound : ∀ ξ ∈ ball (0 : ℂ) R, ‖f ξ‖ ≤ M)
    {a b t a' b' t' : ℂ} (ha : a ∈ ball 0 (R / 4)) (hb : b ∈ ball 0 (R / 4))
    (ht : t ∈ ball 0 (R / 4)) (ha' : a' ∈ ball 0 (R / 4))
    (hb' : b' ∈ ball 0 (R / 4)) (ht' : t' ∈ ball 0 (R / 4)) :
    ‖dslope (dslope f a) b t - dslope (dslope f a') b' t'‖ ≤
      (256 * M / R ^ 3) * (‖a - a'‖ + ‖b - b'‖ + ‖t - t'‖) := by
  have hlarge : ball (0 : ℂ) (R / 4) ⊆ ball 0 R := ball_subset_ball (by linarith)
  have hperm (a b t : ℂ) (ha : a ∈ ball 0 (R / 4)) (hb : b ∈ ball 0 (R / 4)) :
      dslope (dslope f a) b t = dslope (dslope f b) t a :=
    (cepsNormal_second_dslope_swap
      ((hf _ (hlarge ha)).differentiableAt (isOpen_ball.mem_nhds (hlarge ha)))
      ((hf _ (hlarge hb)).differentiableAt (isOpen_ball.mem_nhds (hlarge hb))) t).symm.trans
        (cepsNormal_dslope_swap (dslope f b) a t)
  have h1 : ‖dslope (dslope f a) b t - dslope (dslope f a') b t‖ ≤
      (256 * M / R ^ 3) * ‖a - a'‖ := by
    rw [hperm a b t ha hb, hperm a' b t ha' hb]
    exact cepsNormal_second_dslope_marker_lipschitz hR hf hbound hb ht ha ha'
  have h2 : ‖dslope (dslope f a') b t - dslope (dslope f a') b' t‖ ≤
      (256 * M / R ^ 3) * ‖b - b'‖ := by
    rw [cepsNormal_dslope_swap (dslope f a') b t, cepsNormal_dslope_swap (dslope f a') b' t]
    exact cepsNormal_second_dslope_marker_lipschitz hR hf hbound ha' ht hb hb'
  have h3 := cepsNormal_second_dslope_marker_lipschitz hR hf hbound ha' hb' ht ht'
  calc
    _ ≤ ‖dslope (dslope f a) b t - dslope (dslope f a') b t‖ +
        ‖dslope (dslope f a') b t - dslope (dslope f a') b' t'‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖dslope (dslope f a) b t - dslope (dslope f a') b t‖ +
        (‖dslope (dslope f a') b t - dslope (dslope f a') b' t‖ +
          ‖dslope (dslope f a') b' t - dslope (dslope f a') b' t'‖) :=
      add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ (256 * M / R ^ 3) * ‖a - a'‖ +
        ((256 * M / R ^ 3) * ‖b - b'‖ + (256 * M / R ^ 3) * ‖t - t'‖) :=
      add_le_add h1 (add_le_add h2 h3)
    _ = _ := by ring

end PGM
