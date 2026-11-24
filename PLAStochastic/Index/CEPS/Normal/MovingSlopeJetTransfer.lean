import PLAStochastic.Index.CEPS.Normal.MovingSlopeGerms
import PLAStochastic.Index.CEPS.Normal.FirstSlopeError
import PLAStochastic.Index.CEPS.Normal.SecondSlopeCurveError
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorSeriesCongr

/-! # Exact finite jets of moving first and second slopes from spatial and node budgets -/

noncomputable section
open Complex Set Metric Filter Topology Asymptotics PowerSeries
namespace PGM

theorem cepsNormal_moving_dslope_taylorJets_transfer {F G : ℂ → ℂ → ℂ} {R B C M : ℝ}
    (hR : 0 < R) (hB : 0 < B)
    (hF : DifferentiableOn ℂ (fun x : ℂ × ℂ => F x.1 x.2) (ball 0 B ×ˢ ball 0 R))
    (hG : DifferentiableOn ℂ (fun x : ℂ × ℂ => G x.1 x.2) (ball 0 B ×ˢ ball 0 R))
    (hbound : ∀ b ∈ ball (0 : ℂ) B, ∀ ξ ∈ ball (0 : ℂ) R, ‖G b ξ‖ ≤ M) (N : ℕ)
    (he : ∀ b ∈ ball (0 : ℂ) B, ∀ ξ ∈ ball (0 : ℂ) R, ‖F b ξ - G b ξ‖ ≤ C * ‖b‖ ^ (N + 1))
    {a t a' t' : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (ht : AnalyticAt ℂ t 0)
    (ha' : AnalyticAt ℂ a' 0) (ht' : AnalyticAt ℂ t' 0)
    (ha0 : a 0 ∈ ball 0 (R / 2)) (ht0 : t 0 ∈ ball 0 (R / 2))
    (ha'0 : a' 0 ∈ ball 0 (R / 2)) (ht'0 : t' 0 ∈ ball 0 (R / 2))
    (hae : (fun b => a b - a' b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)))
    (hte : (fun b => t b - t' b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1))) :
    ∀ j ≤ N, coeff j (complexTaylorSeries (fun b => dslope (F b) (a b) (t b)) 0) =
      coeff j (complexTaylorSeries (fun b => dslope (G b) (a' b) (t' b)) 0) := by
  have hFS : ∀ b ∈ ball (0 : ℂ) B, DifferentiableOn ℂ (F b) (ball 0 R) := fun b hb ξ hξ =>
    (differentiableAt_slice_snd (isOpen_ball.prod isOpen_ball) hF ⟨hb, hξ⟩).differentiableWithinAt
  have hGS : ∀ b ∈ ball (0 : ℂ) B, DifferentiableOn ℂ (G b) (ball 0 R) := fun b hb ξ hξ =>
    (differentiableAt_slice_snd (isOpen_ball.prod isOpen_ball) hG ⟨hb, hξ⟩).differentiableWithinAt
  have hfamily := cepsNormal_dslope_curve_error_isBigO hR hB hFS hGS N he
    ha.continuousAt ht.continuousAt ha0 ht0
  have hnodes := cepsNormal_dslope_node_curves_isBigO hR hB hGS hbound N
    ha.continuousAt ht.continuousAt ha'.continuousAt ht'.continuousAt ha0 ht0 ha'0 ht'0 hae hte
  have herr : (fun b => dslope (F b) (a b) (t b) - dslope (G b) (a' b) (t' b))
      =O[𝓝 (0 : ℂ)] (fun b => b ^ (N + 1)) := by
    apply (hfamily.add hnodes).congr' (Eventually.of_forall fun b => ?_) Filter.EventuallyEq.rfl
    ring
  have hsub : ball (0 : ℂ) (R / 2) ⊆ ball 0 R := ball_subset_ball (half_le_self hR.le)
  exact complexTaylorSeries_coeff_eq_of_isBigO
    (cepsNormal_moving_dslope_analyticAt_of_differentiableOn hB hF ha ht (hsub ha0) (hsub ht0))
    (cepsNormal_moving_dslope_analyticAt_of_differentiableOn hB hG ha' ht' (hsub ha'0) (hsub ht'0)) N herr

theorem cepsNormal_moving_second_dslope_taylorJets_transfer {F G : ℂ → ℂ → ℂ} {R B C M : ℝ}
    (hR : 0 < R) (hB : 0 < B)
    (hF : DifferentiableOn ℂ (fun x : ℂ × ℂ => F x.1 x.2) (ball 0 B ×ˢ ball 0 R))
    (hG : DifferentiableOn ℂ (fun x : ℂ × ℂ => G x.1 x.2) (ball 0 B ×ˢ ball 0 R))
    (hbound : ∀ b ∈ ball (0 : ℂ) B, ∀ ξ ∈ ball (0 : ℂ) R, ‖G b ξ‖ ≤ M) (N : ℕ)
    (he : ∀ b ∈ ball (0 : ℂ) B, ∀ ξ ∈ ball (0 : ℂ) R, ‖F b ξ - G b ξ‖ ≤ C * ‖b‖ ^ (N + 1))
    {a d t a' d' t' : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (hd : AnalyticAt ℂ d 0) (ht : AnalyticAt ℂ t 0)
    (ha' : AnalyticAt ℂ a' 0) (hd' : AnalyticAt ℂ d' 0) (ht' : AnalyticAt ℂ t' 0)
    (ha0 : a 0 ∈ ball 0 (R / 4)) (hd0 : d 0 ∈ ball 0 (R / 4)) (ht0 : t 0 ∈ ball 0 (R / 4))
    (ha'0 : a' 0 ∈ ball 0 (R / 4)) (hd'0 : d' 0 ∈ ball 0 (R / 4)) (ht'0 : t' 0 ∈ ball 0 (R / 4))
    (hae : (fun b => a b - a' b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)))
    (hde : (fun b => d b - d' b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)))
    (hte : (fun b => t b - t' b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1))) :
    ∀ j ≤ N, coeff j (complexTaylorSeries (fun b => dslope (dslope (F b) (a b)) (d b) (t b)) 0) =
      coeff j (complexTaylorSeries (fun b => dslope (dslope (G b) (a' b)) (d' b) (t' b)) 0) := by
  have hFS : ∀ b ∈ ball (0 : ℂ) B, DifferentiableOn ℂ (F b) (ball 0 R) := fun b hb ξ hξ =>
    (differentiableAt_slice_snd (isOpen_ball.prod isOpen_ball) hF ⟨hb, hξ⟩).differentiableWithinAt
  have hGS : ∀ b ∈ ball (0 : ℂ) B, DifferentiableOn ℂ (G b) (ball 0 R) := fun b hb ξ hξ =>
    (differentiableAt_slice_snd (isOpen_ball.prod isOpen_ball) hG ⟨hb, hξ⟩).differentiableWithinAt
  have hsmall : ball (0 : ℂ) (R / 4) ⊆ ball 0 (R / 2) := ball_subset_ball (by linarith)
  have hlarge : ball (0 : ℂ) (R / 4) ⊆ ball 0 R := ball_subset_ball (by linarith)
  have hfamily := cepsNormal_second_dslope_curve_error_isBigO hR hB hFS hGS N he
    ha.continuousAt hd.continuousAt ht.continuousAt (hsmall ha0) (hsmall hd0) (hsmall ht0)
  have hnodes := cepsNormal_second_dslope_node_curves_isBigO hR hB hGS hbound N
    ha.continuousAt hd.continuousAt ht.continuousAt ha'.continuousAt hd'.continuousAt ht'.continuousAt
    ha0 hd0 ht0 ha'0 hd'0 ht'0 hae hde hte
  have herr : (fun b => dslope (dslope (F b) (a b)) (d b) (t b) -
      dslope (dslope (G b) (a' b)) (d' b) (t' b)) =O[𝓝 (0 : ℂ)] (fun b => b ^ (N + 1)) := by
    apply (hfamily.add hnodes).congr' (Eventually.of_forall fun b => ?_) Filter.EventuallyEq.rfl
    ring
  exact complexTaylorSeries_coeff_eq_of_isBigO
    (cepsNormal_moving_second_dslope_analyticAt_of_differentiableOn hB hF ha hd ht
      (hlarge ha0) (hlarge hd0) (hlarge ht0))
    (cepsNormal_moving_second_dslope_analyticAt_of_differentiableOn hB hG ha' hd' ht'
      (hlarge ha'0) (hlarge hd'0) (hlarge ht'0)) N herr

end PGM
