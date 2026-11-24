import PLAStochastic.Index.CEPS.Normal.SecondSlopeNodeError

/-! # Preservation of finite node-curve error orders in removable second slopes -/

noncomputable section
open Complex Set Metric Filter Topology Asymptotics
namespace PGM

theorem cepsNormal_second_dslope_node_curves_isBigO {G : ℂ → ℂ → ℂ} {R B M : ℝ}
    (hR : 0 < R) (hB : 0 < B)
    (hG : ∀ b ∈ ball (0 : ℂ) B, DifferentiableOn ℂ (G b) (ball 0 R))
    (hbound : ∀ b ∈ ball (0 : ℂ) B, ∀ ξ ∈ ball (0 : ℂ) R, ‖G b ξ‖ ≤ M) (N : ℕ)
    {a d t a' d' t' : ℂ → ℂ}
    (ha : ContinuousAt a 0) (hd : ContinuousAt d 0) (ht : ContinuousAt t 0)
    (ha' : ContinuousAt a' 0) (hd' : ContinuousAt d' 0) (ht' : ContinuousAt t' 0)
    (ha0 : a 0 ∈ ball 0 (R / 4)) (hd0 : d 0 ∈ ball 0 (R / 4)) (ht0 : t 0 ∈ ball 0 (R / 4))
    (ha'0 : a' 0 ∈ ball 0 (R / 4)) (hd'0 : d' 0 ∈ ball 0 (R / 4)) (ht'0 : t' 0 ∈ ball 0 (R / 4))
    (hae : (fun b => a b - a' b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)))
    (hde : (fun b => d b - d' b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)))
    (hte : (fun b => t b - t' b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1))) :
    (fun b => dslope (dslope (G b) (a b)) (d b) (t b) -
      dslope (dslope (G b) (a' b)) (d' b) (t' b))
      =O[𝓝 (0 : ℂ)] (fun b => b ^ (N + 1)) := by
  have hBmem : ∀ᶠ b : ℂ in 𝓝 0, b ∈ ball (0 : ℂ) B := ball_mem_nhds _ hB
  have he : (fun b => dslope (dslope (G b) (a b)) (d b) (t b) -
      dslope (dslope (G b) (a' b)) (d' b) (t' b)) =O[𝓝 (0 : ℂ)]
      (fun b => ‖a b - a' b‖ + ‖d b - d' b‖ + ‖t b - t' b‖) := by
    apply IsBigO.of_bound (256 * M / R ^ 3)
    filter_upwards [hBmem, ha.eventually (isOpen_ball.mem_nhds ha0),
      hd.eventually (isOpen_ball.mem_nhds hd0), ht.eventually (isOpen_ball.mem_nhds ht0),
      ha'.eventually (isOpen_ball.mem_nhds ha'0), hd'.eventually (isOpen_ball.mem_nhds hd'0),
      ht'.eventually (isOpen_ball.mem_nhds ht'0)] with b hb hab hdb htb hab' hdb' htb'
    simpa only [Real.norm_of_nonneg (show 0 ≤ ‖a b - a' b‖ + ‖d b - d' b‖ + ‖t b - t' b‖
      from by positivity)] using
        cepsNormal_second_dslope_nodes_lipschitz hR (hG b hb) (hbound b hb) hab hdb htb hab' hdb' htb'
  exact he.trans ((hae.norm_left.add hde.norm_left).add hte.norm_left)

end PGM
