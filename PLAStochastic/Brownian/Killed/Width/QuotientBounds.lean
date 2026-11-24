import PLAStochastic.Brownian.Killed.Width.BoundaryQuotient

/-! # Uniform summable bounds for the actual heat kernel boundary quotients -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem norm_heatSpatialSeries_le_width_bound {l u r δ t : ℝ}
    (hl : 0 < l) (hlr : l ≤ r) (hru : r ≤ u) (hδ : 0 < δ) (ht : δ ≤ t)
    (a b : ℕ) (x z : ℝ) :
    ‖heatSpatialSeries r a b t x z‖ ≤ ∑' n, heatWidthBound l u δ a b n := by
  have hs := summable_heatSpatialMode (hl.trans_le hlr) (hδ.trans_le ht) a b x z
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    (hs.norm.tsum_le_tsum (fun n => heatSpatialMode_width_bound hl hlr hru hδ.le ht a b n x z)
      (summable_heatWidthBound ((hl.trans_le hlr).trans_le hru) hδ l a b))

/-- A single bound works for every spatial position and all admissible right quotients. -/
theorem norm_heatSpatialSeries_right_quotient_le {l u r δ t x : ℝ}
    (hl : 0 < l) (hlr : l ≤ r) (hru : r ≤ u) (hδ : 0 < δ) (ht : δ ≤ t)
    (hx : x < r) (b : ℕ) (z : ℝ) :
    ‖heatSpatialSeries r 0 b t x z / (r-x)‖ ≤ ∑' n, heatWidthBound l u δ 1 b n := by
  obtain ⟨c, _, he⟩ := heatSpatialSeries_right_quotient_mvt
    (hl.trans_le hlr) (hδ.trans_le ht) hx z b
  rw [he, norm_neg]
  exact norm_heatSpatialSeries_le_width_bound hl hlr hru hδ ht 1 b c z

/-- The left quotient has the same global spatial majorant. -/
theorem norm_heatSpatialSeries_left_quotient_le {l u r δ t x : ℝ}
    (hl : 0 < l) (hlr : l ≤ r) (hru : r ≤ u) (hδ : 0 < δ) (ht : δ ≤ t)
    (hx : 0 < x) (b : ℕ) (z : ℝ) :
    ‖heatSpatialSeries r 0 b t x z / x‖ ≤ ∑' n, heatWidthBound l u δ 1 b n := by
  obtain ⟨c, _, he⟩ := heatSpatialSeries_left_quotient_mvt
    (hl.trans_le hlr) (hδ.trans_le ht) hx z b
  rw [he]
  exact norm_heatSpatialSeries_le_width_bound hl hlr hru hδ ht 1 b c z

/-- Actual width-perturbation quotients are uniformly bounded away from time zero. -/
theorem norm_dirichletHeatKernel_width_quotient_le {r δ t e : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (ht : δ ≤ t) (he : 0 < e) (her : e ≤ r) (z : ℝ) :
    ‖dirichletHeatKernel (r+e) t r z / e‖ ≤ ∑' n, heatWidthBound r (2*r) δ 1 0 n := by
  simpa only [dirichletHeatKernel, add_sub_cancel_left] using
    norm_heatSpatialSeries_right_quotient_le hr (by linarith : r ≤ r+e)
      (by linarith : r+e ≤ 2*r) hδ ht (by linarith : r < r+e) 0 z

/-- The cross-boundary quotient is uniformly bounded on positive-time half-lines. -/
theorem norm_heatBoundaryRight_width_quotient_le {r δ t e : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (ht : δ ≤ t) (he : 0 < e) (her : e ≤ r) :
    ‖heatBoundaryRight (r+e) t e / e‖ ≤ ∑' n, heatWidthBound r (2*r) δ 1 1 n := by
  simpa only [heatBoundaryRight, neg_div, norm_neg] using
    norm_heatSpatialSeries_left_quotient_le hr (by linarith : r ≤ r+e)
      (by linarith : r+e ≤ 2*r) hδ ht he 1 (r+e)

end BrownianAffine
