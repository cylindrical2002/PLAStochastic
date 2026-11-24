import PLAStochastic.Affine.Extrema.Contact.ExtremaApproximation

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The second contact clock records elapsed time after the first actual exit. -/
def orderedContactLag {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (x r e : ℝ) (ω : Ω) : ℝ≥0 :=
  intervalTouchClock (brownianRestartAt B (intervalTouchTime B x r)) e (r+e) ω

/-- On any eventually valid shrinking contact layers, both actual stopping clocks
converge to the extremum time and to the lag between the two extrema. -/
theorem tendsto_orderedContact_clocks {Ω : Type*}
    {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω))
    (hl : DifferentiableAt ℝ (slopeLower (unitPath (processPath B ω) 1)) 0)
    (hu : DifferentiableAt ℝ (slopeUpper (unitPath (processPath B ω) 1)) 0)
    {X R E F : ℕ → ℝ} (hR : ∀ n, 0 < R n) (hE : ∀ n, 0 < E n) (hF : ∀ n, 0 < F n)
    (hElim : Tendsto E atTop (𝓝 0)) (hFlim : Tendsto F atTop (𝓝 0))
    {S D₁ D₂ : Set ℝ}
    (hEv : ∀ᶠ n in atTop, orderedContactLayerEvent B (X n) (R n) (E n) (F n) 1 S D₁ D₂ ω) :
    Tendsto (fun n => (intervalTouchClock B (X n) (R n) ω : ℝ)) atTop
      (𝓝 (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ)) ∧
    Tendsto (fun n => (orderedContactLag B (X n) (R n) (E n) ω : ℝ)) atTop
      (𝓝 ((upperTime (unitPath (processPath B ω) 1) 0 : ℝ)-
        (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ))) := by
  constructor
  · apply Metric.tendsto_nhds.mpr
    intro eps heps
    let D := (Metric.ball (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ) eps)ᶜ
    have hb : (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ) ∉ closure D := by
      rw [show closure D=D from Metric.isOpen_ball.isClosed_compl.closure_eq]
      exact fun h => h (Metric.mem_ball_self heps)
    filter_upwards [hEv,eventually_not_orderedContactLayer_of_time_window
      (X := X) (S := S) (D₁ := D) (D₂ := D₂) hc hl hu hR hE hF hElim hFlim (Or.inl hb)] with n hn hb
    by_contra h
    exact hb ⟨⟨h,hn.1.2⟩,hn.2⟩
  · apply Metric.tendsto_nhds.mpr
    intro eps heps
    let D := (Metric.ball ((upperTime (unitPath (processPath B ω) 1) 0 : ℝ)-
      (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ)) eps)ᶜ
    have hb : ((upperTime (unitPath (processPath B ω) 1) 0 : ℝ)-
        (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ)) ∉ closure D := by
      rw [show closure D=D from Metric.isOpen_ball.isClosed_compl.closure_eq]
      exact fun h => h (Metric.mem_ball_self heps)
    filter_upwards [hEv,eventually_not_orderedContactLayer_of_time_window
      (X := X) (S := S) (D₁ := D₁) (D₂ := D) hc hl hu hR hE hF hElim hFlim (Or.inr hb)] with n hn hb
    by_contra h
    exact hb ⟨hn.1,hn.2.1,hn.2.2.1,h⟩

end BrownianAffine
