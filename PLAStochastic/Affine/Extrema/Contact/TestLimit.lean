import PLAStochastic.Affine.Extrema.Contact.Observable

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Every continuous test of the actual five marked contact coordinates converges
to the corresponding extrema test on the lower-first order. -/
theorem tendsto_orderedContactTest_of_ordered_rectangles {Ω : Type*}
    {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω)) (h0 : B 0 ω=0)
    (hl : DifferentiableAt ℝ (slopeLower (unitPath (processPath B ω) 1)) 0)
    (hu : DifferentiableAt ℝ (slopeUpper (unitPath (processPath B ω) 1)) 0)
    (horder : (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ) <
      (upperTime (unitPath (processPath B ω) 1) 0 : ℝ))
    {X R E F : ℕ → ℝ} (hR : ∀ n, 0 < R n) (hX : ∀ n, X n ∈ Ioo 0 (R n))
    (hE : ∀ n, 0 < E n) (hF : ∀ n, 0 < F n)
    (hElim : Tendsto E atTop (𝓝 0)) (hFlim : Tendsto F atTop (𝓝 0))
    (hrect : ∀ n, -E n < X n+slopeLower (unitPath (processPath B ω) 1) 0 ∧
      X n+slopeLower (unitPath (processPath B ω) 1) 0 < 0 ∧
      R n < X n+slopeUpper (unitPath (processPath B ω) 1) 0 ∧
      X n+slopeUpper (unitPath (processPath B ω) 1) 0 < R n+F n)
    {φ : ExtremaVector → ℝ} (hφ : ContinuousAt φ (brownianExtremaVector B ω)) :
    Tendsto (fun n => orderedContactTest φ B (X n) (R n) (E n) (F n) ω) atTop
      (𝓝 (φ (brownianExtremaVector B ω))) := by
  let g := unitPath (processPath B ω) 1
  have hev := eventually_orderedContactLayer_of_ordered_extrema hc h0 hu horder hR hX hE hF hFlim hrect
  have hcl := tendsto_orderedContact_clocks hc hl hu hR hE hF hElim hFlim hev
  have hxmin : Tendsto (fun n => -X n) atTop (𝓝 (slopeLower g 0)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [add_zero] using tendsto_const_nhds.add hElim)
    · intro n
      have h := (hrect n).2.1
      change X n+slopeLower g 0 < 0 at h
      linarith
    · intro n
      have h := (hrect n).1
      change -E n < X n+slopeLower g 0 at h
      linarith
  have hrmax : Tendsto (fun n => R n-X n) atTop (𝓝 (slopeUpper g 0)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa only [sub_zero] using tendsto_const_nhds.sub hFlim) tendsto_const_nhds
    · intro n
      have h := (hrect n).2.2.2
      change X n+slopeUpper g 0 < R n+F n at h
      linarith
    · intro n
      have h := (hrect n).2.2.1
      change R n < X n+slopeUpper g 0 at h
      linarith
  have hsum : Tendsto (fun n => (intervalTouchClock B (X n) (R n) ω : ℝ)+
      (orderedContactLag B (X n) (R n) (E n) ω : ℝ)) atTop
      (𝓝 (upperTime g 0 : ℝ)) := by
    simpa only [add_sub_cancel] using hcl.1.add hcl.2
  have hvec : Tendsto (fun n => orderedContactVector B (X n) (R n) (E n) ω) atTop
      (𝓝 (brownianExtremaVector B ω)) :=
    hxmin.prodMk_nhds (hrmax.prodMk_nhds (hcl.1.prodMk_nhds (hsum.prodMk_nhds tendsto_const_nhds)))
  apply (hφ.tendsto.comp hvec).congr'
  filter_upwards [hev] with n hn
  simp only [orderedContactTest,if_pos hn]
  rfl

/-- On the reverse extremum order, every contact observable eventually vanishes. -/
theorem eventually_orderedContactTest_eq_zero_of_reverse {Ω : Type*}
    {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω))
    (hl : DifferentiableAt ℝ (slopeLower (unitPath (processPath B ω) 1)) 0)
    (hu : DifferentiableAt ℝ (slopeUpper (unitPath (processPath B ω) 1)) 0)
    (horder : (upperTime (unitPath (processPath B ω) 1) 0 : ℝ) <
      (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ))
    {X R E F : ℕ → ℝ} (hR : ∀ n, 0 < R n) (hE : ∀ n, 0 < E n) (hF : ∀ n, 0 < F n)
    (hElim : Tendsto E atTop (𝓝 0)) (hFlim : Tendsto F atTop (𝓝 0))
    (φ : ExtremaVector → ℝ) :
    ∀ᶠ n in atTop, orderedContactTest φ B (X n) (R n) (E n) (F n) ω=0 := by
  filter_upwards [eventually_not_orderedContactLayer_of_reverse_extrema
    (X := X) (S := univ) (D₁ := univ) (D₂ := univ) hc hl hu horder hR hE hF hElim hFlim] with n hn
  simp only [orderedContactTest,if_neg hn]

end BrownianAffine
