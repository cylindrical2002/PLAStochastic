import PLAStochastic.Affine.Extrema.Contact.Geometry

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Any sequence of true shrinking two-contact layers can accumulate only at the
actual ordered extremum times and the closures of their prescribed time windows. -/
theorem orderedContactLayer_limit_times {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω))
    (hl : DifferentiableAt ℝ (slopeLower (unitPath (processPath B ω) 1)) 0)
    (hu : DifferentiableAt ℝ (slopeUpper (unitPath (processPath B ω) 1)) 0)
    {X R E F : ℕ → ℝ} (hR : ∀ n, 0 < R n) (hE : ∀ n, 0 < E n) (hF : ∀ n, 0 < F n)
    (hElim : Tendsto E atTop (𝓝 0)) (hFlim : Tendsto F atTop (𝓝 0))
    {S D₁ D₂ : Set ℝ}
    (hEv : ∀ n, orderedContactLayerEvent B (X n) (R n) (E n) (F n) 1 S D₁ D₂ ω) :
    (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ) ≤
        (upperTime (unitPath (processPath B ω) 1) 0 : ℝ) ∧
      (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ) ∈ closure D₁ ∧
      ((upperTime (unitPath (processPath B ω) 1) 0 : ℝ)-
        (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ)) ∈ closure D₂ := by
  let g := unitPath (processPath B ω) 1
  have hg (n : ℕ) := orderedContactLayer_geometry hc (hR n) (hE n) (hF n) (hEv n)
  have hb (n : ℕ) := orderedContactLayer_extrema_rectangle hc (hR n) (hE n) (hF n) (hEv n)
  choose s v hs0 hsv hvT hsz hvr hsD hvD using (fun n => (hg n).2.1)
  let a : ℕ → RangeTime := fun n => nnrealRangeTime (s n) ((hsv n).le.trans (hvT n))
  let b : ℕ → RangeTime := fun n => nnrealRangeTime (v n) (hvT n)
  have ha (n : ℕ) : slopeResidual g 0 (a n)=B (s n) ω := by
    simpa only [zero_mul,sub_zero] using
      slopeResidual_actual_unit B hc 0 (s n) ((hsv n).le.trans (hvT n))
  have hbval (n : ℕ) : slopeResidual g 0 (b n)=B (v n) ω := by
    simpa only [zero_mul,sub_zero] using slopeResidual_actual_unit B hc 0 (v n) (hvT n)
  have hamin : Tendsto (fun n => slopeResidual g 0 (a n)) atTop (𝓝 (slopeLower g 0)) := by
    simp_rw [ha]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [add_zero] using tendsto_const_nhds.add hElim)
    · intro n
      have hh := hb n
      have hz := hsz n
      change -E n < X n+slopeLower g 0 ∧ X n+slopeLower g 0 ≤ 0 ∧ _ at hh
      linarith [hh.2.1]
    · intro n
      have hh := hb n
      have hz := hsz n
      change -E n < X n+slopeLower g 0 ∧ _ at hh
      linarith [hh.1]
  have hbmax : Tendsto (fun n => slopeResidual g 0 (b n)) atTop (𝓝 (slopeUpper g 0)) := by
    simp_rw [hbval]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa only [sub_zero] using tendsto_const_nhds.sub hFlim) tendsto_const_nhds
    · intro n
      have hh := hb n
      have hz := hvr n
      change _ ∧ _ ∧ R n ≤ X n+slopeUpper g 0 ∧ X n+slopeUpper g 0 < R n+F n at hh
      linarith [hh.2.2.2]
    · intro n
      have hh := hb n
      have hz := hvr n
      change _ ∧ _ ∧ R n ≤ X n+slopeUpper g 0 ∧ _ at hh
      linarith [hh.2.2.1]
  have hsa : Tendsto (fun n => (s n : ℝ)) atTop (𝓝 (lowerTime g 0 : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp (tendsto_lowerTime_of_residual_values g hl hamin)
  have hvb : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 (upperTime g 0 : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp (tendsto_upperTime_of_residual_values g hu hbmax)
  refine ⟨le_of_tendsto_of_tendsto' hsa hvb (fun n => ?_),
    isClosed_closure.mem_of_tendsto hsa (Eventually.of_forall (fun n => subset_closure (hsD n))),?_⟩
  · exact_mod_cast (hsv n).le
  · apply isClosed_closure.mem_of_tendsto (hvb.sub hsa)
    apply Eventually.of_forall
    intro n
    apply subset_closure
    have h := hvD n
    rwa [NNReal.coe_sub (hsv n).le] at h

end BrownianAffine
