import PLAStochastic.Affine.Extrema.Contact.TestLimit

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Test the actual extrema vector on the lower-first order. -/
def orderedExtremaTest {Ω : Type*} (φ : ExtremaVector → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  if (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ) <
      (upperTime (unitPath (processPath B ω) 1) 0 : ℝ) then
    φ (brownianExtremaVector B ω) else 0

/-- Finite initial choices of levels have no effect on the contact-layer test limit. -/
theorem tendsto_orderedContactTest_of_eventual_rectangles {Ω : Type*}
    {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω)) (h0 : B 0 ω=0)
    (hl : DifferentiableAt ℝ (slopeLower (unitPath (processPath B ω) 1)) 0)
    (hu : DifferentiableAt ℝ (slopeUpper (unitPath (processPath B ω) 1)) 0)
    (hne : (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ) ≠
      (upperTime (unitPath (processPath B ω) 1) 0 : ℝ))
    {X R E F : ℕ → ℝ} (hElim : Tendsto E atTop (𝓝 0)) (hFlim : Tendsto F atTop (𝓝 0))
    (hvalid : ∀ᶠ n in atTop, 0 < X n ∧ X n < R n ∧ 0 < E n ∧ 0 < F n ∧
      -E n < X n+slopeLower (unitPath (processPath B ω) 1) 0 ∧
      X n+slopeLower (unitPath (processPath B ω) 1) 0 < 0 ∧
      R n < X n+slopeUpper (unitPath (processPath B ω) 1) 0 ∧
      X n+slopeUpper (unitPath (processPath B ω) 1) 0 < R n+F n)
    {φ : ExtremaVector → ℝ} (hφ : ContinuousAt φ (brownianExtremaVector B ω)) :
    Tendsto (fun n => orderedContactTest φ B (X n) (R n) (E n) (F n) ω) atTop
      (𝓝 (orderedExtremaTest φ B ω)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hvalid
  have hv (n : ℕ) := hN (n+N) (Nat.le_add_left N n)
  apply (tendsto_add_atTop_iff_nat N).mp
  by_cases ho : (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ) <
      (upperTime (unitPath (processPath B ω) 1) 0 : ℝ)
  · rw [orderedExtremaTest,if_pos ho]
    exact tendsto_orderedContactTest_of_ordered_rectangles hc h0 hl hu ho
      (fun n => (hv n).1.trans (hv n).2.1) (fun n => ⟨(hv n).1,(hv n).2.1⟩)
      (fun n => (hv n).2.2.1) (fun n => (hv n).2.2.2.1)
      (hElim.comp (tendsto_add_atTop_nat N)) (hFlim.comp (tendsto_add_atTop_nat N))
      (fun n => (hv n).2.2.2.2) hφ
  · rw [orderedExtremaTest,if_neg ho]
    apply tendsto_const_nhds.congr'
    have hz := eventually_orderedContactTest_eq_zero_of_reverse (X := fun n => X (n+N))
      hc hl hu (lt_of_le_of_ne (le_of_not_gt ho) (Ne.symm hne))
      (fun n => (hv n).1.trans (hv n).2.1)
      (fun n => (hv n).2.2.1) (fun n => (hv n).2.2.2.1)
      (hElim.comp (tendsto_add_atTop_nat N)) (hFlim.comp (tendsto_add_atTop_nat N)) φ
    exact hz.mono (fun _ hn => hn.symm)

/-- Sample levels uniformly inside the small rectangle around the true extremal
values; the probability normalization is supplied by the unit square. -/
def rescaledOrderedContactTest {Ω : Type*} (φ : ExtremaVector → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (e d a b : ℝ) (ω : Ω) : ℝ :=
  let g := unitPath (processPath B ω) 1
  let l := slopeLower g 0+e*a
  let h := slopeUpper g 0-d*b
  orderedContactTest φ B (-l) (h-l) e d ω

/-- Pointwise convergence for every interior unit-square parameter, on every
continuous path with strict endpoint gaps and distinct unique extremum times. -/
theorem tendsto_rescaledOrderedContactTest {Ω : Type*}
    {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω)) (h0 : B 0 ω=0)
    (hl : DifferentiableAt ℝ (slopeLower (unitPath (processPath B ω) 1)) 0)
    (hu : DifferentiableAt ℝ (slopeUpper (unitPath (processPath B ω) 1)) 0)
    (hne : (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ) ≠
      (upperTime (unitPath (processPath B ω) 1) 0 : ℝ))
    (hm : slopeLower (unitPath (processPath B ω) 1) 0 < 0)
    (hM : 0 < slopeUpper (unitPath (processPath B ω) 1) 0)
    {E F : ℕ → ℝ} (hE : ∀ n, 0 < E n) (hF : ∀ n, 0 < F n)
    (hElim : Tendsto E atTop (𝓝 0)) (hFlim : Tendsto F atTop (𝓝 0))
    {a b : ℝ} (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1)
    {φ : ExtremaVector → ℝ} (hφ : ContinuousAt φ (brownianExtremaVector B ω)) :
    Tendsto (fun n => rescaledOrderedContactTest φ B (E n) (F n) a b ω) atTop
      (𝓝 (orderedExtremaTest φ B ω)) := by
  let g := unitPath (processPath B ω) 1
  let l : ℕ → ℝ := fun n => slopeLower g 0+E n*a
  let h : ℕ → ℝ := fun n => slopeUpper g 0-F n*b
  have hl0 : Tendsto l atTop (𝓝 (slopeLower g 0)) := by
    simpa only [zero_mul,add_zero] using tendsto_const_nhds.add (hElim.mul_const a)
  have hh0 : Tendsto h atTop (𝓝 (slopeUpper g 0)) := by
    simpa only [zero_mul,sub_zero] using tendsto_const_nhds.sub (hFlim.mul_const b)
  apply tendsto_orderedContactTest_of_eventual_rectangles hc h0 hl hu hne hElim hFlim _ hφ
  filter_upwards [hl0.eventually (gt_mem_nhds hm),hh0.eventually (lt_mem_nhds hM)] with n hln hhn
  change 0 < -l n ∧ -l n < h n-l n ∧ 0 < E n ∧ 0 < F n ∧ _
  refine ⟨by linarith,by linarith,hE n,hF n,?_⟩
  change -E n < -(slopeLower g 0+E n*a)+slopeLower g 0 ∧
    -(slopeLower g 0+E n*a)+slopeLower g 0 < 0 ∧
    slopeUpper g 0-F n*b-(slopeLower g 0+E n*a) <
      -(slopeLower g 0+E n*a)+slopeUpper g 0 ∧
    -(slopeLower g 0+E n*a)+slopeUpper g 0 <
      slopeUpper g 0-F n*b-(slopeLower g 0+E n*a)+F n
  have hea := mul_pos (hE n) ha.1
  have heb := mul_lt_of_lt_one_right (hE n) ha.2
  have hfa := mul_pos (hF n) hb.1
  have hfb := mul_lt_of_lt_one_right (hF n) hb.2
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

end BrownianAffine
