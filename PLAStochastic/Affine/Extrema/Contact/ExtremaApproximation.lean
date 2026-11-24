import PLAStochastic.Affine.Extrema.Contact.Construction
import PLAStochastic.Affine.Extrema.Contact.Localization

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Uniqueness of the maximum gives a strict, uniform gap on any earlier compact prefix. -/
theorem exists_prefix_gap_before_upperTime {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω))
    (hu : DifferentiableAt ℝ (slopeUpper (unitPath (processPath B ω) 1)) 0)
    {q : ℝ≥0} (hq : (q : ℝ) < (upperTime (unitPath (processPath B ω) 1) 0 : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ≥0, t ≤ q →
      B t ω ≤ slopeUpper (unitPath (processPath B ω) 1) 0-c := by
  let g := unitPath (processPath B ω) 1
  have hq1 : q ≤ 1 := by
    exact_mod_cast hq.le.trans (upperTime g 0).property.2
  obtain ⟨t,ht,hm⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) q)).exists_isMaxOn
    ⟨0,bot_le,bot_le⟩ hc.continuousOn
  have hv := slopeResidual_le_upper g 0 (nnrealRangeTime t (ht.2.trans hq1))
  rw [slopeResidual_actual_unit B hc 0 t (ht.2.trans hq1)] at hv
  simp only [zero_mul,sub_zero] at hv
  have hlt : B t ω < slopeUpper g 0 := by
    apply lt_of_le_of_ne hv
    intro heq
    have huq := upperTime_unique_of_differentiable g hu
      (show slopeResidual g 0 (nnrealRangeTime t (ht.2.trans hq1))=slopeUpper g 0 by
        rw [slopeResidual_actual_unit B hc 0 t (ht.2.trans hq1)]
        simpa only [zero_mul,sub_zero] using heq)
    have htime : (t : ℝ)=(upperTime g 0 : ℝ) := congrArg Subtype.val huq
    have htq : (t : ℝ) ≤ (q : ℝ) := by exact_mod_cast ht.2
    linarith
  refine ⟨slopeUpper g 0-B t ω,sub_pos.mpr hlt,?_⟩
  intro u huq
  have h := hm ⟨bot_le,huq⟩
  change B u ω ≤ B t ω at h
  change B u ω ≤ slopeUpper g 0-(slopeUpper g 0-B t ω)
  linarith

/-- If the minimum occurs first, every sufficiently thin valid minimum-maximum
rectangle contains the actual ordered two-contact path event. -/
theorem eventually_orderedContactLayer_of_ordered_extrema {Ω : Type*}
    {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω)) (h0 : B 0 ω=0)
    (hu : DifferentiableAt ℝ (slopeUpper (unitPath (processPath B ω) 1)) 0)
    (horder : (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ) <
      (upperTime (unitPath (processPath B ω) 1) 0 : ℝ))
    {X R E F : ℕ → ℝ} (hR : ∀ n, 0 < R n) (hX : ∀ n, X n ∈ Ioo 0 (R n))
    (hE : ∀ n, 0 < E n) (hF : ∀ n, 0 < F n) (hFlim : Tendsto F atTop (𝓝 0))
    (hrect : ∀ n, -E n < X n+slopeLower (unitPath (processPath B ω) 1) 0 ∧
      X n+slopeLower (unitPath (processPath B ω) 1) 0 < 0 ∧
      R n < X n+slopeUpper (unitPath (processPath B ω) 1) 0 ∧
      X n+slopeUpper (unitPath (processPath B ω) 1) 0 < R n+F n) :
    ∀ᶠ n in atTop, orderedContactLayerEvent B (X n) (R n) (E n) (F n) 1 univ univ univ ω := by
  let g := unitPath (processPath B ω) 1
  let q : ℝ≥0 := ⟨(lowerTime g 0 : ℝ),(lowerTime g 0).property.1⟩
  let v : ℝ≥0 := ⟨(upperTime g 0 : ℝ),(upperTime g 0).property.1⟩
  have hqv : q < v := by exact_mod_cast horder
  have hv1 : v ≤ 1 := by exact_mod_cast (upperTime g 0).property.2
  have hq1 : q ≤ 1 := hqv.le.trans hv1
  have heq : nnrealRangeTime q hq1=lowerTime g 0 := Subtype.ext rfl
  have hev : nnrealRangeTime v hv1=upperTime g 0 := Subtype.ext rfl
  have hmin := lowerTime_attains g 0
  have hmax := upperTime_attains g 0
  rw [← heq,slopeResidual_actual_unit B hc 0 q hq1] at hmin
  rw [← hev,slopeResidual_actual_unit B hc 0 v hv1] at hmax
  simp only [zero_mul,sub_zero] at hmin hmax
  obtain ⟨c,hc0,hgap⟩ := exists_prefix_gap_before_upperTime hc hu (q := q) horder
  filter_upwards [hFlim.eventually_lt_const hc0] with n hn
  apply orderedContactLayer_of_separated_contacts hc h0 (hR n) (hX n) (hE n) (hF n) hqv hv1
  · rw [hmin]
    exact (hrect n).2.1
  · intro t ht
    have h := hgap t ht
    have hb := (hrect n).2.2.2
    change X n+slopeUpper g 0 < R n+F n at hb
    linarith
  · rw [hmax]
    exact (hrect n).2.2.1
  · intro t ht
    have hl := slopeLower_le_residual g 0 (nnrealRangeTime t ht)
    have hh := slopeResidual_le_upper g 0 (nnrealRangeTime t ht)
    rw [slopeResidual_actual_unit B hc 0 t ht] at hl hh
    simp only [zero_mul,sub_zero] at hl hh
    have hb := hrect n
    change -E n < X n+slopeLower g 0 ∧ _ ∧ _ ∧ X n+slopeUpper g 0 < R n+F n at hb
    constructor <;> linarith [hb.1,hb.2.2.2]
  · exact mem_univ _

/-- Reverse-ordered extrema eventually exclude every shrinking ordered contact layer. -/
theorem eventually_not_orderedContactLayer_of_reverse_extrema {Ω : Type*}
    {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω))
    (hl : DifferentiableAt ℝ (slopeLower (unitPath (processPath B ω) 1)) 0)
    (hu : DifferentiableAt ℝ (slopeUpper (unitPath (processPath B ω) 1)) 0)
    (horder : (upperTime (unitPath (processPath B ω) 1) 0 : ℝ) <
      (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ))
    {X R E F : ℕ → ℝ} (hR : ∀ n, 0 < R n) (hE : ∀ n, 0 < E n) (hF : ∀ n, 0 < F n)
    (hElim : Tendsto E atTop (𝓝 0)) (hFlim : Tendsto F atTop (𝓝 0)) {S D₁ D₂ : Set ℝ} :
    ∀ᶠ n in atTop, ¬ orderedContactLayerEvent B (X n) (R n) (E n) (F n) 1 S D₁ D₂ ω := by
  by_contra h
  have hf : ∃ᶠ n in atTop, orderedContactLayerEvent B (X n) (R n) (E n) (F n) 1 S D₁ D₂ ω := h
  obtain ⟨k,hk,hke⟩ := exists_seq_forall_of_frequently hf
  have htime := orderedContactLayer_limit_times hc hl hu
    (fun n => hR (k n)) (fun n => hE (k n)) (fun n => hF (k n))
    (hElim.comp hk) (hFlim.comp hk) hke
  exact horder.not_ge htime.1

/-- A time window whose closure misses the actual limiting time eventually excludes
the shrinking layer, even when its two level parameters vary arbitrarily. -/
theorem eventually_not_orderedContactLayer_of_time_window {Ω : Type*}
    {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω))
    (hl : DifferentiableAt ℝ (slopeLower (unitPath (processPath B ω) 1)) 0)
    (hu : DifferentiableAt ℝ (slopeUpper (unitPath (processPath B ω) 1)) 0)
    {X R E F : ℕ → ℝ} (hR : ∀ n, 0 < R n) (hE : ∀ n, 0 < E n) (hF : ∀ n, 0 < F n)
    (hElim : Tendsto E atTop (𝓝 0)) (hFlim : Tendsto F atTop (𝓝 0)) {S D₁ D₂ : Set ℝ}
    (hbad : (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ) ∉ closure D₁ ∨
      ((upperTime (unitPath (processPath B ω) 1) 0 : ℝ)-
        (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ)) ∉ closure D₂) :
    ∀ᶠ n in atTop, ¬ orderedContactLayerEvent B (X n) (R n) (E n) (F n) 1 S D₁ D₂ ω := by
  by_contra h
  have hf : ∃ᶠ n in atTop, orderedContactLayerEvent B (X n) (R n) (E n) (F n) 1 S D₁ D₂ ω := h
  obtain ⟨k,hk,hke⟩ := exists_seq_forall_of_frequently hf
  have htime := orderedContactLayer_limit_times hc hl hu
    (fun n => hR (k n)) (fun n => hE (k n)) (fun n => hF (k n))
    (hElim.comp hk) (hFlim.comp hk) hke
  exact hbad.elim (fun h => h htime.2.1) (fun h => h htime.2.2)

/-- Ordered extrema in open time windows generate the actual marked contact layer
for every sufficiently thin valid rectangle around the two extremal values. -/
theorem eventually_orderedContactLayer_of_open_time_windows {Ω : Type*}
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
    {D₁ D₂ : Set ℝ} (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    (ht₁ : (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ) ∈ D₁)
    (ht₂ : ((upperTime (unitPath (processPath B ω) 1) 0 : ℝ)-
      (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ)) ∈ D₂) :
    ∀ᶠ n in atTop, orderedContactLayerEvent B (X n) (R n) (E n) (F n) 1 univ D₁ D₂ ω := by
  have hb₁ : (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ) ∉ closure D₁ᶜ := by
    rw [hD₁.isClosed_compl.closure_eq]
    exact fun h => h ht₁
  have hb₂ : ((upperTime (unitPath (processPath B ω) 1) 0 : ℝ)-
      (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ)) ∉ closure D₂ᶜ := by
    rw [hD₂.isClosed_compl.closure_eq]
    exact fun h => h ht₂
  filter_upwards [eventually_orderedContactLayer_of_ordered_extrema hc h0 hu horder
      hR hX hE hF hFlim hrect,
    eventually_not_orderedContactLayer_of_time_window (X := X) (S := univ) (D₂ := univ)
      hc hl hu hR hE hF hElim hFlim (Or.inl hb₁),
    eventually_not_orderedContactLayer_of_time_window (X := X) (S := univ) (D₁ := univ)
      hc hl hu hR hE hF hElim hFlim (Or.inr hb₂)] with n hn hn₁ hn₂
  refine ⟨⟨?_,hn.1.2⟩,hn.2.1,hn.2.2.1,?_⟩
  · by_contra h
    exact hn₁ ⟨⟨h,hn.1.2⟩,hn.2.1,hn.2.2⟩
  · by_contra h
    exact hn₂ ⟨hn.1,hn.2.1,hn.2.2.1,h⟩

end BrownianAffine
