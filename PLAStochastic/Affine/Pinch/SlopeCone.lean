import PLAStochastic.Affine.Pinch.OffsetAnchor

/-!
# The literal continuous slope cone

The lower and upper bounds are exactly the manuscript's sup/inf of
`(f(t)-η∓ε)/t` over `0 < t ≤ T`. Whenever one feasible line exists,
these are finite real bounds and the feasible set is precisely their interval.
The first closed-budget hit is identified with their first equality.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def continuousSlopeFeasible (f : ℝ → ℝ) (η ε T a : ℝ) : Prop :=
  ∀ t : Icc (0 : ℝ) T, |f t - η - a * (t : ℝ)| ≤ ε

def continuousLowerSlope (f : ℝ → ℝ) (η ε T : ℝ) : ℝ :=
  sSup (range (fun t : Ioc (0 : ℝ) T => (f t - η - ε) / (t : ℝ)))

def continuousUpperSlope (f : ℝ → ℝ) (η ε T : ℝ) : ℝ :=
  sInf (range (fun t : Ioc (0 : ℝ) T => (f t - η + ε) / (t : ℝ)))

theorem lowerSlope_range_bddAbove {f : ℝ → ℝ} {η ε T a : ℝ}
    (ha : continuousSlopeFeasible f η ε T a) :
    BddAbove (range (fun t : Ioc (0 : ℝ) T => (f t - η - ε) / (t : ℝ))) := by
  refine ⟨a, ?_⟩
  rintro _ ⟨t, rfl⟩
  apply (div_le_iff₀ t.property.1).mpr
  have hh := (abs_le.mp (ha ⟨t, t.property.1.le, t.property.2⟩)).2
  linarith

theorem upperSlope_range_bddBelow {f : ℝ → ℝ} {η ε T a : ℝ}
    (ha : continuousSlopeFeasible f η ε T a) :
    BddBelow (range (fun t : Ioc (0 : ℝ) T => (f t - η + ε) / (t : ℝ))) := by
  refine ⟨a, ?_⟩
  rintro _ ⟨t, rfl⟩
  apply (le_div_iff₀ t.property.1).mpr
  have hh := (abs_le.mp (ha ⟨t, t.property.1.le, t.property.2⟩)).1
  linarith

theorem continuousLowerSlope_le_feasible {f : ℝ → ℝ} {η ε T a : ℝ} (hT : 0 < T)
    (ha : continuousSlopeFeasible f η ε T a) : continuousLowerSlope f η ε T ≤ a := by
  have hne : (range (fun t : Ioc (0 : ℝ) T => (f t - η - ε) / (t : ℝ))).Nonempty :=
    ⟨_, ⟨⟨T, hT, le_rfl⟩, rfl⟩⟩
  apply csSup_le hne
  rintro _ ⟨t, rfl⟩
  apply (div_le_iff₀ t.property.1).mpr
  have hh := (abs_le.mp (ha ⟨t, t.property.1.le, t.property.2⟩)).2
  linarith

theorem feasible_le_continuousUpperSlope {f : ℝ → ℝ} {η ε T a : ℝ} (hT : 0 < T)
    (ha : continuousSlopeFeasible f η ε T a) : a ≤ continuousUpperSlope f η ε T := by
  have hne : (range (fun t : Ioc (0 : ℝ) T => (f t - η + ε) / (t : ℝ))).Nonempty :=
    ⟨_, ⟨⟨T, hT, le_rfl⟩, rfl⟩⟩
  apply le_csInf hne
  rintro _ ⟨t, rfl⟩
  apply (le_div_iff₀ t.property.1).mpr
  have hh := (abs_le.mp (ha ⟨t, t.property.1.le, t.property.2⟩)).1
  linarith

/-- An existing feasible slope supplies the bounds required by conditional
suprema/infima; no infinite cone endpoint is silently represented by zero. -/
theorem continuousSlopeFeasible_iff_mem_Icc {f : ℝ → ℝ} {η ε T : ℝ} (hT : 0 < T)
    (hex : ∃ a, continuousSlopeFeasible f η ε T a) (b : ℝ) :
    continuousSlopeFeasible f η ε T b ↔
      b ∈ Icc (continuousLowerSlope f η ε T) (continuousUpperSlope f η ε T) := by
  obtain ⟨a, ha⟩ := hex
  refine ⟨fun hb => ⟨continuousLowerSlope_le_feasible hT hb,
    feasible_le_continuousUpperSlope hT hb⟩, fun hb t => ?_⟩
  by_cases ht : (t : ℝ) = 0
  · have h0 := ha ⟨0, le_rfl, hT.le⟩
    simpa only [ht, mul_zero, sub_zero] using h0
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    have hl : (f t - η - ε) / (t : ℝ) ≤ b :=
      (le_csSup (lowerSlope_range_bddAbove ha) ⟨⟨t, htpos, t.property.2⟩, rfl⟩).trans hb.1
    have hu : b ≤ (f t - η + ε) / (t : ℝ) :=
      hb.2.trans (csInf_le (upperSlope_range_bddBelow ha) ⟨⟨t, htpos, t.property.2⟩, rfl⟩)
    have hl' := (div_le_iff₀ htpos).mp hl
    have hu' := (le_div_iff₀ htpos).mp hu
    apply abs_le.mpr
    constructor <;> linarith

/-- A singleton feasible set is literally equality of the two cone endpoints. -/
theorem continuousCone_eq_of_unique {f : ℝ → ℝ} {η ε T a : ℝ} (hT : 0 < T)
    (ha : continuousSlopeFeasible f η ε T a)
    (hu : ∀ b, continuousSlopeFeasible f η ε T b → b = a) :
    continuousLowerSlope f η ε T = a ∧ continuousUpperSlope f η ε T = a := by
  have hl := continuousLowerSlope_le_feasible hT ha
  have hh := feasible_le_continuousUpperSlope hT ha
  constructor
  · apply hu
    exact (continuousSlopeFeasible_iff_mem_Icc hT ⟨a, ha⟩ _).mpr ⟨le_rfl, hl.trans hh⟩
  · apply hu
    exact (continuousSlopeFeasible_iff_mem_Icc hT ⟨a, ha⟩ _).mpr ⟨hl.trans hh, le_rfl⟩

/-- A fit with a uniform strict margin leaves a nontrivial interval of slopes. -/
theorem continuousCone_lt_of_strict_fit {f : ℝ → ℝ} {η ε d T a : ℝ} (hT : 0 < T)
    (hd : d < ε) (ha : continuousSlopeFeasible f η d T a) :
    continuousLowerSlope f η ε T < continuousUpperSlope f η ε T := by
  let r := (ε - d) / (T + 1)
  have hr : 0 < r := div_pos (sub_pos.mpr hd) (by linarith)
  have hmul : r * (T + 1) = ε - d := div_mul_cancel₀ _ (by linarith)
  have ha' : continuousSlopeFeasible f η ε T a := fun t => (ha t).trans hd.le
  have hb : continuousSlopeFeasible f η ε T (a + r) := by
    intro t
    have hrt : r * (t : ℝ) ≤ r * T := mul_le_mul_of_nonneg_left t.property.2 hr.le
    calc
      |f t - η - (a + r) * (t : ℝ)| = |(f t - η - a * (t : ℝ)) - r * (t : ℝ)| := by congr 1; ring
      _ ≤ |f t - η - a * (t : ℝ)| + |r * (t : ℝ)| := abs_sub _ _
      _ ≤ ε := by
        rw [abs_mul, abs_of_pos hr, abs_of_nonneg t.property.1]
        have hh := ha t
        nlinarith
  exact (continuousLowerSlope_le_feasible hT ha').trans_lt
    ((by linarith : a < a + r).trans_le (feasible_le_continuousUpperSlope hT hb))

theorem continuousCone_lt_of_error_lt (f : C(ℝ, ℝ)) (η : ℝ) {ε : ℝ}
    {T : ℝ≥0} (hT : 0 < T) (herr : anchoredTimeError (offsetPath f η) T < ε) :
    continuousLowerSlope f η ε T < continuousUpperSlope f η ε T := by
  have heq := anchoredTimeError_eq_interval T.property (offsetPath f η)
  obtain ⟨a, ha⟩ := (anchoredError_le_iff_exists_fit T.property (intervalPath (offsetPath f η) T)).mp
    (le_refl (anchoredError (intervalPath (offsetPath f η) T)))
  exact continuousCone_lt_of_strict_fit hT (heq.symm.trans_lt herr) ha

theorem continuousCone_eq_at_firstReach (f : C(ℝ, ℝ)) {η ε : ℝ}
    (hzero : |f 0 - η| < ε) {σ : ℝ≥0} (hpos : 0 < σ)
    (hσ : firstReach (fun t : ℝ≥0 => anchoredTimeError (offsetPath f η) t) ε = σ) :
    continuousLowerSlope f η ε σ = continuousUpperSlope f η ε σ := by
  have herr := error_at_firstReach (anchoredTimeError_nnreal_monotone (offsetPath f η))
    ((continuous_anchoredTimeError _).comp continuous_subtype_val)
    (by simpa only [NNReal.coe_zero, anchoredTimeError_zero, offsetPath_apply] using hzero) hσ
  have he : anchoredError (intervalPath (offsetPath f η) σ) = ε :=
    (anchoredTimeError_eq_interval σ.property (offsetPath f η)).symm.trans herr
  obtain ⟨a, ha⟩ := (anchoredError_le_iff_exists_fit σ.property (intervalPath (offsetPath f η) σ)).mp he.le
  have hu : ∀ b, continuousSlopeFeasible f η ε σ b → b = a := by
    intro b hb
    exact anchored_feasible_slope_unique σ.property ((abs_nonneg _).trans_lt hzero)
      (intervalPath (offsetPath f η) σ) hzero he hb ha
  have heq := continuousCone_eq_of_unique hpos ha hu
  exact heq.1.trans heq.2.symm

theorem continuousCone_lt_before_firstReach (f : C(ℝ, ℝ)) (η ε : ℝ)
    {T σ : ℝ≥0} (hT : 0 < T) (hTσ : T < σ)
    (hσ : firstReach (fun t : ℝ≥0 => anchoredTimeError (offsetPath f η) t) ε = σ) :
    continuousLowerSlope f η ε T < continuousUpperSlope f η ε T := by
  apply continuousCone_lt_of_error_lt f η hT
  by_contra h
  have hle := firstReach_le_of_reaches
    (D := fun t : ℝ≥0 => anchoredTimeError (offsetPath f η) t) (t := T) (le_of_not_gt h)
  rw [hσ] at hle
  exact hTσ.not_ge (ENNReal.coe_le_coe.mp hle)

/-- The manuscript's first equality of the literal lower and upper cone bounds. -/
def firstContinuousConePinch (f : ℝ → ℝ) (η ε : ℝ) : ℝ≥0∞ :=
  ⨅ t : ℝ≥0, if 0 < t ∧ continuousLowerSlope f η ε t = continuousUpperSlope f η ε t
    then (t : ℝ≥0∞) else ⊤

/-- The first cone equality is the first closed-budget hit for every continuous
path with interior initial residual and a positive finite first hit. -/
theorem firstContinuousConePinch_eq_firstReach (f : C(ℝ, ℝ)) {η ε : ℝ}
    (hzero : |f 0 - η| < ε) {σ : ℝ≥0} (hpos : 0 < σ)
    (hσ : firstReach (fun t : ℝ≥0 => anchoredTimeError (offsetPath f η) t) ε = σ) :
    firstContinuousConePinch f η ε = σ := by
  apply le_antisymm
  · exact (iInf_le _ σ).trans_eq (if_pos
      ⟨hpos, continuousCone_eq_at_firstReach f hzero hpos hσ⟩)
  · apply le_iInf
    intro t
    split_ifs with ht
    · by_contra h
      have hts : t < σ := ENNReal.coe_lt_coe.mp (lt_of_not_ge h)
      exact (continuousCone_lt_before_firstReach f η ε ht.1 hts hσ).ne ht.2
    · exact le_top

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- For Brownian motion the paper's literal cone pinch equals the actual
failure lifetime with the given interior fitted offset. -/
theorem firstContinuousConePinch_ae_eq_offsetLifetime (hB : IsBrownianReal B μ)
    {η ε : ℝ} (hη : |η| < ε) :
    (fun ω => firstContinuousConePinch (processPath B ω) η ε) =ᵐ[μ]
      offsetProcessLifetime B η ε := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero, continuousBrownianPath_ae_eq hB,
    brownianOffsetPinch_ae_pos hB hη, brownianOffsetPinch_ae_ne_top hB hη,
    brownianOffsetPinch_ae_eq_lifetime hB hη] with ω hc hz hp hpos hf heq
  obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.mp hf
  have hσ' : brownianOffsetPinch hB η ε ω = (σ : ℝ≥0∞) := hσ.symm
  have hposENN : (0 : ℝ≥0∞) < (σ : ℝ≥0∞) := by
    rw [← hσ']
    exact hpos
  have hpos' : 0 < σ := ENNReal.coe_pos.mp hposENN
  have hfirst : firstReach (fun t : ℝ≥0 => anchoredTimeError (offsetPath (processPath B ω) η) t) ε = σ := by
    rw [← hp]
    exact hσ.symm
  have hzero : |processPath B ω 0 - η| < ε := by
    rw [← NNReal.coe_zero, processPath_apply_of_continuous hc 0, hz, zero_sub, abs_neg]
    exact hη
  exact (firstContinuousConePinch_eq_firstReach (processPath B ω) hzero hpos' hfirst).trans
    (hσ.trans heq)

end BrownianAffine

