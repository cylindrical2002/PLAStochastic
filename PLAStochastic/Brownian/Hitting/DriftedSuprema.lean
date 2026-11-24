import PLAStochastic.Brownian.PathLaw.TimeInversion

/-!
# The joint law of the two drifted suprema

Both suprema are formed from one path. Extended nonnegative values retain
possible infinity; no finiteness or independence assumption is imposed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

/-- The nonnegative extended supremum of a path minus linear drift. -/
def driftedSup (X : ℝ≥0 → ℝ) (e : ℝ) : ℝ≥0∞ :=
  ⨆ u : ℝ≥0, ENNReal.ofReal (X u - e * (u : ℝ))

/-- The upward and downward suprema of the same path. -/
def driftedPair (X : ℝ≥0 → ℝ) (e : ℝ) : ℝ≥0∞ × ℝ≥0∞ :=
  (driftedSup X e, driftedSup (fun u => -X u) e)

def driftedSum (X : ℝ≥0 → ℝ) (e : ℝ) : ℝ≥0∞ :=
  driftedSup X e + driftedSup (fun u => -X u) e

/-- The manuscript's real supremum; agreement with the extended version is
proved whenever the latter is finite and the path starts at zero. -/
def realDriftedSup (X : ℝ≥0 → ℝ) (e : ℝ) : ℝ :=
  ⨆ u : ℝ≥0, X u - e * (u : ℝ)

def realDriftedSum (X : ℝ≥0 → ℝ) (e : ℝ) : ℝ :=
  realDriftedSup X e + realDriftedSup (fun u => -X u) e

theorem driftedSup_bddAbove {X : ℝ≥0 → ℝ} {e : ℝ} (h : driftedSup X e ≠ ⊤) :
    BddAbove (Set.range (fun u : ℝ≥0 => X u - e * (u : ℝ))) := by
  refine ⟨(driftedSup X e).toReal, ?_⟩
  rintro _ ⟨u, rfl⟩
  exact (ENNReal.ofReal_le_iff_le_toReal h).mp
    (le_iSup (fun u : ℝ≥0 => ENNReal.ofReal (X u - e * (u : ℝ))) u)

theorem driftedSup_eq_ofReal_realDriftedSup {X : ℝ≥0 → ℝ} {e : ℝ}
    (h : driftedSup X e ≠ ⊤) : driftedSup X e = ENNReal.ofReal (realDriftedSup X e) := by
  apply le_antisymm
  · apply iSup_le
    intro u
    exact ENNReal.ofReal_le_ofReal (le_ciSup (driftedSup_bddAbove h) u)
  · apply ENNReal.ofReal_le_of_le_toReal
    apply ciSup_le
    intro u
    exact (ENNReal.ofReal_le_iff_le_toReal h).mp
      (le_iSup (fun u : ℝ≥0 => ENNReal.ofReal (X u - e * (u : ℝ))) u)

theorem driftedSup_toReal_eq_realDriftedSup {X : ℝ≥0 → ℝ} {e : ℝ}
    (h0 : X 0 = 0) (h : driftedSup X e ≠ ⊤) :
    (driftedSup X e).toReal = realDriftedSup X e := by
  have hn : 0 ≤ realDriftedSup X e := by
    simpa only [realDriftedSup, h0, NNReal.coe_zero, mul_zero, sub_zero] using!
      (le_ciSup (driftedSup_bddAbove h) (0 : ℝ≥0))
  rw [driftedSup_eq_ofReal_realDriftedSup h, ENNReal.toReal_ofReal hn]

theorem driftedSum_toReal_eq_realDriftedSum {X : ℝ≥0 → ℝ} {e : ℝ}
    (h0 : X 0 = 0) (hA : driftedSup X e ≠ ⊤) (hC : driftedSup (fun u => -X u) e ≠ ⊤) :
    (driftedSum X e).toReal = realDriftedSum X e := by
  unfold driftedSum realDriftedSum
  rw [ENNReal.toReal_add hA hC, driftedSup_toReal_eq_realDriftedSup h0 hA,
    driftedSup_toReal_eq_realDriftedSup (by simp [h0]) hC]

def sampledDriftedSup (g : InversionSample → ℝ) (e : ℝ) : ℝ≥0∞ :=
  ⨆ q : InversionSample, ENNReal.ofReal (g q - e * (q.1 : ℝ))

def sampledDriftedPair (g : InversionSample → ℝ) (e : ℝ) : ℝ≥0∞ × ℝ≥0∞ :=
  (sampledDriftedSup g e, sampledDriftedSup (fun q => -g q) e)

theorem measurable_sampledDriftedSup (e : ℝ) :
    Measurable (fun g => sampledDriftedSup g e) := by
  apply Measurable.iSup
  intro q
  exact ENNReal.measurable_ofReal.comp ((measurable_pi_apply q).sub measurable_const)

theorem measurable_sampledDriftedPair (e : ℝ) :
    Measurable (fun g => sampledDriftedPair g e) :=
  (measurable_sampledDriftedSup e).prodMk
    ((measurable_sampledDriftedSup e).comp
      (measurable_pi_lambda _ (fun q => (measurable_pi_apply q).neg)))

/-- Continuity recovers each full-time supremum on a countable dense set. -/
theorem sampledDriftedSup_eq {X : ℝ≥0 → ℝ} (hX : Continuous X) (e : ℝ) :
    sampledDriftedSup (fun q : InversionSample => X q.1) e = driftedSup X e := by
  apply inversionSampleSet_dense.ciSup' (f := fun u : ℝ≥0 => ENNReal.ofReal (X u - e * (u : ℝ)))
  exact ENNReal.continuous_ofReal.comp
    (hX.sub (continuous_const.mul continuous_subtype_val))

theorem sampledDriftedPair_eq {X : ℝ≥0 → ℝ} (hX : Continuous X) (e : ℝ) :
    sampledDriftedPair (fun q : InversionSample => X q.1) e = driftedPair X e := by
  exact Prod.ext (sampledDriftedSup_eq hX e) (sampledDriftedSup_eq hX.neg e)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {B C : ℝ≥0 → Ω → ℝ}

theorem sampledDriftedPair_ae_eq (hB : IsBrownianReal B μ) (e : ℝ) :
    (fun ω => sampledDriftedPair (fun q : InversionSample => B q.1 ω) e) =ᵐ[μ]
      (fun ω => driftedPair (B · ω) e) :=
  hB.cont.mono (fun _ hω => sampledDriftedPair_eq hω e)

theorem aemeasurable_driftedPair (hB : IsBrownianReal B μ) (e : ℝ) :
    AEMeasurable (fun ω => driftedPair (B · ω) e) μ :=
  ((measurable_sampledDriftedPair e).comp_aemeasurable
    (aemeasurable_pi_lambda _ (fun q => hB.aemeasurable q.1))).congr
      (sampledDriftedPair_ae_eq hB e)

theorem aemeasurable_driftedSum (hB : IsBrownianReal B μ) (e : ℝ) :
    AEMeasurable (fun ω => driftedSum (B · ω) e) μ :=
  (aemeasurable_driftedPair hB e).fst.add (aemeasurable_driftedPair hB e).snd

/-- Equal Brownian laws identify the pair jointly, without an independence claim. -/
theorem identDistrib_driftedPair (hB : IsBrownianReal B μ) (hC : IsBrownianReal C μ)
    (e : ℝ) :
    IdentDistrib (fun ω => driftedPair (B · ω) e) (fun ω => driftedPair (C · ω) e) μ μ := by
  have h := (identDistrib_countable_observations hB.toIsPreBrownianReal
    hC.toIsPreBrownianReal (fun q : InversionSample => q.1)).comp
      (measurable_sampledDriftedPair e)
  exact (IdentDistrib.of_ae_eq h.aemeasurable_fst (sampledDriftedPair_ae_eq hB e)).symm.trans
    (h.trans (IdentDistrib.of_ae_eq h.aemeasurable_snd (sampledDriftedPair_ae_eq hC e)))

theorem identDistrib_driftedSum (hB : IsBrownianReal B μ) (hC : IsBrownianReal C μ)
    (e : ℝ) :
    IdentDistrib (fun ω => driftedSum (B · ω) e) (fun ω => driftedSum (C · ω) e) μ μ :=
  (identDistrib_driftedPair hB hC e).comp
    (by fun_prop : Measurable (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 + p.2))

/-- Drift normalization uses the same Brownian scaling for both signs. -/
def driftScaledBrownian (B : ℝ≥0 → Ω → ℝ) (a : ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ :=
  (a : ℝ) * B (u / (a * a)) ω

theorem isBrownianReal_driftScaled (hB : IsBrownianReal B μ) {a : ℝ≥0} (ha : a ≠ 0) :
    IsBrownianReal (driftScaledBrownian B a) μ := by
  convert hB.smul (c := (a * a)⁻¹) (inv_ne_zero (mul_ne_zero ha ha)) using 1
  ext u ω
  simp [driftScaledBrownian, NNReal.coe_inv, NNReal.coe_mul,
    div_eq_mul_inv, mul_comm u]

omit [MeasurableSpace Ω] in
theorem driftedSup_scale (X : ℝ≥0 → ℝ) {a : ℝ≥0} (ha : a ≠ 0) :
    driftedSup (fun u => (a : ℝ) * X (u / (a * a))) 1 =
      ENNReal.ofReal (a : ℝ) * driftedSup X (a : ℝ) := by
  have hsurj : Function.Surjective (fun u : ℝ≥0 => (a * a) * u) := by
    intro u
    exact ⟨u / (a * a), mul_div_cancel₀ u (mul_ne_zero ha ha)⟩
  unfold driftedSup
  rw [← hsurj.iSup_comp, ENNReal.mul_iSup]
  apply iSup_congr
  intro u
  dsimp only
  rw [mul_div_cancel_left₀ u (mul_ne_zero ha ha)]
  calc
    ENNReal.ofReal ((a : ℝ) * X u - 1 * ((a * a * u : ℝ≥0) : ℝ)) =
        ENNReal.ofReal ((a : ℝ) * (X u - (a : ℝ) * (u : ℝ))) := by
      congr 1
      push_cast
      ring
    _ = _ := ENNReal.ofReal_mul a.property

omit [MeasurableSpace Ω] in
theorem driftedSum_scale (X : ℝ≥0 → ℝ) {a : ℝ≥0} (ha : a ≠ 0) :
    driftedSum (fun u => (a : ℝ) * X (u / (a * a))) 1 =
      ENNReal.ofReal (a : ℝ) * driftedSum X (a : ℝ) := by
  unfold driftedSum
  rw [driftedSup_scale X ha]
  have hn : (fun u => -((a : ℝ) * X (u / (a * a)))) =
      (fun u => (a : ℝ) * (-X (u / (a * a)))) := by
    funext u
    ring
  rw [hn, driftedSup_scale (fun u => -X u) ha, mul_add]

/-- Joint scaling yields the law of the sum, even before proving its finiteness. -/
theorem identDistrib_scaled_driftedSum (hB : IsBrownianReal B μ) {a : ℝ≥0} (ha : a ≠ 0) :
    IdentDistrib (fun ω => ENNReal.ofReal (a : ℝ) * driftedSum (B · ω) (a : ℝ))
      (fun ω => driftedSum (B · ω) 1) μ μ := by
  have h := identDistrib_driftedSum (isBrownianReal_driftScaled hB ha) hB 1
  convert h using 1
  funext ω
  exact (driftedSum_scale (B · ω) ha).symm

end BrownianAffine
