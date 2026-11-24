import PLAStochastic.Index.CEPS.Band.WidthHadamard

/-! # First width derivatives in the killed-gap discount half-plane -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

/-- The actual bottom resolvent has the Hadamard derivative throughout the interior bandwidth
window. Both factors are continuous by the previously proved width regularity. -/
theorem cepsBand_bottomSurv_hasDerivAt_interior {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {K : ℝ≥0} (hLip : LipschitzWith K f) {w l : ℝ} (hw : 2 ≤ w)
    (hl : w / 2 < l) (hlw : l < 2 * w) (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|)
    {q : ℂ} (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) :
    HasDerivAt (cepsBottomSurv ν β a q)
      (cepsBridgeSeries ν f β a q l * cepsTopSurv ν β a q l) l := by
  let F := fun z => cepsBridgeSeries ν f β a q z * cepsTopSurv ν β a q z
  have ha' : 1 / 2 ≤ |-a| := by simpa only [abs_neg] using ha
  have hc₁ := cepsBand_bridgeSeries_continuousOn hD hθ hvlo hvhi hν hf hLip hw β ha hq
  have hc₂ := cepsBand_bottomSurv_continuousOn hD hθ hvlo hvhi hν hf hw (-β) ha' hq
  have htop : ContinuousOn (cepsTopSurv ν β a q) (Icc (w / 2) (2 * w)) := by
    have heq : cepsTopSurv ν β a q = cepsBottomSurv ν (-β) (-a) q :=
      funext (cepsBand_topSurv_eq_reverse ν β a q)
    rw [heq]
    exact hc₂
  have hc : ContinuousAt F l := (hc₁.mul htop).continuousAt (Icc_mem_nhds hl hlw)
  have hint : IntegrableOn F (Ioc (w / 2) (2 * w)) :=
    (cepsBand_bottomSurv_sub hD hθ hvlo hvhi hν hf hw β ha hq le_rfl (by linarith) le_rfl).1
  have hII : IntervalIntegrable F volume (w / 2) l :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hl.le).mpr
      (hint.mono_set (Ioc_subset_Ioc le_rfl hlw.le))
  have hmeas : StronglyMeasurableAtFilter F (nhds l) :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
      (s := Ioc (w / 2) (2 * w)) hint.aestronglyMeasurable (Ioc_mem_nhds hl hlw)
  have hd := intervalIntegral.integral_hasDerivAt_right hII hmeas hc
  have heq : (fun u => cepsBottomSurv ν β a q (w / 2) + ∫ x in w / 2..u, F x) =ᶠ[nhds l]
      cepsBottomSurv ν β a q := by
    filter_upwards [Ioo_mem_nhds hl hlw] with u hu
    rw [intervalIntegral.integral_of_le hu.1.le,
      ← (cepsBand_bottomSurv_sub hD hθ hvlo hvhi hν hf hw β ha hq
        le_rfl hu.1.le hu.2.le).2]
    ring
  exact (hd.const_add _).congr_of_eventuallyEq heq.symm

/-- A class constant for the first width derivative. -/
def cepsBandFirstWidthConst (D vlo vhi : ℝ) : ℝ :=
  cepsBandMomentConst (cepsBandPinDecayConst D vlo vhi) (krKappa D vlo vhi) 0 *
    cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) 0

/-- Every point of the closed window, including its ends, has a genuine width derivative.
The smaller discount fraction pays for a neighborhood around either endpoint. -/
theorem cepsBand_bottomSurv_first_width {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {K : ℝ≥0} (hLip : LipschitzWith K f) {w l : ℝ} (hw : 4 ≤ w)
    (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w) (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|)
    {q : ℂ} (hq : -(krKappa D vlo vhi / (64 * w ^ 2)) ≤ q.re) :
    HasDerivAt (cepsBottomSurv ν β a q)
      (cepsBridgeSeries ν f β a q l * cepsTopSurv ν β a q l) l ∧
    ‖deriv (cepsBottomSurv ν β a q) l‖ ≤ cepsBandFirstWidthConst D vlo vhi * w ^ 6 := by
  have hκ := krKappa_pos hD hvlo hvhi
  have hw2 : 2 ≤ w := by linarith
  have hl2 : 2 ≤ l := by linarith
  have hl0 : 0 < l := by linarith
  have hql : -(krKappa D vlo vhi / (16 * l ^ 2)) ≤ q.re := by
    have hb : krKappa D vlo vhi / (64 * w ^ 2) ≤ krKappa D vlo vhi / (16 * l ^ 2) := by
      apply div_le_div_of_nonneg_left hκ.le (by positivity)
      nlinarith
    linarith
  have hq' : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re := by
    have hb : krKappa D vlo vhi / (64 * w ^ 2) ≤ krKappa D vlo vhi / (16 * w ^ 2) := by
      apply div_le_div_of_nonneg_left hκ.le (by positivity)
      nlinarith
    linarith
  have hd := cepsBand_bottomSurv_hasDerivAt_interior hD hθ hvlo hvhi hν hf hLip
    (w := l) (l := l) hl2 (by linarith) (by linarith) β ha hql
  refine ⟨hd, ?_⟩
  rw [hd.deriv, norm_mul]
  have ha' : 1 / 2 ≤ |-a| := by simpa only [abs_neg] using ha
  have hb := cepsBand_bottomSurv_le hD hθ hvlo hvhi hν hw2 hl hlw (-β) ha' hq'
  rw [← cepsBand_topSurv_eq_reverse ν β a q l] at hb
  calc
    _ ≤ (cepsBandMomentConst (cepsBandPinDecayConst D vlo vhi) (krKappa D vlo vhi) 0 * w ^ 3) *
        (cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) 0 * w ^ 3) :=
      mul_le_mul (cepsBand_bridgeSeries_le hD hθ hvlo hvhi hν hf hw2 hl hlw β ha hq') hb
        (norm_nonneg _) (by unfold cepsBandMomentConst cepsBandPinDecayConst cepsBandDecayConst; positivity)
    _ = _ := by unfold cepsBandFirstWidthConst; ring

end
end PGM
