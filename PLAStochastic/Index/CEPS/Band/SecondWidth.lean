import PLAStochastic.Index.CEPS.Band.PinWidth
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Genuine almost-everywhere second width derivatives

A Lipschitz density gives a continuously differentiable bottom resolvent whose
first derivative is Lipschitz with a class polynomial. Rademacher's theorem
then gives actual second differentiability almost everywhere, together with the
same polynomial budget. No assertion of pointwise twice differentiability is
made under the Lipschitz-density hypothesis.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff

def cepsBandSecondWidthConst (D vlo vhi K : ℝ) : ℝ :=
  cepsBandPinWidthConst D vlo vhi K *
      cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) 0 +
    cepsBandMomentConst (cepsBandPinDecayConst D vlo vhi) (krKappa D vlo vhi) 0 *
      cepsBandFirstWidthConst D vlo vhi

theorem cepsBandSecondWidthConst_nonneg {D vlo vhi K : ℝ} (hD : 0 < D)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) (hK : 0 ≤ K) :
    0 ≤ cepsBandSecondWidthConst D vlo vhi K := by
  have hκ := krKappa_pos hD hvlo hvhi
  have hC₁ := cepsBandFirstWidthConst_nonneg hD hvlo hvhi
  have hC₂ := cepsBandPinWidthConst_nonneg hD hvlo hvhi hK
  unfold cepsBandSecondWidthConst cepsBandMomentConst cepsBandPinDecayConst cepsBandDecayConst
  positivity

/-- The first width derivative is Lipschitz with a polynomial class budget. -/
theorem cepsBand_bottomSurv_deriv_lipschitz {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {K : ℝ≥0} (hLip : LipschitzWith K f) {w : ℝ} (hw : 4 ≤ w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (64 * w ^ 2)) ≤ q.re) :
    LipschitzOnWith ⟨cepsBandSecondWidthConst D vlo vhi K * w ^ 9,
      mul_nonneg (cepsBandSecondWidthConst_nonneg hD hvlo hvhi K.coe_nonneg) (pow_nonneg (by linarith) _)⟩
      (deriv (cepsBottomSurv ν β a q)) (Icc (w / 2) (2 * w)) := by
  have hκ := krKappa_pos hD hvlo hvhi
  have hq' : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re := by
    have hb : krKappa D vlo vhi / (64 * w ^ 2) ≤ krKappa D vlo vhi / (16 * w ^ 2) := by
      apply div_le_div_of_nonneg_left hκ.le (by positivity)
      nlinarith
    linarith
  have ha' : 1 / 2 ≤ |-a| := by simpa only [abs_neg] using ha
  have hU := cepsBand_bridgeSeries_lipschitz hD hθ hvlo hvhi hν hf hLip hw β ha hq
  have hH := cepsBand_bottomSurv_lipschitz hD hθ hvlo hvhi hν hf hLip hw (-β) ha' hq
  have heq : cepsTopSurv ν β a q = cepsBottomSurv ν (-β) (-a) q :=
    funext (cepsBand_topSurv_eq_reverse ν β a q)
  have htop := heq.symm ▸ hH
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change dist (deriv (cepsBottomSurv ν β a q) x) (deriv (cepsBottomSurv ν β a q) y) ≤
    cepsBandSecondWidthConst D vlo vhi K * w ^ 9 * dist x y
  have hdx := (cepsBand_bottomSurv_first_width hD hθ hvlo hvhi hν hf hLip hw hx.1 hx.2 β ha hq).1.deriv
  have hdy := (cepsBand_bottomSurv_first_width hD hθ hvlo hvhi hν hf hLip hw hy.1 hy.2 β ha hq).1.deriv
  have hUd : ‖cepsBridgeSeries ν f β a q x - cepsBridgeSeries ν f β a q y‖ ≤
      cepsBandPinWidthConst D vlo vhi K * w ^ 6 * dist x y := by
    have hu := hU.dist_le_mul x hx y hy
    change dist (cepsBridgeSeries ν f β a q x) (cepsBridgeSeries ν f β a q y) ≤
      cepsBandPinWidthConst D vlo vhi K * w ^ 6 * dist x y at hu
    simpa only [dist_eq_norm] using hu
  have hHd : ‖cepsTopSurv ν β a q x - cepsTopSurv ν β a q y‖ ≤
      cepsBandFirstWidthConst D vlo vhi * w ^ 6 * dist x y := by
    have hh := htop.dist_le_mul x hx y hy
    change dist (cepsTopSurv ν β a q x) (cepsTopSurv ν β a q y) ≤
      cepsBandFirstWidthConst D vlo vhi * w ^ 6 * dist x y at hh
    simpa only [dist_eq_norm] using hh
  have hHx : ‖cepsTopSurv ν β a q x‖ ≤
      cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) 0 * w ^ 3 := by
    rw [cepsBand_topSurv_eq_reverse]
    exact cepsBand_bottomSurv_le hD hθ hvlo hvhi hν (by linarith) hx.1 hx.2 (-β) ha' hq'
  have hUy := cepsBand_bridgeSeries_le hD hθ hvlo hvhi hν hf (by linarith : 2 ≤ w) hy.1 hy.2 β ha hq'
  rw [dist_eq_norm, hdx, hdy,
    show cepsBridgeSeries ν f β a q x * cepsTopSurv ν β a q x -
        cepsBridgeSeries ν f β a q y * cepsTopSurv ν β a q y =
        (cepsBridgeSeries ν f β a q x - cepsBridgeSeries ν f β a q y) * cepsTopSurv ν β a q x +
        cepsBridgeSeries ν f β a q y * (cepsTopSurv ν β a q x - cepsTopSurv ν β a q y) by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (cepsBandPinWidthConst D vlo vhi K * w ^ 6 * dist x y) *
        (cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) 0 * w ^ 3) +
        (cepsBandMomentConst (cepsBandPinDecayConst D vlo vhi) (krKappa D vlo vhi) 0 * w ^ 3) *
        (cepsBandFirstWidthConst D vlo vhi * w ^ 6 * dist x y) :=
      add_le_add (mul_le_mul hUd hHx (norm_nonneg _) (by
        unfold cepsBandPinWidthConst cepsBandFirstWidthConst cepsBandMomentConst
          cepsBandPinDecayConst cepsBandDecayConst
        positivity)) (mul_le_mul hUy hHd (norm_nonneg _) (by
          unfold cepsBandMomentConst cepsBandPinDecayConst cepsBandDecayConst
          positivity))
    _ = _ := by unfold cepsBandSecondWidthConst; ring

/-- The bottom survival resolvent is genuinely `C¹` on the bandwidth window. -/
theorem cepsBand_bottomSurv_contDiffOn_one {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {K : ℝ≥0} (hLip : LipschitzWith K f) {w : ℝ} (hw : 4 ≤ w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (64 * w ^ 2)) ≤ q.re) :
    ContDiffOn ℝ 1 (cepsBottomSurv ν β a q) (Ioo (w / 2) (2 * w)) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 by rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun l hl =>
    (cepsBand_bottomSurv_first_width hD hθ hvlo hvhi hν hf hLip hw hl.1.le hl.2.le β ha hq).1.differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  exact (cepsBand_bottomSurv_deriv_lipschitz hD hθ hvlo hvhi hν hf hLip hw β ha hq).continuousOn.mono Ioo_subset_Icc_self

/-- Actual second width derivatives exist almost everywhere and obey a uniform polynomial
bound. The differentiability assertion rules out reliance on total `deriv` at singular points. -/
theorem cepsBand_bottomSurv_second_width_ae {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {K : ℝ≥0} (hLip : LipschitzWith K f) {w : ℝ} (hw : 4 ≤ w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (64 * w ^ 2)) ≤ q.re) :
    ∀ᵐ l ∂(volume.restrict (Ioo (w / 2) (2 * w))),
      DifferentiableAt ℝ (deriv (cepsBottomSurv ν β a q)) l ∧
        ‖deriv (deriv (cepsBottomSurv ν β a q)) l‖ ≤
          cepsBandSecondWidthConst D vlo vhi K * w ^ 9 := by
  have h := cepsBand_bottomSurv_deriv_lipschitz hD hθ hvlo hvhi hν hf hLip hw β ha hq
  have h' := (h.mono Ioo_subset_Icc_self).ae_differentiableWithinAt (μ := volume) measurableSet_Ioo
  filter_upwards [h', ae_restrict_mem measurableSet_Ioo] with l hd hl
  exact ⟨hd.differentiableAt (isOpen_Ioo.mem_nhds hl),
    norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hl.1 hl.2) h⟩

end
end PGM
