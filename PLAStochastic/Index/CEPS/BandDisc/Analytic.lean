import PLAStochastic.Index.CEPS.BandDisc.Actual

/-! # Genuine holomorphy of the actual survival and bridge series in the discount -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- Survival entrances are holomorphic at every point of the closed target half-plane. -/
theorem cepsBandDisc_survival_analyticAt {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (32 * w ^ 2)) ≤ q.re) (y : ℝ) :
    AnalyticAt ℂ (fun z : ℂ => ∑' n : ℕ, Complex.exp (-z * n) *
      (krSurv (Icc 0 l) (ν : Measure ℝ) β a n y : ℂ)) q := by
  let b := -(krKappa D vlo vhi / (16 * w ^ 2))
  let c : ℕ → ℂ := fun n => krSurv (Icc 0 l) (ν : Measure ℝ) β a n y
  have he : ∀ n : ℕ, ‖Complex.exp (-(b : ℂ) * n) * c n‖ =
      ‖Complex.exp (-(b : ℂ) * n)‖ * krSurv (Icc 0 l) (ν : Measure ℝ) β a n y := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (krSurv_nonneg measurableSet_Icc ν β a n y)]
  have hM : CepsDiscMoments c 0 b := by
    intro j
    simpa only [Nat.add_zero, he, mul_assoc] using
      (cepsBand_survival_moments hD hθ hvlo hvhi hν hw hl hlw β ha
        (q := (b : ℂ)) (by change b ≤ b; exact le_rfl) j y).1
  have h := cepsDiscJet_analyticAt (by omega : 0 ≤ 1) hM
    (cepsBandDisc_discount_margin (krKappa_pos hD hvlo hvhi) (by linarith) hq) 0
  have hfun : cepsDiscJet c 0 0 = (fun z : ℂ => ∑' n : ℕ,
      Complex.exp (-z * n) * (krSurv (Icc 0 l) (ν : Measure ℝ) β a n y : ℂ)) := by
    funext z
    simp [cepsDiscJet, c]
  rw [hfun] at h
  exact h

/-- The actual marked entrance is holomorphic for every nonnegative real part of its mark. -/
theorem cepsBandDisc_stripEntrance_analyticAt {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    {t q : ℂ} (ht : 0 ≤ t.re)
    (hq : -(krKappa D vlo vhi / (32 * w ^ 2)) ≤ q.re) (μ : ℝ) :
    AnalyticAt ℂ (fun z => cepsStripEntrance ν t μ z l) q := by
  let b := -(krKappa D vlo vhi / (16 * w ^ 2))
  have hM : CepsDiscMoments (cepsStripTerm ν t μ l) 0 b := by
    intro j
    simpa only [Nat.add_zero] using
      (cepsBand_strip_moments hD hθ hvlo hvhi hν hw hl hlw ht
        (q := (b : ℂ)) (by change b ≤ b; exact le_rfl) μ j).1
  have h := cepsDiscJet_analyticAt (by omega : 0 ≤ 1) hM
    (cepsBandDisc_discount_margin (krKappa_pos hD hvlo hvhi) (by linarith) hq) 0
  have hfun : cepsDiscJet (cepsStripTerm ν t μ l) 0 0 =
      (fun z => cepsStripEntrance ν t μ z l) := by
    funext z
    simp [cepsDiscJet, cepsStripEntrance]
  rw [hfun] at h
  exact h

/-- Pointwise bridge densities need no width regularity for discount holomorphy. -/
theorem cepsBandDisc_bridgeSeries_analyticAt {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (32 * w ^ 2)) ≤ q.re) :
    AnalyticAt ℂ (fun z => cepsBridgeSeries ν f β a z l) q := by
  let b := -(krKappa D vlo vhi / (16 * w ^ 2))
  let c : ℕ → ℂ := fun n => krDens (Icc 0 l) ν f β a (n + 1) 0 l
  have he : ∀ n : ℕ, ‖Complex.exp (-(b : ℂ) * (n + 1 : ℕ)) * c n‖ =
      ‖Complex.exp (-(b : ℂ) * ((n : ℂ) + 1))‖ *
        krDens (Icc 0 l) ν f β a (n + 1) 0 l := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (krDens_nonneg ν hf.nonneg _ _ _)]
    simp
  have hM : CepsDiscMoments c 1 b := by
    intro j
    simpa only [he, mul_assoc] using
      (cepsBand_density_moments hD hθ hvlo hvhi hν hf hw hl hlw β ha
        (q := (b : ℂ)) (by change b ≤ b; exact le_rfl) j 0 l).1
  have h := cepsDiscJet_analyticAt (by omega : 1 ≤ 1) hM
    (cepsBandDisc_discount_margin (krKappa_pos hD hvlo hvhi) (by linarith) hq) 0
  have hfun : cepsDiscJet c 1 0 = (fun z => cepsBridgeSeries ν f β a z l) := by
    funext z
    simp [cepsDiscJet, cepsBridgeSeries, c]
  rw [hfun] at h
  exact h

end
end PGM
