import PLAStochastic.Index.CEPS.BandDisc.Series

/-! # Polynomial bounds for every genuine discount derivative of the actual CEPS objects -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

lemma cepsBandDisc_discount_margin {κ w : ℝ} (hκ : 0 < κ) (hw : 0 < w)
    {q : ℂ} (hq : -(κ / (32 * w ^ 2)) ≤ q.re) :
    -(κ / (16 * w ^ 2)) < q.re := by
  have hm : κ / (32 * w ^ 2) < κ / (16 * w ^ 2) := by
    apply div_lt_div_of_pos_left hκ (by positivity)
    nlinarith [sq_pos_of_pos hw]
  linarith

/-- The marked entrance has true complex derivatives of every order, with class constants.
The bound includes all marks with nonnegative real part, hence the characteristic line. -/
theorem cepsBandDisc_stripEntrance_iteratedDeriv_le {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    {t q : ℂ} (ht : 0 ≤ t.re)
    (hq : -(krKappa D vlo vhi / (32 * w ^ 2)) ≤ q.re) (μ : ℝ) (k : ℕ) :
    ‖iteratedDeriv k (fun z => cepsStripEntrance ν t μ z l) q‖ ≤
      cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) k *
        w ^ (2 * k + 3) := by
  let b := -(krKappa D vlo vhi / (16 * w ^ 2))
  have hM : CepsDiscMoments (cepsStripTerm ν t μ l) 0 b := by
    intro j
    simpa only [Nat.add_zero] using
      (cepsBand_strip_moments hD hθ hvlo hvhi hν hw hl hlw ht
        (q := (b : ℂ)) (by change b ≤ b; exact le_rfl) μ j).1
  have hb := (cepsBand_strip_moments hD hθ hvlo hvhi hν hw hl hlw ht
    (q := (b : ℂ)) (by change b ≤ b; exact le_rfl) μ k).2
  have hh := cepsDiscJet_norm_iteratedDeriv_le (by omega : 0 ≤ 1) hM k
    (cepsBandDisc_discount_margin (krKappa_pos hD hvlo hvhi) (by linarith) hq)
  have he : cepsDiscJet (cepsStripTerm ν t μ l) 0 0 =
      (fun z => cepsStripEntrance ν t μ z l) := by
    funext z
    simp [cepsDiscJet, cepsStripEntrance]
  rw [he] at hh
  exact hh.trans (by simpa only [Nat.add_zero] using hb)

/-- General survival entrances, at any starting point, have the same all-order discount bound. -/
theorem cepsBandDisc_survival_iteratedDeriv_le {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (32 * w ^ 2)) ≤ q.re) (y : ℝ) (k : ℕ) :
    ‖iteratedDeriv k (fun z : ℂ => ∑' n : ℕ, Complex.exp (-z * n) *
      (krSurv (Icc 0 l) (ν : Measure ℝ) β a n y : ℂ)) q‖ ≤
      cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) k *
        w ^ (2 * k + 3) := by
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
  have hb := (cepsBand_survival_moments hD hθ hvlo hvhi hν hw hl hlw β ha
    (q := (b : ℂ)) (by change b ≤ b; exact le_rfl) k y).2
  have hh := cepsDiscJet_norm_iteratedDeriv_le (by omega : 0 ≤ 1) hM k
    (cepsBandDisc_discount_margin (krKappa_pos hD hvlo hvhi) (by linarith) hq)
  have hfun : cepsDiscJet c 0 0 = (fun z : ℂ => ∑' n : ℕ,
      Complex.exp (-z * n) * (krSurv (Icc 0 l) (ν : Measure ℝ) β a n y : ℂ)) := by
    funext z
    simp [cepsDiscJet, c]
  rw [hfun] at hh
  exact hh.trans (by simpa only [Nat.add_zero, he, mul_assoc] using hb)

/-- Both bottom and top entrances are covered without any restriction on the translation. -/
theorem cepsBandDisc_bottomSurv_iteratedDeriv_le {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (32 * w ^ 2)) ≤ q.re) (k : ℕ) :
    ‖iteratedDeriv k (fun z => cepsBottomSurv ν β a z l) q‖ ≤
      cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) k *
        w ^ (2 * k + 3) :=
  cepsBandDisc_survival_iteratedDeriv_le hD hθ hvlo hvhi hν hw hl hlw β ha hq 0 k

theorem cepsBandDisc_topSurv_iteratedDeriv_le {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (32 * w ^ 2)) ≤ q.re) (k : ℕ) :
    ‖iteratedDeriv k (fun z => cepsTopSurv ν β a z l) q‖ ≤
      cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) k *
        w ^ (2 * k + 3) :=
  cepsBandDisc_survival_iteratedDeriv_le hD hθ hvlo hvhi hν hw hl hlw β ha hq l k

/-- The full pointwise bridge has true discount derivatives of every order. -/
theorem cepsBandDisc_bridgeSeries_iteratedDeriv_le {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (32 * w ^ 2)) ≤ q.re) (k : ℕ) :
    ‖iteratedDeriv k (fun z => cepsBridgeSeries ν f β a z l) q‖ ≤
      cepsBandMomentConst (cepsBandPinDecayConst D vlo vhi) (krKappa D vlo vhi) k *
        w ^ (2 * k + 3) := by
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
  have hb := (cepsBand_density_moments hD hθ hvlo hvhi hν hf hw hl hlw β ha
    (q := (b : ℂ)) (by change b ≤ b; exact le_rfl) k 0 l).2
  have hh := cepsDiscJet_norm_iteratedDeriv_le (by omega : 1 ≤ 1) hM k
    (cepsBandDisc_discount_margin (krKappa_pos hD hvlo hvhi) (by linarith) hq)
  have hfun : cepsDiscJet c 1 0 = (fun z => cepsBridgeSeries ν f β a z l) := by
    funext z
    simp [cepsDiscJet, cepsBridgeSeries, c]
  rw [hfun] at hh
  exact hh.trans (by simpa only [he, mul_assoc] using hb)

/-- The WP8 bridge is the general bridge at the actual drift parameters. -/
theorem cepsBandDisc_bridge_iteratedDeriv_le {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    {q : ℂ} (hq : -(krKappa D vlo vhi / (32 * w ^ 2)) ≤ q.re) (μ : ℝ) (k : ℕ) :
    ‖iteratedDeriv k (fun z => cepsBridge ν f μ z l) q‖ ≤
      cepsBandMomentConst (cepsBandPinDecayConst D vlo vhi) (krKappa D vlo vhi) k *
        w ^ (2 * k + 3) :=
  cepsBandDisc_bridgeSeries_iteratedDeriv_le hD hθ hvlo hvhi hν hf hw hl hlw
    (1 + μ) (a := 1) (by norm_num) hq k

end
end PGM
