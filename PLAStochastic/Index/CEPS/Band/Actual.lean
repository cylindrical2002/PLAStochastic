import PLAStochastic.Index.CEPS.Band.Moments

/-! # Fixed-window budgets for the actual CEPS strip and bridge series -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- Absolute strip entrance moments; a nonnegative real part of the mark costs no amplitude. -/
theorem cepsBand_strip_moments {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l)
    (hlw : l ≤ 2 * w) {t q : ℂ} (ht : 0 ≤ t.re)
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) (μ : ℝ) (j : ℕ) :
    Summable (fun n : ℕ => (n + 1 : ℝ) ^ j *
      ‖Complex.exp (-q * n) * cepsStripTerm ν t μ l n‖) ∧
    (∑' n : ℕ, (n + 1 : ℝ) ^ j *
      ‖Complex.exp (-q * n) * cepsStripTerm ν t μ l n‖) ≤
      cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) j *
        w ^ (2 * j + 3) := by
  obtain ⟨hs, hsum⟩ := cepsBand_survival_moments hD hθ hvlo hvhi hν hw hl hlw
    (-(1 + μ)) (a := -1) (by norm_num) hq j 0
  have hb : ∀ n : ℕ, (n + 1 : ℝ) ^ j *
      ‖Complex.exp (-q * n) * cepsStripTerm ν t μ l n‖ ≤
      (n + 1 : ℝ) ^ j * ‖Complex.exp (-q * n)‖ *
        krSurv (Icc 0 l) (ν : Measure ℝ) (-(1 + μ)) (-1) n 0 := by
    intro n
    rw [norm_mul, mul_assoc]
    gcongr
    exact norm_cepsStripTerm_le ν ht μ l n
  have hss := hs.of_nonneg_of_le (fun _ => by positivity) hb
  exact ⟨hss, (hss.tsum_le_tsum hb hs).trans hsum⟩

/-- The actual strip entrance is bounded on the slightly growing discount half-plane. -/
theorem cepsBand_stripEntrance_le {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l)
    (hlw : l ≤ 2 * w) {t q : ℂ} (ht : 0 ≤ t.re)
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) (μ : ℝ) :
    ‖cepsStripEntrance ν t μ q l‖ ≤
      cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) 0 * w ^ 3 := by
  obtain ⟨hs, hb⟩ := cepsBand_strip_moments hD hθ hvlo hvhi hν hw hl hlw ht hq μ 0
  simp only [pow_zero, one_mul, Nat.mul_zero, Nat.zero_add] at hs hb
  exact (norm_tsum_le_tsum_norm hs).trans hb

/-- The actual bridge has every absolute time moment. -/
theorem cepsBand_bridge_moments {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) (μ : ℝ) (j : ℕ) :
    Summable (fun n : ℕ => (n + 1 : ℝ) ^ j *
      ‖Complex.exp (-q * ((n : ℂ) + 1)) * cepsBridgeDens ν f μ l (n + 1)‖) ∧
    (∑' n : ℕ, (n + 1 : ℝ) ^ j *
      ‖Complex.exp (-q * ((n : ℂ) + 1)) * cepsBridgeDens ν f μ l (n + 1)‖) ≤
      cepsBandMomentConst (cepsBandPinDecayConst D vlo vhi) (krKappa D vlo vhi) j *
        w ^ (2 * j + 3) := by
  have he : ∀ n : ℕ, ‖Complex.exp (-q * ((n : ℂ) + 1)) *
      cepsBridgeDens ν f μ l (n + 1)‖ =
      ‖Complex.exp (-q * ((n : ℂ) + 1))‖ * krDens (Icc 0 l) ν f (1 + μ) 1 (n + 1) 0 l := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hf.cepsBridgeDens_nonneg μ l (n + 1))]
    rfl
  simp_rw [he, ← mul_assoc]
  exact cepsBand_density_moments hD hθ hvlo hvhi hν hf hw hl hlw (1 + μ)
    (a := 1) (by norm_num) hq j 0 l

/-- The actual bridge resolvent is bounded by a class polynomial. -/
theorem cepsBand_bridge_le {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) (μ : ℝ) :
    ‖cepsBridge ν f μ q l‖ ≤
      cepsBandMomentConst (cepsBandPinDecayConst D vlo vhi) (krKappa D vlo vhi) 0 * w ^ 3 := by
  obtain ⟨hs, hb⟩ := cepsBand_bridge_moments hD hθ hvlo hvhi hν hf hw hl hlw hq μ 0
  simp only [pow_zero, one_mul, Nat.mul_zero, Nat.zero_add] at hs hb
  exact (norm_tsum_le_tsum_norm hs).trans hb

/-- The length-minus-width marked pin series converges absolutely and is polynomially bounded. -/
theorem cepsBand_markedBridge_budget {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) (μ : ℝ) :
    Summable (fun n : ℕ => ‖(((n : ℝ) + 1 - w : ℝ) : ℂ) *
      Complex.exp (-q * ((n : ℂ) + 1)) * cepsBridgeDens ν f μ l (n + 1)‖) ∧
    ‖cepsMarkedBridge ν f w μ q l‖ ≤
      2 * cepsBandMomentConst (cepsBandPinDecayConst D vlo vhi) (krKappa D vlo vhi) 1 * w ^ 6 := by
  let F := fun n : ℕ => ‖Complex.exp (-q * ((n : ℂ) + 1)) *
    cepsBridgeDens ν f μ l (n + 1)‖
  obtain ⟨hs, hb⟩ := cepsBand_bridge_moments hD hθ hvlo hvhi hν hf hw hl hlw hq μ 1
  simp only [pow_one] at hs hb
  have hpoint : ∀ n : ℕ, ‖(((n : ℝ) + 1 - w : ℝ) : ℂ) *
      Complex.exp (-q * ((n : ℂ) + 1)) * cepsBridgeDens ν f μ l (n + 1)‖ ≤
      (2 * w) * ((n + 1 : ℝ) * F n) := by
    intro n
    rw [mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hab : |(n : ℝ) + 1 - w| ≤ (n : ℝ) + 1 + w := by
      have h := abs_sub ((n : ℝ) + 1) w
      rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1),
        abs_of_nonneg (by linarith : 0 ≤ w)] at h
      exact h
    have hmul : (n : ℝ) + 1 + w ≤ 2 * w * ((n : ℝ) + 1) := by nlinarith
    exact (mul_le_mul_of_nonneg_right (hab.trans hmul) (norm_nonneg _)).trans_eq (by ring)
  have hss := (hs.mul_left (2 * w)).of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  refine ⟨hss, (norm_tsum_le_tsum_norm hss).trans ?_⟩
  calc
    _ ≤ ∑' n : ℕ, (2 * w) * ((n + 1 : ℝ) * F n) :=
      hss.tsum_le_tsum hpoint (hs.mul_left (2 * w))
    _ = (2 * w) * ∑' n : ℕ, (n + 1 : ℝ) * F n := tsum_mul_left
    _ ≤ (2 * w) * (cepsBandMomentConst (cepsBandPinDecayConst D vlo vhi)
        (krKappa D vlo vhi) 1 * w ^ 5) :=
      mul_le_mul_of_nonneg_left hb (by linarith)
    _ = _ := by ring

end
end PGM
