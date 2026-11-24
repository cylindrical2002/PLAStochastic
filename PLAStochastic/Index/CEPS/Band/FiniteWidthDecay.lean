import PLAStochastic.Index.CEPS.Band.WidthFinite

/-! # Summable finite width moduli from the killed gap -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

/-- A summable modulus for each finite survival width increment, including discount. -/
theorem cepsBand_survival_width_decay {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {w : ℝ} (hw : 2 ≤ w) (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re)
    {x y : ℝ} (hx : w / 2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2 * w) (n : ℕ) :
    ‖Complex.exp (-q * n)‖ *
      (krSurv (Icc 0 y) (ν : Measure ℝ) β a n 0 - krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0) ≤
      (n : ℝ) * (cepsBandPinDecayConst D vlo vhi * cepsBandDecayConst D vlo vhi * w ^ 2 *
        Real.exp (-(krKappa D vlo vhi / (16 * w ^ 2)) * ((n : ℝ) - 1))) * (y - x) := by
  have ha0 : a ≠ 0 := abs_pos.mp (by linarith : 0 < |a|)
  have hx0 : 0 ≤ x := by linarith
  let C := cepsBandPinDecayConst D vlo vhi * cepsBandDecayConst D vlo vhi * w ^ 2 *
    Real.exp (-(krKappa D vlo vhi / (16 * w ^ 2)) * ((n : ℝ) - 1))
  have hb : ∀ j ∈ Finset.range n, ∀ z ∈ Ioc x y,
      ‖Complex.exp (-q * n)‖ *
        (krDens (Icc 0 z) ν f β a (j + 1) 0 z *
          krSurv (Icc 0 z) (ν : Measure ℝ) β a (n - (j + 1)) z) ≤ C := by
    intro j hj z hz
    have hjn := Finset.mem_range.mp hj
    have he : -q * (n : ℂ) = -q * ((j : ℂ) + 1) + -q * ((n - (j + 1) : ℕ) : ℂ) := by
      have hc : (n : ℂ) = (j : ℂ) + 1 + ((n - (j + 1) : ℕ) : ℂ) := by
        exact_mod_cast (show n = j + 1 + (n - (j + 1)) by omega)
      rw [hc]; ring
    have hd := cepsBand_discount_density_decay hD hθ hvlo hvhi hν hf hw
      (hx.trans hz.1.le) (hz.2.trans hy) β ha hq j 0 z
    have hs := cepsBand_discount_survival_decay hD hθ hvlo hvhi hν hw
      (hx.trans hz.1.le) (hz.2.trans hy) β ha hq (n - (j + 1)) z
    rw [he, Complex.exp_add, norm_mul]
    calc
      _ = (‖Complex.exp (-q * ((j : ℂ) + 1))‖ * krDens (Icc 0 z) ν f β a (j + 1) 0 z) *
          (‖Complex.exp (-q * ((n - (j + 1) : ℕ) : ℂ))‖ *
            krSurv (Icc 0 z) (ν : Measure ℝ) β a (n - (j + 1)) z) := by ring
      _ ≤ (cepsBandPinDecayConst D vlo vhi * w *
            Real.exp (-(krKappa D vlo vhi / (16 * w ^ 2)) * j)) *
          (cepsBandDecayConst D vlo vhi * w *
            Real.exp (-(krKappa D vlo vhi / (16 * w ^ 2)) * (n - (j + 1) : ℕ))) :=
        mul_le_mul hd hs (mul_nonneg (norm_nonneg _) (krSurv_nonneg measurableSet_Icc ν β a _ z))
          (by unfold cepsBandPinDecayConst cepsBandDecayConst; positivity)
      _ = C := by
        have hn : (j : ℝ) + (n - (j + 1) : ℕ) = (n : ℝ) - 1 := by
          have heq : n = j + (n - (j + 1)) + 1 := by omega
          exact_mod_cast (show (j : ℤ) + (n - (j + 1) : ℕ) = (n : ℤ) - 1 by omega)
        dsimp [C]
        rw [show (cepsBandPinDecayConst D vlo vhi * w * Real.exp (-(krKappa D vlo vhi / (16 * w ^ 2)) * j)) *
            (cepsBandDecayConst D vlo vhi * w * Real.exp (-(krKappa D vlo vhi / (16 * w ^ 2)) * (n - (j + 1) : ℕ))) =
            (cepsBandPinDecayConst D vlo vhi * cepsBandDecayConst D vlo vhi * w ^ 2) *
            (Real.exp (-(krKappa D vlo vhi / (16 * w ^ 2)) * j) *
              Real.exp (-(krKappa D vlo vhi / (16 * w ^ 2)) * (n - (j + 1) : ℕ))) by ring,
          ← Real.exp_add, ← mul_add, hn]
  rw [hf.krSurv_bottom_sub ha0 β hx0 hxy n, Finset.mul_sum]
  have hC : 0 ≤ C := by dsimp [C]; unfold cepsBandPinDecayConst cepsBandDecayConst; positivity
  calc
    _ ≤ ∑ j ∈ Finset.range n, ∫ z in Ioc x y, C := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← integral_const_mul]
      exact setIntegral_mono_on ((hf.integrableOn_krDens_mul a β j (n - (j + 1)) x y).const_mul _)
        (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc (hb j hj)
    _ = _ := by
      simp only [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hxy,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp [C]; ring

/-- The discounted finite bridge terms admit a summable uniform width modulus. -/
theorem cepsBand_pin_finite_lipschitz {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {K : ℝ≥0} (hLip : LipschitzWith K f) {w : ℝ} (hw : 2 ≤ w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) :
    ∃ M : ℕ → ℝ≥0, Summable (fun n => (M n : ℝ)) ∧ ∀ n,
      LipschitzOnWith (M n)
        (fun l => Complex.exp (-q * ((n : ℂ) + 1)) *
          (krDens (Icc 0 l) ν f β a (n + 1) 0 l : ℂ)) (Icc (w / 2) (2 * w)) := by
  let r := krKappa D vlo vhi / (16 * w ^ 2)
  let E := Real.exp (krKappa D vlo vhi / 16)
  let B := cepsBandDecayConst D vlo vhi
  let P := cepsBandPinDecayConst D vlo vhi
  let M := fun n : ℕ => E * (2 * D * ((n : ℝ) * (P * B * w ^ 2 * Real.exp (-r * ((n : ℝ) - 1)))) +
    4 * K * (B * w * Real.exp (-r * n)))
  have hB : 0 ≤ B := by dsimp [B]; unfold cepsBandDecayConst; positivity
  have hP : 0 ≤ P := by dsimp [P]; unfold cepsBandPinDecayConst cepsBandDecayConst; positivity
  have hM : ∀ n, 0 ≤ M n := by intro n; dsimp [M, E]; positivity
  have hr : 0 < r := by dsimp [r]; exact div_pos (krKappa_pos hD hvlo hvhi) (by positivity)
  have he : ∀ n : ℕ, Real.exp (-r * ((n : ℝ) - 1)) = Real.exp r * Real.exp (-r * n) := by
    intro n; rw [← Real.exp_add]; congr 1; ring
  have hs0 : Summable (fun n : ℕ => Real.exp (-r * n)) := by
    simp_rw [mul_comm (-r), Real.exp_nat_mul]
    exact summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_lt_one_iff.mpr (by linarith))
  have hs1 : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-r * n)) := by
    simpa only [pow_one] using Real.summable_pow_mul_exp_neg_nat_mul 1 hr
  have hsM : Summable M := by
    have heq : M = fun (n : ℕ) => (E * (2 * D * P * B * w ^ 2 * Real.exp r)) * ((n : ℝ) * Real.exp (-r * n)) +
        (E * 4 * K * B * w) * Real.exp (-r * n) := by
      funext n; dsimp [M]; rw [he]; ring
    rw [heq]; exact (hs1.mul_left _).add (hs0.mul_left _)
  refine ⟨fun n => ⟨M n, hM n⟩, hsM, fun n => ?_⟩
  have ha0 : a ≠ 0 := abs_pos.mp (by linarith : 0 < |a|)
  have habs : 0 < |a| := abs_pos.mpr ha0
  have hdiv : D / |a| ≤ 2 * D := by rw [div_le_iff₀ habs]; nlinarith
  have hdivK : (K : ℝ) / |a| ^ 2 ≤ 4 * K := by
    rw [div_le_iff₀ (sq_pos_of_pos habs)]
    have hsq : 1 / 4 ≤ |a| ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left hsq K.coe_nonneg; nlinarith
  have hnorm : ‖Complex.exp (-q)‖ ≤ E := by
    rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_exp]
    have hb : krKappa D vlo vhi / (16 * w ^ 2) ≤ krKappa D vlo vhi / 16 := by
      apply div_le_div_of_nonneg_left (krKappa_pos hD hvlo hvhi).le (by norm_num); nlinarith
    linarith
  have hb : ∀ {x y : ℝ}, w / 2 ≤ x → x ≤ y → y ≤ 2 * w →
      ‖Complex.exp (-q * ((n : ℂ) + 1)) * (krDens (Icc 0 y) ν f β a (n + 1) 0 y : ℂ) -
        Complex.exp (-q * ((n : ℂ) + 1)) * (krDens (Icc 0 x) ν f β a (n + 1) 0 x : ℂ)‖ ≤ M n * (y - x) := by
    intro x y hx hxy hy
    have hx0 : 0 ≤ x := by linarith
    have hdiff := hf.cepsBand_pin_width_le hLip ha0 β hx0 hxy n
    have hdiff' : |krDens (Icc 0 y) ν f β a (n + 1) 0 y - krDens (Icc 0 x) ν f β a (n + 1) 0 x| ≤
        2 * D * (krSurv (Icc 0 y) (ν : Measure ℝ) β a n 0 - krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0) +
        4 * K * (y - x) * krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0 :=
      hdiff.trans (add_le_add (mul_le_mul_of_nonneg_right hdiv
        (hf.cepsBand_survival_width_le ha0 β hx0 hxy n).1)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdivK (sub_nonneg.mpr hxy))
          (krSurv_nonneg measurableSet_Icc ν β a n 0)))
    have hs := cepsBand_survival_width_decay hD hθ hvlo hvhi hν hf hw β ha hq hx hxy hy n
    have hsurv := cepsBand_discount_survival_decay hD hθ hvlo hvhi hν hw hx (hxy.trans hy) β ha hq n 0
    rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show -q * ((n : ℂ) + 1) = -q + -q * n by ring, Complex.exp_add, norm_mul]
    calc
      _ ≤ (E * ‖Complex.exp (-q * n)‖) *
          (2 * D * (krSurv (Icc 0 y) (ν : Measure ℝ) β a n 0 - krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0) +
            4 * K * (y - x) * krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)) hdiff' (abs_nonneg _) (by positivity)
      _ = E * (2 * D * (‖Complex.exp (-q * n)‖ *
            (krSurv (Icc 0 y) (ν : Measure ℝ) β a n 0 - krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0)) +
          4 * K * (y - x) * (‖Complex.exp (-q * n)‖ * krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0)) := by ring
      _ ≤ E * (2 * D * ((n : ℝ) * (P * B * w ^ 2 * Real.exp (-r * ((n : ℝ) - 1))) * (y - x)) +
          4 * K * (y - x) * (B * w * Real.exp (-r * n))) := by
        gcongr
      _ = _ := by dsimp [M]; ring
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change dist _ _ ≤ M n * dist x y
  rcases le_total y x with h | h
  · simpa only [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h)] using hb hy.1 h hx.2
  · rw [dist_comm, dist_comm x y]
    simpa only [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h)] using hb hx.1 h hy.2

end
end PGM
