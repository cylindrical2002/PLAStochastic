import PLAStochastic.Index.GEP.Kernel.Row.Long.MeasurableBV
import PLAStochastic.Index.GEP.Kernel.Row.Long.TimeWeightedInfinite

/-!
# Actual long Green rows with jointly measurable decompositions

All class, bandwidth and window constants are fixed before the slope parameter.
The chosen regular and remainder parts are jointly measurable in that parameter
and the terminal location. The original variation and Lipschitz budgets are
preserved; the uniformly small remainder is enlarged by a factor four.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

def krLongRow (w : ℝ) (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (β a : ℝ)
    (P : ℕ) (b z : ℝ) : ℝ :=
  ∑' i : ℕ, krDens (Icc 0 w) ν f β a (P + 1 + i) b z

def krLongRowExpw (w : ℝ) (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (β a ε : ℝ)
    (P : ℕ) (b z : ℝ) : ℝ :=
  ∑' i : ℕ, Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) *
    krDens (Icc 0 w) ν f β a (P + 1 + i) b z

variable {X : Type*} [MeasurableSpace X] [Nonempty X]
variable {D θ vlo vhi K L w A : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
variable {a β a' : X → ℝ}

theorem krLong_measurable_decomposition (hβ : Measurable β) (ha' : Measurable a')
    (H : ∀ p, KrBand D θ vlo vhi K L ν f w A (a p) (β p) (a' p))
    {b : ℝ} (hb : b = 0 ∨ b = w) {P : ℕ} (hP : 12 ≤ P) :
    ∃ G R : X → ℝ → ℂ,
      Measurable (fun p : X × ℝ => G p.1 p.2) ∧
      Measurable (fun p : X × ℝ => R p.1 p.2) ∧
      (∀ p x, x ∉ Icc 0 w → G p x = 0 ∧ R p x = 0) ∧
      (∀ p x, (krLongRow w ν f (β p) (a' p) P b x : ℂ) = G p x + R p x) ∧
      (∀ p, eVariationOn (G p) univ ≤ ENNReal.ofReal
        (krCV D K L vlo vhi * (1 + A) * (Real.sqrt w / krFourthRoot P + 1))) ∧
      (∀ p, ∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖G p x - G p y‖ ≤
        (2 * D * (krCV D K L vlo vhi * (1 + A) *
          (Real.sqrt w / krFourthRoot P + 1))) * |x-y|) ∧
      (∀ p x, ‖R p x‖ ≤ 4 * (krCR D K L vlo vhi * (1 + A) *
        kBVClassRho D vlo vhi ^ (P / 3 - 1))) ∧
      (∀ p b', (b' = 0 ∨ b' = w) → b ≠ b' → A ≤ w →
        ‖G p b'‖ ≤ krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w +
          4 * (krCR D K L vlo vhi * (1 + A) * kBVClassRho D vlo vhi ^ (P / 3 - 1))) := by
  classical
  have H₀ := H (Classical.choice ‹Nonempty X›)
  let VB := krCV D K L vlo vhi * (1 + A) * (Real.sqrt w / krFourthRoot P + 1)
  let RB := krCR D K L vlo vhi * (1 + A) * kBVClassRho D vlo vhi ^ (P / 3 - 1)
  have hVB : 0 ≤ VB := mul_nonneg (mul_nonneg H₀.krCV_nonneg (by linarith [H₀.hA]))
    (add_nonneg (div_nonneg (Real.sqrt_nonneg _) (krFourthRoot_nonneg _)) zero_le_one)
  have hRB : 0 ≤ RB := mul_nonneg (mul_nonneg H₀.krCR_nonneg (by linarith [H₀.hA]))
    (pow_nonneg H₀.classConsts.1 _)
  let q : X → ℝ → ℂ := fun p x => (krLongRow w ν f (β p) (a' p) P b x : ℂ)
  have hq : Measurable (fun p : X × ℝ => q p.1 p.2) :=
    Complex.measurable_ofReal.comp (Measurable.tsum fun i =>
      measurable_krDens_param ν measurableSet_Icc H₀.hf (hβ.comp measurable_fst)
        (ha'.comp measurable_fst) measurable_const measurable_snd (P + 1 + i))
  have hqs : ∀ p x, x ∉ Icc 0 w → q p x = 0 := by
    intro p x hx
    have hz : ∀ i : ℕ, krDens (Icc 0 w) ν f (β p) (a' p) (P + 1 + i) b x = 0 :=
      fun i => krDens_eq_zero_of_right_notMem ν hx _ _
    simp only [q, krLongRow, hz, tsum_zero, Complex.ofReal_zero]
  have hex : ∀ p, ∃ g : ℝ → ℂ,
      (∀ x, x ∉ Icc 0 w → g x = 0) ∧ eVariationOn g univ ≤ ENNReal.ofReal VB ∧
      (∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖g x-g y‖ ≤ (2 * D * VB) * |x-y|) ∧
      (∀ x, ‖q p x-g x‖ ≤ RB) := by
    intro p
    obtain ⟨g, r, _, _, hs, he, hv, hl, hr, _⟩ := krLong_infinite_decomposition ν (H p) hb hP
    refine ⟨g, fun x hx => (hs x hx).1, hv, hl, ?_⟩
    intro x
    change ‖((∑' i : ℕ, krDens (Icc 0 w) ν f (β p) (a' p) (P + 1 + i) b x : ℝ) : ℂ) - g x‖ ≤ _
    rw [he x, add_sub_cancel_left]
    exact hr x
  obtain ⟨G, R, hG, hR, hs, he, hv, hl, hr⟩ :=
    kr_measurable_bv_decomposition (le_trans zero_le_one H₀.hw)
      (mul_nonneg (by linarith [H₀.hD0]) hVB) hRB hq hqs hex
  refine ⟨G, R, hG, hR, hs, he, hv, hl, hr, ?_⟩
  intro p b' hb' hbb hAw
  have hpin : krLongRow w ν f (β p) (a' p) P b b' ≤
      krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w := by
    apply Real.tsum_le_of_sum_range_le (fun i => krDens_nonneg ν (H p).hf0 _ _ _)
    intro M
    refine le_trans ?_ (sum_krDens_bdry_pin_le ν (H p) hAw hb hb' hbb (P + M))
    rw [Finset.sum_range_add]
    have hi : ∀ i : ℕ, P + 1 + i = P + i + 1 := fun i => by omega
    simp_rw [hi]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => krDens_nonneg ν (H p).hf0 _ _ _)
  have hq0 : 0 ≤ krLongRow w ν f (β p) (a' p) P b b' :=
    tsum_nonneg fun i => krDens_nonneg ν (H p).hf0 _ _ _
  have hg : G p b' = q p b' - R p b' := by rw [he p b']; ring
  calc
    ‖G p b'‖ ≤ ‖q p b'‖ + ‖R p b'‖ := by rw [hg]; exact norm_sub_le _ _
    _ ≤ krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w + 4 * RB := by
      refine add_le_add ?_ (hr p b')
      simpa only [q, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0] using hpin

/-- Joint parameter selection for the actual weighted long Green row. -/
theorem krLong_measurable_decomposition_expw (hβ : Measurable β) (ha' : Measurable a')
    (H : ∀ p, KrBand D θ vlo vhi K L ν f w A (a p) (β p) (a' p))
    {b : ℝ} (hb : b = 0 ∨ b = w) {P : ℕ} (hP : 12 ≤ P)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krEps D vlo vhi) :
    ∃ G R : X → ℝ → ℂ,
      Measurable (fun p : X × ℝ => G p.1 p.2) ∧
      Measurable (fun p : X × ℝ => R p.1 p.2) ∧
      (∀ p x, x ∉ Icc 0 w → G p x = 0 ∧ R p x = 0) ∧
      (∀ p x, (krLongRowExpw w ν f (β p) (a' p) ε P b x : ℂ) = G p x + R p x) ∧
      (∀ p, eVariationOn (G p) univ ≤ ENNReal.ofReal
        (2 * Real.exp (3 * ε) * krCV D K L vlo vhi * (1 + A) * (Real.sqrt w / krFourthRoot P + 1))) ∧
      (∀ p, ∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖G p x - G p y‖ ≤
        (2 * D * (2 * Real.exp (3 * ε) * krCV D K L vlo vhi * (1 + A) *
          (Real.sqrt w / krFourthRoot P + 1))) * |x-y|) ∧
      (∀ p x, ‖R p x‖ ≤ 4 * (2 * Real.exp (5 * ε) * krCR D K L vlo vhi * (1 + A) *
        ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1))) ∧
      (∀ p b', (b' = 0 ∨ b' = w) → b ≠ b' → A ≤ w →
        ‖G p b'‖ ≤ Real.exp (3 * ε) * ((krCP D θ K L vlo vhi + 12 * krC₂ D K L / krKappa D vlo vhi) *
        (1 + A) ^ 2 / Real.sqrt w) +
          4 * (2 * Real.exp (5 * ε) * krCR D K L vlo vhi * (1 + A) * ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1))) := by
  classical
  have H₀ := H (Classical.choice ‹Nonempty X›)
  let VB := 2 * Real.exp (3 * ε) * krCV D K L vlo vhi * (1 + A) * (Real.sqrt w / krFourthRoot P + 1)
  let RB := 2 * Real.exp (5 * ε) * krCR D K L vlo vhi * (1 + A) * ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1)
  have hVB : 0 ≤ VB := mul_nonneg (mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) H₀.krCV_nonneg)
      (by linarith [H₀.hA])) (add_nonneg (div_nonneg (Real.sqrt_nonneg _) (krFourthRoot_nonneg _)) zero_le_one)
  have hRB : 0 ≤ RB := mul_nonneg (mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) H₀.krCR_nonneg)
      (by linarith [H₀.hA])) (pow_nonneg (by linarith [H₀.classConsts.1]) _)
  have hεκ : ε ≤ krKappa D vlo vhi / 16 := by
    have := hε.trans H₀.krEps_le_kappa
    have := H₀.kappa_pos
    linarith
  let q : X → ℝ → ℂ := fun p x => (krLongRowExpw w ν f (β p) (a' p) ε P b x : ℂ)
  have hq : Measurable (fun p : X × ℝ => q p.1 p.2) :=
    Complex.measurable_ofReal.comp (Measurable.tsum fun i =>
      (measurable_krDens_param ν measurableSet_Icc H₀.hf (hβ.comp measurable_fst)
        (ha'.comp measurable_fst) measurable_const measurable_snd (P + 1 + i)).const_mul _)
  have hqs : ∀ p x, x ∉ Icc 0 w → q p x = 0 := by
    intro p x hx
    have hz : ∀ i : ℕ, krDens (Icc 0 w) ν f (β p) (a' p) (P + 1 + i) b x = 0 :=
      fun i => krDens_eq_zero_of_right_notMem ν hx _ _
    simp only [q, krLongRowExpw, hz, mul_zero, tsum_zero, Complex.ofReal_zero]
  have hex : ∀ p, ∃ g : ℝ → ℂ,
      (∀ x, x ∉ Icc 0 w → g x = 0) ∧ eVariationOn g univ ≤ ENNReal.ofReal VB ∧
      (∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖g x-g y‖ ≤ (2 * D * VB) * |x-y|) ∧
      (∀ x, ‖q p x-g x‖ ≤ RB) := by
    intro p
    obtain ⟨g, r, _, _, hs, he, hv, hl, hr, _⟩ := krLong_infinite_decomposition_expw ν (H p) hb hP hε0 hε
    refine ⟨g, fun x hx => (hs x hx).1, hv, hl, ?_⟩
    intro x
    change ‖((∑' i : ℕ, Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) * krDens (Icc 0 w) ν f (β p) (a' p) (P + 1 + i) b x : ℝ) : ℂ) - g x‖ ≤ _
    rw [he x, add_sub_cancel_left]
    exact hr x
  obtain ⟨G, R, hG, hR, hs, he, hv, hl, hr⟩ :=
    kr_measurable_bv_decomposition (le_trans zero_le_one H₀.hw)
      (mul_nonneg (by linarith [H₀.hD0]) hVB) hRB hq hqs hex
  refine ⟨G, R, hG, hR, hs, he, hv, hl, hr, ?_⟩
  intro p b' hb' hbb hAw
  have hpin : krLongRowExpw w ν f (β p) (a' p) ε P b b' ≤
      Real.exp (3 * ε) * ((krCP D θ K L vlo vhi + 12 * krC₂ D K L / krKappa D vlo vhi) *
        (1 + A) ^ 2 / Real.sqrt w) := by
    apply Real.tsum_le_of_sum_range_le
      (fun i => mul_nonneg (Real.exp_pos _).le (krDens_nonneg ν (H p).hf0 _ _ _))
    intro M
    refine le_trans ?_ (sum_expw_krDens_bdry_pin_le ν (H p) hAw hb hb' hbb hε0 hεκ (P + M))
    rw [Finset.sum_range_add]
    have hi : ∀ i : ℕ, P + 1 + i = P + i + 1 := fun i => by omega
    simp_rw [hi]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ =>
      mul_nonneg (Real.exp_pos _).le (krDens_nonneg ν (H p).hf0 _ _ _))
  have hq0 : 0 ≤ krLongRowExpw w ν f (β p) (a' p) ε P b b' :=
    tsum_nonneg fun i => mul_nonneg (Real.exp_pos _).le (krDens_nonneg ν (H p).hf0 _ _ _)
  have hg : G p b' = q p b' - R p b' := by rw [he p b']; ring
  calc
    ‖G p b'‖ ≤ ‖q p b'‖ + ‖R p b'‖ := by rw [hg]; exact norm_sub_le _ _
    _ ≤ Real.exp (3 * ε) * ((krCP D θ K L vlo vhi + 12 * krC₂ D K L / krKappa D vlo vhi) *
        (1 + A) ^ 2 / Real.sqrt w) + 4 * RB := by
      refine add_le_add ?_ (hr p b')
      simpa only [q, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0] using hpin

end
end PGM
