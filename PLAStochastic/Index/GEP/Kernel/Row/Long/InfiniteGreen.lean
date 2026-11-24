import PLAStochastic.Index.GEP.Kernel.Row.Long.Decomposition

/-!
# WP4 kernel rows: a decomposition of the actual infinite long Green row

For a fixed admissible slope, choose the decomposition of each individual row
once. The variation and remainder budgets are summable, so their chosen parts
give actual pointwise series `G` and `R`. This preserves the constants of
`krLong_decomposition`, including the opposite-endpoint trace. Measurability here
is in the terminal location; no measurability of the choice in the slope is asserted.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

variable {β a : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}

/-- Removing any finite initial segment leaves a summable actual Green row. -/
theorem summable_krDens_long_row {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    (P : ℕ) (z : ℝ) :
    Summable fun i : ℕ => krDens (Icc 0 w) ν f β a' (P + 1 + i) b z := by
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (summable_nat_add_iff P).2 (summable_krDens_bdry_row ν H hb z)

/-- The actual infinite long Green row has the same pointwise BV, Lipschitz,
remainder and opposite-endpoint bounds as the finite sums. -/
theorem krLong_infinite_decomposition {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {P : ℕ} (hP : 12 ≤ P) :
    ∃ G R : ℝ → ℂ, Measurable G ∧ Measurable R ∧
      (∀ x, x ∉ Icc 0 w → G x = 0 ∧ R x = 0) ∧
      (∀ z, ((∑' i : ℕ, krDens (Icc 0 w) ν f β a' (P + 1 + i) b z : ℝ) : ℂ) =
        G z + R z) ∧
      eVariationOn G univ ≤ ENNReal.ofReal (krCV D K L vlo vhi * (1 + A) *
        (Real.sqrt w / krFourthRoot P + 1)) ∧
      (∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖G x - G y‖ ≤
        (2 * D * (krCV D K L vlo vhi * (1 + A) *
          (Real.sqrt w / krFourthRoot P + 1))) * |x - y|) ∧
      (∀ x, ‖R x‖ ≤ krCR D K L vlo vhi * (1 + A) *
        kBVClassRho D vlo vhi ^ (P / 3 - 1)) ∧
      (∀ b', (b' = 0 ∨ b' = w) → b ≠ b' → A ≤ w →
        ‖G b'‖ ≤ krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w +
          krCR D K L vlo vhi * (1 + A) * kBVClassRho D vlo vhi ^ (P / 3 - 1)) := by
  classical
  have hw0 := H.hw0
  have hA := H.hA
  have hcc := H.classConsts
  let V : ℕ → ℝ := fun i => kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) *
    (1 + A) * krVarTerm D vlo vhi w (P + 1 + i)
  let Rc : ℕ → ℝ := fun i => Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
    Real.sqrt (3 * krC₂ D K L) * (1 + A) *
      kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1))
  let VB : ℝ := krCV D K L vlo vhi * (1 + A) * (Real.sqrt w / krFourthRoot P + 1)
  let RB : ℝ := krCR D K L vlo vhi * (1 + A) * kBVClassRho D vlo vhi ^ (P / 3 - 1)
  have hV0 : ∀ i, 0 ≤ V i := fun i =>
    mul_nonneg (mul_nonneg (mul_nonneg hcc.2.2.2.2.le (Real.sqrt_nonneg _)) (by linarith))
      (krVarTerm_nonneg hw0 _)
  have hRc0 : ∀ i, 0 ≤ Rc i := fun i =>
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg hcc.2.2.2.1.le (Real.sqrt_nonneg _))
        (by linarith)) (pow_nonneg hcc.1 _))
  -- The same budgets as the finite theorem, now for a single fixed sequence of rows.
  have hVsum : ∀ M : ℕ, ∑ i ∈ Finset.range M, V i ≤ VB := by
    intro M
    dsimp only [V, VB]
    rw [← Finset.mul_sum]
    have hs := H.sum_krVarTerm_le (by omega : 1 ≤ P) M
    have hq0 : 0 ≤ Real.sqrt w / krFourthRoot P :=
      div_nonneg (Real.sqrt_nonneg _) (krFourthRoot_nonneg _)
    have hr0 : 0 ≤ 2 * Real.sqrt 6 / kBVClassRate D vlo vhi :=
      div_nonneg (by positivity) hcc.2.2.1.le
    have hs' : 16 * Real.sqrt w / krFourthRoot P + 2 * Real.sqrt 6 / kBVClassRate D vlo vhi ≤
        (16 + 2 * Real.sqrt 6 / kBVClassRate D vlo vhi) * (Real.sqrt w / krFourthRoot P + 1) := by
      have : 16 * Real.sqrt w / krFourthRoot P = 16 * (Real.sqrt w / krFourthRoot P) := by ring
      rw [this]
      nlinarith
    calc kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
          ∑ i ∈ Finset.range M, krVarTerm D vlo vhi w (P + 1 + i)
        ≤ kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
          ((16 + 2 * Real.sqrt 6 / kBVClassRate D vlo vhi) *
            (Real.sqrt w / krFourthRoot P + 1)) :=
          mul_le_mul_of_nonneg_left (hs.trans hs')
            (mul_nonneg (mul_nonneg hcc.2.2.2.2.le (Real.sqrt_nonneg _)) (by linarith))
      _ = _ := by unfold krCV; ring
  have hRsum : ∀ M : ℕ, ∑ i ∈ Finset.range M, Rc i ≤ RB := by
    intro M
    dsimp only [Rc, RB]
    have e : ∀ i ∈ Finset.range M, Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
        Real.sqrt (3 * krC₂ D K L) * (1 + A) *
          kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1)) =
        (Real.sqrt (2 * D) * kBVClassRemConst D vlo vhi * Real.sqrt (3 * krC₂ D K L) * (1 + A)) *
          kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1) := fun i _ => by ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    have hsum := kr_sum_rho_pow_le hcc.1 hcc.2.1 (by omega : 3 ≤ P) M
    calc (Real.sqrt (2 * D) * kBVClassRemConst D vlo vhi * Real.sqrt (3 * krC₂ D K L) * (1 + A)) *
          ∑ i ∈ Finset.range M, kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1)
        ≤ (Real.sqrt (2 * D) * kBVClassRemConst D vlo vhi * Real.sqrt (3 * krC₂ D K L) * (1 + A)) *
          (3 * kBVClassRho D vlo vhi ^ (P / 3 - 1) / (1 - kBVClassRho D vlo vhi)) :=
          mul_le_mul_of_nonneg_left hsum
            (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hcc.2.2.2.1.le)
              (Real.sqrt_nonneg _)) (by linarith))
      _ = _ := by unfold krCR; field_simp
  have hVs : Summable V := summable_of_sum_range_le hV0 hVsum
  have hRcs : Summable Rc := summable_of_sum_range_le hRc0 hRsum
  have hdec : ∀ i : ℕ, ∃ g r : ℝ → ℂ, Measurable g ∧ Measurable r ∧
      (∀ x, x ∉ Icc 0 w → g x = 0 ∧ r x = 0) ∧
      (∀ z, (krDens (Icc 0 w) ν f β a' (P + 1 + i) b z : ℂ) = g z + r z) ∧
      eVariationOn g univ ≤ ENNReal.ofReal (V i) ∧
      (∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖g x - g y‖ ≤ (2 * D * V i) * |x - y|) ∧
      (∀ x, ‖r x‖ ≤ Rc i) :=
    fun i => krDens_row_decomposition ν H hb (n := P + 1 + i) (by omega)
  choose g r hg hr hs hsum hvar hlip hrem using hdec
  -- Zero support outside the band turns the variation budget into a uniform norm bound.
  have hgV : ∀ i x, ‖g i x‖ ≤ V i := by
    intro i x
    have hgv : BoundedVariationOn (g i) univ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hvar i)
    have hd := hgv.dist_le (mem_univ x) (mem_univ (-1 : ℝ))
    have hv := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvar i)
    rw [ENNReal.toReal_ofReal (hV0 i)] at hv
    rw [(hs i (-1) (by simp)).1, dist_zero_right] at hd
    exact hd.trans hv
  have hgs : ∀ x, Summable fun i => g i x := fun x =>
    hVs.of_norm_bounded fun i => hgV i x
  have hrs : ∀ x, Summable fun i => r i x := fun x =>
    hRcs.of_norm_bounded fun i => hrem i x
  let G : ℝ → ℂ := fun x => ∑' i : ℕ, g i x
  let R : ℝ → ℂ := fun x => ∑' i : ℕ, r i x
  have hGm : Measurable G := Measurable.tsum hg
  have hRm : Measurable R := Measurable.tsum hr
  have hGRs : ∀ x, x ∉ Icc 0 w → G x = 0 ∧ R x = 0 := by
    intro x hx
    constructor
    · change (∑' i : ℕ, g i x) = 0
      calc
        _ = ∑' _ : ℕ, (0 : ℂ) := tsum_congr fun i => (hs i x hx).1
        _ = 0 := tsum_zero
    · change (∑' i : ℕ, r i x) = 0
      calc
        _ = ∑' _ : ℕ, (0 : ℂ) := tsum_congr fun i => (hs i x hx).2
        _ = 0 := tsum_zero
  have hGR : ∀ z, ((∑' i : ℕ, krDens (Icc 0 w) ν f β a' (P + 1 + i) b z : ℝ) : ℂ) =
      G z + R z := by
    intro z
    rw [Complex.ofReal_tsum]
    simp_rw [hsum]
    exact (hgs z).tsum_add (hrs z)
  -- Lower semicontinuity applies to the partial sums of these same chosen rows.
  have hGvar : eVariationOn G univ ≤ ENNReal.ofReal VB := by
    by_contra h
    have hpt : ∀ x ∈ (univ : Set ℝ),
        Tendsto (fun M => ∑ i ∈ Finset.range M, g i x) atTop (𝓝 (G x)) :=
      fun x _ => (hgs x).hasSum.tendsto_sum_nat
    have hev := eVariationOn.lowerSemicontinuous_aux hpt (lt_of_not_ge h)
    obtain ⟨M, hM⟩ := hev.exists
    exact (not_lt_of_ge ((kr_eVariationOn_sum_le hV0 hvar M).trans
      (ENNReal.ofReal_le_ofReal (hVsum M)))) hM
  have hGlip : ∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖G x - G y‖ ≤ (2 * D * VB) * |x - y| := by
    intro x hx y hy
    have hM : ∀ M : ℕ, ‖(∑ i ∈ Finset.range M, g i x) - ∑ i ∈ Finset.range M, g i y‖ ≤
        (2 * D * VB) * |x - y| := by
      intro M
      calc
        _ = ‖∑ i ∈ Finset.range M, (g i x - g i y)‖ := by rw [Finset.sum_sub_distrib]
        _ ≤ ∑ i ∈ Finset.range M, ‖g i x - g i y‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range M, (2 * D * V i) * |x - y| :=
          Finset.sum_le_sum fun i _ => hlip i x hx y hy
        _ = (2 * D * (∑ i ∈ Finset.range M, V i)) * |x - y| := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ (2 * D * VB) * |x - y| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hVsum M) (by linarith [H.hD0])) (abs_nonneg _)
    exact le_of_tendsto
      (((hgs x).hasSum.tendsto_sum_nat).sub ((hgs y).hasSum.tendsto_sum_nat)).norm
      (Eventually.of_forall hM)
  have hRsup : ∀ x, ‖R x‖ ≤ RB := fun x =>
    (tsum_of_norm_bounded hRcs.hasSum (fun i => hrem i x)).trans
      (Real.tsum_le_of_sum_range_le hRc0 hRsum)
  refine ⟨G, R, hGm, hRm, hGRs, hGR, hGvar, hGlip, hRsup, ?_⟩
  intro b' hb' hbb hAw
  have hGb : G b' = ((∑' i : ℕ, krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' : ℝ) : ℂ) - R b' := by
    rw [hGR b']; ring
  have hpin : ∑' i : ℕ, krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' ≤
      krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w := by
    apply Real.tsum_le_of_sum_range_le (fun i => krDens_nonneg ν H.hf0 _ _ _)
    intro M
    refine le_trans ?_ (sum_krDens_bdry_pin_le ν H hAw hb hb' hbb (P + M))
    rw [Finset.sum_range_add]
    have e : ∑ i ∈ Finset.range M, krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' =
        ∑ i ∈ Finset.range M, krDens (Icc 0 w) ν f β a' (P + i + 1) b b' :=
      Finset.sum_congr rfl fun i _ => by rw [show P + 1 + i = P + i + 1 by omega]
    rw [e]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun n _ => krDens_nonneg ν H.hf0 (n + 1) b b')
  have hpin0 : 0 ≤ ∑' i : ℕ, krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' :=
    tsum_nonneg fun i => krDens_nonneg ν H.hf0 _ _ _
  calc ‖G b'‖
      ≤ ‖((∑' i : ℕ, krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' : ℝ) : ℂ)‖ + ‖R b'‖ := by
        rw [hGb]
        exact norm_sub_le _ _
    _ ≤ krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w +
        krCR D K L vlo vhi * (1 + A) * kBVClassRho D vlo vhi ^ (P / 3 - 1) := by
      refine add_le_add ?_ (hRsup b')
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpin0]
      exact hpin

end

end PGM
