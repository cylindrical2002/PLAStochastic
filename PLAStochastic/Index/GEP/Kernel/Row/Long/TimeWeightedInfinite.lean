import PLAStochastic.Index.GEP.Kernel.Row.Long.TimeWeightedGreen

/-!
# The actual exponentially weighted infinite long Green decomposition

The time-weighted per-row parts are selected once and summed by their proven
summable budgets. All constants and the weight cutoff are those of the finite
`krLong_decomposition_expw`; the resulting equality holds pointwise at the two
boundary traces as well. Joint selection in the slope is handled separately.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

variable {β a : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}

/-- The true time-weighted Green row remains summable after any finite cutoff. -/
theorem summable_expw_krDens_long_row {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    (P : ℕ) (z : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi / 16) :
    Summable fun i : ℕ => Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) *
      krDens (Icc 0 w) ν f β a' (P + 1 + i) b z := by
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (summable_nat_add_iff P).2 (summable_expw_krDens_bdry_row ν H hb z hε0 hε)

/-- Fixed-slope infinite long decomposition with the original weighted constants. -/
theorem krLong_infinite_decomposition_expw {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {P : ℕ} (hP : 12 ≤ P) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krEps D vlo vhi) :
    ∃ G R : ℝ → ℂ, Measurable G ∧ Measurable R ∧
      (∀ x, x ∉ Icc 0 w → G x = 0 ∧ R x = 0) ∧
      (∀ z, ((∑' i : ℕ, Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) *
        krDens (Icc 0 w) ν f β a' (P + 1 + i) b z : ℝ) : ℂ) = G z + R z) ∧
      eVariationOn G univ ≤ ENNReal.ofReal (2 * Real.exp (3 * ε) * krCV D K L vlo vhi * (1 + A) *
        (Real.sqrt w / krFourthRoot P + 1)) ∧
      (∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖G x - G y‖ ≤
        (2 * D * (2 * Real.exp (3 * ε) * krCV D K L vlo vhi * (1 + A) *
          (Real.sqrt w / krFourthRoot P + 1))) * |x - y|) ∧
      (∀ x, ‖R x‖ ≤ 2 * Real.exp (5 * ε) * krCR D K L vlo vhi * (1 + A) *
        ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1)) ∧
      (∀ b', (b' = 0 ∨ b' = w) → b ≠ b' → A ≤ w →
        ‖G b'‖ ≤ Real.exp (3 * ε) * ((krCP D θ K L vlo vhi + 12 * krC₂ D K L / krKappa D vlo vhi) *
          (1 + A) ^ 2 / Real.sqrt w) +
          2 * Real.exp (5 * ε) * krCR D K L vlo vhi * (1 + A) *
            ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1)) := by
  have hw0 := H.hw0
  have hw := H.hw
  have hA := H.hA
  have hcc := H.classConsts
  have hC := krC₂_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  have hD0 := H.hD0
  have hεκ : ε ≤ krKappa D vlo vhi / 16 := by
    have := hε.trans H.krEps_le_kappa
    have := H.kappa_pos
    linarith
  set ω : ℕ → ℝ := fun i => Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) with hω_def
  have hω0 : ∀ i, 0 ≤ ω i := fun i => (Real.exp_pos _).le
  -- per-row decompositions, scaled
  have hdec : ∀ i : ℕ, ∃ g r : ℝ → ℂ, Measurable g ∧ Measurable r ∧
      (∀ x, x ∉ Icc 0 w → g x = 0 ∧ r x = 0) ∧
      (∀ z, ((ω i * krDens (Icc 0 w) ν f β a' (P + 1 + i) b z : ℝ) : ℂ) = g z + r z) ∧
      eVariationOn g univ ≤ ENNReal.ofReal (ω i * (kBVClassVarConst D vlo vhi *
        Real.sqrt (krC₂ D K L) * (1 + A) * krVarTerm D vlo vhi w (P + 1 + i))) ∧
      (∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖g x - g y‖ ≤
        (ω i * (2 * D * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
          krVarTerm D vlo vhi w (P + 1 + i)))) * |x - y|) ∧
      (∀ x, ‖r x‖ ≤ ω i * (Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
        Real.sqrt (3 * krC₂ D K L) * (1 + A) * kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1)))) := by
    intro i
    obtain ⟨g, r, hg, hr, hs, hsum, hvar, hlip, hrem⟩ :=
      krDens_row_decomposition ν H hb (n := P + 1 + i) (by omega)
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
      kr_scale_decomposition (hω0 i) hg hr hs hsum hvar hlip hrem
    exact ⟨_, _, h1, h2, h3, h4, h5, h6, h7⟩
  choose g r hg hr hs hsum hvar hlip hrem using hdec
  have hV0 : ∀ i, 0 ≤ ω i * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
      krVarTerm D vlo vhi w (P + 1 + i)) := fun i =>
    mul_nonneg (hω0 i) (mul_nonneg (mul_nonneg (mul_nonneg hcc.2.2.2.2.le (Real.sqrt_nonneg _))
      (by linarith)) (krVarTerm_nonneg hw0 _))
  -- the variation sum
  have hrate := hcc.2.2.1
  have hrate' : ε ≤ kBVClassRate D vlo vhi / 2 := by
    have := hε.trans H.krEps_le_kappa
    unfold kBVClassRate
    unfold krKappa at this
    linarith
  have hρε : 0 < kBVClassRate D vlo vhi - ε := by linarith
  have hVsum : ∀ M : ℕ, ∑ i ∈ Finset.range M, ω i * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) *
      (1 + A) * krVarTerm D vlo vhi w (P + 1 + i)) ≤
      2 * Real.exp (3 * ε) * krCV D K L vlo vhi * (1 + A) * (Real.sqrt w / krFourthRoot P + 1) := by
    intro M
    have hterm : ∀ i ∈ Finset.range M, ω i * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) *
        (1 + A) * krVarTerm D vlo vhi w (P + 1 + i)) ≤
        (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) * Real.exp (3 * ε)) *
          krVarTermGen (kBVClassRate D vlo vhi - ε) w (P + 1 + i) := fun i _ => by
      have := H.expw_varTerm hε0 (kBVClassRate D vlo vhi) (P + 1 + i)
      have e : ω i * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
          krVarTerm D vlo vhi w (P + 1 + i)) =
          (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A)) *
            (Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) *
              krVarTermGen (kBVClassRate D vlo vhi) w (P + 1 + i)) := by
        simp only [hω_def, krVarTerm]
        ring
      rw [e, mul_assoc _ (Real.exp (3 * ε))]
      exact mul_le_mul_of_nonneg_left this
        (mul_nonneg (mul_nonneg hcc.2.2.2.2.le (Real.sqrt_nonneg _)) (by linarith))
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hs := kr_sum_krVarTermGen_le hρε hw
      (by linarith [H.rate_le_one, one_le_pow₀ (n := 2) hw]) (by omega : 1 ≤ P) M
    have hq0 : 0 ≤ Real.sqrt w / krFourthRoot P :=
      div_nonneg (Real.sqrt_nonneg _) (krFourthRoot_nonneg _)
    have hinv : 2 * Real.sqrt 6 / (kBVClassRate D vlo vhi - ε) ≤
        4 * Real.sqrt 6 / kBVClassRate D vlo vhi := by
      rw [div_le_div_iff₀ hρε hrate]
      nlinarith [Real.sqrt_nonneg 6]
    have hs' : 16 * Real.sqrt w / krFourthRoot P + 2 * Real.sqrt 6 / (kBVClassRate D vlo vhi - ε) ≤
        2 * ((16 + 2 * Real.sqrt 6 / kBVClassRate D vlo vhi) * (Real.sqrt w / krFourthRoot P + 1)) := by
      have h2 : 0 ≤ 2 * Real.sqrt 6 / kBVClassRate D vlo vhi := by positivity
      have hcx := mul_nonneg h2 hq0
      have e1 : 16 * Real.sqrt w / krFourthRoot P = 16 * (Real.sqrt w / krFourthRoot P) := by ring
      have e2 : 2 * ((16 + 2 * Real.sqrt 6 / kBVClassRate D vlo vhi) *
          (Real.sqrt w / krFourthRoot P + 1)) =
          32 * (Real.sqrt w / krFourthRoot P) + 32 +
            2 * (2 * Real.sqrt 6 / kBVClassRate D vlo vhi * (Real.sqrt w / krFourthRoot P)) +
            2 * (2 * Real.sqrt 6 / kBVClassRate D vlo vhi) := by ring
      have e3 : 4 * Real.sqrt 6 / kBVClassRate D vlo vhi =
          2 * (2 * Real.sqrt 6 / kBVClassRate D vlo vhi) := by ring
      rw [e1, e2]
      rw [e3] at hinv
      linarith
    calc kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) * Real.exp (3 * ε) *
          ∑ i ∈ Finset.range M, krVarTermGen (kBVClassRate D vlo vhi - ε) w (P + 1 + i)
        ≤ kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) * Real.exp (3 * ε) *
          (2 * ((16 + 2 * Real.sqrt 6 / kBVClassRate D vlo vhi) *
            (Real.sqrt w / krFourthRoot P + 1))) :=
          mul_le_mul_of_nonneg_left (hs.trans hs')
            (mul_nonneg (mul_nonneg (mul_nonneg hcc.2.2.2.2.le (Real.sqrt_nonneg _))
              (by linarith)) (Real.exp_pos _).le)
      _ = _ := by unfold krCV; ring
  -- the remainder sum
  set ρ' := kBVClassRho D vlo vhi * Real.exp (3 * ε / w ^ 2) with hρ'_def
  have hρ'0 : 0 ≤ ρ' := mul_nonneg hcc.1 (Real.exp_pos _).le
  have hρ'le := H.rho_expw_le hε0 hε
  have hρ'1 : ρ' < 1 := by linarith [hcc.2.1]
  have hRsum : ∀ M : ℕ, ∑ i ∈ Finset.range M, ω i * (Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
      Real.sqrt (3 * krC₂ D K L) * (1 + A) * kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1))) ≤
      2 * Real.exp (5 * ε) * krCR D K L vlo vhi * (1 + A) *
        ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1) := by
    intro M
    set Cr := Real.sqrt (2 * D) * kBVClassRemConst D vlo vhi * Real.sqrt (3 * krC₂ D K L) * (1 + A)
      with hCr_def
    have hCr0 : 0 ≤ Cr :=
      mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hcc.2.2.2.1.le)
        (Real.sqrt_nonneg _)) (by linarith)
    have hterm : ∀ i ∈ Finset.range M, ω i * (Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
        Real.sqrt (3 * krC₂ D K L) * (1 + A) * kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1))) ≤
        (Cr * Real.exp (5 * ε)) * ρ' ^ ((P + 1 + i) / 3 - 1) := fun i _ => by
      have := kr_expw_rho (ε := ε) (w := w) hε0 hw hcc.1 (P + 1 + i)
      have e : ω i * (Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
          Real.sqrt (3 * krC₂ D K L) * (1 + A) * kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1))) =
          Cr * (Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) *
            kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1)) := by
        simp only [hω_def, hCr_def]
        ring
      rw [e]
      refine (mul_le_mul_of_nonneg_left this hCr0).trans (le_of_eq ?_)
      rw [hρ'_def]
      ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hsum := kr_sum_rho_pow_le hρ'0 hρ'1 (by omega : 3 ≤ P) M
    have hpow : ρ' ^ (P / 3 - 1) ≤ ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1) :=
      pow_le_pow_left₀ hρ'0 hρ'le _
    have hhalf : 0 < (1 - kBVClassRho D vlo vhi) / 2 := by linarith [hcc.2.1]
    have hinv : 1 / (1 - ρ') ≤ 1 / ((1 - kBVClassRho D vlo vhi) / 2) :=
      one_div_le_one_div_of_le hhalf (by linarith)
    have hgeom : 3 * ρ' ^ (P / 3 - 1) / (1 - ρ') ≤
        3 * ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1) / ((1 - kBVClassRho D vlo vhi) / 2) := by
      have hρ1' : 0 ≤ (1 + kBVClassRho D vlo vhi) / 2 := by linarith [hcc.1]
      exact div_le_div₀ (mul_nonneg (by norm_num) (pow_nonneg hρ1' _)) (by gcongr) hhalf
        (by linarith)
    calc Cr * Real.exp (5 * ε) * ∑ i ∈ Finset.range M, ρ' ^ ((P + 1 + i) / 3 - 1)
        ≤ Cr * Real.exp (5 * ε) *
          (3 * ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1) / ((1 - kBVClassRho D vlo vhi) / 2)) :=
          mul_le_mul_of_nonneg_left (hsum.trans hgeom) (mul_nonneg hCr0 (Real.exp_pos _).le)
      _ = _ := by
          simp only [hCr_def]
          unfold krCR
          field_simp
  let V : ℕ → ℝ := fun i => ω i * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) *
    (1 + A) * krVarTerm D vlo vhi w (P + 1 + i))
  let Rc : ℕ → ℝ := fun i => ω i * (Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
    Real.sqrt (3 * krC₂ D K L) * (1 + A) *
      kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1)))
  let VB : ℝ := 2 * Real.exp (3 * ε) * krCV D K L vlo vhi * (1 + A) *
    (Real.sqrt w / krFourthRoot P + 1)
  let RB : ℝ := 2 * Real.exp (5 * ε) * krCR D K L vlo vhi * (1 + A) *
    ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1)
  have hRc0 : ∀ i, 0 ≤ Rc i := fun i =>
    mul_nonneg (hω0 i) (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg hcc.2.2.2.1.le (Real.sqrt_nonneg _))
        (by linarith)) (pow_nonneg hcc.1 _)))
  have hVs : Summable V := summable_of_sum_range_le hV0 hVsum
  have hRcs : Summable Rc := summable_of_sum_range_le hRc0 hRsum
  have hlip' : ∀ i, ∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w,
      ‖g i x - g i y‖ ≤ (2 * D * V i) * |x - y| := by
    intro i x hx y hy
    convert hlip i x hx y hy using 1
    dsimp only [V]
    ring
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
  have hGR : ∀ z, ((∑' i : ℕ, ω i * krDens (Icc 0 w) ν f β a' (P + 1 + i) b z : ℝ) : ℂ) =
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
          Finset.sum_le_sum fun i _ => hlip' i x hx y hy
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
  have hGb : G b' =
      ((∑' i : ℕ, ω i * krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' : ℝ) : ℂ) -
        R b' := by
    rw [hGR b']; ring
  have hpin : ∑' i : ℕ, ω i * krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' ≤
      Real.exp (3 * ε) * ((krCP D θ K L vlo vhi + 12 * krC₂ D K L / krKappa D vlo vhi) *
        (1 + A) ^ 2 / Real.sqrt w) := by
    apply Real.tsum_le_of_sum_range_le
      (fun i => mul_nonneg (hω0 i) (krDens_nonneg ν H.hf0 _ _ _))
    intro M
    refine le_trans ?_ (sum_expw_krDens_bdry_pin_le ν H hAw hb hb' hbb hε0 hεκ (P + M))
    rw [Finset.sum_range_add]
    have e : ∑ i ∈ Finset.range M, ω i * krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' =
        ∑ i ∈ Finset.range M, Real.exp (ε * ((P + i + 1 : ℕ) : ℝ) / w ^ 2) *
          krDens (Icc 0 w) ν f β a' (P + i + 1) b b' :=
      Finset.sum_congr rfl fun i _ => by
        simp only [hω_def]
        rw [show P + 1 + i = P + i + 1 by omega]
    rw [e]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun n _ =>
      mul_nonneg (Real.exp_pos _).le (krDens_nonneg ν H.hf0 (n + 1) b b'))
  have hpin0 : 0 ≤ ∑' i : ℕ, ω i * krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' :=
    tsum_nonneg fun i => mul_nonneg (hω0 i) (krDens_nonneg ν H.hf0 _ _ _)
  calc ‖G b'‖
      ≤ ‖((∑' i : ℕ, ω i * krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' : ℝ) : ℂ)‖ +
        ‖R b'‖ := by rw [hGb]; exact norm_sub_le _ _
    _ ≤ _ := by
        refine add_le_add ?_ (hRsup b')
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpin0]
        exact hpin

end
end PGM
