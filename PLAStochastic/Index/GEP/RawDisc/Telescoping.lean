import PLAStochastic.Index.GEP.RawDisc.MixtureLaws

/-!
# WP4 `RawDisc` assembly, part 4: telescoping the stopped test

For a test `F` with `|F y| ≤ e^{l y}` on `y ≥ 0`:

* `tendsto_telescope`: under any law of the path with nonnegative gaps and `T < ∞` a.s., if
  `1{i<T} e^{l S_T}` is integrable, then
  `∑_{j<n} E[1{i+j<T}(F(S_{i+j+1}) - F(S_{i+j}))] → E[1{i<T} F(S_T)] - E[1{i<T} F(S_i)]`
  (dominated convergence; the partial sums are `1{i<T}(F(S_{min(i+n,T)}) - F(S_i))`);
* `integral_incInd`: under a product law, the coordinate `g k` is independent of `{k < T}` and
  `S_k`, so `E[1{k<T}(F(S_{k+1}) - F(S_k))] = E[1{k<T} G_{ρ k}(S_k)]` with the increment
  `incFn F α s = ∫ (F(s+x) - F(s)) dα(x)` (Fubini in the coordinate `k`, `integral_piLaw_insert`);
* `SmallMgf l α`: `α` lives on `(0,∞)` with `E_α e^{l X} ≤ 2`; then `|incFn F α s| ≤ 3 e^{l s}` and
  the increment is linear along the mixture (`incFn_mixPM`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-! ## Small exponential moments -/

/-- A law on `(0, ∞)` with `E e^{l X} ≤ 2`. -/
structure SmallMgf (l : ℝ) (α : ProbabilityMeasure ℝ) : Prop where
  pos : (α : Measure ℝ) (Iic 0) = 0
  int : Integrable (fun x => Real.exp (l * x)) (α : Measure ℝ)
  le : ∫ x, Real.exp (l * x) ∂(α : Measure ℝ) ≤ 2
  lle : ∫⁻ x, ENNReal.ofReal (Real.exp (l * x)) ∂(α : Measure ℝ) ≤ 2

theorem SmallMgf.ae_pos {l : ℝ} {α : ProbabilityMeasure ℝ} (h : SmallMgf l α) :
    ∀ᵐ x ∂(α : Measure ℝ), 0 < x := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h.pos] with x hx
  simpa using hx

theorem SmallMgf.mix {l : ℝ} {ν σ : ProbabilityMeasure ℝ} (hν : SmallMgf l ν)
    (hσ : SmallMgf l σ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : SmallMgf l (mixPM ν σ t) where
  pos := mixPM_pos hν.pos hσ.pos t
  int := integrable_mixPM ht hν.int hσ.int
  le := by
    rw [integral_mixPM ht hν.int hσ.int]
    have := hν.le
    have := hσ.le
    nlinarith [ht.1, ht.2]
  lle := lintegral_mixPM_le ht hν.lle hσ.lle

/-! ## Keys of nonnegative gaps -/

theorem zero_lt_gapSegLen {eps : ℝ} (heps : 0 ≤ eps) (g : ℕ → ℝ) :
    (0 : ℕ∞) < gapSegLen eps g := by
  have h : ((0 : ℕ) : ℕ∞) < gapSegLen eps g := by
    rw [gapSegLen, lt_segLen_iff]
    refine ⟨0, 0, fun i hi => ?_⟩
    have : i = 0 := by omega
    subst this
    simpa using heps
  simpa using h

theorem survSet_zero {eps : ℝ} (heps : 0 ≤ eps) : survSet eps 0 = univ := by
  ext g
  simp only [survSet, mem_ofPred_eq, mem_univ, iff_true]
  exact_mod_cast zero_lt_gapSegLen heps g

theorem gapKeys_nonneg {g : ℕ → ℝ} (hg : ∀ j, 0 ≤ g j) (k : ℕ) : 0 ≤ gapKeys g k :=
  Finset.sum_nonneg fun j _ => hg j

theorem gapKeys_mono {g : ℕ → ℝ} (hg : ∀ j, 0 ≤ g j) {a b : ℕ} (hab : a ≤ b) :
    gapKeys g a ≤ gapKeys g b :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) fun j _ _ => hg j

theorem stopSum_of_eq {eps : ℝ} {g : ℕ → ℝ} {m : ℕ} (hm : gapSegLen eps g = m) :
    stopSum eps g = gapKeys g m := by
  rw [stopSum, hm, ENat.toNat_natCast]

theorem rawAsm_stopSum_nonneg {eps : ℝ} {g : ℕ → ℝ} (hg : ∀ j, 0 ≤ g j) : 0 ≤ stopSum eps g :=
  gapKeys_nonneg hg _

theorem mem_survSet_iff_of_eq {eps : ℝ} {g : ℕ → ℝ} {m : ℕ} (hm : gapSegLen eps g = m) (k : ℕ) :
    g ∈ survSet eps k ↔ k < m := by
  simp only [survSet, mem_ofPred_eq, hm, Nat.cast_lt]

/-! ## The telescoping identity -/

/-- The increment integrand `1{k<T} (F(S_{k+1}) - F(S_k))`. -/
def incInd (eps : ℝ) (F : ℝ → ℝ) (k : ℕ) : (ℕ → ℝ) → ℝ :=
  (survSet eps k).indicator (fun g => F (gapKeys g (k + 1)) - F (gapKeys g k))

theorem measurable_incInd (eps : ℝ) {F : ℝ → ℝ} (hF : Measurable F) (k : ℕ) :
    Measurable (incInd eps F k) :=
  ((hF.comp (rawAsm_measurable_gapKeys (k + 1))).sub (hF.comp (rawAsm_measurable_gapKeys k))).indicator
    (measurableSet_survSet eps k)

/-- The partial sums of the telescoping series, pathwise. -/
theorem sum_incInd_eq {eps : ℝ} (F : ℝ → ℝ) {g : ℕ → ℝ} {m : ℕ} (hm : gapSegLen eps g = m)
    (i n : ℕ) :
    ∑ j ∈ Finset.range n, incInd eps F (i + j) g =
      if i < m then F (gapKeys g (min (i + n) m)) - F (gapKeys g i) else 0 := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    split_ifs with h
    · rw [min_eq_left h.le, sub_self]
    · rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, incInd]
    by_cases hin : i + n < m
    · have hi : i < m := by omega
      rw [Set.indicator_of_mem ((mem_survSet_iff_of_eq hm _).2 hin), if_pos hi, if_pos hi,
        min_eq_left hin.le, min_eq_left (show i + (n + 1) ≤ m by omega),
        show i + n + 1 = i + (n + 1) by omega]
      ring
    · rw [Set.indicator_of_notMem (fun h => hin ((mem_survSet_iff_of_eq hm _).1 h)), add_zero,
        min_eq_right (show m ≤ i + n by omega), min_eq_right (show m ≤ i + (n + 1) by omega)]

/-- **The telescoping series of the stopped test.** -/
theorem tendsto_telescope {μ : Measure (ℕ → ℝ)} [IsProbabilityMeasure μ] {eps l : ℝ}
    (hl : 0 ≤ l) {F : ℝ → ℝ} (hF : Measurable F)
    (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y)) (hpos : ∀ᵐ g ∂μ, ∀ j, 0 ≤ g j)
    (hfin : ∀ᵐ g ∂μ, gapSegLen eps g ≠ ⊤) (i : ℕ)
    (hint : Integrable ((survSet eps i).indicator (fun g => Real.exp (l * stopSum eps g))) μ) :
    Tendsto (fun n => ∑ j ∈ Finset.range n, ∫ g, incInd eps F (i + j) g ∂μ) atTop
      (𝓝 (∫ g, (survSet eps i).indicator (fun g => F (stopSum eps g)) g ∂μ -
        ∫ g, (survSet eps i).indicator (fun g => F (gapKeys g i)) g ∂μ)) := by
  set bnd : (ℕ → ℝ) → ℝ :=
    fun g => 2 * (survSet eps i).indicator (fun g => Real.exp (l * stopSum eps g)) g with hbnd
  have hbint : Integrable bnd μ := hint.const_mul 2
  have hmono : ∀ g : ℕ → ℝ, (∀ j, 0 ≤ g j) → ∀ {m : ℕ}, gapSegLen eps g = m → ∀ a ≤ m,
      |F (gapKeys g a)| ≤ Real.exp (l * stopSum eps g) := by
    intro g hg m hm a ha
    refine (hFb _ (gapKeys_nonneg hg a)).trans (Real.exp_le_exp.2 ?_)
    rw [stopSum_of_eq hm]
    exact mul_le_mul_of_nonneg_left (gapKeys_mono hg ha) hl
  have hb0 : ∀ g, 0 ≤ bnd g := fun g =>
    mul_nonneg zero_le_two (Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)
  -- pathwise bound on the partial sums
  have hpart : ∀ᵐ g ∂μ, ∀ n, ‖∑ j ∈ Finset.range n, incInd eps F (i + j) g‖ ≤ bnd g := by
    filter_upwards [hpos, hfin] with g hg hT n
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hT
    rw [sum_incInd_eq F hm.symm i n, Real.norm_eq_abs]
    split_ifs with him
    · rw [hbnd]
      simp only
      rw [Set.indicator_of_mem ((mem_survSet_iff_of_eq hm.symm i).2 him)]
      have h1 := hmono g hg hm.symm (min (i + n) m) (min_le_right _ _)
      have h2 := hmono g hg hm.symm i him.le
      calc |F (gapKeys g (min (i + n) m)) - F (gapKeys g i)|
          ≤ |F (gapKeys g (min (i + n) m))| + |F (gapKeys g i)| := abs_sub _ _
        _ ≤ 2 * Real.exp (l * stopSum eps g) := by linarith
    · rw [abs_zero]
      exact hb0 g
  -- pathwise bound on the single terms
  have hsingle : ∀ᵐ g ∂μ, ∀ j, ‖incInd eps F (i + j) g‖ ≤ bnd g := by
    filter_upwards [hpos, hfin] with g hg hT j
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hT
    unfold incInd
    by_cases h : i + j < m
    · rw [Set.indicator_of_mem ((mem_survSet_iff_of_eq hm.symm _).2 h), hbnd]
      simp only
      rw [Set.indicator_of_mem ((mem_survSet_iff_of_eq hm.symm i).2 (by omega)),
        Real.norm_eq_abs]
      have h1 := hmono g hg hm.symm (i + j + 1) (by omega)
      have h2 := hmono g hg hm.symm (i + j) h.le
      calc |F (gapKeys g (i + j + 1)) - F (gapKeys g (i + j))|
          ≤ |F (gapKeys g (i + j + 1))| + |F (gapKeys g (i + j))| := abs_sub _ _
        _ ≤ 2 * Real.exp (l * stopSum eps g) := by linarith
    · rw [Set.indicator_of_notMem (fun h' => h ((mem_survSet_iff_of_eq hm.symm _).1 h')),
        norm_zero]
      exact hb0 g
  have hterm : ∀ j, Integrable (incInd eps F (i + j)) μ := fun j =>
    hbint.mono' (measurable_incInd eps hF _).aestronglyMeasurable (hsingle.mono fun g hg => hg j)
  -- the pathwise limit
  have hlim : ∀ᵐ g ∂μ, Tendsto (fun n => ∑ j ∈ Finset.range n, incInd eps F (i + j) g) atTop
      (𝓝 ((survSet eps i).indicator (fun g => F (stopSum eps g)) g -
        (survSet eps i).indicator (fun g => F (gapKeys g i)) g)) := by
    filter_upwards [hfin] with g hT
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hT
    refine tendsto_atTop_of_eventually_const (i₀ := m) fun n hn => ?_
    rw [sum_incInd_eq F hm.symm i n]
    split_ifs with him
    · rw [min_eq_right (by omega), Set.indicator_of_mem ((mem_survSet_iff_of_eq hm.symm i).2 him),
        Set.indicator_of_mem ((mem_survSet_iff_of_eq hm.symm i).2 him), stopSum_of_eq hm.symm]
    · rw [Set.indicator_of_notMem (fun h => him ((mem_survSet_iff_of_eq hm.symm i).1 h)),
        Set.indicator_of_notMem (fun h => him ((mem_survSet_iff_of_eq hm.symm i).1 h)), sub_zero]
  have hmeasn : ∀ n, AEStronglyMeasurable
      (fun g => ∑ j ∈ Finset.range n, incInd eps F (i + j) g) μ := fun n =>
    (Finset.measurable_sum _ fun j _ => measurable_incInd eps hF (i + j)).aestronglyMeasurable
  have hdom := tendsto_integral_of_dominated_convergence bnd hmeasn hbint
    (fun n => hpart.mono fun g hg => hg n) hlim
  -- integrability of the two limit terms
  have hA : Integrable ((survSet eps i).indicator (fun g => F (stopSum eps g))) μ := by
    refine hint.mono' ((hF.comp (measurable_stopSum eps)).indicator
      (measurableSet_survSet eps i)).aestronglyMeasurable ?_
    filter_upwards [hpos] with g hg
    by_cases hs : g ∈ survSet eps i
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, Real.norm_eq_abs]
      exact hFb _ (rawAsm_stopSum_nonneg hg)
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, norm_zero]
  have hB : Integrable ((survSet eps i).indicator (fun g => F (gapKeys g i))) μ := by
    refine hint.mono' (measurable_survInd eps i hF).aestronglyMeasurable ?_
    filter_upwards [hpos, hfin] with g hg hT
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hT
    by_cases hs : g ∈ survSet eps i
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, Real.norm_eq_abs]
      exact hmono g hg hm.symm i ((mem_survSet_iff_of_eq hm.symm i).1 hs).le
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, norm_zero]
  rw [← integral_sub hA hB]
  refine hdom.congr fun n => ?_
  exact integral_finsetSum _ fun j _ => hterm j

/-! ## The increment of one coordinate -/

/-- The one-step increment `G_α(s) = ∫ (F(s + x) - F(s)) dα(x)`. -/
def incFn (F : ℝ → ℝ) (α : ProbabilityMeasure ℝ) (s : ℝ) : ℝ :=
  ∫ x, (F (s + x) - F s) ∂(α : Measure ℝ)

theorem measurable_incFn {F : ℝ → ℝ} (hF : Measurable F) (α : ProbabilityMeasure ℝ) :
    Measurable (incFn F α) := by
  have hm : Measurable fun p : ℝ × ℝ => F (p.1 + p.2) - F p.1 :=
    (hF.comp (measurable_fst.add measurable_snd)).sub (hF.comp measurable_fst)
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := (α : Measure ℝ))).measurable

theorem integrable_incFn_integrand {l : ℝ} {α : ProbabilityMeasure ℝ} (hα : SmallMgf l α)
    {F : ℝ → ℝ} (hF : Measurable F) (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y)) {s : ℝ}
    (hs : 0 ≤ s) : Integrable (fun x => F (s + x) - F s) (α : Measure ℝ) := by
  have hb : Integrable (fun x => Real.exp (l * s) * Real.exp (l * x) + |F s|)
      (α : Measure ℝ) := (hα.int.const_mul _).add (integrable_const _)
  refine hb.mono' ((hF.comp (measurable_const.add measurable_id)).sub
    measurable_const).aestronglyMeasurable ?_
  filter_upwards [hα.ae_pos] with x hx
  rw [Real.norm_eq_abs]
  have h1 := hFb (s + x) (by linarith)
  rw [mul_add, Real.exp_add] at h1
  exact (abs_sub _ _).trans (by linarith)

/-- `|G_α(s)| ≤ 3 e^{l s}` on `s ≥ 0`. -/
theorem abs_incFn_le {l : ℝ} {α : ProbabilityMeasure ℝ} (hα : SmallMgf l α) {F : ℝ → ℝ}
    (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y)) {s : ℝ} (hs : 0 ≤ s) :
    |incFn F α s| ≤ 3 * Real.exp (l * s) := by
  have hb : Integrable (fun x => Real.exp (l * s) * Real.exp (l * x) + Real.exp (l * s))
      (α : Measure ℝ) := (hα.int.const_mul _).add (integrable_const _)
  have h := norm_integral_le_of_norm_le hb (f := fun x => F (s + x) - F s) (by
    filter_upwards [hα.ae_pos] with x hx
    rw [Real.norm_eq_abs]
    have h1 := hFb (s + x) (by linarith)
    have h2 := hFb s hs
    rw [mul_add, Real.exp_add] at h1
    exact (abs_sub _ _).trans (by linarith))
  rw [integral_add (hα.int.const_mul _) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, one_smul] at h
  rw [incFn, ← Real.norm_eq_abs]
  have h3 := hα.le
  have h4 : 0 < Real.exp (l * s) := Real.exp_pos _
  nlinarith

/-- The increment is linear along the mixture. -/
theorem incFn_mixPM {l : ℝ} {ν σ : ProbabilityMeasure ℝ} (hν : SmallMgf l ν)
    (hσ : SmallMgf l σ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {F : ℝ → ℝ} (hF : Measurable F)
    (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y)) {s : ℝ} (hs : 0 ≤ s) :
    incFn F (mixPM ν σ t) s = (1 - t) * incFn F ν s + t * incFn F σ s :=
  integral_mixPM ht (integrable_incFn_integrand hν hF hFb hs)
    (integrable_incFn_integrand hσ hF hFb hs)

/-- **Independence of the next gap**: `E[1{k<T}(F(S_{k+1}) - F(S_k))] = E[1{k<T} G_{ρ k}(S_k)]`
under a product law. -/
theorem integral_incInd (ρ : ℕ → ProbabilityMeasure ℝ) (eps : ℝ) {F : ℝ → ℝ}
    (hF : Measurable F) (k : ℕ) (hint : Integrable (incInd eps F k) (piLaw ρ)) :
    ∫ g, incInd eps F k g ∂(piLaw ρ) = survInt eps (piLaw ρ) k (incFn F (ρ k)) := by
  rw [integral_piLaw_insert ρ k (measurable_incInd eps hF k) hint, survInt]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [incInd]
  by_cases hg : g ∈ survSet eps k
  · have hg' : ∀ y, Function.update g k y ∈ survSet eps k := fun y =>
      (mem_survSet_update le_rfl g y).2 hg
    simp only [Set.indicator_of_mem (hg' _), Set.indicator_of_mem hg, gapKeys_update_succ,
      gapKeys_update_self]
    rfl
  · have hg' : ∀ y, Function.update g k y ∉ survSet eps k := fun y h =>
      hg ((mem_survSet_update le_rfl g y).1 h)
    simp only [Set.indicator_of_notMem (hg' _), Set.indicator_of_notMem hg, integral_zero]

/-- Integrability of the increment integrand under a product law with small moments. -/
theorem integrable_incInd {l : ℝ} {ρ : ℕ → ProbabilityMeasure ℝ} (hρ : ∀ j, SmallMgf l (ρ j))
    (eps : ℝ) {F : ℝ → ℝ} (hF : Measurable F) (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y))
    (k : ℕ) : Integrable (incInd eps F k) (piLaw ρ) := by
  have hb := (rawAsm_integrable_exp_gapKeys (fun j => (hρ j).lle) (k + 1)).add
    (rawAsm_integrable_exp_gapKeys (fun j => (hρ j).lle) k)
  refine hb.mono' (measurable_incInd eps hF k).aestronglyMeasurable ?_
  filter_upwards [ae_pos_piLaw fun j => (hρ j).pos] with g hg
  unfold incInd
  simp only [Pi.add_apply]
  by_cases hs : g ∈ survSet eps k
  · rw [Set.indicator_of_mem hs, Real.norm_eq_abs]
    have h1 := hFb _ (gapKeys_nonneg (fun j => (hg j).le) (k + 1))
    have h2 := hFb _ (gapKeys_nonneg (fun j => (hg j).le) k)
    exact (abs_sub _ _).trans (by linarith)
  · rw [Set.indicator_of_notMem hs, norm_zero]
    exact add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

end

end PGM
