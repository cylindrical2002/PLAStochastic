import PLAStochastic.Index.GEP.DirectTerm.Defs
import PLAStochastic.Index.GEP.Response.Score.Continuity
import PLAStochastic.Index.GEP.OrbitClosure.CyclicReduction
import PLAStochastic.Index.GEP.Response.KappaBound

/-!
# WP4 leaf `DirectTerm`, part 1: the coarse bound of the insertion kernel

The deleted-mark window argument of `positive-direction-response.md` (PD) §8.1 (29) and §8.3
(34).  Fix `x`, a coordinate `i` and write `g' = g with g_i := x`.  On `{i < T(g)}` (which is
`{i < T(g')}`) and `{T(g') = t}`:

* `i < t`, and the stopped sum is `S_T(g') = x + ∑_{s < t, s ≠ i} g_s` (`stopSum_update_eq`);
* the left window `{i < T(g)}` (the keys `0, …, i`) and the right window
  `{t - 2 - i < T(g_{i+1+·})}` (the keys `i+1, …, t-1`) are both feasible, and neither reads
  the coordinate `i` (`mem_winSet_of_eq`, `prefixAffineFeasible_window`).  The longer window has
  about `t/2` gaps, so `P(winSet) ≤ (72/71) q^{2(t-2)}` with `q⁴ = a_ε` the stopping ratio
  (`measure_winSet_le`, shift invariance `map_shift_iidLaw`);
* the exponential weight `e^{κ Σ}` of the other `t - 1` gaps has second moment
  `m(2κ)^{t-1}` with `m(λ) = E e^{λX} ≤ e^{8Dλ/θ²}` (`lintegral_exp_sum_eq`,
  `RegLaw.lintegral_exp_le_exp`), and the Cauchy–Schwarz step is done in the AM-GM form
  `1_W E ≤ (u 1_W + E²/u)/2` (`lintegral_indicator_exp_le`).

For `κ ε² ≤ κ₁` the resulting series `∑_t t (72/71 + 1)/2 · q^{t-2} r^{t-1}` is at most
`K₁ ε⁴` (`coarse_bound`), uniformly in `x`.  Consequently, for measurable `F` with
`|F y| ≤ e^{κ y}` on `y ≥ 0`, the insertion kernel `I_F = insKernel ε ν (F ∘ S_T)` is
measurable (`measurable_insKernel`), absolutely summable at every `x ≥ 0` with
`|I_F(x)| ≤ K₁ ε⁴ e^{κx}` (`abs_insKernel_le`), and linear in `F` (`insKernel_const_mul`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

variable {D θ vlo vhi : ℝ}

/-! ## Exponential moments of one gap -/

theorem exp_le_one_add_mul_exp (u : ℝ) : Real.exp u ≤ 1 + u * Real.exp u := by
  have h := Real.add_one_le_exp (-u)
  have h2 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos u
  nlinarith

/-- `E_ν e^{λX} ≤ e^{8Dλ/θ²}` for `0 ≤ λ ≤ θ/4` on the class. -/
theorem RegLaw.lintegral_exp_le_exp {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) {l : ℝ} (hl0 : 0 ≤ l) (hl : l ≤ θ / 4) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (l * y)) ∂(ν : Measure ℝ) ≤
      ENNReal.ofReal (Real.exp (8 * D / θ ^ 2 * l)) := by
  have hD := h.D_nonneg
  have hlt : l < θ / 2 := by linarith
  have hpt : ∀ᵐ y ∂(ν : Measure ℝ), ENNReal.ofReal (Real.exp (l * y)) ≤
      1 + ENNReal.ofReal (4 * l / θ) * ENNReal.ofReal (Real.exp (θ / 2 * y)) := by
    filter_upwards [h.ae_pos] with y hy
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 := exp_le_one_add_mul_exp (l * y)
    have h2 : y * Real.exp (l * y) ≤ Real.exp (θ / 2 * y) / (θ / 2 - l) :=
      mul_exp_le_exp_div hlt
    have h3 : Real.exp (θ / 2 * y) / (θ / 2 - l) ≤ 4 / θ * Real.exp (θ / 2 * y) := by
      rw [div_le_iff₀ (by linarith)]
      have : 0 ≤ Real.exp (θ / 2 * y) := (Real.exp_pos _).le
      have e : 4 / θ * Real.exp (θ / 2 * y) * (θ / 2 - l) =
          Real.exp (θ / 2 * y) * (2 - 4 * l / θ) := by field_simp; ring
      rw [e]
      have : 4 * l / θ ≤ 1 := by rw [div_le_one hθ]; linarith
      nlinarith
    calc Real.exp (l * y) ≤ 1 + l * (y * Real.exp (l * y)) := by linarith [h1]
      _ ≤ 1 + l * (4 / θ * Real.exp (θ / 2 * y)) := by
        linarith [mul_le_mul_of_nonneg_left (h2.trans h3) hl0]
      _ = 1 + 4 * l / θ * Real.exp (θ / 2 * y) := by ring
  have hθ2 := h.lintegral_exp_le (a := θ / 2) (by linarith)
  have e2 : D / (θ - θ / 2) = 2 * D / θ := by field_simp; ring
  rw [e2] at hθ2
  calc ∫⁻ y, ENNReal.ofReal (Real.exp (l * y)) ∂(ν : Measure ℝ)
      ≤ ∫⁻ y, (1 + ENNReal.ofReal (4 * l / θ) * ENNReal.ofReal (Real.exp (θ / 2 * y)))
          ∂(ν : Measure ℝ) := lintegral_mono_ae hpt
    _ = 1 + ENNReal.ofReal (4 * l / θ) *
          ∫⁻ y, ENNReal.ofReal (Real.exp (θ / 2 * y)) ∂(ν : Measure ℝ) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul,
          lintegral_const_mul _ (by fun_prop)]
    _ ≤ 1 + ENNReal.ofReal (4 * l / θ) * ENNReal.ofReal (2 * D / θ) := by gcongr
    _ = ENNReal.ofReal (1 + 8 * D / θ ^ 2 * l) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add zero_le_one (by positivity)]
        congr 1
        field_simp
        ring
    _ ≤ ENNReal.ofReal (Real.exp (8 * D / θ ^ 2 * l)) := by
        apply ENNReal.ofReal_le_ofReal
        linarith [Real.add_one_le_exp (8 * D / θ ^ 2 * l)]

/-- Exponential moment of a sum of distinct coordinates of the iid space. -/
theorem lintegral_exp_sum_eq (ν : ProbabilityMeasure ℝ) (l : ℝ) (S : Finset ℕ) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (l * ∑ s ∈ S, g s)) ∂(iidLaw ν) =
      (∫⁻ y, ENNReal.ofReal (Real.exp (l * y)) ∂(ν : Measure ℝ)) ^ S.card := by
  have e : ∀ g : ℕ → ℝ, ENNReal.ofReal (Real.exp (l * ∑ s ∈ S, g s)) =
      ∏ j ∈ S, ENNReal.ofReal (Real.exp (l * g j)) := by
    intro g
    rw [Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg fun j _ => (Real.exp_pos _).le]
  simp_rw [e]
  have hX : ∀ j : ℕ, Measurable fun g : ℕ → ℝ => ENNReal.ofReal (Real.exp (l * g j)) :=
    fun j => (Real.measurable_exp.comp (measurable_const.mul (measurable_pi_apply j))).ennreal_ofReal
  have hind : iIndepFun (fun (j : ℕ) (g : ℕ → ℝ) => ENNReal.ofReal (Real.exp (l * g j)))
      (iidLaw ν) :=
    (iIndepFun_coord ν).comp (fun _ x => ENNReal.ofReal (Real.exp (l * x)))
      fun _ => (Real.measurable_exp.comp (measurable_const.mul measurable_id)).ennreal_ofReal
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hind hX]
  rw [Finset.prod_congr rfl fun _ _ => lintegral_coord ν _
    (f := fun x => ENNReal.ofReal (Real.exp (l * x)))
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).ennreal_ofReal]
  simp

/-! ## The deleted-mark windows -/

/-- The two windows around the inserted coordinate `i`, for a stopping value `t`. -/
def winSet (eps : ℝ) (i t : ℕ) : Set (ℕ → ℝ) :=
  {g | (i : ℕ∞) < gapSegLen eps g} ∩
    {g | i + 2 ≤ t → ((t - (i + 2) : ℕ) : ℕ∞) < gapSegLen eps (fun s => g (i + 1 + s))}

theorem measurable_shiftGap (u : ℕ) : Measurable fun (g : ℕ → ℝ) (s : ℕ) => g (u + s) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

theorem measurableSet_winSet (eps : ℝ) (i t : ℕ) : MeasurableSet (winSet eps i t) := by
  refine (measurableSet_lt_gapSegLen eps i).inter ?_
  by_cases hit : i + 2 ≤ t
  · simp only [hit, true_imp_iff]
    exact measurable_shiftGap (i + 1) (measurableSet_lt_gapSegLen eps (t - (i + 2)))
  · simp only [hit, false_imp_iff, ofPred_true, MeasurableSet.univ]

theorem update_shift_eq (g : ℕ → ℝ) (i : ℕ) (x : ℝ) :
    (fun s => Function.update g i x (i + 1 + s)) = fun s => g (i + 1 + s) := by
  funext s
  exact Function.update_of_ne (by omega) _ _

theorem lt_gapSegLen_update_iff {eps x : ℝ} {g : ℕ → ℝ} {i : ℕ} :
    (i : ℕ∞) < gapSegLen eps (Function.update g i x) ↔ (i : ℕ∞) < gapSegLen eps g :=
  lt_gapSegLen_congr fun _ hj => Function.update_of_ne (Nat.ne_of_lt hj) _ _

/-- **The windows are feasible** on `{T(g') = t} ∩ {i < T(g)}`. -/
theorem mem_winSet_of_eq {eps x : ℝ} {g : ℕ → ℝ} {i t : ℕ}
    (hT : gapSegLen eps (Function.update g i x) = t) (hi : (i : ℕ∞) < gapSegLen eps g) :
    g ∈ winSet eps i t ∧ i < t := by
  have hit : i < t := by
    have h := (lt_gapSegLen_update_iff (x := x)).2 hi
    rw [hT] at h
    exact_mod_cast h
  refine ⟨⟨hi, fun h2 => ?_⟩, hit⟩
  set g' := Function.update g i x with hg'
  have ht1 : ((t - 1 : ℕ) : ℕ∞) < gapSegLen eps g' := by
    rw [hT]; exact_mod_cast (by omega : t - 1 < t)
  rw [gapSegLen, lt_segLen_iff, show t - 1 + 1 = t by omega] at ht1
  have hw := prefixAffineFeasible_window (r := i + 1) (w := t - (i + 2) + 1) ht1 (by omega)
  have hs : ((t - (i + 2) : ℕ) : ℕ∞) < segLen eps (fun j => gapKeys g' (i + 1 + j)) :=
    (lt_segLen_iff _).2 hw
  rw [segLen_gapKeys_shift, hg', update_shift_eq] at hs
  exact hs

/-- On `{T(g') = ⊤}` the right window is feasible forever. -/
theorem gapSegLen_shift_eq_top {eps x : ℝ} {g : ℕ → ℝ} {i : ℕ}
    (hT : gapSegLen eps (Function.update g i x) = ⊤) :
    gapSegLen eps (fun s => g (i + 1 + s)) = ⊤ := by
  rw [gapSegLen, segLen_eq_top_iff] at hT
  have h : segLen eps (fun j => gapKeys (Function.update g i x) (i + 1 + j)) = ⊤ := by
    rw [segLen_eq_top_iff]
    intro w
    exact prefixAffineFeasible_window (hT (i + 1 + w)) le_rfl
  rwa [segLen_gapKeys_shift, update_shift_eq] at h

/-- The stopped sum after the insertion: `S_T(g') = x + ∑_{s < t, s ≠ i} g_s`. -/
theorem stopSum_update_eq {eps x : ℝ} {g : ℕ → ℝ} {i t : ℕ}
    (hT : gapSegLen eps (Function.update g i x) = t) (hit : i < t) :
    stopSum eps (Function.update g i x) = x + ∑ s ∈ (Finset.range t).erase i, g s := by
  rw [stopSum, hT, ENat.toNat_natCast, gapKeys,
    ← Finset.add_sum_erase _ _ (Finset.mem_range.2 hit), Function.update_self]
  congr 1
  exact Finset.sum_congr rfl fun s hs => Function.update_of_ne (Finset.ne_of_mem_erase hs) _ _

theorem card_range_erase {i t : ℕ} (hit : i < t) : ((Finset.range t).erase i).card = t - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_range.2 hit), Finset.card_range]

/-! ## Probability of the windows -/

/-- Shift invariance of the stopping events. -/
theorem measure_lt_gapSegLen_shift (ν : ProbabilityMeasure ℝ) (eps : ℝ) (u m : ℕ) :
    iidLaw ν {g | (m : ℕ∞) < gapSegLen eps (fun s => g (u + s))} =
      iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} := by
  have h := Measure.map_apply (μ := iidLaw ν) (measurable_shiftGap u)
    (measurableSet_lt_gapSegLen eps m)
  rw [map_shift_iidLaw] at h
  exact h.symm

theorem measure_gapSegLen_shift_top (ν : ProbabilityMeasure ℝ) (eps : ℝ) (u : ℕ) :
    iidLaw ν {g | gapSegLen eps (fun s => g (u + s)) = ⊤} =
      iidLaw ν {g | gapSegLen eps g = ⊤} := by
  have hm : MeasurableSet {g : ℕ → ℝ | gapSegLen eps g = ⊤} :=
    (isStoppingRule_gapSegLen eps).measurable (measurableSet_singleton ⊤)
  have h := Measure.map_apply (μ := iidLaw ν) (measurable_shiftGap u) hm
  rw [map_shift_iidLaw] at h
  exact h.symm

/-- **The window bound**: `P(winSet) ≤ (72/71) q^{2(t-2)}` when `P(m < T) ≤ (72/71) q^{4m}`. -/
theorem measure_winSet_le {ν : ProbabilityMeasure ℝ} {eps q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (htail : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
      ENNReal.ofReal (72 / 71 * (q ^ 4) ^ m)) {i t : ℕ} (hit : i < t) :
    iidLaw ν (winSet eps i t) ≤ ENNReal.ofReal (72 / 71 * q ^ (2 * (t - 2))) := by
  have hmono : ∀ {m n : ℕ}, n ≤ m → ENNReal.ofReal (72 / 71 * q ^ m) ≤
      ENNReal.ofReal (72 / 71 * q ^ n) := fun hnm =>
    ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1 hnm) (by norm_num))
  have h1 : iidLaw ν (winSet eps i t) ≤ ENNReal.ofReal (72 / 71 * q ^ (4 * i)) := by
    refine (measure_mono inter_subset_left).trans ((htail i).trans (le_of_eq ?_))
    rw [← pow_mul]
  by_cases h2 : i + 2 ≤ t
  · have hW2 : iidLaw ν (winSet eps i t) ≤
        ENNReal.ofReal (72 / 71 * q ^ (4 * (t - (i + 2)))) := by
      have hsub : winSet eps i t ⊆
          {g | ((t - (i + 2) : ℕ) : ℕ∞) < gapSegLen eps (fun s => g (i + 1 + s))} :=
        fun g hg => hg.2 h2
      refine (measure_mono hsub).trans ?_
      rw [measure_lt_gapSegLen_shift, pow_mul]
      exact htail _
    by_cases hc : t - (i + 2) ≤ i
    · exact h1.trans (hmono (by omega))
    · exact hW2.trans (hmono (by omega))
  · exact h1.trans (hmono (by omega))

/-! ## The Cauchy–Schwarz step in AM-GM form -/

/-- `∫ 1_W e^S ≤ (u/2) P(W) + (1/(2u)) ∫ e^{2S}`. -/
theorem lintegral_indicator_exp_le {P : Measure (ℕ → ℝ)} {W : Set (ℕ → ℝ)} (hW : MeasurableSet W)
    {S : (ℕ → ℝ) → ℝ} (hS : Measurable S) {u : ℝ} (hu : 0 < u) :
    ∫⁻ g, W.indicator (fun g => ENNReal.ofReal (Real.exp (S g))) g ∂P ≤
      ENNReal.ofReal (u / 2) * P W +
        ENNReal.ofReal (1 / (2 * u)) * ∫⁻ g, ENNReal.ofReal (Real.exp (2 * S g)) ∂P := by
  have hpt : ∀ g, W.indicator (fun g => ENNReal.ofReal (Real.exp (S g))) g ≤
      ENNReal.ofReal (u / 2) * W.indicator 1 g +
        ENNReal.ofReal (1 / (2 * u)) * ENNReal.ofReal (Real.exp (2 * S g)) := by
    intro g
    by_cases hg : g ∈ W
    · rw [indicator_of_mem hg, indicator_of_mem hg, Pi.one_apply, mul_one,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have e : Real.exp (2 * S g) = Real.exp (S g) ^ 2 := by rw [sq, ← Real.exp_add, two_mul]
      rw [e]
      have h1 : 0 ≤ (u - Real.exp (S g)) ^ 2 / (2 * u) := by positivity
      have h2 : u / 2 + 1 / (2 * u) * Real.exp (S g) ^ 2 - Real.exp (S g) =
          (u - Real.exp (S g)) ^ 2 / (2 * u) := by field_simp; ring
      linarith
    · rw [indicator_of_notMem hg]; exact zero_le
  have hm1 : Measurable (W.indicator (1 : (ℕ → ℝ) → ℝ≥0∞)) := measurable_one.indicator hW
  have hm2 : Measurable fun g => ENNReal.ofReal (Real.exp (2 * S g)) :=
    (Real.measurable_exp.comp (measurable_const.mul hS)).ennreal_ofReal
  calc ∫⁻ g, W.indicator (fun g => ENNReal.ofReal (Real.exp (S g))) g ∂P
      ≤ ∫⁻ g, (ENNReal.ofReal (u / 2) * W.indicator 1 g +
          ENNReal.ofReal (1 / (2 * u)) * ENNReal.ofReal (Real.exp (2 * S g))) ∂P :=
        lintegral_mono hpt
    _ = _ := by
        rw [lintegral_add_left (hm1.const_mul _), lintegral_const_mul _ hm1,
          lintegral_indicator_one hW, lintegral_const_mul _ hm2]

/-! ## Elementary series bounds -/

theorem one_div_one_sub_exp_neg_le {u : ℝ} (hu : 0 < u) :
    1 / (1 - Real.exp (-u)) ≤ 1 + 1 / u := by
  have h1 : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have h2 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (-u) := Real.exp_pos _
  have h3 : Real.exp (-u) * (1 + u) ≤ 1 := by nlinarith
  have h4 : u / (1 + u) ≤ 1 - Real.exp (-u) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h5 : 0 < u / (1 + u) := by positivity
  calc 1 / (1 - Real.exp (-u)) ≤ 1 / (u / (1 + u)) := one_div_le_one_div_of_le h5 h4
    _ = 1 + 1 / u := by field_simp; ring

theorem pow_sub_two_mul_pow_sub_one_le {q r ρ : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hr : 1 ≤ r)
    (hqr : q * r ≤ ρ) (t : ℕ) : q ^ (t - 2) * r ^ (t - 1) ≤ ρ ^ t / q ^ 2 := by
  have hq2 : q ^ (t - 2) * q ^ 2 ≤ q ^ t := by
    rw [← pow_add]; exact pow_le_pow_of_le_one hq0.le hq1 (by omega)
  have hqt : q ^ (t - 2) ≤ q ^ t / q ^ 2 := by rw [le_div_iff₀ (by positivity)]; exact hq2
  have hrt : r ^ (t - 1) ≤ r ^ t := pow_le_pow_right₀ hr (by omega)
  have hρ : (q * r) ^ t ≤ ρ ^ t := pow_le_pow_left₀ (by positivity) hqr t
  calc q ^ (t - 2) * r ^ (t - 1) ≤ q ^ t / q ^ 2 * r ^ t :=
        mul_le_mul hqt hrt (by positivity) (by positivity)
    _ = (q * r) ^ t / q ^ 2 := by rw [mul_pow]; ring
    _ ≤ ρ ^ t / q ^ 2 := by gcongr

/-! ## One term of the window decomposition -/

/-- The constant of the AM-GM window bound. -/
def winConst : ℝ := (72 / 71 + 1) / 2

theorem winConst_pos : 0 < winConst := by unfold winConst; norm_num

/-- **One term**: `E[1_{winSet} e^{κ(x + Σ)}] ≤ e^{κx} (72/71 + 1)/2 · q^{t-2} r^{t-1}`,
`r = e^{8Dκ/θ²}`. -/
theorem lintegral_winSet_le {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) {eps q κ x : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (htail : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
      ENNReal.ofReal (72 / 71 * (q ^ 4) ^ m))
    (hκ0 : 0 ≤ κ) (hκ : 2 * κ ≤ θ / 4) {i t : ℕ} (hit : i < t) :
    ∫⁻ g, (winSet eps i t).indicator
        (fun g => ENNReal.ofReal (Real.exp (κ * (x + ∑ s ∈ (Finset.range t).erase i, g s)))) g
        ∂(iidLaw ν) ≤
      ENNReal.ofReal (Real.exp (κ * x) *
        (winConst * q ^ (t - 2) * Real.exp (8 * D / θ ^ 2 * κ) ^ (t - 1))) := by
  set r := Real.exp (8 * D / θ ^ 2 * κ) with hr
  set Sg : (ℕ → ℝ) → ℝ := fun g => κ * ∑ s ∈ (Finset.range t).erase i, g s with hSg
  have hSm : Measurable Sg :=
    measurable_const.mul (Finset.measurable_sum _ fun s _ => measurable_pi_apply s)
  have hW := measurableSet_winSet eps i t
  have hsplit : ∀ g, (winSet eps i t).indicator
      (fun g => ENNReal.ofReal (Real.exp (κ * (x + ∑ s ∈ (Finset.range t).erase i, g s)))) g =
      ENNReal.ofReal (Real.exp (κ * x)) *
        (winSet eps i t).indicator (fun g => ENNReal.ofReal (Real.exp (Sg g))) g := by
    intro g
    by_cases hg : g ∈ winSet eps i t
    · rw [indicator_of_mem hg, indicator_of_mem hg, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add, hSg, mul_add]
    · rw [indicator_of_notMem hg, indicator_of_notMem hg, mul_zero]
  simp_rw [hsplit]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  set u : ℝ := r ^ (t - 1) / q ^ (t - 2) with hu
  have hr1 : 1 ≤ r := Real.one_le_exp (by
    have : 0 ≤ D := hν.D_nonneg; positivity)
  have hupos : 0 < u := by positivity
  have hAM := lintegral_indicator_exp_le (P := iidLaw ν) hW hSm hupos
  have hsq : ∫⁻ g, ENNReal.ofReal (Real.exp (2 * Sg g)) ∂(iidLaw ν) ≤
      ENNReal.ofReal ((r ^ 2) ^ (t - 1)) := by
    have e : ∀ g, 2 * Sg g = (2 * κ) * ∑ s ∈ (Finset.range t).erase i, g s := fun g => by
      rw [hSg]; ring
    simp_rw [e]
    rw [lintegral_exp_sum_eq, card_range_erase hit, ENNReal.ofReal_pow (by positivity)]
    gcongr
    refine (hν.lintegral_exp_le_exp hθ (by linarith) hκ).trans (le_of_eq ?_)
    rw [hr, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hP := measure_winSet_le hq0.le hq1 htail hit
  calc ENNReal.ofReal (Real.exp (κ * x)) *
        ∫⁻ g, (winSet eps i t).indicator (fun g => ENNReal.ofReal (Real.exp (Sg g))) g ∂(iidLaw ν)
      ≤ ENNReal.ofReal (Real.exp (κ * x)) *
          (ENNReal.ofReal (u / 2) * ENNReal.ofReal (72 / 71 * q ^ (2 * (t - 2))) +
            ENNReal.ofReal (1 / (2 * u)) * ENNReal.ofReal ((r ^ 2) ^ (t - 1))) := by
        gcongr
        exact hAM.trans (by gcongr)
    _ = ENNReal.ofReal (Real.exp (κ * x) *
          (winConst * q ^ (t - 2) * r ^ (t - 1))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 2
        rw [hu, winConst, ← pow_mul, pow_mul q 2, ← pow_mul]
        have hq' : 0 < q ^ (t - 2) := by positivity
        have hr' : 0 < r ^ (t - 1) := by positivity
        field_simp
        ring

/-! ## The coarse bound -/

/-- On the class, `T(g') < ∞` a.s. for every inserted value. -/
theorem ae_gapSegLen_update_ne_top {ν : ProbabilityMeasure ℝ} {eps : ℝ}
    (hfin : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤) (i : ℕ) (x : ℝ) :
    ∀ᵐ g ∂(iidLaw ν), gapSegLen eps (Function.update g i x) ≠ ⊤ := by
  have h0 : iidLaw ν {g | gapSegLen eps g = ⊤} = 0 := by
    have := ae_iff.1 hfin
    simpa only [ne_eq, not_not] using this
  have h1 : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps (fun s => g (i + 1 + s)) ≠ ⊤ := by
    rw [ae_iff]
    simpa only [ne_eq, not_not, measure_gapSegLen_shift_top] using h0
  filter_upwards [h1] with g hg
  exact fun h => hg (gapSegLen_shift_eq_top h)

/-- **The coarse bound** (PD (29), (34)): for `κ ε² ≤ κ₁` and every `x`,
`∑_i E[e^{κ S_T(g with g_i := x)}; i < T] ≤ K₁ ε⁴ e^{κx}`. -/
theorem coarse_bound (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ κ₁ K₁ e₁ : ℝ, 0 < κ₁ ∧ 0 ≤ K₁ ∧ 1 ≤ e₁ ∧ ∀ eps, e₁ ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∀ κ : ℝ, 0 ≤ κ → κ * eps ^ 2 ≤ κ₁ → ∀ x : ℝ,
        ∑' i : ℕ, ∫⁻ g, {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
          (fun g => ENNReal.ofReal (Real.exp (κ * stopSum eps (Function.update g i x)))) g
          ∂(iidLaw ν) ≤ ENNReal.ofReal (K₁ * eps ^ 4 * Real.exp (κ * x)) := by
  obtain ⟨e₀, he₀1, hfacts⟩ := regLaw_facts hD hθ hvlo hv
  set c := tailRate * regV vlo with hc
  have hcpos : 0 < c := mul_pos tailRate_pos (regV_pos hvlo)
  have hW0 := winConst_pos
  refine ⟨min (θ / 8) (c * θ ^ 2 / (64 * D)), winConst * Real.exp (c / 2) * (1 + 8 / c) ^ 2, e₀,
    lt_min (by positivity) (by positivity), by positivity, he₀1, ?_⟩
  intro eps heps ν hν κ hκ0 hκ x
  obtain ⟨hfin, -, htail, -⟩ := hfacts eps heps ν hν
  have heps1 : 1 ≤ eps := he₀1.trans heps
  have heps0 : 0 < eps := by linarith
  have he2 : 1 ≤ eps ^ 2 := one_le_pow₀ heps1
  have he2p : 0 < eps ^ 2 := by positivity
  set q := Real.exp (-c / (4 * eps ^ 2)) with hq
  set r := Real.exp (8 * D / θ ^ 2 * κ) with hr
  set ρ := Real.exp (-(c / (8 * eps ^ 2))) with hρ
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (by positivity))
  have hq4 : q ^ 4 = tailA vlo eps := by
    rw [hq, ← Real.exp_nat_mul, tailA]
    congr 1
    rw [hc]
    field_simp
    push_cast
    ring
  have htail' : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
      ENNReal.ofReal (72 / 71 * (q ^ 4) ^ m) := by rw [hq4]; exact htail
  have hκ1 : κ * eps ^ 2 ≤ θ / 8 := hκ.trans (min_le_left _ _)
  have hκ2 : κ * eps ^ 2 ≤ c * θ ^ 2 / (64 * D) := hκ.trans (min_le_right _ _)
  have hκθ : 2 * κ ≤ θ / 4 := by nlinarith
  have hr1 : 1 ≤ r := Real.one_le_exp (by positivity)
  have hqr : q * r ≤ ρ := by
    rw [hq, hr, hρ, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : 64 * D * (κ * eps ^ 2) ≤ c * θ ^ 2 := by
      rw [le_div_iff₀ (by positivity)] at hκ2; linarith
    have h2 : 8 * D / θ ^ 2 * κ ≤ c / (8 * eps ^ 2) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h3 : -c / (4 * eps ^ 2) = -(c / (8 * eps ^ 2)) - c / (8 * eps ^ 2) := by
      field_simp; ring
    linarith
  set B : ℕ → ℝ := fun t => Real.exp (κ * x) * (winConst * q ^ (t - 2) * r ^ (t - 1)) with hB
  -- the bound for one inserted coordinate
  have hstep : ∀ i : ℕ, ∫⁻ g, {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
      (fun g => ENNReal.ofReal (Real.exp (κ * stopSum eps (Function.update g i x)))) g
        ∂(iidLaw ν) ≤ ∑' t : ℕ, if i < t then ENNReal.ofReal (B t) else 0 := by
    intro i
    set term : ℕ → (ℕ → ℝ) → ℝ≥0∞ := fun t g => if i < t then (winSet eps i t).indicator
      (fun g => ENNReal.ofReal (Real.exp (κ * (x + ∑ s ∈ (Finset.range t).erase i, g s)))) g
      else 0 with hterm
    have hterm_m : ∀ t, Measurable (term t) := by
      intro t
      by_cases hit : i < t
      · simp only [hterm, if_pos hit]
        exact ((Real.measurable_exp.comp (measurable_const.mul (measurable_const.add
          (Finset.measurable_sum _ fun s _ => measurable_pi_apply s)))).ennreal_ofReal).indicator
          (measurableSet_winSet eps i t)
      · simp only [hterm, if_neg hit]
        exact measurable_const
    have hle : ∀ᵐ g ∂(iidLaw ν), {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
        (fun g => ENNReal.ofReal (Real.exp (κ * stopSum eps (Function.update g i x)))) g ≤
          ∑' t, term t g := by
      filter_upwards [ae_gapSegLen_update_ne_top hfin i x] with g hg
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hg
      by_cases hi : (i : ℕ∞) < gapSegLen eps g
      · obtain ⟨hW, hin⟩ := mem_winSet_of_eq hn.symm hi
        rw [indicator_of_mem (show g ∈ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hi)]
        refine le_trans (le_of_eq ?_) (ENNReal.le_tsum n)
        simp only [hterm, if_pos hin, indicator_of_mem hW, stopSum_update_eq hn.symm hin]
      · rw [indicator_of_notMem (show g ∉ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hi)]
        exact zero_le
    calc _ ≤ ∫⁻ g, ∑' t, term t g ∂(iidLaw ν) := lintegral_mono_ae hle
      _ = ∑' t, ∫⁻ g, term t g ∂(iidLaw ν) := lintegral_tsum fun t => (hterm_m t).aemeasurable
      _ ≤ ∑' t : ℕ, if i < t then ENNReal.ofReal (B t) else 0 := by
          refine ENNReal.tsum_le_tsum fun t => ?_
          by_cases hit : i < t
          · simp only [hterm, if_pos hit]
            exact lintegral_winSet_le hν hθ hq0 hq1 htail' hκ0 hκθ hit
          · simp only [hterm, if_neg hit, lintegral_const, zero_mul, le_refl]
  -- the series
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.2 (by
    have : 0 < c / (8 * eps ^ 2) := by positivity
    linarith)
  have hρn : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hρ0]; exact hρ1
  set C₀ : ℝ := Real.exp (κ * x) * winConst / q ^ 2 with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  have hsum : Summable fun t : ℕ => C₀ * ((t : ℝ) * ρ ^ t) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hρn).summable.mul_left _
  have hBt : ∀ t : ℕ, (t : ℝ≥0∞) * ENNReal.ofReal (B t) ≤
      ENNReal.ofReal (C₀ * ((t : ℝ) * ρ ^ t)) := by
    intro t
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have h := pow_sub_two_mul_pow_sub_one_le hq0 hq1 hr1 hqr t
    have hex : 0 ≤ Real.exp (κ * x) * winConst := by positivity
    calc (t : ℝ) * B t = (t : ℝ) * (Real.exp (κ * x) * winConst * (q ^ (t - 2) * r ^ (t - 1))) := by
          rw [hB]; ring
      _ ≤ (t : ℝ) * (Real.exp (κ * x) * winConst * (ρ ^ t / q ^ 2)) := by gcongr
      _ = C₀ * ((t : ℝ) * ρ ^ t) := by rw [hC₀]; ring
  -- the final numerical bound
  have hfin' : C₀ * (ρ / (1 - ρ) ^ 2) ≤
      winConst * Real.exp (c / 2) * (1 + 8 / c) ^ 2 * eps ^ 4 * Real.exp (κ * x) := by
    have hq2 : 1 / q ^ 2 ≤ Real.exp (c / 2) := by
      rw [hq, ← Real.exp_nat_mul, one_div, ← Real.exp_neg]
      apply Real.exp_le_exp.2
      push_cast
      rw [show -(2 * (-c / (4 * eps ^ 2))) = c / (2 * eps ^ 2) by field_simp; ring]
      apply div_le_div_of_nonneg_left hcpos.le (by norm_num)
      nlinarith
    have hw : 1 / (1 - ρ) ≤ (1 + 8 / c) * eps ^ 2 := by
      have h := one_div_one_sub_exp_neg_le (u := c / (8 * eps ^ 2)) (by positivity)
      rw [← hρ] at h
      refine h.trans ?_
      rw [one_div_div, show 8 * eps ^ 2 / c = 8 / c * eps ^ 2 by ring]
      have : 0 ≤ 8 / c := by positivity
      nlinarith
    have h1ρ : 0 < 1 - ρ := by linarith
    have hw0 : 0 ≤ 1 / (1 - ρ) := by positivity
    have hρw : ρ / (1 - ρ) ^ 2 ≤ ((1 + 8 / c) * eps ^ 2) ^ 2 := by
      calc ρ / (1 - ρ) ^ 2 ≤ 1 / (1 - ρ) ^ 2 := by gcongr
        _ = (1 / (1 - ρ)) ^ 2 := by rw [one_div_pow]
        _ ≤ ((1 + 8 / c) * eps ^ 2) ^ 2 := by gcongr
    calc C₀ * (ρ / (1 - ρ) ^ 2) = Real.exp (κ * x) * winConst * (1 / q ^ 2) *
          (ρ / (1 - ρ) ^ 2) := by rw [hC₀]; ring
      _ ≤ Real.exp (κ * x) * winConst * Real.exp (c / 2) * ((1 + 8 / c) * eps ^ 2) ^ 2 := by
          gcongr
      _ = winConst * Real.exp (c / 2) * (1 + 8 / c) ^ 2 * eps ^ 4 * Real.exp (κ * x) := by ring
  calc ∑' i : ℕ, ∫⁻ g, {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
        (fun g => ENNReal.ofReal (Real.exp (κ * stopSum eps (Function.update g i x)))) g
          ∂(iidLaw ν)
      ≤ ∑' i : ℕ, ∑' t : ℕ, if i < t then ENNReal.ofReal (B t) else 0 :=
        ENNReal.tsum_le_tsum hstep
    _ = ∑' t : ℕ, ∑' i : ℕ, if i < t then ENNReal.ofReal (B t) else 0 := ENNReal.tsum_comm
    _ = ∑' t : ℕ, (t : ℝ≥0∞) * ENNReal.ofReal (B t) := by
        congr 1
        funext t
        rw [tsum_eq_sum (s := Finset.range t) (fun i hi => if_neg (by
          rw [Finset.mem_range] at hi; exact hi))]
        rw [Finset.sum_congr rfl fun i hi => if_pos (Finset.mem_range.1 hi), Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑' t : ℕ, ENNReal.ofReal (C₀ * ((t : ℝ) * ρ ^ t)) := ENNReal.tsum_le_tsum hBt
    _ = ENNReal.ofReal (∑' t : ℕ, C₀ * ((t : ℝ) * ρ ^ t)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun t => by positivity) hsum).symm
    _ = ENNReal.ofReal (C₀ * (ρ / (1 - ρ) ^ 2)) := by
        rw [tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one hρn]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfin'

/-! ## The insertion kernel of a test of the stopped sum -/

/-- The integrand of `insKernel` is the inserted functional `1_{i<T} Φ`. -/
theorem indicator_update_eq (eps : ℝ) (Φ : (ℕ → ℝ) → ℝ) (i : ℕ) (x : ℝ) (g : ℕ → ℝ) :
    {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator (fun g => Φ (Function.update g i x)) g =
      ({g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator Φ) (Function.update g i x) := by
  by_cases hgi : (i : ℕ∞) < gapSegLen eps g
  · rw [indicator_of_mem (show g ∈ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hgi),
      indicator_of_mem (show Function.update g i x ∈ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}
        from lt_gapSegLen_update_iff.2 hgi)]
  · rw [indicator_of_notMem (show g ∉ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hgi),
      indicator_of_notMem (show Function.update g i x ∉ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}
        from fun h => hgi (lt_gapSegLen_update_iff.1 h))]

theorem insKernel_eq_tsum_update (eps : ℝ) (ν : ProbabilityMeasure ℝ) (Φ : (ℕ → ℝ) → ℝ)
    (x : ℝ) :
    insKernel eps ν Φ x = ∑' i : ℕ, ∫ g, ({g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator Φ)
      (Function.update g i x) ∂(iidLaw ν) := by
  rw [insKernel]
  exact tsum_congr fun i => integral_congr_ae (Eventually.of_forall fun g =>
    indicator_update_eq eps Φ i x g)

/-- **Measurability of the insertion kernel.** -/
theorem measurable_insKernel (eps : ℝ) (ν : ProbabilityMeasure ℝ) {Φ : (ℕ → ℝ) → ℝ}
    (hΦ : Measurable Φ) : Measurable (insKernel eps ν Φ) := by
  have h : insKernel eps ν Φ = fun x => ∑' i : ℕ, ∫ g,
      ({g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator Φ) (Function.update g i x)
        ∂(iidLaw ν) := funext (insKernel_eq_tsum_update eps ν Φ)
  rw [h]
  exact Measurable.tsum fun i => measurable_integral_update ν i
    (hΦ.indicator (measurableSet_lt_gapSegLen eps i))

/-- **Linearity** of the insertion kernel in the functional. -/
theorem insKernel_const_mul (eps : ℝ) (ν : ProbabilityMeasure ℝ) (c : ℝ) (Φ : (ℕ → ℝ) → ℝ)
    (x : ℝ) : insKernel eps ν (fun g => c * Φ g) x = c * insKernel eps ν Φ x := by
  rw [insKernel, insKernel, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  dsimp only
  by_cases hgi : (i : ℕ∞) < gapSegLen eps g
  · rw [indicator_of_mem (show g ∈ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hgi),
      indicator_of_mem (show g ∈ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hgi)]
  · rw [indicator_of_notMem (show g ∉ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hgi),
      indicator_of_notMem (show g ∉ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hgi), mul_zero]

/-- The gaps of a regular law are positive: all coordinates are a.s. nonnegative. -/
theorem RegLaw.ae_coord_nonneg {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) :
    ∀ᵐ g ∂(iidLaw ν), ∀ s, 0 ≤ g s := by
  rw [ae_all_iff]
  intro s
  have hmap : (iidLaw ν).map (fun g => g s) = (ν : Measure ℝ) :=
    Measure.infinitePi_map_eval _ s
  refine ae_of_ae_map (measurable_pi_apply s).aemeasurable ?_
  rw [hmap]
  filter_upwards [hν.ae_pos] with y hy using hy.le

theorem stopSum_nonneg {eps : ℝ} {g : ℕ → ℝ} (hg : ∀ s, 0 ≤ g s) : 0 ≤ stopSum eps g := by
  show 0 ≤ ∑ s ∈ Finset.range (gapSegLen eps g).toNat, g s
  exact Finset.sum_nonneg fun s _ => hg s

theorem update_nonneg {g : ℕ → ℝ} (hg : ∀ s, 0 ≤ g s) {x : ℝ} (hx : 0 ≤ x) (i : ℕ) :
    ∀ s, 0 ≤ Function.update g i x s := by
  intro s
  by_cases h : s = i
  · subst h; rw [Function.update_self]; exact hx
  · rw [Function.update_of_ne h]; exact hg s

/-- **The pointwise kernel bound**: the series defining `I_F(x)` converges absolutely and
`|I_F(x)| ≤ B` whenever the exponential series is at most `B`. -/
theorem insKernel_bound {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) {eps κ B : ℝ}
    {F : ℝ → ℝ} (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (κ * y))
    {x : ℝ} (hx : 0 ≤ x) (hB0 : 0 ≤ B)
    (hco : ∑' i : ℕ, ∫⁻ g, {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
          (fun g => ENNReal.ofReal (Real.exp (κ * stopSum eps (Function.update g i x)))) g
          ∂(iidLaw ν) ≤ ENNReal.ofReal B) :
    (∑' i : ℕ, ∫⁻ g, ‖{g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
          (fun g => F (stopSum eps (Function.update g i x))) g‖ₑ ∂(iidLaw ν) ≤
        ENNReal.ofReal B) ∧
      |insKernel eps ν (fun g => F (stopSum eps g)) x| ≤ B := by
  set a : ℕ → ℝ≥0∞ := fun i => ∫⁻ g, ‖{g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
    (fun g => F (stopSum eps (Function.update g i x))) g‖ₑ ∂(iidLaw ν) with ha
  have hle : ∀ i, a i ≤ ∫⁻ g, {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
      (fun g => ENNReal.ofReal (Real.exp (κ * stopSum eps (Function.update g i x)))) g
      ∂(iidLaw ν) := by
    intro i
    refine lintegral_mono_ae ?_
    filter_upwards [hν.ae_coord_nonneg] with g hg
    by_cases hgi : (i : ℕ∞) < gapSegLen eps g
    · rw [indicator_of_mem (show g ∈ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hgi),
        indicator_of_mem (show g ∈ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hgi),
        Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (hFb _ (stopSum_nonneg (update_nonneg hg hx i)))
    · rw [indicator_of_notMem (show g ∉ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hgi),
        enorm_zero]
      exact zero_le
  have hsumle : ∑' i, a i ≤ ENNReal.ofReal B := (ENNReal.tsum_le_tsum hle).trans hco
  refine ⟨hsumle, ?_⟩
  have hfin : ∑' i, a i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsumle
  have hai : ∀ i, a i ≠ ⊤ := fun i => ne_top_of_le_ne_top hfin (ENNReal.le_tsum i)
  set b : ℕ → ℝ := fun i => ∫ g, {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
    (fun g => F (stopSum eps (Function.update g i x))) g ∂(iidLaw ν) with hb
  have hnb : ∀ i, ‖b i‖ ≤ (a i).toReal := by
    intro i
    refine (norm_integral_le_lintegral_norm _).trans ?_
    simp only [ofReal_norm]
    exact le_rfl
  have hsa : Summable fun i => (a i).toReal := ENNReal.summable_toReal hfin
  have hsb : Summable fun i => ‖b i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hnb hsa
  calc |insKernel eps ν (fun g => F (stopSum eps g)) x| = ‖∑' i, b i‖ := by
        rw [insKernel, Real.norm_eq_abs]
    _ ≤ ∑' i, ‖b i‖ := norm_tsum_le_tsum_norm hsb
    _ ≤ ∑' i, (a i).toReal := hsb.tsum_le_tsum hnb hsa
    _ = (∑' i, a i).toReal := (ENNReal.tsum_toReal_eq hai).symm
    _ ≤ B := ENNReal.toReal_le_of_le_ofReal hB0 hsumle

end

end PGM
