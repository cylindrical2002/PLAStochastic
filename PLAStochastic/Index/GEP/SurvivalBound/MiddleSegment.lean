import PLAStochastic.Index.GEP.SurvivalBound.WordFunctional
import PLAStochastic.Index.GEP.SurvivalBound.Certificate.ThreeBlocks

/-!
# WP4 `SurvivalBound`: the middle segment of a good-slope certificate

Source: `task-survival.md` (P2, items 1–2), `progress-surv.md` (中段引理).

Coordinates `0, …, L-1` carry the middle segment of a certificate `(i, j)`, `L = j - i`; the chord
slope is `a = c / p_L` with `c = L - 2ε`, and the middle walk `y_l = l - a p_l` must stay in
`J = [0, 2ε]`.  For a bounded measurable `Ψ` supported in `[1/2, 2]`,

`‖surv_wint L (Ψ(a) ∏_{l ≤ L} 1_J(y_l))‖ ≤ ∑_{m < L} ‖1-z‖ ‖z‖^{L-1-m} (3c/2) D RB(m) + ‖z‖^L`

(`surv_mid_bound`), where `RB m` bounds the killed rows `kRow J ν σ z 1 a m` on tests of norm
`≤ D` (`‖kRow … φ 0‖ ≤ D RB m`).

**Proof.**  A word is all `σ` (contributing `‖z‖^L`) or has a last `ν` letter `m`
(`surv_sum_powerset_last`).  In the `m`-group the coordinate `m` is translated to `t = p_L`
(`surv_integral_wordLaw_shift`); for fixed `t` the slope `a = c/t` is fixed and the integrand
splits (`surv_shift_eq_split`) into the forward walk on the coordinates `< m` (a `kWordInt`, whose
word sum is `kRow J ν σ z 1 a m φ 0`), the reversed all-`σ` second half on the coordinates `> m`
(`surv_bwd`) and the density `f` of the inserted coordinate expressed through the forward end
(`surv_testF`).  Fubini over the disjoint coordinate sets (`surv_integral_diag'`) and coordinate
agreement (`surv_integral_wordLaw_congr`) identify the word sum as a row; the `t`-integral is over
`{c/t ∈ [1/2, 2]} = [c/2, 2c]`, of length `3c/2`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

/-! ## Notation -/

/-- The killing interval `J = [0, 2ε]`. -/
def surv_J (eps : ℝ) : Set ℝ := Icc 0 (2 * eps)

theorem surv_measurableSet_J (eps : ℝ) : MeasurableSet (surv_J eps) := measurableSet_Icc

theorem surv_norm_indicator_one_le (J : Set ℝ) (y : ℝ) :
    ‖J.indicator (fun _ => (1 : ℂ)) y‖ ≤ 1 := by
  by_cases h : y ∈ J
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h]

theorem surv_norm_prod_indicator_le {ι : Type*} (s : Finset ι) (J : Set ℝ) (x : ι → ℝ) :
    ‖∏ l ∈ s, J.indicator (fun _ => (1 : ℂ)) (x l)‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one (fun l _ => norm_nonneg _) fun l _ => surv_norm_indicator_one_le J (x l)

/-- The walk reads only the first `l` coordinates. -/
theorem surv_kWalk_congr {y₀ β a : ℝ} {g g' : ℕ → ℝ} {l : ℕ} (h : ∀ s < l, g s = g' s) :
    kWalk y₀ β a g l = kWalk y₀ β a g' l := by
  simp only [kWalk, gapKeys]
  rw [Finset.sum_congr rfl fun s hs => h s (Finset.mem_range.1 hs)]

theorem surv_measurable_kWalk (y₀ β a : ℝ) (l : ℕ) :
    Measurable fun g : ℕ → ℝ => kWalk y₀ β a g l :=
  (measurable_kWalk_prod β a l).comp (measurable_const.prodMk measurable_id)

/-- The word integrand reads only the first `n` coordinates. -/
theorem surv_kWordInt_congr {J : Set ℝ} {β a : ℝ} {n : ℕ} {φ : ℝ → ℂ} {y₀ : ℝ} {g g' : ℕ → ℝ}
    (h : ∀ s < n, g s = g' s) : kWordInt J β a n φ y₀ g = kWordInt J β a n φ y₀ g' := by
  unfold kWordInt
  rw [surv_kWalk_congr h]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  rw [surv_kWalk_congr fun s hs => h s (by omega)]

/-- The slope of the middle chord, `c / p_L`. -/
def surv_slope (c : ℝ) (L : ℕ) (g : ℕ → ℝ) : ℝ := c / gapKeys g L

theorem surv_measurable_slope (c : ℝ) (L : ℕ) : Measurable (surv_slope c L) :=
  measurable_const.div (rawAsm_measurable_gapKeys L)

/-- The middle integrand `Ψ(a) ∏_{l ≤ L} 1_J(y_l)`, `a = c / p_L`, `y_l = l - a p_l`. -/
def surv_midInt (eps : ℝ) (Ψ : ℝ → ℂ) (c : ℝ) (L : ℕ) (g : ℕ → ℝ) : ℂ :=
  Ψ (surv_slope c L g) * ∏ l ∈ Finset.range (L + 1),
    (surv_J eps).indicator (fun _ => (1 : ℂ)) (kWalk 0 1 (surv_slope c L g) g l)

theorem surv_measurable_midInt (eps : ℝ) {Ψ : ℝ → ℂ} (hΨ : Measurable Ψ) (c : ℝ) (L : ℕ) :
    Measurable (surv_midInt eps Ψ c L) := by
  unfold surv_midInt
  refine (hΨ.comp (surv_measurable_slope c L)).mul (Finset.measurable_prod _ fun l _ => ?_)
  refine (measurable_const.indicator (surv_measurableSet_J eps)).comp ?_
  unfold kWalk
  exact measurable_const.sub ((surv_measurable_slope c L).mul (rawAsm_measurable_gapKeys l))

theorem surv_norm_midInt_le (eps : ℝ) {Ψ : ℝ → ℂ} (hΨ1 : ∀ a, ‖Ψ a‖ ≤ 1) (c : ℝ) (L : ℕ)
    (g : ℕ → ℝ) : ‖surv_midInt eps Ψ c L g‖ ≤ 1 := by
  unfold surv_midInt
  rw [norm_mul]
  exact mul_le_one₀ (hΨ1 _) (norm_nonneg _) (surv_norm_prod_indicator_le _ _ _)

/-! ## The tail sum, the reversed second half and the split integrand -/

/-- The sum of the coordinates strictly between `m` and `L`. -/
def surv_tailSum (L m : ℕ) (g : ℕ → ℝ) : ℝ := ∑ l ∈ Finset.Ico (m + 1) L, g l

theorem surv_measurable_tailSum (L m : ℕ) : Measurable (surv_tailSum L m) :=
  Finset.measurable_sum _ fun l _ => measurable_pi_apply l

theorem surv_tailSum_congr {L m : ℕ} {g g' : ℕ → ℝ} (h : ∀ l, m < l → l < L → g l = g' l) :
    surv_tailSum L m g = surv_tailSum L m g' :=
  Finset.sum_congr rfl fun l hl => by
    have := Finset.mem_Ico.1 hl
    exact h l (by omega) this.2

/-- The keys after inserting `x` at the coordinate `m < L`. -/
theorem surv_gapKeys_update {L m : ℕ} (hm : m < L) (g : ℕ → ℝ) (x : ℝ) :
    gapKeys (Function.update g m x) L = gapKeys g m + surv_tailSum L m g + x := by
  unfold gapKeys surv_tailSum
  rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le m) hm.le, Finset.sum_eq_sum_Ico_succ_bot hm,
    Function.update_self]
  have h1 : ∑ s ∈ Finset.Ico 0 m, Function.update g m x s = ∑ s ∈ Finset.Ico 0 m, g s :=
    Finset.sum_congr rfl fun s hs =>
      Function.update_of_ne (by have := (Finset.mem_Ico.1 hs).2; omega) _ _
  have h2 : ∑ s ∈ Finset.Ico (m + 1) L, Function.update g m x s =
      ∑ s ∈ Finset.Ico (m + 1) L, g s :=
    Finset.sum_congr rfl fun s hs =>
      Function.update_of_ne (by have := (Finset.mem_Ico.1 hs).1; omega) _ _
  rw [h1, h2]
  ring

/-- **The second half of the middle walk, reversed.**  If `p_L = t` after the insertion and
`a t = L - 2ε`, then for `j < L - m` the point `y_{L-j}` of the forward walk is the point `j` of
the reversed walk from `2ε` with steps `a x - 1` over the coordinates `L-1, L-2, …`. -/
theorem surv_kWalk_second_half {eps a t : ℝ} {L m : ℕ} (hm : m < L) (g : ℕ → ℝ) (x : ℝ)
    (ht : gapKeys (Function.update g m x) L = t) (hat : a * t = L - 2 * eps) {j : ℕ}
    (hj : j < L - m) :
    kWalk 0 1 a (Function.update g m x) (L - j) =
      kWalk (2 * eps) (-1) (-a) (fun s => g (L - 1 - s)) j := by
  have hjL : j ≤ L := by omega
  have hrev : gapKeys (fun s => g (L - 1 - s)) j =
      gapKeys (fun s => Function.update g m x (L - 1 - s)) j := by
    unfold gapKeys
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := Finset.mem_range.1 hs
    show g (L - 1 - s) = Function.update g m x (L - 1 - s)
    rw [Function.update_of_ne (show L - 1 - s ≠ m by omega)]
  simp only [kWalk]
  rw [hrev, cert_gapKeys_rev (Function.update g m x) j hjL, ht, Nat.cast_sub hjL]
  linear_combination (-1 : ℝ) * hat

/-- The reversed all-`σ` second half of the middle walk, over the coordinates `L-1, …, m+1`. -/
def surv_bwd (eps a : ℝ) (L m : ℕ) (g : ℕ → ℝ) : ℂ :=
  ∏ l ∈ Finset.range (L - m), (surv_J eps).indicator (fun _ => (1 : ℂ))
    (kWalk (2 * eps) (-1) (-a) (fun s => g (L - 1 - s)) l)

theorem surv_measurable_bwd (eps a : ℝ) (L m : ℕ) : Measurable (surv_bwd eps a L m) := by
  unfold surv_bwd
  refine Finset.measurable_prod _ fun l _ => ?_
  refine (measurable_const.indicator (surv_measurableSet_J eps)).comp ?_
  exact (surv_measurable_kWalk _ _ _ l).comp
    (measurable_pi_lambda _ fun s => measurable_pi_apply (L - 1 - s))

theorem surv_norm_bwd_le (eps a : ℝ) (L m : ℕ) (g : ℕ → ℝ) : ‖surv_bwd eps a L m g‖ ≤ 1 :=
  surv_norm_prod_indicator_le _ _ _

theorem surv_bwd_congr {eps a : ℝ} {L m : ℕ} {g g' : ℕ → ℝ}
    (h : ∀ l, m < l → l < L → g l = g' l) : surv_bwd eps a L m g = surv_bwd eps a L m g' := by
  unfold surv_bwd
  refine Finset.prod_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  congr 1
  refine surv_kWalk_congr fun s hs => ?_
  exact h _ (by omega) (by omega)

/-- **The middle walk splits at the inserted coordinate**: the points `l ≤ m` form the forward
walk on the old coordinates, and the points `l > m` the reversed second half. -/
theorem surv_mid_prod_split {eps a t : ℝ} {L m : ℕ} (hm : m < L) (g : ℕ → ℝ) (x : ℝ)
    (ht : gapKeys (Function.update g m x) L = t) (hat : a * t = L - 2 * eps) :
    ∏ l ∈ Finset.range (L + 1), (surv_J eps).indicator (fun _ => (1 : ℂ))
        (kWalk 0 1 a (Function.update g m x) l) =
      (∏ l ∈ Finset.range (m + 1),
        (surv_J eps).indicator (fun _ => (1 : ℂ)) (kWalk 0 1 a g l)) * surv_bwd eps a L m g := by
  rw [show L + 1 = (m + 1) + (L - m) by omega, Finset.prod_range_add]
  congr 1
  · refine Finset.prod_congr rfl fun l hl => ?_
    have hl' := Finset.mem_range.1 hl
    congr 1
    refine surv_kWalk_congr fun s hs => ?_
    exact Function.update_of_ne (by omega) _ _
  · unfold surv_bwd
    conv_lhs => rw [← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun l hl => ?_
    have hl' := Finset.mem_range.1 hl
    congr 1
    rw [show m + 1 + (L - m - 1 - l) = L - l by omega]
    exact surv_kWalk_second_half hm g x ht hat (by omega)

/-- The density of the inserted coordinate as a test on the forward end `y = y_m`:
`f(t - (m - y)/a - Σ₂)`. -/
def surv_testF (f : ℝ → ℝ) (t a : ℝ) (L m : ℕ) (g₂ : ℕ → ℝ) (y : ℝ) : ℂ :=
  (f (t - (m - y) / a - surv_tailSum L m g₂) : ℂ)

theorem surv_measurable_testF {f : ℝ → ℝ} (hf : Measurable f) (t a : ℝ) (L m : ℕ) :
    Measurable (fun p : (ℕ → ℝ) × ℝ => surv_testF f t a L m p.1 p.2) := by
  unfold surv_testF
  refine Complex.measurable_ofReal.comp (hf.comp ?_)
  exact (measurable_const.sub ((measurable_const.sub measurable_snd).div_const a)).sub
    ((surv_measurable_tailSum L m).comp measurable_fst)

theorem surv_norm_testF_le {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hfD : ∀ x, f x ≤ D)
    (t a : ℝ) (L m : ℕ) (g₂ : ℕ → ℝ) (y : ℝ) : ‖surv_testF f t a L m g₂ y‖ ≤ D := by
  unfold surv_testF
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
  exact hfD _

/-- The split integrand `F_t(g₁, g₂) = Ψ(a) bwd(g₂) kWordInt(φ_{t,g₂})(g₁)`, `a = c/t`. -/
def surv_splitInt (eps : ℝ) (Ψ : ℝ → ℂ) (f : ℝ → ℝ) (c : ℝ) (L m : ℕ) (t : ℝ)
    (g₁ g₂ : ℕ → ℝ) : ℂ :=
  Ψ (c / t) * surv_bwd eps (c / t) L m g₂ *
    kWordInt (surv_J eps) 1 (c / t) m (surv_testF f t (c / t) L m g₂) 0 g₁

theorem surv_measurable_splitInt (eps : ℝ) (Ψ : ℝ → ℂ) {f : ℝ → ℝ} (hf : Measurable f) (c : ℝ)
    (L m : ℕ) (t : ℝ) : Measurable (Function.uncurry (surv_splitInt eps Ψ f c L m t)) := by
  show Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => Ψ (c / t) * surv_bwd eps (c / t) L m p.2 *
    kWordInt (surv_J eps) 1 (c / t) m (surv_testF f t (c / t) L m p.2) 0 p.1
  refine (measurable_const.mul ((surv_measurable_bwd eps (c / t) L m).comp measurable_snd)).mul ?_
  unfold kWordInt
  refine (Finset.measurable_prod _ fun l _ => (measurable_const.indicator
    (surv_measurableSet_J eps)).comp ((surv_measurable_kWalk 0 1 (c / t) l).comp
      measurable_fst)).mul ?_
  exact (surv_measurable_testF hf t (c / t) L m).comp
    (measurable_snd.prodMk ((surv_measurable_kWalk 0 1 (c / t) m).comp measurable_fst))

theorem surv_norm_splitInt_le (eps : ℝ) {Ψ : ℝ → ℂ} (hΨ1 : ∀ a, ‖Ψ a‖ ≤ 1) {f : ℝ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hfD : ∀ x, f x ≤ D) (c : ℝ) (L m : ℕ) (t : ℝ)
    (g₁ g₂ : ℕ → ℝ) : ‖surv_splitInt eps Ψ f c L m t g₁ g₂‖ ≤ D := by
  unfold surv_splitInt
  have h := mul_le_mul (mul_le_mul (hΨ1 (c / t)) (surv_norm_bwd_le eps (c / t) L m g₂)
    (norm_nonneg _) zero_le_one) (norm_kWordInt_le (J := surv_J eps) 1 (c / t) m
      (surv_norm_testF_le hf0 hfD t (c / t) L m g₂) 0 g₁) (norm_nonneg _) (by norm_num)
  simpa using h

theorem surv_splitInt_congr_left (eps : ℝ) (Ψ : ℝ → ℂ) (f : ℝ → ℝ) (c : ℝ) (L m : ℕ) (t : ℝ)
    {g₁ g₁' g₂ : ℕ → ℝ} (h : ∀ l < m, g₁ l = g₁' l) :
    surv_splitInt eps Ψ f c L m t g₁ g₂ = surv_splitInt eps Ψ f c L m t g₁' g₂ := by
  unfold surv_splitInt
  rw [surv_kWordInt_congr h]

theorem surv_splitInt_congr_right (eps : ℝ) (Ψ : ℝ → ℂ) (f : ℝ → ℝ) (c : ℝ) (L m : ℕ) (t : ℝ)
    {g₁ g₂ g₂' : ℕ → ℝ} (h : ∀ l, m < l → l < L → g₂ l = g₂' l) :
    surv_splitInt eps Ψ f c L m t g₁ g₂ = surv_splitInt eps Ψ f c L m t g₁ g₂' := by
  unfold surv_splitInt kWordInt surv_testF
  rw [surv_bwd_congr h, surv_tailSum_congr h]

/-- **The translated integrand splits.**  With `R g = p_m + Σ₂(g)`, inserting `t - R g` at the
coordinate `m` makes `p_L = t`, and
`f(t - R g) · midInt(update g m (t - R g)) = F_t(g, g)`. -/
theorem surv_shift_eq_split (eps : ℝ) {Ψ : ℝ → ℂ} (hΨ0 : ∀ a, a ∉ Icc (1 / 2 : ℝ) 2 → Ψ a = 0)
    (f : ℝ → ℝ) {c : ℝ} {L m : ℕ} (hm : m < L) (hc : c = L - 2 * eps) (t : ℝ) (g : ℕ → ℝ) :
    (f (t - (gapKeys g m + surv_tailSum L m g)) : ℂ) *
        surv_midInt eps Ψ c L (Function.update g m (t - (gapKeys g m + surv_tailSum L m g))) =
      surv_splitInt eps Ψ f c L m t g g := by
  set x := t - (gapKeys g m + surv_tailSum L m g) with hx
  have ht : gapKeys (Function.update g m x) L = t := by
    rw [surv_gapKeys_update hm, hx]; ring
  have hslope : surv_slope c L (Function.update g m x) = c / t := by
    rw [surv_slope, ht]
  unfold surv_midInt surv_splitInt
  rw [hslope]
  by_cases ha : c / t ∈ Icc (1 / 2 : ℝ) 2
  · have ht0 : t ≠ 0 := by
      intro ht0
      rw [ht0, div_zero] at ha
      norm_num at ha
    have hat : c / t * t = L - 2 * eps := by rw [div_mul_cancel₀ _ ht0, hc]
    have ha0 : c / t ≠ 0 := by
      intro h
      rw [h] at ha
      norm_num at ha
    rw [surv_mid_prod_split hm g x ht hat]
    unfold kWordInt surv_testF
    have hy : t - (m - kWalk 0 1 (c / t) g m) / (c / t) - surv_tailSum L m g = x := by
      rw [show (m : ℝ) - kWalk 0 1 (c / t) g m = c / t * gapKeys g m by simp only [kWalk]; ring,
        mul_div_cancel_left₀ _ ha0, hx]
      ring
    rw [hy]
    ring
  · rw [hΨ0 _ ha]
    simp

/-- Integrability of the translated integrand on the product `wordLaw × volume`. -/
theorem surv_integrable_shift_prod (ν σ : ProbabilityMeasure ℝ) (S : Finset ℕ) (m : ℕ)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hνf : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {R : (ℕ → ℝ) → ℝ} (hR : Measurable R) {F : (ℕ → ℝ) → ℂ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ g, ‖F g‖ ≤ M) :
    Integrable (fun p : (ℕ → ℝ) × ℝ =>
      (f (p.2 - R p.1) : ℂ) * F (Function.update p.1 m (p.2 - R p.1)))
      ((wordLaw ν σ S).prod volume) := by
  obtain ⟨hfi, -⟩ := surv_integrable_density hf hf0 hνf
  have hU : Measurable fun p : (ℕ → ℝ) × ℝ => Function.update p.1 m (p.2 - R p.1) :=
    (measurable_update_pair m).comp ((measurable_snd.sub (hR.comp measurable_fst)).prodMk
      measurable_fst)
  have hfm : Measurable fun p : (ℕ → ℝ) × ℝ => f (p.2 - R p.1) :=
    hf.comp (measurable_snd.sub (hR.comp measurable_fst))
  have hdom : Integrable (fun p : (ℕ → ℝ) × ℝ => M * f (p.2 - R p.1))
      ((wordLaw ν σ S).prod volume) := by
    refine Integrable.const_mul ?_ M
    refine (integrable_prod_iff hfm.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun g => hfi.comp_sub_right (R g)
    · have e : ∀ g : ℕ → ℝ, ∫ t, ‖f (t - R g)‖ = ∫ t, f t := by
        intro g
        simp only [Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
        exact integral_sub_right_eq_self (fun t => f t) (R g)
      simp only [e]
      exact integrable_const _
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact ((Complex.measurable_ofReal.comp hfm).mul (hF.comp hU)).aestronglyMeasurable
  · show ‖(f (p.2 - R p.1) : ℂ) * F (Function.update p.1 m (p.2 - R p.1))‖ ≤
      M * f (p.2 - R p.1)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _) (hf0 _)

/-! ## The `m`-group at fixed `t` -/

/-- The killed row as the word functional of `kWordInt`. -/
theorem surv_kRow_eq_wint {J : Set ℝ} (hJ : MeasurableSet J) (ν σ : ProbabilityMeasure ℝ)
    (z : ℂ) (β a : ℝ) {φ : ℝ → ℂ} (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M) (n : ℕ)
    (y₀ : ℝ) : kRow J ν σ z β a n φ y₀ = surv_wint ν σ z n (kWordInt J β a n φ y₀) :=
  kRow_eq_surv_wint hJ ν σ z β a hφ hM n y₀

/-- **Fubini for one word of the `m`-group**: for `F g h` reading `g` on `{l < m}` and `h` on
`{m < l < L}`, under `wordLaw (S ∪ [m+1, L))` with `S ⊆ {0, …, m-1}`,
`∫ F g g = ∫_h ∫_g F g h d(wordLaw S) d(wordLaw [m+1, L))`. -/
theorem surv_mid_word_fubini (ν σ : ProbabilityMeasure ℝ) {L m : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range m) {F : (ℕ → ℝ) → (ℕ → ℝ) → ℂ} (hFm : Measurable (Function.uncurry F))
    {M : ℝ} (hFb : ∀ g h, ‖F g h‖ ≤ M) (hA : ∀ g g' h, (∀ l < m, g l = g' l) → F g h = F g' h)
    (hB : ∀ g h h', (∀ l, m < l → l < L → h l = h' l) → F g h = F g h') :
    ∫ g, F g g ∂(wordLaw ν σ (S ∪ Finset.Ico (m + 1) L)) =
      ∫ h, ∫ g, F g h ∂(wordLaw ν σ S) ∂(wordLaw ν σ (Finset.Ico (m + 1) L)) := by
  have hdisj : Disjoint {l : ℕ | l < m} {l : ℕ | m < l ∧ l < L} := by
    rw [Set.disjoint_left]
    intro l h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    omega
  have hA' : ∀ g g' h, (∀ l ∈ {l : ℕ | l < m}, g l = g' l) → F g h = F g' h :=
    fun g g' h hgg => hA g g' h fun l hl => hgg l hl
  have hB' : ∀ g h h', (∀ l ∈ {l : ℕ | m < l ∧ l < L}, h l = h' l) → F g h = F g h' :=
    fun g h h' hhh => hB g h h' fun l h1 h2 => hhh l ⟨h1, h2⟩
  have hFm' : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => F p.2 p.1 := by
    have := hFm.comp measurable_swap
    exact this
  rw [surv_integral_diag' ν σ _ hdisj hFm hFb hA' hB']
  have hin : ∀ h, ∫ g, F g h ∂(wordLaw ν σ (S ∪ Finset.Ico (m + 1) L)) =
      ∫ g, F g h ∂(wordLaw ν σ S) := by
    intro h
    refine surv_integral_wordLaw_congr ν σ (A := {l : ℕ | l < m}) ?_ ?_ ?_
    · intro l hl
      simp only [Set.mem_ofPred_eq] at hl
      simp only [Finset.mem_union, Finset.mem_Ico]
      constructor
      · rintro (h | h)
        · exact h
        · omega
      · intro h
        exact Or.inl h
    · have := hFm.comp (measurable_id.prodMk (measurable_const (a := h)))
      exact this.stronglyMeasurable
    · intro g g' hgg
      exact hA' g g' h hgg
  simp only [hin]
  refine surv_integral_wordLaw_congr ν σ (A := {l : ℕ | m < l ∧ l < L}) ?_ ?_ ?_
  · intro l hl
    simp only [Set.mem_ofPred_eq] at hl
    simp only [Finset.mem_union, Finset.mem_Ico]
    constructor
    · rintro (h | h)
      · have := Finset.mem_range.1 (hS h)
        omega
      · exact h
    · intro h
      exact Or.inr h
  · exact hFm'.stronglyMeasurable.integral_prod_right'
  · intro h h' hhh
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => hB' g h h' hhh)

/-- Integrability of the inner integral of the split integrand as a function of the outer
coordinates. -/
theorem surv_mid_integrable_inner (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (eps : ℝ) {Ψ : ℝ → ℂ}
    (hΨ1 : ∀ a, ‖Ψ a‖ ≤ 1) {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ}
    (hfD : ∀ x, f x ≤ D) (c : ℝ) (L m : ℕ) (t : ℝ) (S W : Finset ℕ) :
    Integrable (fun h => surv_wcoef z m S *
      ∫ g, surv_splitInt eps Ψ f c L m t g h ∂(wordLaw ν σ S)) (wordLaw ν σ W) := by
  have hFm := surv_measurable_splitInt eps Ψ hf c L m t
  have hFm' : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => surv_splitInt eps Ψ f c L m t p.2 p.1 := by
    have := hFm.comp measurable_swap
    exact this
  refine Integrable.const_mul ?_ _
  refine (integrable_const D).mono' hFm'.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => ?_)
  have := norm_integral_le_of_norm_le_const (μ := wordLaw ν σ S)
    (f := fun g => surv_splitInt eps Ψ f c L m t g h)
    (Filter.Eventually.of_forall fun g => surv_norm_splitInt_le eps hΨ1 hf0 hfD c L m t g h)
  simpa using this

/-- **The word sum of the split integrand over the first `m` coordinates is a killed row**, and is
bounded by `D · RB` for `c/t ∈ [1/2, 2]`. -/
theorem surv_mid_row_bound (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (eps : ℝ) {Ψ : ℝ → ℂ}
    (hΨ1 : ∀ a, ‖Ψ a‖ ≤ 1) {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ}
    (hfD : ∀ x, f x ≤ D) {c t : ℝ} (ha : c / t ∈ Icc (1 / 2 : ℝ) 2) (L m : ℕ) {RB : ℝ}
    (hRB : ∀ a ∈ Icc (1 / 2 : ℝ) 2, ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ D) →
      ‖kRow (surv_J eps) ν σ z 1 a m φ 0‖ ≤ D * RB) (h : ℕ → ℝ) :
    ‖∑ S ∈ (Finset.range m).powerset, surv_wcoef z m S *
        ∫ g, surv_splitInt eps Ψ f c L m t g h ∂(wordLaw ν σ S)‖ ≤ D * RB := by
  have hφm : Measurable (surv_testF f t (c / t) L m h) :=
    (surv_measurable_testF hf t (c / t) L m).comp (measurable_const.prodMk measurable_id)
  have hφb : ∀ y, ‖surv_testF f t (c / t) L m h y‖ ≤ D :=
    surv_norm_testF_le hf0 hfD t (c / t) L m h
  have e : (∑ S ∈ (Finset.range m).powerset, surv_wcoef z m S *
      ∫ g, surv_splitInt eps Ψ f c L m t g h ∂(wordLaw ν σ S)) =
        Ψ (c / t) * surv_bwd eps (c / t) L m h *
          kRow (surv_J eps) ν σ z 1 (c / t) m (surv_testF f t (c / t) L m h) 0 := by
    rw [surv_kRow_eq_wint (surv_measurableSet_J eps) ν σ z 1 (c / t) hφm hφb m 0,
      ← surv_wint_const_mul]
    rfl
  rw [e, norm_mul, norm_mul]
  calc ‖Ψ (c / t)‖ * ‖surv_bwd eps (c / t) L m h‖ *
        ‖kRow (surv_J eps) ν σ z 1 (c / t) m (surv_testF f t (c / t) L m h) 0‖
      ≤ 1 * 1 * (D * RB) :=
        mul_le_mul (mul_le_mul (hΨ1 _) (surv_norm_bwd_le _ _ _ _ _) (norm_nonneg _)
          zero_le_one) (hRB _ ha _ hφm hφb) (norm_nonneg _) (by norm_num)
    _ = D * RB := by ring

/-- **The `m`-group at fixed `t`.**  The word sum over `S ⊆ {0, …, m-1}` of the split integrand
under `wordLaw (S ∪ [m+1, L))` is bounded by `D · RB` when `c/t ∈ [1/2, 2]`, and vanishes
otherwise. -/
theorem surv_mid_group_t (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (eps : ℝ) {Ψ : ℝ → ℂ}
    (hΨ1 : ∀ a, ‖Ψ a‖ ≤ 1) (hΨ0 : ∀ a, a ∉ Icc (1 / 2 : ℝ) 2 → Ψ a = 0) {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hfD : ∀ x, f x ≤ D) {c : ℝ} (hc0 : 0 < c)
    {L m : ℕ} {RB : ℝ}
    (hRB : ∀ a ∈ Icc (1 / 2 : ℝ) 2, ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ D) →
      ‖kRow (surv_J eps) ν σ z 1 a m φ 0‖ ≤ D * RB) (t : ℝ) :
    ‖∑ S ∈ (Finset.range m).powerset, surv_wcoef z m S *
        ∫ g, surv_splitInt eps Ψ f c L m t g g ∂(wordLaw ν σ (S ∪ Finset.Ico (m + 1) L))‖ ≤
      (Icc (c / 2) (2 * c)).indicator (fun _ => D * RB) t := by
  have hD : 0 ≤ D := (hf0 0).trans (hfD 0)
  have hDRB : 0 ≤ D * RB := (norm_nonneg _).trans (hRB 1 ⟨by norm_num, by norm_num⟩
    (fun _ => 0) measurable_const (fun _ => by rw [norm_zero]; exact hD))
  by_cases ha : c / t ∈ Icc (1 / 2 : ℝ) 2
  · have ht0 : 0 < t := by
      rcases lt_or_ge 0 t with h | h
      · exact h
      · exfalso
        have : c / t ≤ 0 := div_nonpos_of_nonneg_of_nonpos hc0.le h
        linarith [ha.1]
    have htI : t ∈ Icc (c / 2) (2 * c) := by
      obtain ⟨h1, h2⟩ := ha
      rw [le_div_iff₀ ht0] at h1
      rw [div_le_iff₀ ht0] at h2
      constructor <;> linarith
    rw [Set.indicator_of_mem htI]
    have hword : ∀ S ∈ (Finset.range m).powerset,
        ∫ g, surv_splitInt eps Ψ f c L m t g g ∂(wordLaw ν σ (S ∪ Finset.Ico (m + 1) L)) =
          ∫ h, ∫ g, surv_splitInt eps Ψ f c L m t g h ∂(wordLaw ν σ S)
            ∂(wordLaw ν σ (Finset.Ico (m + 1) L)) := fun S hS =>
      surv_mid_word_fubini ν σ (Finset.mem_powerset.1 hS) (surv_measurable_splitInt eps Ψ hf c L m t)
        (surv_norm_splitInt_le eps hΨ1 hf0 hfD c L m t)
        (fun g g' h hgg => surv_splitInt_congr_left eps Ψ f c L m t hgg)
        (fun g h h' hhh => surv_splitInt_congr_right eps Ψ f c L m t hhh)
    have hsum : ∑ S ∈ (Finset.range m).powerset, surv_wcoef z m S *
        ∫ g, surv_splitInt eps Ψ f c L m t g g ∂(wordLaw ν σ (S ∪ Finset.Ico (m + 1) L)) =
          ∫ h, ∑ S ∈ (Finset.range m).powerset, surv_wcoef z m S *
            ∫ g, surv_splitInt eps Ψ f c L m t g h ∂(wordLaw ν σ S)
              ∂(wordLaw ν σ (Finset.Ico (m + 1) L)) := by
      rw [integral_finsetSum _ fun S _ =>
        surv_mid_integrable_inner ν σ z eps hΨ1 hf hf0 hfD c L m t S _]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [hword S hS, integral_const_mul]
    rw [hsum]
    have := norm_integral_le_of_norm_le_const (μ := wordLaw ν σ (Finset.Ico (m + 1) L))
      (Filter.Eventually.of_forall fun h =>
        surv_mid_row_bound ν σ z eps hΨ1 hf hf0 hfD ha L m hRB h)
    simpa using this
  · have h0 : ∀ g : ℕ → ℝ, surv_splitInt eps Ψ f c L m t g g = 0 := fun g => by
      unfold surv_splitInt
      rw [hΨ0 _ ha]
      simp
    simp only [h0, integral_zero, mul_zero, Finset.sum_const_zero, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hDRB) t


/-! ## The `m`-group -/

/-- **The `m`-group of the middle word sum**: the words with last `ν` letter `m` contribute at
most `(3c/2) D RB` after the translation of the coordinate `m` and the `t`-integral over
`[c/2, 2c]`. -/
theorem surv_mid_group (ν σ : ProbabilityMeasure ℝ) (z : ℂ) {eps : ℝ} {Ψ : ℝ → ℂ}
    (hΨ : Measurable Ψ) (hΨ1 : ∀ a, ‖Ψ a‖ ≤ 1) (hΨ0 : ∀ a, a ∉ Icc (1 / 2 : ℝ) 2 → Ψ a = 0)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hfD : ∀ x, f x ≤ D)
    (hνf : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) {c : ℝ}
    {L m : ℕ} (hc : c = L - 2 * eps) (hc0 : 0 < c) (hm : m < L) {RB : ℝ}
    (hRB : ∀ a ∈ Icc (1 / 2 : ℝ) 2, ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ D) →
      ‖kRow (surv_J eps) ν σ z 1 a m φ 0‖ ≤ D * RB) :
    ‖∑ S ∈ (Finset.range m).powerset, surv_wcoef z m S *
        ∫ g, surv_midInt eps Ψ c L g ∂(wordLaw ν σ (S ∪ Finset.Ico (m + 1) L))‖ ≤
      3 * c / 2 * (D * RB) := by
  have hHm : Measurable (surv_midInt eps Ψ c L) := surv_measurable_midInt eps hΨ c L
  have hH1 : ∀ g, ‖surv_midInt eps Ψ c L g‖ ≤ 1 := surv_norm_midInt_le eps hΨ1 c L
  set R : (ℕ → ℝ) → ℝ := fun g => gapKeys g m + surv_tailSum L m g with hR
  have hRm : Measurable R := (rawAsm_measurable_gapKeys m).add (surv_measurable_tailSum L m)
  have hmS : ∀ S ∈ (Finset.range m).powerset, m ∉ S ∪ Finset.Ico (m + 1) L := by
    intro S hS h
    rcases Finset.mem_union.1 h with h | h
    · have := Finset.mem_range.1 (Finset.mem_powerset.1 hS h)
      omega
    · have := (Finset.mem_Ico.1 h).1
      omega
  -- translation of the coordinate `m`
  have hshift : ∀ S ∈ (Finset.range m).powerset,
      ∫ g, surv_midInt eps Ψ c L g ∂(wordLaw ν σ (S ∪ Finset.Ico (m + 1) L)) =
        ∫ t, ∫ g, surv_splitInt eps Ψ f c L m t g g
          ∂(wordLaw ν σ (S ∪ Finset.Ico (m + 1) L)) := by
    intro S hS
    rw [surv_integral_wordLaw_shift ν σ _ (hmS S hS) hf hf0 hνf hRm hHm hH1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t =>
      integral_congr_ae (Filter.Eventually.of_forall fun g => ?_))
    exact surv_shift_eq_split eps hΨ0 f hm hc t g
  have hintt : ∀ S ∈ (Finset.range m).powerset,
      Integrable (fun t => ∫ g, surv_splitInt eps Ψ f c L m t g g
        ∂(wordLaw ν σ (S ∪ Finset.Ico (m + 1) L))) := by
    intro S _
    have h := (surv_integrable_shift_prod ν σ (S ∪ Finset.Ico (m + 1) L) m hf hf0 hνf hRm hHm
      hH1).integral_prod_right
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact surv_shift_eq_split eps hΨ0 f hm hc t g
  have hsum : ∑ S ∈ (Finset.range m).powerset, surv_wcoef z m S *
      ∫ g, surv_midInt eps Ψ c L g ∂(wordLaw ν σ (S ∪ Finset.Ico (m + 1) L)) =
        ∫ t, ∑ S ∈ (Finset.range m).powerset, surv_wcoef z m S *
          ∫ g, surv_splitInt eps Ψ f c L m t g g ∂(wordLaw ν σ (S ∪ Finset.Ico (m + 1) L)) := by
    rw [integral_finsetSum _ fun S hS => (hintt S hS).const_mul _]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [hshift S hS, integral_const_mul]
  rw [hsum]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hpt : ∀ t, ‖∑ S ∈ (Finset.range m).powerset, surv_wcoef z m S *
      ∫ g, surv_splitInt eps Ψ f c L m t g g ∂(wordLaw ν σ (S ∪ Finset.Ico (m + 1) L))‖ ≤
        (Icc (c / 2) (2 * c)).indicator (fun _ => D * RB) t :=
    fun t => surv_mid_group_t ν σ z eps hΨ1 hΨ0 hf hf0 hfD hc0 hRB t
  have hI : IntegrableOn (fun _ : ℝ => D * RB) (Icc (c / 2) (2 * c)) volume :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  calc ∫ t, ‖∑ S ∈ (Finset.range m).powerset, surv_wcoef z m S *
        ∫ g, surv_splitInt eps Ψ f c L m t g g ∂(wordLaw ν σ (S ∪ Finset.Ico (m + 1) L))‖
      ≤ ∫ t, (Icc (c / 2) (2 * c)).indicator (fun _ => D * RB) t :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
          (hI.integrable_indicator measurableSet_Icc) (Filter.Eventually.of_forall hpt)
    _ = 3 * c / 2 * (D * RB) := by
        rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul,
          Real.volume_real_Icc_of_le (by linarith)]
        ring

/-! ## The middle bound -/

/-- **The middle-segment bound.**  For `Ψ` measurable with `‖Ψ‖ ≤ 1` supported in `[1/2, 2]`,
`ν = f dx` with `f ≤ D`, and killed rows `‖kRow J ν σ z 1 a m φ 0‖ ≤ D RB(m)` on tests
`‖φ‖ ≤ D` (`a ∈ [1/2, 2]`, `m < L`),
`‖surv_wint L (Ψ(a) ∏_{l ≤ L} 1_J(y_l))‖ ≤ ∑_{m<L} ‖1-z‖ ‖z‖^{L-1-m} (3c/2) D RB(m) + ‖z‖^L`,
`c = L - 2ε`. -/
theorem surv_mid_bound (ν σ : ProbabilityMeasure ℝ) (z : ℂ) {eps : ℝ} {L : ℕ}
    (hL : 2 * eps < L) {Ψ : ℝ → ℂ} (hΨ : Measurable Ψ) (hΨ1 : ∀ a, ‖Ψ a‖ ≤ 1)
    (hΨ0 : ∀ a, a ∉ Icc (1 / 2 : ℝ) 2 → Ψ a = 0) {f : ℝ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hfD : ∀ x, f x ≤ D)
    (hνf : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) {RB : ℕ → ℝ}
    (hRB : ∀ a ∈ Icc (1 / 2 : ℝ) 2, ∀ m < L, ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ D) →
      ‖kRow (surv_J eps) ν σ z 1 a m φ 0‖ ≤ D * RB m) :
    ‖surv_wint ν σ z L (surv_midInt eps Ψ (L - 2 * eps) L)‖ ≤
      ∑ m ∈ Finset.range L, ‖1 - z‖ * ‖z‖ ^ (L - 1 - m) * (3 * (L - 2 * eps) / 2 * (D * RB m)) +
        ‖z‖ ^ L := by
  have hc0 : 0 < (L : ℝ) - 2 * eps := by linarith
  unfold surv_wint
  rw [surv_sum_powerset_last L]
  refine (norm_add_le _ _).trans ?_
  rw [add_comm]
  refine add_le_add ?_ ?_
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    have hm' := Finset.mem_range.1 hm
    have e : ∑ S ∈ (Finset.range m).powerset, surv_wcoef z L (S ∪ Finset.Ico (m + 1) L) *
        ∫ g, surv_midInt eps Ψ (L - 2 * eps) L g ∂(wordLaw ν σ (S ∪ Finset.Ico (m + 1) L)) =
          ((1 - z) * z ^ (L - 1 - m)) * ∑ S ∈ (Finset.range m).powerset, surv_wcoef z m S *
            ∫ g, surv_midInt eps Ψ (L - 2 * eps) L g
              ∂(wordLaw ν σ (S ∪ Finset.Ico (m + 1) L)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [surv_wcoef_last z hm' (Finset.mem_powerset.1 hS)]
      ring
    rw [e, norm_mul, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (surv_mid_group ν σ z hΨ hΨ1 hΨ0 hf hf0 hfD hνf rfl hc0 hm'
      fun a ha φ hφ hφb => hRB a ha m hm' φ hφ hφb) (by positivity)
  · rw [norm_mul, norm_surv_wcoef, Finset.card_range, Nat.sub_self, pow_zero, one_mul]
    refine mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) ?_
    have := norm_integral_le_of_norm_le_const (μ := wordLaw ν σ (Finset.range L))
      (Filter.Eventually.of_forall (surv_norm_midInt_le eps hΨ1 (L - 2 * eps) L))
    simpa using this

end

end PGM
