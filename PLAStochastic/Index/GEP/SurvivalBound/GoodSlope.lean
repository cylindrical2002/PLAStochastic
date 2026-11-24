import PLAStochastic.Index.GEP.SurvivalBound.MiddleSegment
import PLAStochastic.Index.GEP.SurvivalBound.Certificate.NullTies

/-!
# WP4 `SurvivalBound`: the good-slope part of one certificate

Source: `task-survival.md` (P2), `progress-surv.md` (好斜率 1–4).

For a certificate pair `(i, j)`, `L = j - i > 2ε`, `j ≤ k`, the good-slope integrand is

`certInt g = 1{certOK (i,j)}(g) · 1{a ∈ [1/2, 2]} · G'(p_k)`,   `a = certSlope ε p i j`.

* **Permutation** (`surv_pi`, `surv_certInt_eq_permInt`): the coordinates are reordered as
  middle segment `i, …, j-1`, reversed prefix `i-1, …, 0`, suffix `j, …`; on positive gaps the
  certificate integrand becomes the three-block form `surv_permInt` (`cert_indicator_certOK_eq_prod`,
  `cert_gapKeys_eq_ends_certSlope`).
* **Prefix Fubini at `L`** (`surv_wint_permInt_eq`): `surv_wint k permInt` is the middle word
  functional of `midProd(g) · surv_pref(a(g))`, where `surv_pref a = surv_wint (i + (k-j)) (preInt a)`
  is the prefix–suffix functional at fixed slope.
* **Prefix Fubini at `i`** (`surv_pref_eq_row`): `surv_pref a` is the prefix row
  `kRow J ν σ z (-1) (-a) i ψ 0` on the suffix row `ψ(u) = kRow J ν σ z 1 a (k-j) φ_u (2ε)`,
  `φ_u(w) = 1_J(u) 1_J(w) G'((k+u-w)/a)`; hence `‖surv_pref a‖ ≤ E · RB(k-j) · RB(i)`
  (`surv_norm_pref_le`).
* **Per-certificate bound** (`surv_good_bound`): with `Ψ = surv_pref / M`, `M = E RB(k-j) RB(i)`,
  the middle lemma `surv_mid_bound` gives
  `‖surv_wint k certInt‖ ≤ M (∑_{m<L} ‖1-z‖ ‖z‖^{L-1-m} (3(L-2ε)/2) D RB(m) + ‖z‖^L)`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

/-! ## Scaling a killed row -/

/-- A row bound on tests of norm `≤ 1` scales to tests of norm `≤ D`. -/
theorem surv_norm_kRow_le_of_bound {J : Set ℝ} (hJ : MeasurableSet J) (ν σ : ProbabilityMeasure ℝ)
    (z : ℂ) (β a : ℝ) (n : ℕ) {RB : ℝ}
    (hRB : ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) → ∀ y, ‖kRow J ν σ z β a n φ y‖ ≤ RB)
    {φ : ℝ → ℂ} (hφ : Measurable φ) {D : ℝ} (hD : 0 < D) (hφD : ∀ y, ‖φ y‖ ≤ D) (y : ℝ) :
    ‖kRow J ν σ z β a n φ y‖ ≤ D * RB := by
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hφ'm : Measurable fun w => (D : ℂ)⁻¹ * φ w := measurable_const.mul hφ
  have hφ'1 : ∀ w, ‖(D : ℂ)⁻¹ * φ w‖ ≤ 1 := fun w => by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD,
      inv_mul_le_iff₀ hD, mul_one]
    exact hφD w
  have e : kRow J ν σ z β a n φ y = (D : ℂ) * kRow J ν σ z β a n (fun w => (D : ℂ)⁻¹ * φ w) y := by
    rw [surv_kRow_eq_wint hJ ν σ z β a hφ hφD n y, surv_kRow_eq_wint hJ ν σ z β a hφ'm hφ'1 n y,
      ← surv_wint_const_mul]
    refine surv_wint_congr ν σ z n fun S _ => Filter.Eventually.of_forall fun g => ?_
    simp only [kWordInt]
    rw [mul_left_comm (D : ℂ), ← mul_assoc (D : ℂ) (D : ℂ)⁻¹, mul_inv_cancel₀ hDc, one_mul]
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
  exact mul_le_mul_of_nonneg_left (hRB _ hφ'm hφ'1 y) hD.le

/-! ## The permutation -/

/-- The permutation putting the middle segment `i, …, j-1` first, then the reversed prefix
`i-1, …, 0`, then the suffix `j, …` (with `L = j - i`). -/
def surv_pi (i j L l : ℕ) : ℕ := if l < L then i + l else if l < j then i - 1 - (l - L) else l

theorem surv_pi_injective {i j L : ℕ} (hij : i < j) (hL : i + L = j) :
    Function.Injective (surv_pi i j L) := by
  intro l l' h
  unfold surv_pi at h
  split_ifs at h <;> omega

theorem surv_pi_lt {i j L k : ℕ} (_hij : i < j) (hL : i + L = j) (hjk : j ≤ k) (l : ℕ) :
    surv_pi i j L l < k ↔ l < k := by
  unfold surv_pi
  split_ifs <;> omega

theorem surv_pi_of_lt {i j L l : ℕ} (hl : l < L) : surv_pi i j L l = i + l := by
  unfold surv_pi; rw [if_pos hl]

theorem surv_pi_prefix {i j L s : ℕ} (_hij : i < j) (hL : i + L = j) (hs : s < i) :
    surv_pi i j L (L + s) = i - 1 - s := by
  unfold surv_pi
  rw [if_neg (by omega), if_pos (by omega)]
  omega

theorem surv_pi_suffix {i j L m : ℕ} (hL : i + L = j) :
    surv_pi i j L (L + (i + m)) = j + m := by
  unfold surv_pi
  rw [if_neg (by omega), if_neg (by omega)]
  omega

/-! ## The prefix–suffix functional -/

theorem surv_measurable_kWalk_slope (y₀ β : ℝ) (l : ℕ) :
    Measurable fun p : ℝ × (ℕ → ℝ) => kWalk y₀ β p.1 p.2 l := by
  unfold kWalk
  exact measurable_const.sub (measurable_fst.mul ((rawAsm_measurable_gapKeys l).comp measurable_snd))

theorem surv_measurable_kWalk_negslope (y₀ β : ℝ) (l : ℕ) :
    Measurable fun p : ℝ × (ℕ → ℝ) => kWalk y₀ β (-p.1) p.2 l := by
  unfold kWalk
  exact measurable_const.sub
    (measurable_fst.neg.mul ((rawAsm_measurable_gapKeys l).comp measurable_snd))

/-- The prefix–suffix integrand on `h = (reversed prefix, suffix)`: the prefix walk
`kWalk 0 (-1) (-a)` over `h 0, …, h (i-1)`, the suffix walk `kWalk 2ε 1 a` over `h i, …`, the slope
indicator and the test at the last key `(k + u - w)/a`. -/
def surv_preInt (eps : ℝ) (k i j : ℕ) (G' : ℝ → ℝ) (a : ℝ) (h : ℕ → ℝ) : ℂ :=
  (∏ l ∈ Finset.range (i + 1), (surv_J eps).indicator (fun _ => (1 : ℂ)) (kWalk 0 (-1) (-a) h l)) *
    (∏ l ∈ Finset.range (k - j + 1), (surv_J eps).indicator (fun _ => (1 : ℂ))
      (kWalk (2 * eps) 1 a (fun m => h (i + m)) l)) *
    (Icc (1 / 2 : ℝ) 2).indicator (fun _ => (1 : ℂ)) a *
    (G' ((k + kWalk 0 (-1) (-a) h i - kWalk (2 * eps) 1 a (fun m => h (i + m)) (k - j)) / a) : ℂ)

theorem surv_measurable_preInt (eps : ℝ) (k i j : ℕ) {G' : ℝ → ℝ} (hG' : Measurable G') :
    Measurable fun p : ℝ × (ℕ → ℝ) => surv_preInt eps k i j G' p.1 p.2 := by
  unfold surv_preInt
  have hsh : Measurable fun p : ℝ × (ℕ → ℝ) => (p.1, fun m => p.2 (i + m)) :=
    measurable_fst.prodMk
      (measurable_pi_lambda _ fun m => (measurable_pi_apply (i + m)).comp measurable_snd)
  have hJ := surv_measurableSet_J eps
  have h1 : Measurable fun p : ℝ × (ℕ → ℝ) => ∏ l ∈ Finset.range (i + 1),
      (surv_J eps).indicator (fun _ => (1 : ℂ)) (kWalk 0 (-1) (-p.1) p.2 l) :=
    Finset.measurable_prod _ fun l _ =>
      (measurable_const.indicator hJ).comp (surv_measurable_kWalk_negslope 0 (-1) l)
  have h2 : Measurable fun p : ℝ × (ℕ → ℝ) => ∏ l ∈ Finset.range (k - j + 1),
      (surv_J eps).indicator (fun _ => (1 : ℂ)) (kWalk (2 * eps) 1 p.1 (fun m => p.2 (i + m)) l) :=
    Finset.measurable_prod _ fun l _ =>
      (measurable_const.indicator hJ).comp ((surv_measurable_kWalk_slope (2 * eps) 1 l).comp hsh)
  have h3 : Measurable fun p : ℝ × (ℕ → ℝ) =>
      (Icc (1 / 2 : ℝ) 2).indicator (fun _ => (1 : ℂ)) p.1 :=
    (measurable_const.indicator measurableSet_Icc).comp measurable_fst
  have h4 : Measurable fun p : ℝ × (ℕ → ℝ) => (G' ((k + kWalk 0 (-1) (-p.1) p.2 i -
      kWalk (2 * eps) 1 p.1 (fun m => p.2 (i + m)) (k - j)) / p.1) : ℂ) := by
    refine Complex.measurable_ofReal.comp (hG'.comp ?_)
    exact ((measurable_const.add (surv_measurable_kWalk_negslope 0 (-1) i)).sub
      ((surv_measurable_kWalk_slope (2 * eps) 1 (k - j)).comp hsh)).div measurable_fst
  exact ((h1.mul h2).mul h3).mul h4

/-- The argument of the test stays below `2(k + 2ε)`. -/
theorem surv_test_arg_le {eps : ℝ} (heps : 0 ≤ eps) (k : ℕ) {a u w : ℝ}
    (ha : a ∈ Icc (1 / 2 : ℝ) 2) (hu : u ∈ surv_J eps) (hw : w ∈ surv_J eps) :
    (k + u - w) / a ≤ 2 * (k + 2 * eps) := by
  have ha0 : 0 < a := by linarith [ha.1]
  rw [div_le_iff₀ ha0]
  have h1 : 0 ≤ 2 * ((k : ℝ) + 2 * eps) := by positivity
  have h2 := mul_le_mul_of_nonneg_left ha.1 h1
  have hu2 := hu.2
  have hw1 := hw.1
  linarith

theorem surv_norm_preInt_le (eps : ℝ) (k i j : ℕ) (heps : 0 ≤ eps) {G' : ℝ → ℝ} {E : ℝ}
    (hE : 0 ≤ E) (hG : ∀ y, y ≤ 2 * (k + 2 * eps) → |G' y| ≤ E) (a : ℝ) (h : ℕ → ℝ) :
    ‖surv_preInt eps k i j G' a h‖ ≤ E := by
  unfold surv_preInt
  by_cases ha : a ∈ Icc (1 / 2 : ℝ) 2
  · by_cases hu : kWalk 0 (-1) (-a) h i ∈ surv_J eps
    · by_cases hw : kWalk (2 * eps) 1 a (fun m => h (i + m)) (k - j) ∈ surv_J eps
      · have hA := surv_norm_prod_indicator_le (Finset.range (i + 1)) (surv_J eps)
          (fun l => kWalk 0 (-1) (-a) h l)
        have hB := surv_norm_prod_indicator_le (Finset.range (k - j + 1)) (surv_J eps)
          (fun l => kWalk (2 * eps) 1 a (fun m => h (i + m)) l)
        have hC := surv_norm_indicator_one_le (Icc (1 / 2 : ℝ) 2) a
        have hD : ‖(G' ((k + kWalk 0 (-1) (-a) h i -
            kWalk (2 * eps) 1 a (fun m => h (i + m)) (k - j)) / a) : ℂ)‖ ≤ E := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact hG _ (surv_test_arg_le heps k ha hu hw)
        rw [norm_mul, norm_mul, norm_mul]
        have := mul_le_mul (mul_le_mul (mul_le_mul hA hB (norm_nonneg _) zero_le_one) hC
          (norm_nonneg _) (by norm_num)) hD (norm_nonneg _) (by norm_num)
        exact this.trans_eq (by ring)
      · rw [Finset.prod_range_succ _ (k - j), indicator_of_notMem hw]
        simp [hE]
    · rw [Finset.prod_range_succ _ i, indicator_of_notMem hu]
      simp [hE]
  · rw [indicator_of_notMem ha]
    simp [hE]

/-- The prefix–suffix functional at fixed slope `a`. -/
def surv_pref (eps : ℝ) (k i j : ℕ) (G' : ℝ → ℝ) (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (a : ℝ) :
    ℂ :=
  surv_wint ν σ z (i + (k - j)) (surv_preInt eps k i j G' a)

theorem surv_measurable_pref (eps : ℝ) (k i j : ℕ) {G' : ℝ → ℝ} (hG' : Measurable G')
    (ν σ : ProbabilityMeasure ℝ) (z : ℂ) : Measurable (surv_pref eps k i j G' ν σ z) := by
  show Measurable fun a => surv_wint ν σ z (i + (k - j)) (surv_preInt eps k i j G' a)
  unfold surv_wint
  refine Finset.measurable_sum _ fun S _ => measurable_const.mul ?_
  exact (surv_measurable_preInt eps k i j hG').stronglyMeasurable.integral_prod_right'.measurable

theorem surv_pref_eq_zero (eps : ℝ) (k i j : ℕ) (G' : ℝ → ℝ) (ν σ : ProbabilityMeasure ℝ) (z : ℂ)
    {a : ℝ} (ha : a ∉ Icc (1 / 2 : ℝ) 2) : surv_pref eps k i j G' ν σ z a = 0 := by
  unfold surv_pref surv_wint
  refine Finset.sum_eq_zero fun S _ => ?_
  have h0 : ∀ h, surv_preInt eps k i j G' a h = 0 := fun h => by
    unfold surv_preInt
    rw [indicator_of_notMem ha]
    simp
  simp [h0]

/-! ## The suffix row and the prefix row -/

/-- The suffix test `φ_u(w) = 1_J(u) 1_J(w) G'((k + u - w)/a)`. -/
def surv_sufTest (eps : ℝ) (k : ℕ) (G' : ℝ → ℝ) (a u w : ℝ) : ℂ :=
  (surv_J eps).indicator (fun _ => (1 : ℂ)) u * (surv_J eps).indicator (fun _ => (1 : ℂ)) w *
    (G' ((k + u - w) / a) : ℂ)

theorem surv_measurable_sufTest (eps : ℝ) (k : ℕ) {G' : ℝ → ℝ} (hG' : Measurable G') (a : ℝ) :
    Measurable fun p : ℝ × ℝ => surv_sufTest eps k G' a p.1 p.2 := by
  unfold surv_sufTest
  have hJ := surv_measurableSet_J eps
  refine (((measurable_const.indicator hJ).comp measurable_fst).mul
    ((measurable_const.indicator hJ).comp measurable_snd)).mul ?_
  exact Complex.measurable_ofReal.comp (hG'.comp
    (((measurable_const.add measurable_fst).sub measurable_snd).div_const a))

theorem surv_norm_sufTest_le {eps : ℝ} (heps : 0 ≤ eps) (k : ℕ) {G' : ℝ → ℝ} {E : ℝ} (hE : 0 ≤ E)
    (hG : ∀ y, y ≤ 2 * (k + 2 * eps) → |G' y| ≤ E) {a : ℝ} (ha : a ∈ Icc (1 / 2 : ℝ) 2)
    (u w : ℝ) : ‖surv_sufTest eps k G' a u w‖ ≤ E := by
  unfold surv_sufTest
  by_cases hu : u ∈ surv_J eps
  · by_cases hw : w ∈ surv_J eps
    · rw [indicator_of_mem hu, indicator_of_mem hw, one_mul, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
      exact hG _ (surv_test_arg_le heps k ha hu hw)
    · rw [indicator_of_notMem hw]
      simp [hE]
  · rw [indicator_of_notMem hu]
    simp [hE]

/-- The suffix row `ψ(u) = kRow J ν σ z 1 a (k - j) φ_u (2ε)`. -/
def surv_sufRow (eps : ℝ) (k j : ℕ) (G' : ℝ → ℝ) (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (a u : ℝ) :
    ℂ :=
  kRow (surv_J eps) ν σ z 1 a (k - j) (surv_sufTest eps k G' a u) (2 * eps)

theorem surv_sufRow_eq_wint {eps : ℝ} (heps : 0 ≤ eps) (k j : ℕ) {G' : ℝ → ℝ}
    (hG' : Measurable G') {E : ℝ} (hE : 0 ≤ E) (hG : ∀ y, y ≤ 2 * (k + 2 * eps) → |G' y| ≤ E)
    (ν σ : ProbabilityMeasure ℝ) (z : ℂ) {a : ℝ} (ha : a ∈ Icc (1 / 2 : ℝ) 2) (u : ℝ) :
    surv_sufRow eps k j G' ν σ z a u = surv_wint ν σ z (k - j)
      (kWordInt (surv_J eps) 1 a (k - j) (surv_sufTest eps k G' a u) (2 * eps)) :=
  surv_kRow_eq_wint (surv_measurableSet_J eps) ν σ z 1 a
    ((surv_measurable_sufTest eps k hG' a).comp (measurable_const.prodMk measurable_id))
    (surv_norm_sufTest_le heps k hE hG ha u) (k - j) (2 * eps)

theorem surv_measurable_sufRow {eps : ℝ} (heps : 0 ≤ eps) (k j : ℕ) {G' : ℝ → ℝ}
    (hG' : Measurable G') {E : ℝ} (hE : 0 ≤ E) (hG : ∀ y, y ≤ 2 * (k + 2 * eps) → |G' y| ≤ E)
    (ν σ : ProbabilityMeasure ℝ) (z : ℂ) {a : ℝ} (ha : a ∈ Icc (1 / 2 : ℝ) 2) :
    Measurable (surv_sufRow eps k j G' ν σ z a) := by
  have e : surv_sufRow eps k j G' ν σ z a = fun u => surv_wint ν σ z (k - j)
      (kWordInt (surv_J eps) 1 a (k - j) (surv_sufTest eps k G' a u) (2 * eps)) := by
    funext u
    exact surv_sufRow_eq_wint heps k j hG' hE hG ν σ z ha u
  rw [e]
  unfold surv_wint
  refine Finset.measurable_sum _ fun S _ => measurable_const.mul ?_
  have hm : Measurable fun p : ℝ × (ℕ → ℝ) =>
      kWordInt (surv_J eps) 1 a (k - j) (surv_sufTest eps k G' a p.1) (2 * eps) p.2 := by
    unfold kWordInt
    refine Measurable.mul ?_ ?_
    · exact Finset.measurable_prod _ fun l _ => (measurable_const.indicator
        (surv_measurableSet_J eps)).comp ((surv_measurable_kWalk (2 * eps) 1 a l).comp
          measurable_snd)
    · have h := (surv_measurable_sufTest eps k hG' a).comp
        (measurable_fst.prodMk ((surv_measurable_kWalk (2 * eps) 1 a (k - j)).comp measurable_snd))
      exact h
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem surv_norm_sufRow_le {eps : ℝ} (heps : 0 ≤ eps) (k j : ℕ) {G' : ℝ → ℝ}
    (hG' : Measurable G') {E : ℝ} (hE : 0 < E) (hG : ∀ y, y ≤ 2 * (k + 2 * eps) → |G' y| ≤ E)
    (ν σ : ProbabilityMeasure ℝ) (z : ℂ) {RB : ℝ}
    (hRB : ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) → ∀ y,
      ‖kRow (surv_J eps) ν σ z 1 a (k - j) φ y‖ ≤ RB) (ha : a ∈ Icc (1 / 2 : ℝ) 2) (u : ℝ) :
    ‖surv_sufRow eps k j G' ν σ z a u‖ ≤ E * RB :=
  surv_norm_kRow_le_of_bound (surv_measurableSet_J eps) ν σ z 1 a (k - j) hRB
    ((surv_measurable_sufTest eps k hG' a).comp (measurable_const.prodMk measurable_id)) hE
    (surv_norm_sufTest_le heps k hE.le hG ha u) (2 * eps)

theorem surv_indicator_one_sq (J : Set ℝ) (x : ℝ) :
    J.indicator (fun _ => (1 : ℂ)) x * J.indicator (fun _ => (1 : ℂ)) x =
      J.indicator (fun _ => (1 : ℂ)) x := by
  by_cases h : x ∈ J
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h]

/-- **The prefix–suffix functional is the prefix row on the suffix row.** -/
theorem surv_pref_eq_row {eps : ℝ} (heps : 0 ≤ eps) (k i j : ℕ) {G' : ℝ → ℝ}
    (hG' : Measurable G') {E : ℝ} (hE : 0 < E) (hG : ∀ y, y ≤ 2 * (k + 2 * eps) → |G' y| ≤ E)
    (ν σ : ProbabilityMeasure ℝ) (z : ℂ) {RB : ℝ}
    (hRB : ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) → ∀ y,
      ‖kRow (surv_J eps) ν σ z 1 a (k - j) φ y‖ ≤ RB) (ha : a ∈ Icc (1 / 2 : ℝ) 2) :
    surv_pref eps k i j G' ν σ z a =
      kRow (surv_J eps) ν σ z (-1) (-a) i (surv_sufRow eps k j G' ν σ z a) 0 := by
  have hψm := surv_measurable_sufRow heps k j hG' hE.le hG ν σ z ha
  have hψb := surv_norm_sufRow_le heps k j hG' hE hG ν σ z hRB ha
  unfold surv_pref
  have hHm : Measurable (surv_preInt eps k i j G' a) := by
    have h := (surv_measurable_preInt eps k i j hG').comp
      ((measurable_const (a := a)).prodMk (measurable_id (α := ℕ → ℝ)))
    exact h
  rw [surv_wint_cat ν σ z i (k - j) (H := surv_preInt eps k i j G' a) hHm
    (surv_norm_preInt_le eps k i j heps hE.le hG a),
    surv_kRow_eq_wint (surv_measurableSet_J eps) ν σ z (-1) (-a) hψm hψb i 0]
  refine surv_wint_congr ν σ z i fun S _ => Filter.Eventually.of_forall fun h₁ => ?_
  simp only [kWordInt]
  rw [surv_sufRow_eq_wint heps k j hG' hE.le hG ν σ z ha, ← surv_wint_const_mul]
  refine surv_wint_congr ν σ z (k - j) fun S _ => Filter.Eventually.of_forall fun h₂ => ?_
  simp only [kWordInt]
  -- the concatenation splits into the two blocks
  have hcat1 : ∀ l ≤ i, kWalk 0 (-1) (-a) (surv_cat i h₁ h₂) l = kWalk 0 (-1) (-a) h₁ l :=
    fun l hl => surv_kWalk_congr fun s hs => surv_cat_apply_lt (by omega) h₁ h₂
  have hcat2 : (fun m => surv_cat i h₁ h₂ (i + m)) = h₂ := by
    funext m
    exact surv_cat_apply_add i m h₁ h₂
  have hP : ∏ l ∈ Finset.range (i + 1), (surv_J eps).indicator (fun _ => (1 : ℂ))
      (kWalk 0 (-1) (-a) (surv_cat i h₁ h₂) l) = ∏ l ∈ Finset.range (i + 1),
        (surv_J eps).indicator (fun _ => (1 : ℂ)) (kWalk 0 (-1) (-a) h₁ l) :=
    Finset.prod_congr rfl fun l hl => by rw [hcat1 l (by have := Finset.mem_range.1 hl; omega)]
  unfold surv_preInt
  rw [hcat2, hP, hcat1 i le_rfl, indicator_of_mem ha]
  unfold surv_sufTest
  simp only [Finset.prod_range_succ]
  by_cases hu : kWalk 0 (-1) (-a) h₁ i ∈ surv_J eps
  · by_cases hw : kWalk (2 * eps) 1 a h₂ (k - j) ∈ surv_J eps
    · simp only [indicator_of_mem hu, indicator_of_mem hw]
      ring
    · simp only [indicator_of_notMem hw]
      ring
  · simp only [indicator_of_notMem hu]
    ring

/-- **Bound on the prefix–suffix functional**: `‖surv_pref a‖ ≤ E · RB(k-j) · RB(i)` for
`a ∈ [1/2, 2]`. -/
theorem surv_norm_pref_le {eps : ℝ} (heps : 0 ≤ eps) (k i j : ℕ) {G' : ℝ → ℝ}
    (hG' : Measurable G') {E : ℝ} (hE : 0 < E) (hG : ∀ y, y ≤ 2 * (k + 2 * eps) → |G' y| ≤ E)
    (ν σ : ProbabilityMeasure ℝ) (z : ℂ) {RB : ℕ → ℝ} (hRBpos : ∀ n, 0 < RB n)
    (hRB : ∀ β a' : ℝ, 1 / 2 ≤ |a'| → ∀ n : ℕ, ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      ∀ y, ‖kRow (surv_J eps) ν σ z β a' n φ y‖ ≤ RB n) {a : ℝ} (ha : a ∈ Icc (1 / 2 : ℝ) 2) :
    ‖surv_pref eps k i j G' ν σ z a‖ ≤ E * RB (k - j) * RB i := by
  have ha0 : 0 < a := by linarith [ha.1]
  have haabs : 1 / 2 ≤ |a| := by rw [abs_of_pos ha0]; exact ha.1
  have hnaabs : 1 / 2 ≤ |-a| := by rw [abs_neg]; exact haabs
  have hRBsuf := hRB 1 a haabs (k - j)
  rw [surv_pref_eq_row heps k i j hG' hE hG ν σ z hRBsuf ha]
  exact surv_norm_kRow_le_of_bound (surv_measurableSet_J eps) ν σ z (-1) (-a) i
    (hRB (-1) (-a) hnaabs i) (surv_measurable_sufRow heps k j hG' hE.le hG ν σ z ha)
    (mul_pos hE (hRBpos (k - j))) (surv_norm_sufRow_le heps k j hG' hE hG ν σ z hRBsuf ha) 0

/-! ## The permuted integrand and the prefix Fubini at `L` -/

/-- The three-block integrand on the permuted coordinates: middle walk on `0, …, L-1`, then
the prefix–suffix integrand on the coordinates `L, …`. -/
def surv_permInt (eps : ℝ) (k i j L : ℕ) (c : ℝ) (G' : ℝ → ℝ) (g : ℕ → ℝ) : ℂ :=
  (∏ l ∈ Finset.range (L + 1),
      (surv_J eps).indicator (fun _ => (1 : ℂ)) (kWalk 0 1 (surv_slope c L g) g l)) *
    surv_preInt eps k i j G' (surv_slope c L g) (fun m => g (L + m))

theorem surv_measurable_permInt (eps : ℝ) (k i j L : ℕ) (c : ℝ) {G' : ℝ → ℝ}
    (hG' : Measurable G') : Measurable (surv_permInt eps k i j L c G') := by
  unfold surv_permInt
  refine Measurable.mul (Finset.measurable_prod _ fun l _ => ?_) ?_
  · refine (measurable_const.indicator (surv_measurableSet_J eps)).comp ?_
    unfold kWalk
    exact measurable_const.sub ((surv_measurable_slope c L).mul (rawAsm_measurable_gapKeys l))
  · have hsh : Measurable fun g : ℕ → ℝ => fun m => g (L + m) :=
      measurable_pi_lambda _ fun m => measurable_pi_apply (L + m)
    have h := (surv_measurable_preInt eps k i j hG').comp ((surv_measurable_slope c L).prodMk hsh)
    exact h

theorem surv_norm_permInt_le (eps : ℝ) (k i j L : ℕ) (c : ℝ) (heps : 0 ≤ eps) {G' : ℝ → ℝ}
    {E : ℝ} (hE : 0 ≤ E) (hG : ∀ y, y ≤ 2 * (k + 2 * eps) → |G' y| ≤ E) (g : ℕ → ℝ) :
    ‖surv_permInt eps k i j L c G' g‖ ≤ E := by
  unfold surv_permInt
  rw [norm_mul]
  calc _ ≤ 1 * E := mul_le_mul (surv_norm_prod_indicator_le _ _ _)
        (surv_norm_preInt_le eps k i j heps hE hG _ _) (norm_nonneg _) zero_le_one
    _ = E := one_mul E

theorem surv_permInt_cat (eps : ℝ) (k i j L : ℕ) (c : ℝ) (G' : ℝ → ℝ) (g h : ℕ → ℝ) :
    surv_permInt eps k i j L c G' (surv_cat L g h) =
      (∏ l ∈ Finset.range (L + 1),
        (surv_J eps).indicator (fun _ => (1 : ℂ)) (kWalk 0 1 (surv_slope c L g) g l)) *
        surv_preInt eps k i j G' (surv_slope c L g) h := by
  have hs : surv_slope c L (surv_cat L g h) = surv_slope c L g := by
    unfold surv_slope gapKeys
    congr 1
    exact Finset.sum_congr rfl fun s hs => surv_cat_apply_lt (Finset.mem_range.1 hs) g h
  have hh : (fun m => surv_cat L g h (L + m)) = h := by
    funext m
    exact surv_cat_apply_add L m g h
  unfold surv_permInt
  rw [hs, hh]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  congr 1
  exact surv_kWalk_congr fun s hs => surv_cat_apply_lt (by omega) g h

/-- **Prefix Fubini at `L`**: the word functional of the permuted integrand is the middle word
functional of `midProd(g) · surv_pref(a(g))`. -/
theorem surv_wint_permInt_eq (ν σ : ProbabilityMeasure ℝ) (z : ℂ) {eps : ℝ} (heps : 0 ≤ eps)
    {k i j L : ℕ} (hL : i + L = j) (hjk : j ≤ k) (c : ℝ) {G' : ℝ → ℝ} (hG' : Measurable G')
    {E : ℝ} (hE : 0 ≤ E) (hG : ∀ y, y ≤ 2 * (k + 2 * eps) → |G' y| ≤ E) :
    surv_wint ν σ z k (surv_permInt eps k i j L c G') =
      surv_wint ν σ z L (fun g => (∏ l ∈ Finset.range (L + 1),
        (surv_J eps).indicator (fun _ => (1 : ℂ)) (kWalk 0 1 (surv_slope c L g) g l)) *
          surv_pref eps k i j G' ν σ z (surv_slope c L g)) := by
  have hk : L + (i + (k - j)) = k := by omega
  have h := surv_wint_cat ν σ z L (i + (k - j)) (surv_measurable_permInt eps k i j L c hG')
    (surv_norm_permInt_le eps k i j L c heps hE hG)
  rw [hk] at h
  rw [h]
  refine surv_wint_congr ν σ z L fun S _ => Filter.Eventually.of_forall fun g => ?_
  unfold surv_pref
  rw [← surv_wint_const_mul]
  refine surv_wint_congr ν σ z (i + (k - j)) fun S _ => Filter.Eventually.of_forall fun h => ?_
  exact surv_permInt_cat eps k i j L c G' g h

/-! ## The certificate integrand -/

/-- The good-slope certificate integrand `1{certOK} · 1{a ∈ [1/2, 2]} · G'(p_k)`. -/
def surv_certInt (eps : ℝ) (k i j : ℕ) (G' : ℝ → ℝ) (g : ℕ → ℝ) : ℂ :=
  {g' : ℕ → ℝ | certOK eps (gapKeys g') k i j}.indicator (fun _ => (1 : ℂ)) g *
    (Icc (1 / 2 : ℝ) 2).indicator (fun _ => (1 : ℂ)) (certSlope eps (gapKeys g) i j) *
    (G' (gapKeys g k) : ℂ)

/-- **On positive gaps the certificate integrand is the permuted three-block integrand.** -/
theorem surv_certInt_eq_permInt {eps : ℝ} {k i j L : ℕ} (hij : i < j) (hL : i + L = j)
    (hjk : j ≤ k) {c : ℝ} (hc : c = L - 2 * eps) (G' : ℝ → ℝ) {g : ℕ → ℝ}
    (hg : ∀ l, 0 < g l) :
    surv_certInt eps k i j G' g = surv_permInt eps k i j L c G' (fun l => g (surv_pi i j L l)) := by
  have hLr : (L : ℝ) = j - i := by
    have := congrArg (Nat.cast (R := ℝ)) hL
    push_cast at this
    linarith
  have hLj : L = j - i := by omega
  -- the middle slope is the certificate slope
  have hgk : gapKeys (fun l => g (surv_pi i j L l)) L = gapKeys g j - gapKeys g i := by
    have e : gapKeys (fun l => g (surv_pi i j L l)) L = gapKeys (fun m => g (i + m)) L := by
      unfold gapKeys
      refine Finset.sum_congr rfl fun s hs => ?_
      have hs' := Finset.mem_range.1 hs
      show g (surv_pi i j L s) = g (i + s)
      rw [surv_pi_of_lt hs']
    rw [e, gapKeys_shift, hL]
  have hslope : surv_slope c L (fun l => g (surv_pi i j L l)) = certSlope eps (gapKeys g) i j := by
    unfold surv_slope certSlope
    rw [hgk, hc, hLr]
  -- the three blocks
  have hmid : ∀ l ≤ L, kWalk 0 1 (certSlope eps (gapKeys g) i j) (fun l => g (surv_pi i j L l)) l =
      kWalk 0 1 (certSlope eps (gapKeys g) i j) (fun m => g (i + m)) l := fun l hl =>
    surv_kWalk_congr fun s hs => by
      show g (surv_pi i j L s) = g (i + s)
      rw [surv_pi_of_lt (by omega)]
  have hpre : ∀ l ≤ i, kWalk 0 (-1) (-certSlope eps (gapKeys g) i j)
      (fun m => g (surv_pi i j L (L + m))) l =
        kWalk 0 (-1) (-certSlope eps (gapKeys g) i j) (fun m => g (i - 1 - m)) l := fun l hl =>
    surv_kWalk_congr fun s hs => by
      show g (surv_pi i j L (L + s)) = g (i - 1 - s)
      rw [surv_pi_prefix hij hL (by omega)]
  have hsuf : (fun m => g (surv_pi i j L (L + (i + m)))) = fun m => g (j + m) := by
    funext m
    rw [surv_pi_suffix hL]
  unfold surv_permInt surv_preInt surv_certInt
  rw [hslope, hsuf, hpre i le_rfl]
  have hPmid : ∏ l ∈ Finset.range (L + 1), (surv_J eps).indicator (fun _ => (1 : ℂ))
      (kWalk 0 1 (certSlope eps (gapKeys g) i j) (fun l => g (surv_pi i j L l)) l) =
        ∏ l ∈ Finset.range (L + 1), (surv_J eps).indicator (fun _ => (1 : ℂ))
          (kWalk 0 1 (certSlope eps (gapKeys g) i j) (fun m => g (i + m)) l) :=
    Finset.prod_congr rfl fun l hl => by rw [hmid l (by have := Finset.mem_range.1 hl; omega)]
  have hPpre : ∏ l ∈ Finset.range (i + 1), (surv_J eps).indicator (fun _ => (1 : ℂ))
      (kWalk 0 (-1) (-certSlope eps (gapKeys g) i j) (fun m => g (surv_pi i j L (L + m))) l) =
        ∏ l ∈ Finset.range (i + 1), (surv_J eps).indicator (fun _ => (1 : ℂ))
          (kWalk 0 (-1) (-certSlope eps (gapKeys g) i j) (fun m => g (i - 1 - m)) l) :=
    Finset.prod_congr rfl fun l hl => by rw [hpre l (by have := Finset.mem_range.1 hl; omega)]
  rw [hPmid, hPpre]
  by_cases ha : certSlope eps (gapKeys g) i j ∈ Icc (1 / 2 : ℝ) 2
  · have ha0 : certSlope eps (gapKeys g) i j ≠ 0 := by
      have := ha.1
      intro h
      rw [h] at this
      norm_num at this
    have hne : gapKeys g i ≠ gapKeys g j :=
      (cert_gapKeys_lt (k := j) (fun l _ => hg l) i j hij le_rfl).ne
    rw [cert_indicator_certOK_eq_prod hij.le hjk hne, cert_gapKeys_eq_ends_certSlope hij.le hjk hne ha0,
      indicator_of_mem ha]
    unfold surv_J
    rw [hLj]
    ring
  · rw [indicator_of_notMem ha]
    simp

/-! ## The good-slope bound for one certificate -/

/-- **The word functional of the certificate integrand** equals `M · surv_wint L (midInt Ψ)` with
`Ψ = surv_pref / M`, for any `M ≠ 0`. -/
theorem surv_certInt_eq (ν σ : ProbabilityMeasure ℝ) (z : ℂ) {eps : ℝ} (heps : 0 ≤ eps)
    {k i j L : ℕ} (hij : i < j) (hL : i + L = j) (hjk : j ≤ k) {c : ℝ} (hc : c = L - 2 * eps)
    (hνpos : (ν : Measure ℝ) (Iic 0) = 0) (hσpos : (σ : Measure ℝ) (Iic 0) = 0) {G' : ℝ → ℝ}
    (hG' : Measurable G') {E : ℝ} (hE : 0 ≤ E) (hG : ∀ y, y ≤ 2 * (k + 2 * eps) → |G' y| ≤ E)
    {M : ℝ} (hM : M ≠ 0) :
    surv_wint ν σ z k (surv_certInt eps k i j G') = (M : ℂ) * surv_wint ν σ z L
      (surv_midInt eps (fun a => surv_pref eps k i j G' ν σ z a / M) c L) := by
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have e1 : surv_wint ν σ z k (surv_certInt eps k i j G') =
      surv_wint ν σ z k (fun g => surv_permInt eps k i j L c G' (fun l => g (surv_pi i j L l))) :=
    surv_wint_congr ν σ z k fun S _ => (cert_ae_pos_wordLaw hνpos hσpos S).mono fun g hg =>
      surv_certInt_eq_permInt hij hL hjk hc G' hg
  rw [e1, surv_wint_perm ν σ z k (surv_pi_injective hij hL) (surv_pi_lt hij hL hjk)
    (surv_measurable_permInt eps k i j L c hG'), surv_wint_permInt_eq ν σ z heps hL hjk c hG' hE hG,
    ← surv_wint_const_mul]
  refine surv_wint_congr ν σ z L fun S _ => Filter.Eventually.of_forall fun g => ?_
  unfold surv_midInt
  beta_reduce
  rw [div_mul_eq_mul_div, ← mul_div_assoc, mul_div_cancel_left₀ _ hMc]
  ring

/-- **The good-slope bound for one certificate.**  With `E` bounding `|G'|` on
`(-∞, 2(k + 2ε)]`, `ν = f dx` with `f ≤ D`, and rows `‖kRow J ν σ z β a' n φ y‖ ≤ RB n` on tests
`‖φ‖ ≤ 1` (`|a'| ≥ 1/2`),
`‖surv_wint k certInt‖ ≤ E RB(k-j) RB(i) (∑_{m<L} ‖1-z‖ ‖z‖^{L-1-m} (3(L-2ε)/2) D RB(m) + ‖z‖^L)`. -/
theorem surv_good_bound (ν σ : ProbabilityMeasure ℝ) (z : ℂ) {eps : ℝ} (heps : 0 ≤ eps)
    {k i j L : ℕ} (hij : i < j) (hL : i + L = j) (hjk : j ≤ k) (hLε : 2 * eps < L)
    (hνpos : (ν : Measure ℝ) (Iic 0) = 0) (hσpos : (σ : Measure ℝ) (Iic 0) = 0) {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hD : 0 < D) (hfD : ∀ x, f x ≤ D)
    (hνf : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) {G' : ℝ → ℝ}
    (hG' : Measurable G') {E : ℝ} (hE : 0 < E) (hG : ∀ y, y ≤ 2 * (k + 2 * eps) → |G' y| ≤ E)
    {RB : ℕ → ℝ} (hRBpos : ∀ n, 0 < RB n)
    (hRB : ∀ β a' : ℝ, 1 / 2 ≤ |a'| → ∀ n : ℕ, ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      ∀ y, ‖kRow (surv_J eps) ν σ z β a' n φ y‖ ≤ RB n) :
    ‖surv_wint ν σ z k (surv_certInt eps k i j G')‖ ≤ E * RB (k - j) * RB i *
      (∑ m ∈ Finset.range L, ‖1 - z‖ * ‖z‖ ^ (L - 1 - m) * (3 * (L - 2 * eps) / 2 * (D * RB m)) +
        ‖z‖ ^ L) := by
  have hMpos : 0 < E * RB (k - j) * RB i := by
    have := hRBpos (k - j); have := hRBpos i; positivity
  set M := E * RB (k - j) * RB i with hMdef
  have hΨm : Measurable fun a => surv_pref eps k i j G' ν σ z a / M :=
    (surv_measurable_pref eps k i j hG' ν σ z).div_const _
  have hΨ1 : ∀ a, ‖surv_pref eps k i j G' ν σ z a / M‖ ≤ 1 := by
    intro a
    by_cases ha : a ∈ Icc (1 / 2 : ℝ) 2
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos, div_le_one hMpos]
      exact surv_norm_pref_le heps k i j hG' hE hG ν σ z hRBpos hRB ha
    · rw [surv_pref_eq_zero eps k i j G' ν σ z ha, zero_div, norm_zero]
      exact zero_le_one
  have hΨ0 : ∀ a, a ∉ Icc (1 / 2 : ℝ) 2 → surv_pref eps k i j G' ν σ z a / M = 0 := fun a ha => by
    rw [surv_pref_eq_zero eps k i j G' ν σ z ha, zero_div]
  have hRB' : ∀ a ∈ Icc (1 / 2 : ℝ) 2, ∀ m < L, ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ D) →
      ‖kRow (surv_J eps) ν σ z 1 a m φ 0‖ ≤ D * RB m := by
    intro a ha m _ φ hφ hφD
    have haabs : 1 / 2 ≤ |a| := by rw [abs_of_pos (by linarith [ha.1])]; exact ha.1
    exact surv_norm_kRow_le_of_bound (surv_measurableSet_J eps) ν σ z 1 a m (hRB 1 a haabs m) hφ hD
      hφD 0
  rw [surv_certInt_eq ν σ z heps hij hL hjk rfl hνpos hσpos hG' hE.le hG hMpos.ne', norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos]
  exact mul_le_mul_of_nonneg_left
    (surv_mid_bound ν σ z hLε hΨm hΨ1 hΨ0 hf hf0 hfD hνf hRB') hMpos.le

end

end PGM
