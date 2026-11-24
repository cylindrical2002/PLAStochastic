import PLAStochastic.Index.GEP.SurvivalBound.LongSegments

/-!
# WP4 `SurvivalBound`: the short segments `1 ≤ k ≤ 8ε`

Source: `task-survival.md` (P3, 短段), `rawdisc-design.md` §3.

For `k ≤ 8ε` both `{T ≤ k}` and "some `p_t ∉ J' = [-ε, 9ε]`" are contained in the large-deviation
event `LD' = {∃ t ≤ k, ε < |p_t - t|}` (the line of slope one is then an admissible line, and
`p_t ∈ [t - ε, t + ε] ⊆ J'`).  Hence the survival integrand differs from the free killed walk
`∏_{t ≤ k} 1_{J'}(p_t) G'(p_k)` only on `LD'`, by at most `2 |G'(p_k)|`.  The free walk is the
killed row `kRow J' ν σ z 0 (-1) k φ 0` at `0` (`surv_short_main_eq`), bounded by the class row
bound without a gap; the difference is bounded through the positive mixture and
`surv_short_integral_le`.

`surv_short_bound`: for `1 ≤ ε`, `1 ≤ k ≤ 8ε`,
`‖cSurv ε ν σ z k G‖ ≤ e^{9εγ'} R + (‖1-z‖ + ‖z‖)^k · 2 (2 e^{20εγ'} e^{-cε/8} + e^{-10ελ₀})`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

/-- The free interval `J' = [-ε, 9ε]`. -/
def surv_J' (eps : ℝ) : Set ℝ := Icc (-eps) (9 * eps)

theorem surv_wint_sub (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (n : ℕ) {H H' : (ℕ → ℝ) → ℂ}
    (h : ∀ S, Integrable H (wordLaw ν σ S)) (h' : ∀ S, Integrable H' (wordLaw ν σ S)) :
    surv_wint ν σ z n (fun g => H g - H' g) = surv_wint ν σ z n H - surv_wint ν σ z n H' := by
  unfold surv_wint
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [integral_sub (h S) (h' S)]
  ring

theorem surv_kWalk_free (g : ℕ → ℝ) (l : ℕ) : kWalk 0 0 (-1) g l = gapKeys g l := by
  simp only [kWalk]
  ring

/-- The scaled free test `φ(y) = 1_{J'}(y) G'(y) / E`. -/
def surv_freeTest (eps : ℝ) (G' : ℝ → ℝ) (E : ℝ) (y : ℝ) : ℂ :=
  (surv_J' eps).indicator (fun y => (G' y : ℂ)) y / (E : ℂ)

theorem surv_measurable_freeTest (eps : ℝ) {G' : ℝ → ℝ} (hG' : Measurable G') (E : ℝ) :
    Measurable (surv_freeTest eps G' E) :=
  ((Complex.measurable_ofReal.comp hG').indicator measurableSet_Icc).div_const _

theorem surv_norm_freeTest_le (eps : ℝ) {G' : ℝ → ℝ} {E : ℝ} (hE : 0 < E)
    (hG : ∀ y, y ≤ 9 * eps → |G' y| ≤ E) (y : ℝ) : ‖surv_freeTest eps G' E y‖ ≤ 1 := by
  unfold surv_freeTest
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE, div_le_one hE]
  by_cases hy : y ∈ surv_J' eps
  · rw [indicator_of_mem hy, Complex.norm_real, Real.norm_eq_abs]
    exact hG y hy.2
  · rw [indicator_of_notMem hy, norm_zero]
    exact hE.le

/-- **The free killed walk**: `E · kWordInt J' 0 (-1) k φ 0 g = (∏_{t ≤ k} 1_{J'}(p_t)) G'(p_k)`. -/
theorem surv_free_kWordInt (eps : ℝ) (G' : ℝ → ℝ) {E : ℝ} (hE : 0 < E) (k : ℕ) (g : ℕ → ℝ) :
    (E : ℂ) * kWordInt (surv_J' eps) 0 (-1) k (surv_freeTest eps G' E) 0 g =
      (∏ l ∈ Finset.range (k + 1), (surv_J' eps).indicator (fun _ => (1 : ℂ)) (gapKeys g l)) *
        (G' (gapKeys g k) : ℂ) := by
  have hEc : (E : ℂ) ≠ 0 := by exact_mod_cast hE.ne'
  unfold kWordInt surv_freeTest
  simp only [surv_kWalk_free]
  rw [mul_left_comm, ← mul_div_assoc, mul_div_cancel_left₀ _ hEc]
  by_cases hk : gapKeys g k ∈ surv_J' eps
  · rw [indicator_of_mem hk]
  · rw [Finset.prod_eq_zero (Finset.mem_range.2 (Nat.lt_succ_self k)) (indicator_of_notMem hk _)]
    simp

/-- Outside `LD'`, the slope-one line is admissible: `k < T`. -/
theorem surv_mem_survSet_of_not_ld' {eps : ℝ} {k : ℕ} {g : ℕ → ℝ} (h : g ∉ surv_ld' eps k) :
    g ∈ survSet eps k := by
  have hin : ∀ t ≤ k, |gapKeys g t - t| ≤ eps := by
    intro t ht
    by_contra hlt
    exact h ⟨t, ht, lt_of_not_ge hlt⟩
  show (k : ℕ∞) < gapSegLen eps g
  unfold gapSegLen
  rw [lt_segLen_iff]
  refine ⟨1, 0, fun t ht => ?_⟩
  rw [one_mul, add_zero, abs_sub_comm]
  exact hin t (by omega)

/-- Outside `LD'` and for `k ≤ 8ε`, all keys `p_t`, `t ≤ k`, lie in `J'`. -/
theorem surv_prod_free_of_not_ld' {eps : ℝ} {k : ℕ} (hk : (k : ℝ) ≤ 8 * eps) {g : ℕ → ℝ}
    (h : g ∉ surv_ld' eps k) :
    ∏ l ∈ Finset.range (k + 1), (surv_J' eps).indicator (fun _ => (1 : ℂ)) (gapKeys g l) = 1 := by
  refine Finset.prod_eq_one fun l hl => ?_
  have hl' : l ≤ k := by have := Finset.mem_range.1 hl; omega
  have hlr : (l : ℝ) ≤ k := by exact_mod_cast hl'
  have hin : |gapKeys g l - l| ≤ eps := by
    by_contra hlt
    exact h ⟨l, hl', lt_of_not_ge hlt⟩
  rw [abs_le] at hin
  have hmem : gapKeys g l ∈ surv_J' eps := by
    refine ⟨by linarith [hin.1, (Nat.cast_nonneg l : (0 : ℝ) ≤ l)], by linarith [hin.2]⟩
  rw [indicator_of_mem hmem]

/-- **Pointwise comparison of the survival integrand with the free walk**: they differ only on
`LD'`, by at most `2 |G'(p_k)| ≤ 2 e^{γ' p_k}`. -/
theorem surv_short_pt {eps : ℝ} {k : ℕ} (hk : (k : ℝ) ≤ 8 * eps) {G' : ℝ → ℝ} {γ' : ℝ}
    (hGb : ∀ y, |G' y| ≤ Real.exp (γ' * y)) {E : ℝ} (hE : 0 < E) (g : ℕ → ℝ) :
    ‖(((survSet eps k).indicator (fun g => G' (gapKeys g k)) g : ℝ) : ℂ) -
        (E : ℂ) * kWordInt (surv_J' eps) 0 (-1) k (surv_freeTest eps G' E) 0 g‖ ≤
      2 * (surv_ld' eps k).indicator (fun g => Real.exp (γ' * gapKeys g k)) g := by
  rw [surv_free_kWordInt eps G' hE k g, surv_ofReal_indicator]
  by_cases hld : g ∈ surv_ld' eps k
  · rw [indicator_of_mem hld]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖(survSet eps k).indicator (fun g => (G' (gapKeys g k) : ℂ)) g‖ ≤
        Real.exp (γ' * gapKeys g k) := by
      refine le_trans (norm_indicator_le_norm_self _ _) ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hGb _
    have h2 : ‖(∏ l ∈ Finset.range (k + 1), (surv_J' eps).indicator (fun _ => (1 : ℂ))
        (gapKeys g l)) * (G' (gapKeys g k) : ℂ)‖ ≤ Real.exp (γ' * gapKeys g k) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc _ ≤ 1 * Real.exp (γ' * gapKeys g k) :=
            mul_le_mul (surv_norm_prod_indicator_le _ _ _) (hGb _) (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    linarith
  · rw [indicator_of_notMem hld, indicator_of_mem (surv_mem_survSet_of_not_ld' hld),
      surv_prod_free_of_not_ld' hk hld, one_mul, sub_self, norm_zero, mul_zero]

theorem surv_depPrefix_short (eps : ℝ) (k : ℕ) (γ' : ℝ) :
    DepPrefix k (fun g => 2 * (surv_ld' eps k).indicator (fun g => Real.exp (γ' * gapKeys g k)) g) := by
  intro g g' hgg
  have hkeys : ∀ t ≤ k, gapKeys g t = gapKeys g' t := fun t ht =>
    Finset.sum_congr rfl fun s hs => hgg s (by have := Finset.mem_range.1 hs; omega)
  have hmem : g ∈ surv_ld' eps k ↔ g' ∈ surv_ld' eps k := by
    simp only [surv_ld', Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht, h⟩; exact ⟨t, ht, by rwa [← hkeys t ht]⟩
    · rintro ⟨t, ht, h⟩; exact ⟨t, ht, by rwa [hkeys t ht]⟩
  show 2 * (surv_ld' eps k).indicator (fun g => Real.exp (γ' * gapKeys g k)) g =
    2 * (surv_ld' eps k).indicator (fun g => Real.exp (γ' * gapKeys g k)) g'
  by_cases hg : g ∈ surv_ld' eps k
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hmem.1 hg), hkeys k le_rfl]
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hmem.2 h))]

/-- **The short-segment bound** (`1 ≤ ε`, `1 ≤ k ≤ 8ε`).  With `R` a bound on the free killed
row `kRow [-ε, 9ε] ν σ z 0 (-1) k φ 0` over tests `‖φ‖ ≤ 1`, and `ρ̃ = mixPM ν σ (surv_tz z)`,
`‖cSurv ε ν σ z k G‖ ≤ e^{9εγ'} R + (‖1-z‖ + ‖z‖)^k · 2 (2 e^{20εγ'} e^{-cε/8} + e^{-10ελ₀})`. -/
theorem surv_short_bound (ν σ : ProbabilityMeasure ℝ) (z : ℂ) {eps : ℝ} (heps : 1 ≤ eps) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : (k : ℝ) ≤ 8 * eps) (hνpos : (ν : Measure ℝ) (Iic 0) = 0)
    (hσpos : (σ : Measure ℝ) (Iic 0) = 0) {G : ℝ → ℝ} (hG : Measurable G) {γ' : ℝ} (hγ0 : 0 ≤ γ')
    (hGb : ∀ y, 0 ≤ y → |G y| ≤ Real.exp (γ' * y))
    (hint : ∀ S, Integrable (fun g => Real.exp (γ' * gapKeys g k)) (wordLaw ν σ S)) {R : ℝ}
    (hRow : ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      ‖kRow (Icc (-eps) (9 * eps)) ν σ z 0 (-1) k φ 0‖ ≤ R) {θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁)
    (hmix : (mixPM ν σ (surv_tz z) : Measure ℝ) (Iic 0) = 0 ∧ lawMean (mixPM ν σ (surv_tz z)) = 1 ∧
      ExpMom θ₁ B₁ (mixPM ν σ (surv_tz z)))
    (hγ : γ' ≤ surv_lam θ₁ B₁ / 8) :
    ‖cSurv eps ν σ z k G‖ ≤ Real.exp (γ' * (9 * eps)) * R + (‖1 - z‖ + ‖z‖) ^ k *
      (2 * (2 * Real.exp (20 * eps * γ') * Real.exp (-(bernsteinRate θ₁ B₁ * eps / 8)) +
        Real.exp (-(10 * eps * surv_lam θ₁ B₁)))) := by
  set G' := surv_Gpos G with hG'def
  have hG'm : Measurable G' := surv_measurable_Gpos hG
  have hG'b : ∀ y, |G' y| ≤ Real.exp (γ' * y) := surv_abs_Gpos_le hGb
  set E := Real.exp (γ' * (9 * eps)) with hEdef
  have hE : 0 < E := Real.exp_pos _
  have hGE : ∀ y, y ≤ 9 * eps → |G' y| ≤ E := fun y hy => surv_abs_Gpos_le_of_le hγ0 hGb y hy
  have hφm : Measurable (surv_freeTest eps G' E) := surv_measurable_freeTest eps hG'm E
  have hφ1 : ∀ y, ‖surv_freeTest eps G' E y‖ ≤ 1 := surv_norm_freeTest_le eps hE hGE
  have hJ' : MeasurableSet (surv_J' eps) := measurableSet_Icc
  -- the two integrands
  have hSm : Measurable fun g => (((survSet eps k).indicator (fun g => G' (gapKeys g k)) g : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_survInd eps k hG'm)
  have hSint : ∀ S, Integrable
      (fun g => (((survSet eps k).indicator (fun g => G' (gapKeys g k)) g : ℝ) : ℂ))
      (wordLaw ν σ S) := fun S => (hint S).mono' hSm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => by
      rw [Complex.norm_real]
      exact le_trans (norm_indicator_le_norm_self _ _) (by rw [Real.norm_eq_abs]; exact hG'b _))
  have hKm : Measurable fun g => (E : ℂ) * kWordInt (surv_J' eps) 0 (-1) k (surv_freeTest eps G' E) 0 g := by
    have h := (measurable_kWordInt_prod hJ' 0 (-1) k hφm).comp
      ((measurable_const (a := (0 : ℝ))).prodMk (measurable_id (α := ℕ → ℝ)))
    exact measurable_const.mul h
  have hKint : ∀ S, Integrable
      (fun g => (E : ℂ) * kWordInt (surv_J' eps) 0 (-1) k (surv_freeTest eps G' E) 0 g)
      (wordLaw ν σ S) := fun S => (integrable_const E).mono' hKm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE]
      exact mul_le_of_le_one_right hE.le (norm_kWordInt_le 0 (-1) k hφ1 0 g))
  -- the main term is the free row
  have hmain : surv_wint ν σ z k
      (fun g => (E : ℂ) * kWordInt (surv_J' eps) 0 (-1) k (surv_freeTest eps G' E) 0 g) =
        (E : ℂ) * kRow (surv_J' eps) ν σ z 0 (-1) k (surv_freeTest eps G' E) 0 := by
    rw [surv_wint_const_mul, surv_kRow_eq_wint hJ' ν σ z 0 (-1) hφm hφ1 k 0]
  -- decomposition
  rw [surv_cSurv_eq_wint]
  have e1 : surv_wint ν σ z k
      (fun g => (((survSet eps k).indicator (fun g => G (gapKeys g k)) g : ℝ) : ℂ)) =
      surv_wint ν σ z k
        (fun g => (((survSet eps k).indicator (fun g => G' (gapKeys g k)) g : ℝ) : ℂ)) :=
    surv_wint_congr ν σ z k fun S _ => (cert_ae_pos_wordLaw hνpos hσpos S).mono fun g hg => by
      rw [surv_survInd_eq_Gpos eps k G hg]
  have e2 : surv_wint ν σ z k
      (fun g => (((survSet eps k).indicator (fun g => G' (gapKeys g k)) g : ℝ) : ℂ)) =
      surv_wint ν σ z k (fun g => (((survSet eps k).indicator (fun g => G' (gapKeys g k)) g : ℝ) : ℂ) -
        (E : ℂ) * kWordInt (surv_J' eps) 0 (-1) k (surv_freeTest eps G' E) 0 g) +
      surv_wint ν σ z k
        (fun g => (E : ℂ) * kWordInt (surv_J' eps) 0 (-1) k (surv_freeTest eps G' E) 0 g) := by
    rw [surv_wint_sub ν σ z k hSint hKint, sub_add_cancel]
  rw [e1, e2, hmain]
  refine (norm_add_le _ _).trans ?_
  rw [add_comm]
  refine add_le_add ?_ ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE]
    exact mul_le_mul_of_nonneg_left (hRow _ hφm hφ1) hE.le
  · have hH'm : Measurable fun g =>
        2 * (surv_ld' eps k).indicator (fun g => Real.exp (γ' * gapKeys g k)) g :=
      measurable_const.mul ((((rawAsm_measurable_gapKeys k).const_mul γ').exp).indicator
        (surv_measurableSet_ld' eps k))
    have hH'int : ∀ S, Integrable
        (fun g => 2 * (surv_ld' eps k).indicator (fun g => Real.exp (γ' * gapKeys g k)) g)
        (wordLaw ν σ S) := fun S => ((hint S).indicator (surv_measurableSet_ld' eps k)).const_mul 2
    have hle : ∀ S, ∀ᵐ g ∂(wordLaw ν σ S),
        ‖(((survSet eps k).indicator (fun g => G' (gapKeys g k)) g : ℝ) : ℂ) -
          (E : ℂ) * kWordInt (surv_J' eps) 0 (-1) k (surv_freeTest eps G' E) 0 g‖ ≤
            2 * (surv_ld' eps k).indicator (fun g => Real.exp (γ' * gapKeys g k)) g := fun S =>
      Filter.Eventually.of_forall fun g => surv_short_pt hk hG'b hE g
    refine (surv_norm_wint_le_mix ν σ z k hH'm (surv_depPrefix_short eps k γ') hH'int hle).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [integral_const_mul]
    obtain ⟨hpos, hmean, hexp⟩ := hmix
    exact mul_le_mul_of_nonneg_left
      (surv_short_integral_le hθ₁ hpos hmean hexp heps hk1 hk hγ0 hγ) (by norm_num)

end

end PGM
