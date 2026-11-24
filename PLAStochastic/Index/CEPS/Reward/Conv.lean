import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.ExpRenewal
import Mathlib.Topology.Algebra.Order.Floor

/-!
# CEPS W-6: half-line convolution algebra

Functions on `ℝ` vanishing on `(-∞, 0)` and bounded on every `(-∞, X]` (`HalfBdd`) form a
convolution algebra under `convC f h x = ∫ f(y) h(x - y) dy`:

* `convC_comm`, `convC_assoc`, `convC_add_right`, `convC_sub_right`;
* `HalfBdd.convC`, `halfBdd_renewalDensity`: closure, and the renewal density of an
  exponential density is half-line bounded;
* `renewalDensity_eq_add_convC`: `u = g + g ⋆ u`;
* `eq_zero_of_eq_convC`: uniqueness for the renewal equation `δ = g ⋆ δ` on `[0, ∞)`
  (Gronwall iteration `‖δ(x)‖ ≤ M Dⁿ xⁿ/n!`).
-/

noncomputable section

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal Nat

namespace PGM.WienerHopf

/-- Measurable, zero on `(-∞, 0)` and bounded on every half-line `(-∞, X]`. -/
structure HalfBdd (f : ℝ → ℂ) : Prop where
  measurable : Measurable f
  eq_zero : ∀ y, y < 0 → f y = 0
  bdd : ∀ X : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ y, y ≤ X → ‖f y‖ ≤ M

/-- The restriction to `[0, ∞)`. -/
def halfLine (b : ℝ → ℂ) : ℝ → ℂ := (Ici (0 : ℝ)).indicator b

theorem halfLine_of_nonneg (b : ℝ → ℂ) {x : ℝ} (hx : 0 ≤ x) : halfLine b x = b x :=
  indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx) _

theorem halfLine_of_neg (b : ℝ → ℂ) {x : ℝ} (hx : x < 0) : halfLine b x = 0 :=
  indicator_of_notMem (show x ∉ Ici (0 : ℝ) from not_le.mpr hx) _

theorem halfBdd_halfLine {b : ℝ → ℂ} (hb : Measurable b)
    (hB : ∀ X : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ y, 0 ≤ y → y ≤ X → ‖b y‖ ≤ M) : HalfBdd (halfLine b) := by
  refine ⟨hb.indicator measurableSet_Ici, fun y hy => halfLine_of_neg b hy, fun X => ?_⟩
  obtain ⟨M, hM0, hM⟩ := hB X
  refine ⟨M, hM0, fun y hy => ?_⟩
  rcases lt_or_ge y 0 with h | h
  · rw [halfLine_of_neg b h, norm_zero]; exact hM0
  · rw [halfLine_of_nonneg b h]; exact hM y h hy

theorem IsExpDensity.halfBdd {g : ℝ → ℂ} {D θ : ℝ} (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ) :
    HalfBdd g :=
  ⟨hg.measurable, fun y hy => hg.eq_zero_of_nonpos y hy.le,
    fun _ => ⟨D, hg.nonneg_D, fun y _ => hg.norm_le_D hθ y⟩⟩

namespace HalfBdd

variable {f h k : ℝ → ℂ}

theorem add (hf : HalfBdd f) (hh : HalfBdd h) : HalfBdd (f + h) := by
  refine ⟨hf.measurable.add hh.measurable, fun y hy => by
    simp [hf.eq_zero y hy, hh.eq_zero y hy], fun X => ?_⟩
  obtain ⟨M, hM0, hM⟩ := hf.bdd X
  obtain ⟨N, hN0, hN⟩ := hh.bdd X
  exact ⟨M + N, by positivity, fun y hy => (norm_add_le _ _).trans (add_le_add (hM y hy) (hN y hy))⟩

theorem sub (hf : HalfBdd f) (hh : HalfBdd h) : HalfBdd (f - h) := by
  refine ⟨hf.measurable.sub hh.measurable, fun y hy => by
    simp [hf.eq_zero y hy, hh.eq_zero y hy], fun X => ?_⟩
  obtain ⟨M, hM0, hM⟩ := hf.bdd X
  obtain ⟨N, hN0, hN⟩ := hh.bdd X
  exact ⟨M + N, by positivity, fun y hy => (norm_sub_le _ _).trans (add_le_add (hM y hy) (hN y hy))⟩

theorem const_mul (hf : HalfBdd f) (c : ℂ) : HalfBdd fun y => c * f y := by
  refine ⟨measurable_const.mul hf.measurable, fun y hy => by simp [hf.eq_zero y hy], fun X => ?_⟩
  obtain ⟨M, hM0, hM⟩ := hf.bdd X
  exact ⟨‖c‖ * M, by positivity, fun y hy => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hM y hy) (norm_nonneg _)⟩

/-- The convolution integrand is bounded by `M N` on `[0, x]` and vanishes elsewhere. -/
theorem norm_convC_integrand_le (hf : HalfBdd f) (hh : HalfBdd h) {x M N : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y, y ≤ x → ‖f y‖ ≤ M) (hN : ∀ y, y ≤ x → ‖h y‖ ≤ N) (y : ℝ) :
    ‖f y * h (x - y)‖ ≤ (Icc 0 x).indicator (fun _ => M * N) y := by
  by_cases hy : y ∈ Icc 0 x
  · rw [indicator_of_mem hy, norm_mul]
    exact mul_le_mul (hM y hy.2) (hN _ (by linarith [hy.1])) (norm_nonneg _) hM0
  · rw [indicator_of_notMem hy]
    simp only [mem_Icc, not_and_or, not_le] at hy
    rcases hy with hy | hy
    · rw [hf.eq_zero y hy, zero_mul, norm_zero]
    · rw [hh.eq_zero (x - y) (by linarith), mul_zero, norm_zero]

theorem integrable_convC_integrand (hf : HalfBdd f) (hh : HalfBdd h) (x : ℝ) :
    Integrable fun y => f y * h (x - y) := by
  obtain ⟨M, hM0, hM⟩ := hf.bdd x
  obtain ⟨N, hN0, hN⟩ := hh.bdd x
  refine Integrable.mono' ((integrableOn_const (C := M * N) (s := Icc 0 x)
    (μ := volume) (isCompact_Icc.measure_lt_top.ne)).integrable_indicator measurableSet_Icc)
    (hf.measurable.mul (hh.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    (Eventually.of_forall fun y => hf.norm_convC_integrand_le hh hM0 hM hN y)

theorem norm_convC_le (hf : HalfBdd f) (hh : HalfBdd h) {x M N : ℝ} (hx : 0 ≤ x) (hM0 : 0 ≤ M)
    (hM : ∀ y, y ≤ x → ‖f y‖ ≤ M) (hN : ∀ y, y ≤ x → ‖h y‖ ≤ N) :
    ‖convC f h x‖ ≤ M * N * x := by
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN x le_rfl)
  calc ‖convC f h x‖ ≤ ∫ y, ‖f y * h (x - y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (Icc 0 x).indicator (fun _ => M * N) y :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          ((integrableOn_const (C := M * N) (s := Icc 0 x)
            (μ := volume) (isCompact_Icc.measure_lt_top.ne)).integrable_indicator measurableSet_Icc)
          (Eventually.of_forall fun y => hf.norm_convC_integrand_le hh hM0 hM hN y)
    _ = M * N * x := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc_of_le hx,
          smul_eq_mul]
        ring

theorem convC (hf : HalfBdd f) (hh : HalfBdd h) : HalfBdd (PGM.WienerHopf.convC f h) := by
  refine ⟨measurable_convC hf.measurable hh.measurable, fun x hx => ?_, fun X => ?_⟩
  · unfold PGM.WienerHopf.convC
    have : (fun y => f y * h (x - y)) = fun _ => 0 := by
      funext y
      rcases lt_or_ge y 0 with hy | hy
      · rw [hf.eq_zero y hy, zero_mul]
      · rw [hh.eq_zero (x - y) (by linarith), mul_zero]
    rw [this, integral_zero]
  · obtain ⟨M, hM0, hM⟩ := hf.bdd X
    obtain ⟨N, hN0, hN⟩ := hh.bdd X
    refine ⟨M * N * max X 0, by positivity, fun x hx => ?_⟩
    rcases lt_or_ge x 0 with hx0 | hx0
    · have : PGM.WienerHopf.convC f h x = 0 := by
        unfold PGM.WienerHopf.convC
        have : (fun y => f y * h (x - y)) = fun _ => 0 := by
          funext y
          rcases lt_or_ge y 0 with hy | hy
          · rw [hf.eq_zero y hy, zero_mul]
          · rw [hh.eq_zero (x - y) (by linarith), mul_zero]
        rw [this, integral_zero]
      rw [this, norm_zero]; positivity
    · calc ‖PGM.WienerHopf.convC f h x‖ ≤ M * N * x :=
            hf.norm_convC_le hh hx0 hM0 (fun y hy => hM y (hy.trans hx))
              (fun y hy => hN y (hy.trans hx))
        _ ≤ M * N * max X 0 := by
            gcongr
            exact le_max_of_le_left hx

theorem convC_eq_zero_of_neg (hf : HalfBdd f) (hh : HalfBdd h) {x : ℝ} (hx : x < 0) :
    PGM.WienerHopf.convC f h x = 0 := (hf.convC hh).eq_zero x hx

end HalfBdd

variable {f h k : ℝ → ℂ}

/-- Convolution is commutative. -/
theorem convC_comm (f h : ℝ → ℂ) (x : ℝ) : convC f h x = convC h f x := by
  unfold convC
  rw [← integral_sub_left_eq_self (fun y => f y * h (x - y)) volume x]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [sub_sub_cancel]
  ring

theorem convC_add_right (hf : HalfBdd f) (hh : HalfBdd h) (hk : HalfBdd k) (x : ℝ) :
    convC f (h + k) x = convC f h x + convC f k x := by
  unfold convC
  rw [← integral_add (hf.integrable_convC_integrand hh x) (hf.integrable_convC_integrand hk x)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply]
  ring

theorem convC_sub_right (hf : HalfBdd f) (hh : HalfBdd h) (hk : HalfBdd k) (x : ℝ) :
    convC f (h - k) x = convC f h x - convC f k x := by
  unfold convC
  rw [← integral_sub (hf.integrable_convC_integrand hh x) (hf.integrable_convC_integrand hk x)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Pi.sub_apply]
  ring

theorem convC_congr_right {h₁ h₂ : ℝ → ℂ} (heq : ∀ y, 0 ≤ y → h₁ y = h₂ y)
    (_hf : ∀ y, y < 0 → f y = 0)
    (hh₁ : ∀ y, y < 0 → h₁ y = 0) (hh₂ : ∀ y, y < 0 → h₂ y = 0)
    (x : ℝ) : convC f h₁ x = convC f h₂ x := by
  unfold convC
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  by_cases hy : y ≤ x
  · rw [heq (x - y) (by linarith)]
  · rw [hh₁ (x - y) (by linarith), hh₂ (x - y) (by linarith)]

/-- **Associativity** of the half-line convolution. -/
theorem convC_assoc (hf : HalfBdd f) (hh : HalfBdd h) (hk : HalfBdd k) (x : ℝ) :
    convC f (convC h k) x = convC (convC f h) k x := by
  obtain ⟨Mf, hMf0, hMf⟩ := hf.bdd x
  obtain ⟨Mh, hMh0, hMh⟩ := hh.bdd x
  obtain ⟨Mk, hMk0, hMk⟩ := hk.bdd x
  set Φ : ℝ × ℝ → ℂ := fun p => f p.1 * h (p.2 - p.1) * k (x - p.2) with hΦdef
  have hΦm : Measurable Φ :=
    ((hf.measurable.comp measurable_fst).mul (hh.measurable.comp
      (measurable_snd.sub measurable_fst))).mul
      (hk.measurable.comp (measurable_const.sub measurable_snd))
  have hΦb : ∀ p, ‖Φ p‖ ≤ (Icc 0 x ×ˢ Icc 0 x).indicator (fun _ => Mf * Mh * Mk) p := by
    intro p
    by_cases h1 : p.1 < 0
    · simp only [Φ, hf.eq_zero _ h1, zero_mul, norm_zero]
      exact indicator_nonneg (fun _ _ => by positivity) _
    by_cases h2 : p.2 - p.1 < 0
    · simp only [Φ, hh.eq_zero _ h2, mul_zero, zero_mul, norm_zero]
      exact indicator_nonneg (fun _ _ => by positivity) _
    by_cases h3 : x - p.2 < 0
    · simp only [Φ, hk.eq_zero _ h3, mul_zero, norm_zero]
      exact indicator_nonneg (fun _ _ => by positivity) _
    push Not at h1 h2 h3
    have hp : p ∈ Icc 0 x ×ˢ Icc 0 x :=
      ⟨⟨h1, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    rw [indicator_of_mem hp]
    simp only [Φ, norm_mul]
    have a1 := hMf p.1 (by linarith)
    have a2 := hMh (p.2 - p.1) (by linarith)
    have a3 := hMk (x - p.2) (by linarith)
    have := mul_le_mul a1 a2 (norm_nonneg _) hMf0
    exact mul_le_mul this a3 (norm_nonneg _) (by positivity)
  have hΦi : Integrable Φ (volume.prod volume) := by
    refine Integrable.mono' ?_ hΦm.aestronglyMeasurable (Eventually.of_forall hΦb)
    refine (integrableOn_const (C := Mf * Mh * Mk) (s := Icc 0 x ×ˢ Icc 0 x)
      (μ := volume.prod volume) ?_).integrable_indicator (measurableSet_Icc.prod measurableSet_Icc)
    exact ((isCompact_Icc.prod isCompact_Icc).measure_lt_top).ne
  have hswap := integral_integral_swap (f := fun w y => Φ (y, w)) (μ := volume) (ν := volume)
    (by exact hΦi.swap)
  calc convC f (convC h k) x = ∫ y, ∫ w, Φ (y, w) := by
        unfold convC
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [Φ]
        rw [← integral_const_mul, ← integral_add_right_eq_self
          (fun w => f y * h (w - y) * k (x - w)) y]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [add_sub_cancel_right]
        rw [show x - (z + y) = x - y - z by ring]; ring
    _ = ∫ w, ∫ y, Φ (y, w) := hswap.symm
    _ = convC (convC f h) k x := by
        unfold convC
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        simp only [Φ]
        rw [← integral_mul_const]

/-! ### The renewal density -/

variable {g : ℝ → ℂ} {D θ : ℝ}

theorem renewalDensity_eq_zero_of_nonpos (hg : IsExpDensity g D θ) {x : ℝ} (hx : x ≤ 0) :
    renewalDensity g x = 0 := by
  unfold renewalDensity
  simp [convPow_eq_zero_of_nonpos hg _ hx]

theorem measurable_renewalDensity (hg : IsExpDensity g D θ) : Measurable (renewalDensity g) := by
  have : renewalDensity g = g + renewalTail g := funext (renewalDensity_eq_add_tail hg)
  rw [this]
  exact hg.measurable.add (measurable_renewalTail hg)

/-- `‖u(y)‖ ≤ D e^{D max X 0}` for `y ≤ X`. -/
theorem norm_renewalDensity_le_of_le (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ) {y X : ℝ}
    (hyX : y ≤ X) : ‖renewalDensity g y‖ ≤ D * Real.exp (D * max X 0) := by
  have hD := hg.nonneg_D
  have hs : Summable fun n : ℕ => D ^ (n + 1) * (max X 0) ^ n / n ! := by
    have := (Real.summable_pow_div_factorial (D * max X 0)).mul_left D
    refine this.congr fun n => ?_
    rw [mul_pow]; ring
  have hle : ∀ n, ‖convPow g n y‖ ≤ D ^ (n + 1) * (max X 0) ^ n / n ! :=
    fun n => norm_convPow_le_of_le hg hθ n hyX
  calc ‖renewalDensity g y‖ ≤ ∑' n, ‖convPow g n y‖ :=
        norm_tsum_le_tsum_norm (summable_norm_convPow hg y)
    _ ≤ ∑' n : ℕ, D ^ (n + 1) * (max X 0) ^ n / n ! :=
        (summable_norm_convPow hg y).tsum_le_tsum hle hs
    _ = D * Real.exp (D * max X 0) := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div, ← tsum_mul_left]
        refine tsum_congr fun n => ?_
        rw [mul_pow]; ring

theorem halfBdd_renewalDensity (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ) :
    HalfBdd (renewalDensity g) :=
  ⟨measurable_renewalDensity hg, fun _y hy => renewalDensity_eq_zero_of_nonpos hg hy.le,
    fun X => ⟨D * Real.exp (D * max X 0), mul_nonneg hg.nonneg_D (Real.exp_pos _).le,
      fun _y hy => norm_renewalDensity_le_of_le hg hθ hy⟩⟩

/-- **`u = g + g ⋆ u`.** -/
theorem renewalDensity_eq_add_convC (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ) (x : ℝ) :
    renewalDensity g x = g x + convC g (renewalDensity g) x := by
  have hD := hg.nonneg_D
  rw [renewalDensity_eq_add_tail hg]
  congr 1
  set m := max x 0
  set F : ℕ → ℝ → ℂ := fun n y => g y * convPow g n (x - y)
  have hgB : HalfBdd g := hg.halfBdd hθ
  have hPB : ∀ n, HalfBdd (convPow g n) := fun n =>
    ⟨measurable_convPow hg n, fun y hy => convPow_eq_zero_of_nonpos hg n hy.le,
      fun X => ⟨D ^ (n + 1) * (max X 0) ^ n / n !, by positivity,
        fun y hy => norm_convPow_le_of_le hg hθ n hy⟩⟩
  have hFi : ∀ n, Integrable (F n) := fun n => hgB.integrable_convC_integrand (hPB n) x
  have hFn : ∀ n, ∫ y, ‖F n y‖ ≤ D * (D ^ (n + 1) * m ^ n / n !) * m := by
    intro n
    rcases lt_or_ge x 0 with hx | hx
    · have : ∀ y, F n y = 0 := by
        intro y
        simp only [F]
        rcases le_or_gt y 0 with hy | hy
        · rw [hg.eq_zero_of_nonpos y hy, zero_mul]
        · rw [convPow_eq_zero_of_nonpos hg n (by linarith), mul_zero]
      simp only [this, norm_zero, integral_zero]
      positivity
    · have hm : m = x := max_eq_left hx
      have hb : ∀ y, ‖F n y‖ ≤ (Icc 0 x).indicator (fun _ => D * (D ^ (n + 1) * m ^ n / n !)) y :=
        hgB.norm_convC_integrand_le (hPB n) hD (fun y _ => hg.norm_le_D hθ y)
          (fun y hy => norm_convPow_le_of_le hg hθ n hy)
      calc ∫ y, ‖F n y‖ ≤ ∫ y, (Icc 0 x).indicator (fun _ => D * (D ^ (n + 1) * m ^ n / n !)) y :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              ((integrableOn_const (s := Icc 0 x) (μ := volume) (isCompact_Icc.measure_lt_top.ne)).integrable_indicator
                measurableSet_Icc) (Eventually.of_forall hb)
        _ = _ := by
            rw [integral_indicator measurableSet_Icc, setIntegral_const,
              Real.volume_real_Icc_of_le hx, smul_eq_mul, hm]
            ring
  have hFs : Summable fun n => ∫ y, ‖F n y‖ := by
    refine Summable.of_nonneg_of_le (fun _n => integral_nonneg fun _ => norm_nonneg _) hFn ?_
    have := ((Real.summable_pow_div_factorial (D * m)).mul_left (D * D * m))
    refine this.congr fun n => ?_
    rw [mul_pow]; ring
  calc renewalTail g x = ∑' n, ∫ y, F n y := by
        unfold renewalTail
        exact tsum_congr fun n => rfl
    _ = ∫ y, ∑' n, F n y := integral_tsum_of_summable_integral_norm hFi hFs
    _ = convC g (renewalDensity g) x := by
        unfold convC renewalDensity
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [F]
        rw [tsum_mul_left]

/-- **Uniqueness for the renewal equation.** If `δ` is half-line bounded and `δ = g ⋆ δ` on
`[0, ∞)`, then `δ = 0`. -/
theorem eq_zero_of_eq_convC (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ) {δ : ℝ → ℂ} (hδ : HalfBdd δ)
    (heq : ∀ x, 0 ≤ x → δ x = convC g δ x) (x : ℝ) : δ x = 0 := by
  rcases lt_or_ge x 0 with hx | hx
  · exact hδ.eq_zero x hx
  have hD := hg.nonneg_D
  obtain ⟨M, hM0, hM⟩ := hδ.bdd x
  have key : ∀ n : ℕ, ∀ y, 0 ≤ y → y ≤ x → ‖δ y‖ ≤ M * ((D * y) ^ n / n !) := by
    intro n
    induction n with
    | zero => intro y _ hy; simpa using hM y hy
    | succ n ih =>
      intro y hy0 hyx
      set B : ℝ → ℝ := (Ioc 0 y).indicator fun z => D * (M * ((D * (y - z)) ^ n / n !))
      have hpt : ∀ z, ‖g z * δ (y - z)‖ ≤ B z := by
        intro z
        by_cases hz : z ∈ Ioc 0 y
        · rw [show B z = D * (M * ((D * (y - z)) ^ n / n !)) from indicator_of_mem hz _, norm_mul]
          exact mul_le_mul (hg.norm_le_D hθ z) (ih (y - z) (by linarith [hz.2])
            (by linarith [hz.1])) (norm_nonneg _) hD
        · rw [show B z = 0 from indicator_of_notMem hz _]
          simp only [mem_Ioc, not_and_or, not_lt, not_le] at hz
          rcases hz with hz | hz
          · rw [hg.eq_zero_of_nonpos z hz, zero_mul, norm_zero]
          · rw [hδ.eq_zero (y - z) (by linarith), mul_zero, norm_zero]
      have hBi : Integrable B := by
        refine IntegrableOn.integrable_indicator ?_ measurableSet_Ioc
        exact ((by fun_prop : Continuous fun z : ℝ =>
          D * (M * ((D * (y - z)) ^ n / n !))).integrableOn_Icc).mono_set Ioc_subset_Icc_self
      calc ‖δ y‖ = ‖convC g δ y‖ := by rw [← heq y hy0]
        _ ≤ ∫ z, ‖g z * δ (y - z)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ z, B z := integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            hBi (Eventually.of_forall hpt)
        _ = D * M * D ^ n / n ! * ∫ z in Ioc 0 y, (y - z) ^ n := by
            rw [integral_indicator measurableSet_Ioc, ← integral_const_mul]
            refine integral_congr_ae (Eventually.of_forall fun z => ?_)
            simp only
            rw [mul_pow]; ring
        _ = M * ((D * y) ^ (n + 1) / (n + 1)!) := by
            rw [integral_Ioc_eq_integral_Ioo, integral_Ioo_sub_pow y hy0 n, Nat.factorial_succ]
            push_cast
            rw [mul_pow]
            field_simp
            ring
  have hlim : Tendsto (fun n : ℕ => M * ((D * x) ^ n / n !)) atTop (𝓝 (M * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop (D * x)).const_mul M
  rw [mul_zero] at hlim
  have h0 : ‖δ x‖ ≤ 0 := ge_of_tendsto' hlim fun n => key n x hx le_rfl
  exact norm_le_zero_iff.mp h0

end PGM.WienerHopf
