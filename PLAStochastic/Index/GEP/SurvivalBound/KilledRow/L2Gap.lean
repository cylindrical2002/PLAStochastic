import PLAStochastic.ForMathlib.Analysis.Fourier.AffineMeasureConvolution
import PLAStochastic.Index.GEP.SurvivalBound.KilledRow.Defs

/-!
# WP4 `SurvivalBound`: the killed `L²` gap of `kStepZ`

Source: `research/2026-09-28-gep-closure/analytic-response-tools.md` §2 (命题 2);
`rawdisc-design.md` §2.1.

The killed step is `kStepZ J ν σ z β a u = 1_J · w` with `w = (1 - z) kConv ν + z kConv σ`
(`kStepZ_eq_indicator`).  By `fourier_kConv`, `𝓕 w ξ = e^{2πiξβ} m(ξ) 𝓕 u ξ` with the multiplier
`m(ξ) = kMult ν σ z a ξ = (1 - z) charFun ν (-2πaξ) + z charFun σ (-2πaξ)`, so Plancherel gives

`∫ ‖kStepZ u‖² ≤ ∫ ‖w‖² = ∫ ‖m‖² ‖𝓕 u‖²` (`integral_norm_kStepZ_sq_le_mult`).

* Only `‖m‖ ≤ 1` known: `∫ ‖kStepZ u‖² ≤ ∫ ‖u‖²` (`integral_norm_kStepZ_sq_le`).
* **Gap** (`integral_norm_kStepZ_sq_le_gap`): if `‖(1-z) φ_ν(t) + z φ_σ(t)‖² ≤ 1 - c min(t², 1)`,
  `J = [α, α + w]`, `w ≥ 1`, `|a| ≥ a₀ > 0` and `u` is supported in `J`, then
  `∫ ‖kStepZ u‖² ≤ (1 - c₁/w²) ∫ ‖u‖²` with `c₁ = killGapConst c a₀ = c min(π²a₀²/4, 1)/2`.
  Low frequencies `|ξ| ≤ δ = 1/(4w)`: `‖𝓕 u ξ‖² ≤ (∫ ‖u‖)² ≤ w ∫ ‖u‖²` (Cauchy–Schwarz on `J`),
  so they carry at most half of `∫ ‖𝓕 u‖² = ∫ ‖u‖²`; at `|ξ| > δ`,
  `min(4π²a²ξ², 1) ≥ min(π²a₀²/4, 1)/w²`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory FourierTransform Complex Set
open scoped Real

/-- The Fourier multiplier of the killed step,
`m(ξ) = (1 - z) charFun ν (-2πaξ) + z charFun σ (-2πaξ)`. -/
def kMult (ν σ : Measure ℝ) (z : ℂ) (a ξ : ℝ) : ℂ :=
  (1 - z) * charFun ν (-(2 * π * a * ξ)) + z * charFun σ (-(2 * π * a * ξ))

/-- The gap constant `c₁ = c min(π²a₀²/4, 1)/2` of the killed step. -/
def killGapConst (c a₀ : ℝ) : ℝ := c * min (π ^ 2 * a₀ ^ 2 / 4) 1 / 2

theorem killGapConst_pos {c a₀ : ℝ} (hc : 0 < c) (ha₀ : 0 < a₀) : 0 < killGapConst c a₀ := by
  unfold killGapConst
  have : 0 < min (π ^ 2 * a₀ ^ 2 / 4) 1 := lt_min (by positivity) one_pos
  positivity

/-- The killed step is the indicator of the untruncated combination. -/
theorem kStepZ_eq_indicator (J : Set ℝ) (ν σ : Measure ℝ) (z : ℂ) (β a : ℝ) (u : ℝ → ℂ) :
    kStepZ J ν σ z β a u =
      J.indicator (fun y => (1 - z) * kConv ν β a u y + z * kConv σ β a u y) := by
  funext y
  unfold kStepZ kStep
  by_cases hy : y ∈ J
  · simp only [indicator_of_mem hy, kConv]
  · simp only [indicator_of_notMem hy, mul_zero, add_zero]

/-- Linearity of the integral transform on integrable functions. -/
theorem kill_fourier_lin {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (c d : ℂ)
    (ξ : ℝ) : 𝓕 (fun y => c * f y + d * g y) ξ = c * 𝓕 f ξ + d * 𝓕 g ξ := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  have hE : ∀ {h : ℝ → ℂ}, Integrable h →
      Integrable (fun v : ℝ => Complex.exp (↑(-2 * π * v * ξ) * I) * h v) := by
    intro h hh
    refine hh.norm.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact (Continuous.aestronglyMeasurable (by fun_prop)).mul hh.aestronglyMeasurable
    · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have e : (fun v : ℝ => Complex.exp (↑(-2 * π * v * ξ) * I) * (c * f v + d * g v)) =
      fun v => c * (Complex.exp (↑(-2 * π * v * ξ) * I) * f v) +
        d * (Complex.exp (↑(-2 * π * v * ξ) * I) * g v) := by
    funext v; ring
  rw [e, integral_add ((hE hf).const_mul c) ((hE hg).const_mul d), integral_const_mul,
    integral_const_mul]

variable {J : Set ℝ} {ν σ : Measure ℝ} {z : ℂ} {β a : ℝ} {u : ℝ → ℂ}

/-- **Fourier side of the killed step.**  `∫ ‖kStepZ u‖² ≤ ∫ ‖m‖² ‖𝓕 u‖²` for finite `ν, σ`,
any `J` and `u` measurable in `L¹ ∩ L²`. -/
theorem integral_norm_kStepZ_sq_le_mult [IsFiniteMeasure ν]
    [IsFiniteMeasure σ] (hu : Measurable u) (h1 : Integrable u) (h2 : MemLp u 2) :
    ∫ y, ‖kStepZ J ν σ z β a u y‖ ^ 2 ≤ ∫ ξ, ‖kMult ν σ z a ξ‖ ^ 2 * ‖𝓕 u ξ‖ ^ 2 := by
  set w : ℝ → ℂ := fun y => (1 - z) * kConv ν β a u y + z * kConv σ β a u y with hw
  have hν1 := integrable_kConv ν hu h1 β a
  have hσ1 := integrable_kConv σ hu h1 β a
  have hw1 : Integrable w := (hν1.const_mul _).add (hσ1.const_mul _)
  have hw2 : MemLp w 2 :=
    ((memLp_two_kConv ν hu h1 h2 β a).1.const_mul _).add
      ((memLp_two_kConv σ hu h1 h2 β a).1.const_mul _)
  have hwm : Measurable w :=
    ((measurable_kConv ν hu β a).const_mul _).add ((measurable_kConv σ hu β a).const_mul _)
  have hwsq : Integrable (fun y => ‖w y‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hwm.aestronglyMeasurable).1 hw2
  have hind : ∫ y, ‖kStepZ J ν σ z β a u y‖ ^ 2 ≤ ∫ y, ‖w y‖ ^ 2 := by
    rw [kStepZ_eq_indicator]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity) hwsq
      (Filter.Eventually.of_forall fun y => ?_)
    simp only
    gcongr
    exact norm_indicator_le_norm_self _ _
  have hF : ∀ ξ, 𝓕 w ξ = Complex.exp (↑(2 * π * ξ * β) * I) * kMult ν σ z a ξ * 𝓕 u ξ := by
    intro ξ
    rw [hw, kill_fourier_lin hν1 hσ1, fourier_kConv ν hu h1, fourier_kConv σ hu h1, kMult]
    ring
  have hFn : ∀ ξ, ‖𝓕 w ξ‖ ^ 2 = ‖kMult ν σ z a ξ‖ ^ 2 * ‖𝓕 u ξ‖ ^ 2 := by
    intro ξ
    rw [hF, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, mul_pow]
  calc ∫ y, ‖kStepZ J ν σ z β a u y‖ ^ 2 ≤ ∫ y, ‖w y‖ ^ 2 := hind
    _ = ∫ ξ, ‖𝓕 w ξ‖ ^ 2 := (plancherel_integrable_memLp hw1 hw2).symm
    _ = ∫ ξ, ‖kMult ν σ z a ξ‖ ^ 2 * ‖𝓕 u ξ‖ ^ 2 := by simp only [hFn]

/-- **Killed step, coefficient one.**  If `‖(1 - z) φ_ν(t) + z φ_σ(t)‖ ≤ 1` for all `t`, then
`∫ ‖kStepZ u‖² ≤ ∫ ‖u‖²` for `u` measurable in `L¹ ∩ L²`. -/
theorem integral_norm_kStepZ_sq_le [IsFiniteMeasure ν]
    [IsFiniteMeasure σ] (hm : ∀ t : ℝ, ‖(1 - z) * charFun ν t + z * charFun σ t‖ ≤ 1)
    (hu : Measurable u) (h1 : Integrable u) (h2 : MemLp u 2) :
    ∫ y, ‖kStepZ J ν σ z β a u y‖ ^ 2 ≤ ∫ y, ‖u y‖ ^ 2 := by
  refine (integral_norm_kStepZ_sq_le_mult (J := J) (z := z) (β := β) (a := a) hu h1 h2).trans ?_
  rw [← plancherel_integrable_memLp h1 h2]
  have hFsq : Integrable (fun ξ => ‖𝓕 u ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm
      (kill_continuous_fourier h1).aestronglyMeasurable).1 (kill_memLp_two_fourier h1 h2)
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => by positivity) hFsq
    (Filter.Eventually.of_forall fun ξ => ?_)
  have h := hm (-(2 * π * a * ξ))
  have h0 := norm_nonneg (kMult ν σ z a ξ)
  have hk : ‖kMult ν σ z a ξ‖ ^ 2 ≤ 1 := by
    unfold kMult; nlinarith [norm_nonneg ((1 - z) * charFun ν (-(2 * π * a * ξ)) +
      z * charFun σ (-(2 * π * a * ξ)))]
  simp only
  nlinarith [sq_nonneg ‖𝓕 u ξ‖]

/-- A square-integrable function supported in a set of finite measure is integrable. -/
theorem kill_integrable_of_support {s : Set ℝ} (hs : volume s ≠ ⊤)
    (hsupp : ∀ y, y ∉ s → u y = 0) (h2 : MemLp u 2) : Integrable u := by
  have hsub : Function.support u ⊆ s := by
    intro y hy
    by_contra h
    exact hy (hsupp y h)
  rw [← integrableOn_iff_integrable_of_support_subset hsub]
  have : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.2 hs
  exact (h2.restrict s).integrable one_le_two

/-- Cauchy–Schwarz on an interval: `(∫ ‖u‖)² ≤ w ∫ ‖u‖²` for `u` supported in `[α, α + w]`. -/
theorem kill_sq_integral_norm_le {α w : ℝ} (hw : 0 ≤ w)
    (hsupp : ∀ y, y ∉ Icc α (α + w) → u y = 0) (h1 : Integrable u)
    (h2 : Integrable (fun y => ‖u y‖ ^ 2)) :
    (∫ y, ‖u y‖) ^ 2 ≤ w * ∫ y, ‖u y‖ ^ 2 := by
  have hs1 : ∫ y, ‖u y‖ = ∫ y in Icc α (α + w), ‖u y‖ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by simp [hsupp y hy]).symm
  have hs2 : ∫ y, ‖u y‖ ^ 2 = ∫ y in Icc α (α + w), ‖u y‖ ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by simp [hsupp y hy]).symm
  have hvol : (volume.restrict (Icc α (α + w))).real univ = w := by
    rw [measureReal_restrict_apply_univ, Real.volume_real_Icc_of_le (by linarith)]
    ring
  rw [hs1, hs2]
  have h := kill_sq_integral_le (μ := volume.restrict (Icc α (α + w))) h1.norm.integrableOn
    h2.integrableOn
  rwa [hvol] at h

/-- **The killed `L²` gap** (AT 命题 2).  Let `J = [α, α + w]` with `w ≥ 1`, `ν, σ` finite,
`0 < a₀ ≤ |a|`, and assume the multiplier gap
`‖(1 - z) φ_ν(t) + z φ_σ(t)‖² ≤ 1 - c min(t², 1)` (`c > 0`).  Then for `u` measurable,
vanishing off `J` and square integrable,
`∫ ‖kStepZ J ν σ z β a u‖² ≤ (1 - c₁/w²) ∫ ‖u‖²` with `c₁ = killGapConst c a₀ > 0`
depending only on `c` and `a₀`. -/
theorem integral_norm_kStepZ_sq_le_gap [IsFiniteMeasure ν] [IsFiniteMeasure σ]
    {α w c a₀ : ℝ} (hw : 1 ≤ w) (hc : 0 < c) (ha₀ : 0 < a₀) (ha : a₀ ≤ |a|)
    (hgap : ∀ t : ℝ, ‖(1 - z) * charFun ν t + z * charFun σ t‖ ^ 2 ≤ 1 - c * min (t ^ 2) 1)
    (hu : Measurable u) (hsupp : ∀ y, y ∉ Icc α (α + w) → u y = 0)
    (h2 : Integrable (fun y => ‖u y‖ ^ 2)) :
    ∫ y, ‖kStepZ (Icc α (α + w)) ν σ z β a u y‖ ^ 2 ≤
      (1 - killGapConst c a₀ / w ^ 2) * ∫ y, ‖u y‖ ^ 2 := by
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw
  have hmem : MemLp u 2 := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).2 h2
  have h1 : Integrable u := kill_integrable_of_support (s := Icc α (α + w))
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hsupp hmem
  set Q := ∫ y, ‖u y‖ ^ 2 with hQ
  have hQ0 : 0 ≤ Q := integral_nonneg fun y => by positivity
  -- low-frequency bound
  have hlow : ∀ ξ, ‖𝓕 u ξ‖ ^ 2 ≤ w * Q := by
    intro ξ
    have h := kill_norm_fourier_le u ξ
    have hcs := kill_sq_integral_norm_le hw0.le hsupp h1 h2
    calc ‖𝓕 u ξ‖ ^ 2 ≤ (∫ y, ‖u y‖) ^ 2 := by gcongr
      _ ≤ w * Q := hcs
  set κ := min (π ^ 2 * a₀ ^ 2 / 4) 1 with hκ
  have hκ0 : 0 ≤ κ := le_min (by positivity) zero_le_one
  set K := c * κ / w ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set δ := 1 / (4 * w) with hδ
  have hδ0 : 0 < δ := by positivity
  have hFsq : Integrable (fun ξ => ‖𝓕 u ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm
      (kill_continuous_fourier h1).aestronglyMeasurable).1 (kill_memLp_two_fourier h1 hmem)
  set B : ℝ → ℝ := fun ξ => (1 - K) * ‖𝓕 u ξ‖ ^ 2 +
    K * (Icc (-δ) δ).indicator (fun _ => w * Q) ξ with hB
  have hBi : Integrable B :=
    (hFsq.const_mul _).add (((integrableOn_const (C := w * Q) (s := Icc (-δ) δ) (μ := volume) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc).const_mul K)
  have hpt : ∀ ξ, ‖kMult ν σ z a ξ‖ ^ 2 * ‖𝓕 u ξ‖ ^ 2 ≤ B ξ := by
    intro ξ
    have hg := hgap (-(2 * π * a * ξ))
    have hm2 : ‖kMult ν σ z a ξ‖ ^ 2 ≤ 1 - c * min ((-(2 * π * a * ξ)) ^ 2) 1 := hg
    have hmin0 : 0 ≤ min ((-(2 * π * a * ξ)) ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
    have hF0 : 0 ≤ ‖𝓕 u ξ‖ ^ 2 := sq_nonneg _
    by_cases hξ : ξ ∈ Icc (-δ) δ
    · rw [hB]
      simp only [indicator_of_mem hξ]
      have hk1 : ‖kMult ν σ z a ξ‖ ^ 2 ≤ 1 := by nlinarith
      have := hlow ξ
      nlinarith
    · rw [hB]
      simp only [indicator_of_notMem hξ, mul_zero, add_zero]
      have hξ' : δ < |ξ| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hξ
        rcases hξ with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact h
      -- `t² = 4π²a²ξ² ≥ π²a₀²/(4w²)`
      have ht : π ^ 2 * a₀ ^ 2 / 4 / w ^ 2 ≤ (-(2 * π * a * ξ)) ^ 2 := by
        have e1 : (-(2 * π * a * ξ)) ^ 2 = 4 * π ^ 2 * |a| ^ 2 * |ξ| ^ 2 := by
          rw [neg_sq, sq_abs, sq_abs]; ring
        have ha2 : a₀ ^ 2 ≤ |a| ^ 2 := by gcongr
        have hξ2 : δ ^ 2 ≤ |ξ| ^ 2 := by gcongr
        have hδ2 : δ ^ 2 = 1 / (16 * w ^ 2) := by rw [hδ]; field_simp; ring
        rw [e1]
        calc π ^ 2 * a₀ ^ 2 / 4 / w ^ 2 = 4 * π ^ 2 * a₀ ^ 2 * δ ^ 2 := by
              rw [hδ2]; field_simp; ring
          _ ≤ 4 * π ^ 2 * |a| ^ 2 * |ξ| ^ 2 := by gcongr
      have hmin : κ / w ^ 2 ≤ min ((-(2 * π * a * ξ)) ^ 2) 1 := by
        have hw2 : 1 ≤ w ^ 2 := by nlinarith
        refine le_min ?_ ?_
        · calc κ / w ^ 2 ≤ π ^ 2 * a₀ ^ 2 / 4 / w ^ 2 := by
                gcongr; exact min_le_left _ _
            _ ≤ _ := ht
        · calc κ / w ^ 2 ≤ 1 / w ^ 2 := by gcongr; exact min_le_right _ _
            _ ≤ 1 := by rw [div_le_one (by positivity)]; exact hw2
      have hKle : K ≤ c * min ((-(2 * π * a * ξ)) ^ 2) 1 := by
        rw [hK, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hmin hc.le
      have : ‖kMult ν σ z a ξ‖ ^ 2 ≤ 1 - K := by linarith
      exact mul_le_mul_of_nonneg_right this hF0
  have hmain := integral_norm_kStepZ_sq_le_mult (J := Icc α (α + w)) (z := z) (β := β) (a := a)
    (ν := ν) (σ := σ) hu h1 hmem
  have hint : ∫ ξ, ‖kMult ν σ z a ξ‖ ^ 2 * ‖𝓕 u ξ‖ ^ 2 ≤ ∫ ξ, B ξ :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => by positivity) hBi
      (Filter.Eventually.of_forall hpt)
  have hBint : ∫ ξ, B ξ = (1 - K) * Q + K * (w * Q * (2 * δ)) := by
    rw [hB, integral_add (hFsq.const_mul _)
      (((integrableOn_const (C := w * Q) (s := Icc (-δ) δ) (μ := volume) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc).const_mul K),
      integral_const_mul, integral_const_mul, integral_indicator_const _ measurableSet_Icc,
      Real.volume_real_Icc_of_le (by linarith), plancherel_integrable_memLp h1 hmem, smul_eq_mul]
    ring
  have hfin : (1 - K) * Q + K * (w * Q * (2 * δ)) = (1 - killGapConst c a₀ / w ^ 2) * Q := by
    rw [hδ, hK, killGapConst, ← hκ]
    field_simp
    ring
  calc ∫ y, ‖kStepZ (Icc α (α + w)) ν σ z β a u y‖ ^ 2
      ≤ ∫ ξ, ‖kMult ν σ z a ξ‖ ^ 2 * ‖𝓕 u ξ‖ ^ 2 := hmain
    _ ≤ ∫ ξ, B ξ := hint
    _ = (1 - killGapConst c a₀ / w ^ 2) * Q := by rw [hBint, hfin]

/-- The killed gap in set-integral form over `J = [α, α + w]`. -/
theorem setIntegral_norm_kStepZ_sq_le_gap [IsFiniteMeasure ν] [IsFiniteMeasure σ]
    {α w c a₀ : ℝ} (hw : 1 ≤ w) (hc : 0 < c) (ha₀ : 0 < a₀) (ha : a₀ ≤ |a|)
    (hgap : ∀ t : ℝ, ‖(1 - z) * charFun ν t + z * charFun σ t‖ ^ 2 ≤ 1 - c * min (t ^ 2) 1)
    (hu : Measurable u) (hsupp : ∀ y, y ∉ Icc α (α + w) → u y = 0)
    (h2 : Integrable (fun y => ‖u y‖ ^ 2)) :
    ∫ y in Icc α (α + w), ‖kStepZ (Icc α (α + w)) ν σ z β a u y‖ ^ 2 ≤
      (1 - killGapConst c a₀ / w ^ 2) * ∫ y in Icc α (α + w), ‖u y‖ ^ 2 := by
  have hk : ∀ y, y ∉ Icc α (α + w) → ‖kStepZ (Icc α (α + w)) ν σ z β a u y‖ ^ 2 = 0 := by
    intro y hy
    rw [kStepZ_eq_indicator, indicator_of_notMem hy]
    simp
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hk,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by simp [hsupp y hy]]
  exact integral_norm_kStepZ_sq_le_gap hw hc ha₀ ha hgap hu hsupp h2

end

end PGM
