import PLAStochastic.Index.GRE.FixedParameter
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# H-G-RE: asymptotic form of the expected rank-equispaced height

Along sequences `n → ∞`, `ε → ∞` with `log ε = o(log n)`, the fixed-parameter
bounds `integral_reHeight_le` / `integral_reHeight_ge` of `PLAStochastic.Index.GRE.FixedParameter`, used
with the concentration level `t = ⌈4 log n / c₀⌉`, give

* `E H = O(log log n)` (`H_G_RE_upper`), and
* under `log ε ≤ D (log n)^(1-η)` (RE-LOWER), `E H = Ω(log log n)`
  (`H_G_RE_lower`), hence `E H = Θ(log log n)` (`H_G_RE_theta`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Topology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-! ## The concentration level `t = ⌈4 log n / c₀⌉` -/

/-- The common exponential rate of the two per-pair failure terms. -/
def cRE : ℝ := min (Real.log 4) (Real.log (expBound (71 / 72)))

theorem cRE_pos : 0 < cRE :=
  lt_min (Real.log_pos (by norm_num)) log_expBound_low_pos

/-- The concentration level used for `n` keys. -/
def tRE (n : ℕ) : ℕ := ⌈4 * Real.log n / cRE⌉₊

/-- `pairFail (tRE n) ≤ 2 / n⁴`. -/
theorem pairFail_tRE_le {n : ℕ} (hn : 1 ≤ n) :
    pairFail (tRE n) ≤ 2 / (n : ℝ) ^ 4 := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := cRE_pos
  have ht : 4 * Real.log n / cRE ≤ (tRE n : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ hc] at ht
  have hexp : Real.exp (-(4 * Real.log n)) = 1 / (n : ℝ) ^ 4 := by
    rw [Real.exp_neg, one_div]
    congr 1
    rw [show (4 : ℝ) * Real.log n = ((4 : ℕ) : ℝ) * Real.log n by norm_num,
      Real.exp_nat_mul, Real.exp_log hN]
  have ht0 : (0 : ℝ) ≤ tRE n := Nat.cast_nonneg _
  have h1 : (1 / 4 : ℝ) ^ tRE n ≤ 1 / (n : ℝ) ^ 4 := by
    rw [← hexp, ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), one_div,
      Real.log_inv]
    apply Real.exp_le_exp.2
    have : cRE * (tRE n : ℝ) ≤ Real.log 4 * tRE n :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) ht0
    linarith
  have h2 : Real.exp (-(Real.log (expBound (71 / 72))) * tRE n) ≤ 1 / (n : ℝ) ^ 4 := by
    rw [← hexp]
    apply Real.exp_le_exp.2
    have : cRE * (tRE n : ℝ) ≤ Real.log (expBound (71 / 72)) * tRE n :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) ht0
    linarith
  unfold pairFail
  calc _ ≤ 1 / (n : ℝ) ^ 4 + 1 / (n : ℝ) ^ 4 := add_le_add h1 h2
    _ = 2 / (n : ℝ) ^ 4 := by ring

theorem pairFail_nonneg (t : ℕ) : 0 ≤ pairFail t := by
  unfold pairFail; positivity

/-- The union-bound mass of the bad event at level `tRE n` is at most `18 / n²`. -/
theorem badMass_tRE_le {n : ℕ} (hn : 1 ≤ n) :
    ((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail (tRE n) ≤ 18 / (n : ℝ) ^ 2 := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hsq : ((2 * n + 1 : ℕ) : ℝ) ^ 2 ≤ 9 * (n : ℝ) ^ 2 := by
    push_cast
    have : 2 * (n : ℝ) + 1 ≤ 3 * n := by linarith
    calc (2 * (n : ℝ) + 1) ^ 2 ≤ (3 * n) ^ 2 := by gcongr
      _ = 9 * (n : ℝ) ^ 2 := by ring
  calc ((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail (tRE n) ≤ 9 * (n : ℝ) ^ 2 * (2 / (n : ℝ) ^ 4) :=
        mul_le_mul hsq (pairFail_tRE_le hn) (pairFail_nonneg _) (by positivity)
    _ = 18 / (n : ℝ) ^ 2 := by field_simp; ring

/-- `tRE n + 1 ≤ (4/c₀ + 2) log n` once `log n ≥ 1`. -/
theorem tRE_succ_le {n : ℕ} (hL : 1 ≤ Real.log n) :
    (tRE n : ℝ) + 1 ≤ (4 / cRE + 2) * Real.log n := by
  have hc := cRE_pos
  have h0 : 0 ≤ 4 * Real.log n / cRE := by positivity
  have h1 : (tRE n : ℝ) < 4 * Real.log n / cRE + 1 := Nat.ceil_lt_add_one h0
  have h2 : 4 * Real.log n / cRE = 4 / cRE * Real.log n := by ring
  have h3 : 0 ≤ 4 / cRE := by positivity
  nlinarith

/-! ## Fixed-parameter `log log n` bounds -/

/-- The constant inside the second logarithm of `reUpper`. -/
def KUpperRE : ℝ := 2 * (512 / aRE + 1) * (4 / cRE + 2)

theorem one_le_KUpperRE : 1 ≤ KUpperRE := by
  have ha := aRE_pos
  have hc := cRE_pos
  have h1 : 0 ≤ 512 / aRE := by positivity
  have h2 : 0 ≤ 4 / cRE := by positivity
  unfold KUpperRE
  have h3 : 1 ≤ 512 / aRE + 1 := by linarith
  have h4 : 2 ≤ 4 / cRE + 2 := by linarith
  calc (1 : ℝ) ≤ 2 * 1 * 2 := by norm_num
    _ ≤ 2 * (512 / aRE + 1) * (4 / cRE + 2) := by gcongr

/-- The constant of the upper `log log n` bound. -/
def CUpperRE : ℝ := (2 + Real.log KUpperRE) / Real.log 2 + 4 + 36

theorem log_pos_of_loglog {n : ℕ} (hn : 1 ≤ n) (hLL : 1 ≤ Real.log (Real.log n)) :
    0 < Real.log n := by
  refine lt_of_le_of_ne (Real.log_nonneg (by exact_mod_cast hn)) fun h => ?_
  rw [← h, Real.log_zero] at hLL
  norm_num at hLL

/-- `reUpper n G₀ (tRE n) ≤ C log log n` for fixed parameters. -/
theorem reUpper_tRE_le {n : ℕ} {G₀ : ℝ} (hn : 1 ≤ n) (hLL : 1 ≤ Real.log (Real.log n))
    (hq : Real.exp 1 ≤ G₀ / (4 * 128)) :
    reUpper n G₀ (tRE n) ≤ ((2 + Real.log KUpperRE) / Real.log 2 + 4) * Real.log (Real.log n) := by
  set L := Real.log n
  have hL0 := log_pos_of_loglog hn hLL
  have hL1 : 1 ≤ L := by
    have := Real.log_le_sub_one_of_pos hL0
    linarith
  have ha := aRE_pos
  have hc := cRE_pos
  have hlogq : 1 ≤ Real.log (G₀ / (4 * 128)) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hq
  have hT1 : Real.logb 2 (L / Real.log (G₀ / (4 * 128))) ≤ Real.logb 2 L :=
    Real.logb_le_logb_of_le (by norm_num) (div_pos hL0 (by linarith)) (div_le_self hL0.le hlogq)
  have ht := tRE_succ_le hL1
  have ht0 : (0 : ℝ) ≤ tRE n := Nat.cast_nonneg _
  have he : 2 * (128 * (4 * ((tRE n : ℝ) + 1) / aRE) + ((tRE n : ℝ) + 1)) =
      2 * (512 / aRE + 1) * ((tRE n : ℝ) + 1) := by ring
  have hT2 : Real.logb 2 (2 * (128 * (4 * ((tRE n : ℝ) + 1) / aRE) + ((tRE n : ℝ) + 1))) ≤
      Real.logb 2 (KUpperRE * L) := by
    rw [he]
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    have : 2 * (512 / aRE + 1) * ((tRE n : ℝ) + 1) ≤ 2 * (512 / aRE + 1) * ((4 / cRE + 2) * L) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    calc _ ≤ _ := this
      _ = KUpperRE * L := by unfold KUpperRE; ring
  have hsum := logb_sum_le_mul_log one_le_KUpperRE (by norm_num : (0 : ℝ) ≤ 4) hL0 hLL
  unfold reUpper
  linarith

/-- The fixed-parameter upper bound `E H ≤ CUpperRE · log log n`. -/
theorem integral_reHeight_le_loglog [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {x0 : Ω → ℝ} (hx0 : Measurable x0) {eps : ℝ}
    (heps : epsZero (σ₀ ^ 2 / μ₀ ^ 2) (2 + κ₀ / σ₀ ^ 3) ≤ eps) {n : ℕ} (hn : 1 ≤ n)
    (hLL : 1 ≤ Real.log (Real.log n))
    (hq : Real.exp 1 ≤ μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 / (4 * 128))
    (hqn : μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 / (4 * 128) ≤ n) :
    ∫ ω, (reHeight eps (fun s => x0 ω + ∑ i ∈ range s, g i ω) n : ℝ) ∂P ≤
      CUpperRE * Real.log (Real.log n) := by
  have hq1 : 1 < μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 / (4 * 128) := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hmain := integral_reHeight_le hg hx0 heps hn (tRE n) hq1 hqn
  have hU := reUpper_tRE_le hn hLL hq
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hlogn : (Nat.log 2 n : ℝ) + 1 ≤ 2 * n := by
    have : (Nat.log 2 n : ℝ) ≤ n := by exact_mod_cast Nat.log_le_self 2 n
    linarith
  have hbad : ((Nat.log 2 n : ℝ) + 1) * (((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail (tRE n)) ≤ 36 := by
    calc _ ≤ (2 * (n : ℝ)) * (18 / (n : ℝ) ^ 2) :=
          mul_le_mul hlogn (badMass_tRE_le hn) (by have := pairFail_nonneg (tRE n); positivity)
            (by positivity)
      _ = 36 / n := by field_simp; ring
      _ ≤ 36 := div_le_self (by norm_num) hN
  unfold CUpperRE
  have hl : 0 ≤ Real.log (Real.log n) := by linarith
  calc _ ≤ _ := hmain
    _ ≤ ((2 + Real.log KUpperRE) / Real.log 2 + 4) * Real.log (Real.log n) + 36 :=
        add_le_add hU hbad
    _ ≤ ((2 + Real.log KUpperRE) / Real.log 2 + 4) * Real.log (Real.log n) +
          36 * Real.log (Real.log n) := by linarith
    _ = _ := by ring

/-- The constant in the `√n` condition of the lower bound. -/
def KLowerRE : ℝ := 4 * (4 / cRE + 2) / aRE

/-- `reLower n G₀ ≥ (η / (2 log 2)) log log n` for fixed parameters. -/
theorem reLower_ge {n : ℕ} {G₀ η D₁ : ℝ} (hn : 1 ≤ n) (hη : 0 < η) (hD₁ : 0 < D₁)
    (hA : 1 ≤ G₀) (hLL : 1 ≤ Real.log (Real.log n))
    (hLL2 : 2 * Real.log (2 * D₁) / η ≤ Real.log (Real.log n))
    (hD' : Real.log (2 / aRE * G₀) ≤ D₁ * Real.log n ^ (1 - η)) :
    η / (2 * Real.log 2) * Real.log (Real.log n) ≤ reLower n G₀ := by
  set L := Real.log n
  have hL0 := log_pos_of_loglog hn hLL
  have hL1 : 1 < L := by
    have := Real.log_le_sub_one_of_pos hL0
    linarith
  have ha := aRE_pos
  have ha1 := aRE_le_one
  have h2a : 2 ≤ 2 / aRE := by
    rw [le_div_iff₀ ha]; linarith
  have hD'pos : 0 < Real.log (2 / aRE * G₀) := by
    apply Real.log_pos
    calc (1 : ℝ) < 2 * 1 := by norm_num
      _ ≤ 2 / aRE * G₀ := mul_le_mul h2a hA (by norm_num) (by positivity)
  have hr := logb_ratio_ge hD₁ hD'pos hL1 hD'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk : 2 * Real.log (2 * D₁) ≤ Real.log L * η := (div_le_iff₀ hη).1 hLL2
  have hdiff : η / Real.log 2 * Real.log L - Real.log (2 * D₁) / Real.log 2 -
      η / (2 * Real.log 2) * Real.log L =
      (η * Real.log L - 2 * Real.log (2 * D₁)) / (2 * Real.log 2) := by
    field_simp; ring
  have hnn : 0 ≤ (η * Real.log L - 2 * Real.log (2 * D₁)) / (2 * Real.log 2) :=
    div_nonneg (by linarith) (by positivity)
  unfold reLower
  linarith

/-- The fixed-parameter lower bound `E H ≥ (η / (4 log 2)) log log n`. -/
theorem integral_reHeight_ge_loglog [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {x0 : Ω → ℝ} (hx0 : Measurable x0) {eps η D₁ : ℝ}
    (hη : 0 < η) (hD₁ : 0 < D₁)
    (heps : epsZero (σ₀ ^ 2 / μ₀ ^ 2) (2 + κ₀ / σ₀ ^ 3) ≤ eps) {n : ℕ} (hn6 : 6 ≤ (n : ℝ))
    (hA : 1 ≤ μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2)
    (hsq : KLowerRE * Real.log n ≤ Real.sqrt n)
    (hLL : 1 ≤ Real.log (Real.log n))
    (hLL2 : 2 * Real.log (2 * D₁) / η ≤ Real.log (Real.log n))
    (hD' : Real.log (2 / aRE * (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2)) ≤ D₁ * Real.log n ^ (1 - η)) :
    η / (4 * Real.log 2) * Real.log (Real.log n) ≤
      ∫ ω, (reHeight eps (fun s => x0 ω + ∑ i ∈ range s, g i ω) n : ℝ) ∂P := by
  have hn : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith)
  have hL0 := log_pos_of_loglog hn hLL
  have hL1 : 1 ≤ Real.log n := by
    have := Real.log_le_sub_one_of_pos hL0
    linarith
  have ha := aRE_pos
  have hsqrt : 4 * ((tRE n : ℝ) + 1) / aRE ≤ Real.sqrt n := by
    have ht := tRE_succ_le hL1
    calc 4 * ((tRE n : ℝ) + 1) / aRE ≤ 4 * ((4 / cRE + 2) * Real.log n) / aRE := by gcongr
      _ = KLowerRE * Real.log n := by unfold KLowerRE; ring
      _ ≤ _ := hsq
  have hR := reLower_ge hn hη hD₁ hA hLL hLL2 hD'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hR0 : 0 ≤ reLower n (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2) := by
    have : 0 ≤ η / (2 * Real.log 2) * Real.log (Real.log n) := by
      have : 0 ≤ Real.log (Real.log n) := by linarith
      positivity
    linarith
  have hmain := integral_reHeight_ge hg hx0 heps hn (tRE n) hA hsqrt hR0
  have hbad : ((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail (tRE n) ≤ 1 / 2 := by
    calc _ ≤ 18 / (n : ℝ) ^ 2 := badMass_tRE_le hn
      _ ≤ 18 / (6 : ℝ) ^ 2 := by gcongr
      _ = 1 / 2 := by norm_num
  have hhalf : 1 / 2 ≤ 1 - ((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail (tRE n) := by linarith
  calc η / (4 * Real.log 2) * Real.log (Real.log n) =
        η / (2 * Real.log 2) * Real.log (Real.log n) * (1 / 2) := by field_simp; ring
    _ ≤ reLower n (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2) * (1 / 2) := by gcongr
    _ ≤ reLower n (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2) *
          (1 - ((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail (tRE n)) :=
        mul_le_mul_of_nonneg_left hhalf hR0
    _ ≤ _ := hmain

/-! ## The asymptotic theorems -/

/-- **H-G-RE, upper half.**  Along `n → ∞`, `ε → ∞`, `log ε = o(log n)`, the expected
height of ALG-RE on the first `n` keys is `O(log log n)`. -/
theorem H_G_RE_upper [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {x0 : Ω → ℝ} (hx0 : Measurable x0) {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ᶠ k in atTop,
      ∫ ω, (reHeight (ε k) (fun s => x0 ω + ∑ i ∈ range s, g i ω) (n k) : ℝ) ∂P ≤
        C * Real.log (Real.log (n k)) := by
  refine ⟨CUpperRE, ?_⟩
  have hμ := hg.mu_pos
  have hσ := hg.sigma_pos
  set b : ℝ := μ₀ ^ 2 / σ₀ ^ 2 / (4 * 128) with hb
  have hb0 : 0 < b := by positivity
  have hL : Tendsto (fun k => Real.log (n k)) atTop atTop := Real.tendsto_log_atTop.comp hn
  have hLL : Tendsto (fun k => Real.log (Real.log (n k))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  filter_upwards [hn.eventually_ge_atTop 1, hLL.eventually_ge_atTop 1,
    hε.eventually_ge_atTop (epsZero (σ₀ ^ 2 / μ₀ ^ 2) (2 + κ₀ / σ₀ ^ 3)),
    hε.eventually_ge_atTop (max 1 (Real.exp 1 / b)),
    hεn.eventually (eventually_le_nhds (show (0 : ℝ) < 1 / 4 by norm_num)),
    hL.eventually_ge_atTop (2 * Real.log b)] with k h1 h2 h3 h4 h5 h6
  have hn1 : 1 ≤ n k := by exact_mod_cast h1
  have hG : μ₀ ^ 2 * ε k ^ 2 / σ₀ ^ 2 / (4 * 128) = b * ε k ^ 2 := by rw [hb]; ring
  have he1 : 1 ≤ ε k := le_trans (le_max_left _ _) h4
  have hq : Real.exp 1 ≤ μ₀ ^ 2 * ε k ^ 2 / σ₀ ^ 2 / (4 * 128) := by
    rw [hG]
    have h4' : Real.exp 1 / b ≤ ε k := le_trans (le_max_right _ _) h4
    have h7 : Real.exp 1 ≤ ε k * b := (div_le_iff₀ hb0).1 h4'
    have h8 : ε k ≤ ε k ^ 2 := by
      calc ε k = ε k * 1 := (mul_one _).symm
        _ ≤ ε k * ε k := mul_le_mul_of_nonneg_left he1 (by linarith)
        _ = ε k ^ 2 := (sq _).symm
    have h9 : b * ε k ≤ b * ε k ^ 2 := mul_le_mul_of_nonneg_left h8 hb0.le
    linarith
  have hL0 := log_pos_of_loglog hn1 h2
  have hqn : μ₀ ^ 2 * ε k ^ 2 / σ₀ ^ 2 / (4 * 128) ≤ n k := by
    rw [hG]
    have hlogε : Real.log (ε k) ≤ 1 / 4 * Real.log (n k) := by
      have := (div_le_iff₀ hL0).1 h5
      linarith
    have he0 : 0 < ε k := by linarith
    rw [← Real.log_le_log_iff (by positivity) (by linarith : (0 : ℝ) < n k),
      Real.log_mul hb0.ne' (by positivity), Real.log_pow]
    push_cast
    linarith
  exact integral_reHeight_le_loglog hg hx0 h3 hn1 h2 hq hqn

/-- `KLowerRE · log x ≤ √x` for all large `x`. -/
theorem eventually_KLowerRE_log_le_sqrt :
    ∀ᶠ x : ℝ in atTop, KLowerRE * Real.log x ≤ Real.sqrt x := by
  have hKL : 0 < KLowerRE := by unfold KLowerRE; have := cRE_pos; have := aRE_pos; positivity
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound (inv_pos.2 hKL)
  filter_upwards [h, eventually_ge_atTop 1] with x hx hx1
  rw [Real.norm_of_nonneg (Real.log_nonneg hx1),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
  rw [Real.sqrt_eq_rpow]
  calc KLowerRE * Real.log x ≤ KLowerRE * (KLowerRE⁻¹ * x ^ (1 / 2 : ℝ)) := by gcongr
    _ = x ^ (1 / 2 : ℝ) := by field_simp

/-- **H-G-RE, lower half.**  Along `n → ∞`, `ε → ∞` with RE-LOWER
`log ε ≤ D (log n)^(1-η)`, the expected height of ALG-RE is `Ω(log log n)`. -/
theorem H_G_RE_lower [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {x0 : Ω → ℝ} (hx0 : Measurable x0) {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    {η D : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hD : 0 < D)
    (hRE : ∀ᶠ k in atTop, Real.log (ε k) ≤ D * Real.log (n k) ^ (1 - η)) :
    ∃ c > 0, ∀ᶠ k in atTop,
      c * Real.log (Real.log (n k)) ≤
        ∫ ω, (reHeight (ε k) (fun s => x0 ω + ∑ i ∈ range s, g i ω) (n k) : ℝ) ∂P := by
  have hμ := hg.mu_pos
  have hσ := hg.sigma_pos
  have ha := aRE_pos
  set b : ℝ := μ₀ ^ 2 / σ₀ ^ 2 with hb
  have hb0 : 0 < b := by positivity
  have hL : Tendsto (fun k => Real.log (n k)) atTop atTop := Real.tendsto_log_atTop.comp hn
  have hLL : Tendsto (fun k => Real.log (Real.log (n k))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hpow : Tendsto (fun k => Real.log (n k) ^ (1 - η)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hL
  refine ⟨η / (4 * Real.log 2), by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity,
    ?_⟩
  filter_upwards [hn.eventually_ge_atTop 6, hLL.eventually_ge_atTop 1,
    hLL.eventually_ge_atTop (2 * Real.log (2 * (3 * D)) / η),
    hε.eventually_ge_atTop (epsZero (σ₀ ^ 2 / μ₀ ^ 2) (2 + κ₀ / σ₀ ^ 3)),
    hε.eventually_ge_atTop (max 1 (1 / b)), hRE,
    hpow.eventually_ge_atTop (|Real.log (2 / aRE * b)| / D),
    hn.eventually eventually_KLowerRE_log_le_sqrt] with k h1 h2 h3 h4 h5 h6 h7 h8
  have he1 : 1 ≤ ε k := le_trans (le_max_left _ _) h5
  have he0 : 0 < ε k := by linarith
  have hG : μ₀ ^ 2 * ε k ^ 2 / σ₀ ^ 2 = b * ε k ^ 2 := by rw [hb]; ring
  have hA : 1 ≤ μ₀ ^ 2 * ε k ^ 2 / σ₀ ^ 2 := by
    rw [hG]
    have h5' : 1 / b ≤ ε k := le_trans (le_max_right _ _) h5
    have h9 : 1 ≤ ε k * b := (div_le_iff₀ hb0).1 h5'
    have h10 : ε k ≤ ε k ^ 2 := by
      calc ε k = ε k * 1 := (mul_one _).symm
        _ ≤ ε k * ε k := mul_le_mul_of_nonneg_left he1 he0.le
        _ = ε k ^ 2 := (sq _).symm
    have h11 : b * ε k ≤ b * ε k ^ 2 := mul_le_mul_of_nonneg_left h10 hb0.le
    linarith
  have hD' : Real.log (2 / aRE * (μ₀ ^ 2 * ε k ^ 2 / σ₀ ^ 2)) ≤
      3 * D * Real.log (n k) ^ (1 - η) := by
    rw [hG, ← mul_assoc, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have h9 : Real.log (2 / aRE * b) ≤ D * Real.log (n k) ^ (1 - η) := by
      have := (div_le_iff₀ hD).1 h7
      linarith [le_abs_self (Real.log (2 / aRE * b))]
    push_cast
    linarith
  exact integral_reHeight_ge_loglog hg hx0 hη0 (by positivity) h4 h1 hA h8 h2 h3 hD'

/-- **H-G-RE.**  Under `n → ∞`, `ε → ∞`, `log ε = o(log n)` and RE-LOWER,
`E H = Θ(log log n)`. -/
theorem H_G_RE_theta [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {x0 : Ω → ℝ} (hx0 : Measurable x0) {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0))
    {η D : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hD : 0 < D)
    (hRE : ∀ᶠ k in atTop, Real.log (ε k) ≤ D * Real.log (n k) ^ (1 - η)) :
    ∃ c > 0, ∃ C : ℝ, ∀ᶠ k in atTop,
      c * Real.log (Real.log (n k)) ≤
          ∫ ω, (reHeight (ε k) (fun s => x0 ω + ∑ i ∈ range s, g i ω) (n k) : ℝ) ∂P ∧
        ∫ ω, (reHeight (ε k) (fun s => x0 ω + ∑ i ∈ range s, g i ω) (n k) : ℝ) ∂P ≤
          C * Real.log (Real.log (n k)) := by
  obtain ⟨C, hC⟩ := H_G_RE_upper hg hx0 hn hε hεn
  obtain ⟨c, hc, hc'⟩ := H_G_RE_lower hg hx0 hn hε hη0 hη1 hD hRE
  exact ⟨c, hc, C, hc'.and hC⟩

end

end PGM
