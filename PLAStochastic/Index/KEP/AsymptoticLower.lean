import PLAStochastic.Index.KEP.LowerBound
import PLAStochastic.Index.KRE.EventualConditions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Asymptotic lower bound for the Model K ALG-PGM height

Along `n → ∞`, `ε → ∞` with `log ε / log n → 0`, and assuming the local-count bound
`refK ℓ ≤ C₃^ℓ log (e · ε²)` for all large `ε`, the fixed-parameter bound
`integral_epHeight_kKeys_ge` gives, for every `ν ∈ (0, 1/4)`, eventually
`(1 - ν)² log n / (2 log ε) ≤ E H` (`integral_epHeight_kKeys_ge_asymp`).

For `N = n k`, `e = ε k`, `m ℓ = lcount expSeqMeasure (epLayerSeq e expCoord ℓ)` (`kalM`),
`c₂ = cPlus / vIn 1 1` (`kalC2`) and `κ = 2 (Lf / fmin³ + 1) fmax`, the parameters are
* `L = ⌊(1 - ν) log N / (2 log e)⌋₊` (`kalL`), `s = ⌈(2/θK) m L log N⌉₊` (`kalS`),
  `j = jK N`, `Tmax = j · refLen e vmin` (`kalT`);
* `λG = (8/θK) log N`, `λN = (4/θK) log N`, `Gmax ℓ = λG m (ℓ+1)` (`kalG`);
* `R ℓ = ⌈32 Kc s / m (ℓ+1)⌉₊ + ⌈64 Kc log N⌉₊` (`kalR`);
* `d = s + ⌈λN (c₂ e²)^L⌉₊` (`kalD`, using `m (ℓ+1) ≤ (c₂ e²)^L` instead of monotonicity);
* `u ℓ = (Tmax + 3 + 2e) κ Gmax ℓ / N` (`kalU`).

With `m ℓ ≤ (c₂ e²)^ℓ` (`kalM_le_pow`), the failure bound satisfies
`kepLowDelta ≤ L · kalCΔ κ · (c₂ C₃ e²)^L e¹³ (log N)⁸ / N + exp (-N/6) + CK / N²`
(`kal_delta_le`), and `(c₂ C₃ e²)^L ≤ N^(1 - 3ν/4)` (`kal_pow_le_rpow`) makes it at most `ν`
in the regime `KalRegime` (`KalRegime.delta_le`), which holds eventually
(`eventually_kalRegime`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Topology

/-! ## The reference layer counts -/

/-- The threshold `epsK` for iid `Exp(1)` gaps. -/
def kalEps : ℝ := epsK (bIn 1 1) (βIn 1 (lkap expSeqMeasure (inputPairs expCoord)))

/-- The mean layer-`ℓ` count `m ℓ` of the reference hierarchy of iid `Exp(1)` gaps. -/
def kalM (e : ℝ) (ℓ : ℕ) : ℝ := lcount expSeqMeasure (epLayerSeq e expCoord ℓ)

/-- The per-layer growth constant `c₂ = cPlus / vmin` for `vmin = vIn 1 1`. -/
def kalC2 : ℝ := cPlus / vIn 1 1

variable {e : ℝ}

theorem kalHyp (heps : kalEps ≤ e) :
    RefHyp expSeqMeasure expCoord (bIn 1 1) (βIn 1 (lkap expSeqMeasure (inputPairs expCoord)))
      (vIn 1 1) KcIn e :=
  RefHyp.of_gapLaw (gapLaw_exp iidSeq_expCoord (hasLaw_expCoord 0)) heps

theorem vIn_one_pos : 0 < vIn 1 1 := vIn_pos one_pos one_pos

theorem vIn_one_le_one : vIn 1 1 ≤ 1 := by
  unfold vIn
  exact le_trans (min_le_left _ _) (by norm_num)

theorem one_le_kalC2 : 1 ≤ kalC2 := by
  unfold kalC2
  rw [le_div_iff₀ vIn_one_pos, one_mul]
  have := vIn_one_le_one
  unfold cPlus
  linarith

theorem kalC2_pos : 0 < kalC2 := lt_of_lt_of_le one_pos one_le_kalC2

theorem one_le_of_kalEps_le (heps : kalEps ≤ e) : 1 ≤ e := (kalHyp heps).one_le_eps

theorem kalM_zero (e : ℝ) : kalM e 0 = 1 := by
  simp [kalM, epLayerSeq, lcount, inputPairs]

theorem one_le_kalM (heps : kalEps ≤ e) (ℓ : ℕ) : 1 ≤ kalM e ℓ :=
  one_le_lcount_epLayerSeq iidSeq_expCoord (hasLaw_expCoord 0) (kalHyp heps) ℓ

theorem kalM_pos (heps : kalEps ≤ e) (ℓ : ℕ) : 0 < kalM e ℓ :=
  lt_of_lt_of_le one_pos (one_le_kalM heps ℓ)

theorem kalM_succ_le (heps : kalEps ≤ e) (ℓ : ℕ) :
    kalM e (ℓ + 1) ≤ kalM e ℓ * (kalC2 * e ^ 2) := by
  have H := kalHyp heps
  obtain ⟨-, -, hc, -, hhi⟩ := layerOK_all H.input H.hb H.hβ H.hvmin0 H.hvmin H.hKc H.heps ℓ
  have e1 : cPlus * e ^ 2 / vIn 1 1 = kalC2 * e ^ 2 := by unfold kalC2; ring
  rw [e1] at hhi
  unfold kalM
  rw [hc]
  exact mul_le_mul_of_nonneg_left hhi (H.lcount_pos ℓ).le

theorem kalM_le_pow (heps : kalEps ≤ e) : ∀ ℓ, kalM e ℓ ≤ (kalC2 * e ^ 2) ^ ℓ
  | 0 => by rw [kalM_zero, pow_zero]
  | ℓ + 1 => by
    have h0 : 0 ≤ kalC2 * e ^ 2 := mul_nonneg kalC2_pos.le (sq_nonneg e)
    rw [pow_succ]
    exact (kalM_succ_le heps ℓ).trans (mul_le_mul_of_nonneg_right (kalM_le_pow heps ℓ) h0)

theorem one_le_kalC2_mul (heps : kalEps ≤ e) : 1 ≤ kalC2 * e ^ 2 := by
  have he := one_le_of_kalEps_le heps
  have h2 : 1 ≤ e ^ 2 := one_le_pow₀ he
  nlinarith [one_le_kalC2]

theorem kalM_le_pow_of_le (heps : kalEps ≤ e) {ℓ L : ℕ} (h : ℓ ≤ L) :
    kalM e ℓ ≤ (kalC2 * e ^ 2) ^ L :=
  (kalM_le_pow heps ℓ).trans (pow_le_pow_right₀ (one_le_kalC2_mul heps) h)

/-! ## The parameter choices -/

/-- The top layer `L = ⌊(1 - ν) log N / (2 log e)⌋₊`. -/
def kalL (ν : ℝ) (N : ℕ) (e : ℝ) : ℕ := ⌊(1 - ν) * (Real.log N / (2 * Real.log e))⌋₊

/-- The leading-pivot cutoff `s = ⌈(2 / θK) m L log N⌉₊`. -/
def kalS (N : ℕ) (e : ℝ) (L : ℕ) : ℕ := ⌈2 / θK * kalM e L * Real.log N⌉₊

/-- The node-length cutoff `Tmax = j · refLen e vmin` with `j = jK N`. -/
def kalT (N : ℕ) (e : ℝ) : ℕ := jK N * refLen e (vIn 1 1)

/-- The key-span level `λG = (8 / θK) log N`. -/
def kalLamG (N : ℕ) : ℝ := 8 / θK * Real.log N

/-- The count level `λN = (4 / θK) log N`. -/
def kalLamN (N : ℕ) : ℝ := 4 / θK * Real.log N

/-- The key-span cutoff `Gmax ℓ = λG · m (ℓ + 1)`. -/
def kalG (N : ℕ) (e : ℝ) (ℓ : ℕ) : ℝ := kalLamG N * kalM e (ℓ + 1)

/-- The number of blocks `R ℓ = ⌈32 Kc s / m (ℓ + 1)⌉₊ + ⌈64 Kc log N⌉₊`. -/
def kalR (N : ℕ) (e : ℝ) (s ℓ : ℕ) : ℕ :=
  ⌈32 * KcIn * s / kalM e (ℓ + 1)⌉₊ + ⌈64 * KcIn * Real.log N⌉₊

/-- The pivot cutoff `d = s + ⌈λN (c₂ e²)^L⌉₊`. -/
def kalD (N : ℕ) (e : ℝ) (s L : ℕ) : ℕ := s + ⌈kalLamN N * (kalC2 * e ^ 2) ^ L⌉₊

/-- The margin tolerance `u ℓ = (Tmax + 3 + 2e) κ Gmax ℓ / N`. -/
def kalU (κ : ℝ) (N : ℕ) (e : ℝ) (ℓ : ℕ) : ℝ :=
  ((kalT N e : ℝ) + 3 + 2 * e) * κ * kalG N e ℓ / N

/-- The constant of `R ℓ · m (ℓ + 1) ≤ kalCR · M · log N`. -/
def kalCR : ℝ := 64 * KcIn / θK + 96 * KcIn + 2

/-- The constant of `Tmax + 3 + 2e ≤ kalCT · e² · log N`. -/
def kalCT : ℝ := CjK * (5185 / vIn 1 1 + 1) + 5

/-- The constant of `u ℓ ≤ kalCU κ · e² (log N)² M / N`. -/
def kalCU (κ : ℝ) : ℝ := kalCT * κ * (8 / θK)

/-- The constant of the margin bound `refMargin ≤ u · kalCM · K' e¹⁰ (log N)⁵`. -/
def kalCM : ℝ := 2048 * (1 / refRate (vIn 1 1) + 2) ^ 5 + 2

/-- The constant of the per-layer failure bound. -/
def kalCΔ (κ : ℝ) : ℝ := 1 + (96 * KcIn + 2) * (1 + 2 * CK) + 3 * kalCM * kalCR * kalCU κ

/-! ## The cutoff `s` -/

theorem kalS_ge (N : ℕ) (e : ℝ) (L : ℕ) : 2 / θK * kalM e L * Real.log N ≤ kalS N e L :=
  Nat.le_ceil _

theorem kalS_le (heps : kalEps ≤ e) {N L : ℕ} {M : ℝ} (hM : kalM e L ≤ M) :
    (kalS N e L : ℝ) ≤ 2 / θK * M * Real.log N + 1 := by
  have hθ := θK_pos
  have hl := Real.log_natCast_nonneg N
  have hm := one_le_kalM heps L
  have h1 : (kalS N e L : ℝ) < 2 / θK * kalM e L * Real.log N + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h2 : 2 / θK * kalM e L * Real.log N ≤ 2 / θK * M * Real.log N := by gcongr
  linarith

/-! ## The block numbers `R ℓ` -/

theorem kalR_mul_ge (heps : kalEps ≤ e) (N s ℓ : ℕ) :
    32 * KcIn * s ≤ (kalR N e s ℓ : ℝ) * kalM e (ℓ + 1) := by
  have hm := kalM_pos heps (ℓ + 1)
  have h1 : 32 * KcIn * s / kalM e (ℓ + 1) ≤ (⌈32 * KcIn * s / kalM e (ℓ + 1)⌉₊ : ℝ) :=
    Nat.le_ceil _
  rw [div_le_iff₀ hm] at h1
  have h2 : 0 ≤ (⌈64 * KcIn * Real.log N⌉₊ : ℝ) * kalM e (ℓ + 1) := by positivity
  unfold kalR
  push_cast
  nlinarith

theorem kalR_le_add (heps : kalEps ≤ e) (N s ℓ : ℕ) :
    (kalR N e s ℓ : ℝ) ≤ 32 * KcIn * s / kalM e (ℓ + 1) + 64 * KcIn * Real.log N + 2 := by
  have hm := kalM_pos heps (ℓ + 1)
  have hK := one_le_KcIn
  have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have h1 : (⌈32 * KcIn * s / kalM e (ℓ + 1)⌉₊ : ℝ) < 32 * KcIn * s / kalM e (ℓ + 1) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h2 : (⌈64 * KcIn * Real.log N⌉₊ : ℝ) < 64 * KcIn * Real.log N + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  unfold kalR
  push_cast
  linarith

theorem kalR_mul_le (heps : kalEps ≤ e) {N s ℓ : ℕ} {M : ℝ} (hlogN : 1 ≤ Real.log N)
    (hM1 : 1 ≤ M) (hm : kalM e (ℓ + 1) ≤ M) (hs : (s : ℝ) ≤ 2 / θK * M * Real.log N + 1) :
    (kalR N e s ℓ : ℝ) * kalM e (ℓ + 1) ≤ kalCR * M * Real.log N := by
  have hm0 := kalM_pos heps (ℓ + 1)
  have hK := one_le_KcIn
  have hθ := θK_pos
  have hR := kalR_le_add heps N s ℓ
  have hML : 1 ≤ M * Real.log N := by nlinarith
  have e1 : (32 * KcIn * s / kalM e (ℓ + 1) + 64 * KcIn * Real.log N + 2) * kalM e (ℓ + 1) =
      32 * KcIn * s + (64 * KcIn * Real.log N + 2) * kalM e (ℓ + 1) := by
    field_simp
    ring
  have h1 : 32 * KcIn * (s : ℝ) ≤
      64 * KcIn / θK * (M * Real.log N) + 32 * KcIn * (M * Real.log N) := by
    have : 32 * KcIn * (s : ℝ) ≤ 32 * KcIn * (2 / θK * M * Real.log N + 1) := by gcongr
    have e2 : 32 * KcIn * (2 / θK * M * Real.log N + 1) =
        64 * KcIn / θK * (M * Real.log N) + 32 * KcIn := by ring
    nlinarith
  have h2 : (64 * KcIn * Real.log N + 2) * kalM e (ℓ + 1) ≤
      64 * KcIn * (M * Real.log N) + 2 * (M * Real.log N) := by
    have : (64 * KcIn * Real.log N + 2) * kalM e (ℓ + 1) ≤ (64 * KcIn * Real.log N + 2) * M := by
      gcongr
    nlinarith
  calc (kalR N e s ℓ : ℝ) * kalM e (ℓ + 1) ≤
        (32 * KcIn * s / kalM e (ℓ + 1) + 64 * KcIn * Real.log N + 2) * kalM e (ℓ + 1) :=
        mul_le_mul_of_nonneg_right hR hm0.le
    _ = 32 * KcIn * s + (64 * KcIn * Real.log N + 2) * kalM e (ℓ + 1) := e1
    _ ≤ kalCR * M * Real.log N := by unfold kalCR; nlinarith

theorem kalR_le (heps : kalEps ≤ e) {N s ℓ : ℕ} (hN : 1 ≤ N) (hsN : s ≤ N) :
    (kalR N e s ℓ : ℝ) ≤ (96 * KcIn + 2) * N := by
  have hm := one_le_kalM heps (ℓ + 1)
  have hK := one_le_KcIn
  have hR := kalR_le_add heps N s ℓ
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsN' : (s : ℝ) ≤ N := by exact_mod_cast hsN
  have hlog : Real.log N ≤ N := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < N)
    linarith
  have h1 : 32 * KcIn * s / kalM e (ℓ + 1) ≤ 32 * KcIn * s :=
    div_le_self (by positivity) hm
  nlinarith

/-! ## The node-length cutoff -/

theorem kalT_add_le (heps : kalEps ≤ e) {N : ℕ} (hlogN : 1 ≤ Real.log N) :
    (kalT N e : ℝ) + 3 + 2 * e ≤ kalCT * e ^ 2 * Real.log N := by
  have H := kalHyp heps
  have he := one_le_of_kalEps_le heps
  have hj := jK_le hlogN
  have hr := refLen_le H
  have hv := vIn_one_pos
  have hC := one_le_CjK
  have he2 : 1 ≤ e ^ 2 := one_le_pow₀ he
  have hT : (kalT N e : ℝ) ≤ CjK * Real.log N * ((5185 / vIn 1 1 + 1) * e ^ 2) := by
    unfold kalT
    push_cast
    exact mul_le_mul hj hr (Nat.cast_nonneg _) (by positivity)
  have h3 : 3 + 2 * e ≤ 5 * e ^ 2 * Real.log N := by nlinarith
  unfold kalCT
  nlinarith

/-! ## Elementary facts about `N` -/

theorem kal_one_le_N {N : ℕ} (hlogN : 0 < Real.log N) : 1 ≤ N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · rw [h, Nat.cast_zero, Real.log_zero] at hlogN
    exact absurd hlogN (lt_irrefl 0)
  · exact h

theorem kal_N_pos {N : ℕ} (hlogN : 0 < Real.log N) : (0 : ℝ) < N := by
  have := kal_one_le_N hlogN
  exact_mod_cast this

theorem kal_exp_neg_mul_log {N : ℕ} (hN : (0 : ℝ) < N) (k : ℕ) :
    Real.exp (-(k * Real.log N)) = 1 / (N : ℝ) ^ k := by
  rw [Real.exp_neg, one_div]
  congr 1
  rw [Real.exp_nat_mul, Real.exp_log hN]

/-! ## The margin tolerance `u ℓ` -/

theorem kalLamG_pos {N : ℕ} (hlogN : 0 < Real.log N) : 0 < kalLamG N := by
  have := θK_pos
  unfold kalLamG
  positivity

theorem kalU_pos (heps : kalEps ≤ e) {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hlogN : 0 < Real.log N)
    (ℓ : ℕ) : 0 < kalU κ N e ℓ := by
  have he := one_le_of_kalEps_le heps
  have hm := kalM_pos heps (ℓ + 1)
  have hN := kal_N_pos hlogN
  have hG : 0 < kalG N e ℓ := mul_pos (kalLamG_pos hlogN) hm
  have hT : (0 : ℝ) < (kalT N e : ℝ) + 3 + 2 * e := by positivity
  exact div_pos (mul_pos (mul_pos hT hκ) hG) hN

theorem kalU_ge (heps : kalEps ≤ e) {κ : ℝ} (heκ : 1 ≤ e * κ) {N : ℕ}
    (hlogN : 1 ≤ Real.log N) (ℓ : ℕ) : 1 / (N : ℝ) ≤ kalU κ N e ℓ := by
  have he := one_le_of_kalEps_le heps
  have hκ : 0 < κ := by nlinarith
  have hm := one_le_kalM heps (ℓ + 1)
  have hθ := θK_pos
  have hθ1 := θK_le_one
  have hN := kal_N_pos (by linarith : 0 < Real.log N)
  have h8 : 8 ≤ 8 / θK := by rw [le_div_iff₀ hθ]; linarith
  have hlam : 8 ≤ kalLamG N := by unfold kalLamG; nlinarith
  have hT0 := Nat.cast_nonneg (α := ℝ) (kalT N e)
  have h2 : 2 ≤ ((kalT N e : ℝ) + 3 + 2 * e) * κ := by nlinarith
  have h3 : 8 ≤ kalG N e ℓ := by unfold kalG; nlinarith
  have h1 : 1 ≤ ((kalT N e : ℝ) + 3 + 2 * e) * κ * kalG N e ℓ := by nlinarith
  unfold kalU
  exact div_le_div_of_nonneg_right h1 hN.le

theorem kalU_le (heps : kalEps ≤ e) {κ : ℝ} (hκ : 0 ≤ κ) {N : ℕ} (hlogN : 1 ≤ Real.log N)
    {ℓ : ℕ} {M : ℝ} (hm : kalM e (ℓ + 1) ≤ M) :
    kalU κ N e ℓ ≤ kalCU κ * e ^ 2 * Real.log N ^ 2 * M / N := by
  have hT := kalT_add_le heps hlogN
  have he := one_le_of_kalEps_le heps
  have hθ := θK_pos
  have hN := kal_N_pos (by linarith : 0 < Real.log N)
  have hm0 := kalM_pos heps (ℓ + 1)
  have hlam : 0 ≤ kalLamG N := (kalLamG_pos (by linarith)).le
  have hT0 : (0 : ℝ) ≤ (kalT N e : ℝ) + 3 + 2 * e := by positivity
  unfold kalU kalG
  apply div_le_div_of_nonneg_right _ hN.le
  calc ((kalT N e : ℝ) + 3 + 2 * e) * κ * (kalLamG N * kalM e (ℓ + 1)) ≤
        (kalCT * e ^ 2 * Real.log N) * κ * (kalLamG N * M) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hT hκ)
          (mul_le_mul_of_nonneg_left hm hlam) (by positivity)
        have : 0 ≤ kalCT * e ^ 2 * Real.log N := le_trans hT0 hT
        positivity
    _ = kalCU κ * e ^ 2 * Real.log N ^ 2 * M := by unfold kalCU kalLamG; ring

theorem kalR_mul_U_le (heps : kalEps ≤ e) {κ : ℝ} (hκ : 0 ≤ κ) {N s ℓ : ℕ} {M : ℝ}
    (hlogN : 1 ≤ Real.log N) (hM1 : 1 ≤ M) (hm : kalM e (ℓ + 1) ≤ M)
    (hs : (s : ℝ) ≤ 2 / θK * M * Real.log N + 1) :
    (kalR N e s ℓ : ℝ) * kalU κ N e ℓ ≤ kalCU κ * kalCR * e ^ 2 * Real.log N ^ 3 * M / N := by
  have hRm := kalR_mul_le heps hlogN hM1 hm hs
  have hT := kalT_add_le heps hlogN
  have he := one_le_of_kalEps_le heps
  have hN := kal_N_pos (by linarith : 0 < Real.log N)
  have hm0 := kalM_pos heps (ℓ + 1)
  have hlam : 0 ≤ kalLamG N := (kalLamG_pos (by linarith)).le
  have hT0 : (0 : ℝ) ≤ (kalT N e : ℝ) + 3 + 2 * e := by positivity
  have hRm0 : 0 ≤ (kalR N e s ℓ : ℝ) * kalM e (ℓ + 1) := by positivity
  have e1 : (kalR N e s ℓ : ℝ) * kalU κ N e ℓ = ((kalT N e : ℝ) + 3 + 2 * e) * κ * kalLamG N *
      ((kalR N e s ℓ : ℝ) * kalM e (ℓ + 1)) / N := by
    unfold kalU kalG; ring
  rw [e1]
  apply div_le_div_of_nonneg_right _ hN.le
  calc ((kalT N e : ℝ) + 3 + 2 * e) * κ * kalLamG N * ((kalR N e s ℓ : ℝ) * kalM e (ℓ + 1)) ≤
        (kalCT * e ^ 2 * Real.log N) * κ * kalLamG N * (kalCR * M * Real.log N) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hT hκ) hlam)
          hRm hRm0
        have : 0 ≤ kalCT * e ^ 2 * Real.log N := le_trans hT0 hT
        positivity
    _ = kalCU κ * kalCR * e ^ 2 * Real.log N ^ 3 * M := by unfold kalCU kalLamG; ring

/-! ## The hierarchy margin -/

theorem kal_log_inv_le {u : ℝ} {N : ℕ} (hu : 0 < u) (hu1 : u ≤ 1) (huN : 1 / (N : ℝ) ≤ u)
    (hlogN : 1 ≤ Real.log N) :
    0 ≤ Real.log (1 / u) ∧ 1 + Real.log (1 / u) ≤ 2 * Real.log N := by
  have hN := kal_N_pos (by linarith : 0 < Real.log N)
  constructor
  · apply Real.log_nonneg
    rw [le_div_iff₀ hu]
    linarith
  · have h1 : 1 / u ≤ N := by
      rw [div_le_iff₀ hu]
      rw [div_le_iff₀ hN] at huN
      linarith
    have := Real.log_le_log (by positivity) h1
    linarith

theorem refMargin_le_kal {K K' u : ℝ} {N : ℕ} (he : 1 ≤ e) (hK0 : 0 ≤ K) (hK : K ≤ K')
    (hK'1 : 1 ≤ K') (hu : 0 < u) (hu1 : u ≤ 1) (huN : 1 / (N : ℝ) ≤ u)
    (hlogN : 1 ≤ Real.log N) :
    refMargin (vIn 1 1) e K u ≤ u * (kalCM * K' * e ^ 10 * Real.log N ^ 5) := by
  obtain ⟨h0, h1⟩ := kal_log_inv_le hu hu1 huN hlogN
  have hr := refRate_pos vIn_one_pos
  have hc0 : 0 ≤ (1 / refRate (vIn 1 1) + 2) ^ 5 := by positivity
  have hp : (1 + Real.log (1 / u)) ^ 5 ≤ (2 * Real.log N) ^ 5 :=
    pow_le_pow_left₀ (by linarith) h1 5
  have he10 : 1 ≤ e ^ 10 := one_le_pow₀ he
  have hl5 : 1 ≤ Real.log N ^ 5 := one_le_pow₀ hlogN
  have hX1 : 1 ≤ K' * e ^ 10 := by nlinarith
  have hX : 1 ≤ K' * e ^ 10 * Real.log N ^ 5 := by nlinarith
  have hA : 64 * (1 / refRate (vIn 1 1) + 2) ^ 5 * K * e ^ 10 * u * (1 + Real.log (1 / u)) ^ 5 ≤
      64 * (1 / refRate (vIn 1 1) + 2) ^ 5 * K' * e ^ 10 * u * (2 * Real.log N) ^ 5 := by
    gcongr
  have hB : 2 * u ≤ 2 * u * (K' * e ^ 10 * Real.log N ^ 5) :=
    le_mul_of_one_le_right (by positivity) hX
  unfold refMargin
  calc _ ≤ 64 * (1 / refRate (vIn 1 1) + 2) ^ 5 * K' * e ^ 10 * u * (2 * Real.log N) ^ 5 +
        2 * u * (K' * e ^ 10 * Real.log N ^ 5) := add_le_add hA hB
    _ = u * (kalCM * K' * e ^ 10 * Real.log N ^ 5) := by unfold kalCM; ring

/-- The local-count constant: `refK ℓ ≤ C₃^L · 3e` for `ℓ < L`. -/
theorem refK_le_kal (he : 1 ≤ e) {C₃ : ℝ} (hC₃ : 1 ≤ C₃) {ℓ L : ℕ} (hℓ : ℓ ≤ L)
    (hK : refK expSeqMeasure e expCoord ℓ ≤ C₃ ^ ℓ * Real.log (Real.exp 1 * e ^ 2)) :
    refK expSeqMeasure e expCoord ℓ ≤ C₃ ^ L * (3 * e) := by
  have he0 : 0 < e := by linarith
  have hlog : Real.log (Real.exp 1 * e ^ 2) = 1 + 2 * Real.log e := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_pow]
    push_cast
    ring
  have hle : Real.log e ≤ e - 1 := Real.log_le_sub_one_of_pos he0
  have hl0 : 0 ≤ Real.log e := Real.log_nonneg he
  have h1 : Real.log (Real.exp 1 * e ^ 2) ≤ 3 * e := by rw [hlog]; linarith
  have h2 : 0 ≤ Real.log (Real.exp 1 * e ^ 2) := by rw [hlog]; linarith
  have h3 : C₃ ^ ℓ ≤ C₃ ^ L := pow_le_pow_right₀ hC₃ hℓ
  calc _ ≤ C₃ ^ ℓ * Real.log (Real.exp 1 * e ^ 2) := hK
    _ ≤ C₃ ^ L * (3 * e) := mul_le_mul h3 h1 h2 (by positivity)

/-! ## The exponential tails -/

theorem kal_exp_R_le {N : ℕ} (hN : (0 : ℝ) < N) (s ℓ : ℕ) :
    Real.exp (-((kalR N e s ℓ : ℝ) / (16 * KcIn))) ≤ 1 / (N : ℝ) ^ 4 := by
  have hK := one_le_KcIn
  have hR : 64 * KcIn * Real.log N ≤ (kalR N e s ℓ : ℝ) := by
    have h1 : 64 * KcIn * Real.log N ≤ (⌈64 * KcIn * Real.log N⌉₊ : ℝ) := Nat.le_ceil _
    have h2 := Nat.cast_nonneg (α := ℝ) ⌈32 * KcIn * s / kalM e (ℓ + 1)⌉₊
    unfold kalR
    push_cast
    linarith
  have h4 : 4 * Real.log N ≤ (kalR N e s ℓ : ℝ) / (16 * KcIn) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  rw [← kal_exp_neg_mul_log hN 4]
  apply Real.exp_le_exp.2
  push_cast
  linarith

theorem kal_exp_lamG {N : ℕ} (hN : (0 : ℝ) < N) :
    Real.exp (-(θK * kalLamG N / 2)) = 1 / (N : ℝ) ^ 4 := by
  have := θK_pos
  rw [← kal_exp_neg_mul_log hN 4]
  congr 1
  unfold kalLamG
  field_simp
  push_cast
  ring

theorem kal_exp_lamN {N : ℕ} (hN : (0 : ℝ) < N) :
    Real.exp (-(θK * kalLamN N)) = 1 / (N : ℝ) ^ 4 := by
  have := θK_pos
  rw [← kal_exp_neg_mul_log hN 4]
  congr 1
  unfold kalLamN
  field_simp
  push_cast
  ring

theorem kal_exp_s_le (heps : kalEps ≤ e) {N : ℕ} (hN : (0 : ℝ) < N) (L : ℕ) :
    Real.exp (-(θK * ((kalS N e L : ℝ) / kalM e L))) ≤ 1 / (N : ℝ) ^ 2 := by
  have hθ := θK_pos
  have hm := kalM_pos heps L
  have hs := kalS_ge N e L
  have h2 : 2 * Real.log N ≤ θK * ((kalS N e L : ℝ) / kalM e L) := by
    rw [mul_div_assoc', le_div_iff₀ hm]
    have e1 : θK * (2 / θK * kalM e L * Real.log N) = 2 * Real.log N * kalM e L := by
      field_simp
    nlinarith
  rw [← kal_exp_neg_mul_log hN 2]
  apply Real.exp_le_exp.2
  push_cast
  linarith

/-! ## The failure bound `kepLowDelta` -/

theorem kalCM_pos : 0 < kalCM := by
  have := refRate_pos vIn_one_pos
  unfold kalCM
  positivity

theorem kalCT_pos : 0 < kalCT := by
  have := vIn_one_pos
  have := one_le_CjK
  unfold kalCT
  have : 0 ≤ CjK * (5185 / vIn 1 1 + 1) := by positivity
  linarith

theorem kalCR_pos : 0 < kalCR := by
  have := θK_pos
  have := one_le_KcIn
  unfold kalCR
  positivity

theorem kalCU_nonneg {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ kalCU κ := by
  have := θK_pos
  have := kalCT_pos
  unfold kalCU
  positivity

/-- **Per-layer failure bound.**  The layer-`ℓ` summand of `kepLowDelta` is at most
`kalCΔ κ · (c₂ C₃ e²)^L e¹³ (log N)⁸ / N`. -/
theorem kal_term_le (heps : kalEps ≤ e) {κ C₃ : ℝ} (heκ : 1 ≤ e * κ) (hC₃ : 1 ≤ C₃)
    {N L s ℓ : ℕ} (hlogN : 1 ≤ Real.log N) (hℓ : ℓ < L)
    (hK : refK expSeqMeasure e expCoord ℓ ≤ C₃ ^ ℓ * Real.log (Real.exp 1 * e ^ 2))
    (hs : (s : ℝ) ≤ 2 / θK * (kalC2 * e ^ 2) ^ L * Real.log N + 1) (hsN : s ≤ N)
    (hu2 : kalU κ N e ℓ ≤ 1 / 2) :
    Real.exp (-((kalR N e s ℓ : ℝ) / (16 * KcIn))) +
      (kalR N e s ℓ : ℝ) * (refMargin (vIn 1 1) e (refK expSeqMeasure e expCoord ℓ)
        (kalU κ N e ℓ) + (71 / 72 : ℝ) ^ jK N + CK * Real.exp (-(θK * kalLamG N / 2)) +
        CK * Real.exp (-(θK * kalLamN N))) ≤
      kalCΔ κ * ((kalC2 * C₃ * e ^ 2) ^ L * e ^ 13 * Real.log N ^ 8 / N) := by
  have he := one_le_of_kalEps_le heps
  have hκ : 0 < κ := by nlinarith
  have hN0 : (0 : ℝ) < N := kal_N_pos (by linarith)
  have hN1 : 1 ≤ N := kal_one_le_N (by linarith)
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hM1 : 1 ≤ (kalC2 * e ^ 2) ^ L := one_le_pow₀ (one_le_kalC2_mul heps)
  have hm : kalM e (ℓ + 1) ≤ (kalC2 * e ^ 2) ^ L := kalM_le_pow_of_le heps hℓ
  have hu0 := kalU_pos heps hκ (by linarith) ℓ
  have huN := kalU_ge heps heκ hlogN ℓ
  have hK0 := refK_nonneg (kalHyp heps) ℓ
  have hK' := refK_le_kal he hC₃ hℓ.le hK
  have hC3L : 1 ≤ C₃ ^ L := one_le_pow₀ hC₃
  have hK'1 : 1 ≤ C₃ ^ L * (3 * e) := by nlinarith
  have hmargin := refMargin_le_kal he hK0 hK' hK'1 hu0 (by linarith) huN hlogN
  have hRu := kalR_mul_U_le heps hκ.le hlogN hM1 hm hs
  have hR := kalR_le (ℓ := ℓ) heps hN1 hsN
  have hR0 : (0 : ℝ) ≤ kalR N e s ℓ := Nat.cast_nonneg _
  have hCM := kalCM_pos
  have hCR := kalCR_pos
  have hCU := kalCU_nonneg hκ.le
  have hPM : C₃ ^ L * (kalC2 * e ^ 2) ^ L = (kalC2 * C₃ * e ^ 2) ^ L := by
    rw [← mul_pow]; ring
  set W := (kalC2 * C₃ * e ^ 2) ^ L * e ^ 13 * Real.log N ^ 8 / N with hW
  have hW1 : 1 / (N : ℝ) ≤ W := by
    have hP1 : 1 ≤ (kalC2 * C₃ * e ^ 2) ^ L := by rw [← hPM]; nlinarith
    have he13 : 1 ≤ e ^ 13 := one_le_pow₀ he
    have hl8 : 1 ≤ Real.log N ^ 8 := one_le_pow₀ hlogN
    have h1 : 1 ≤ (kalC2 * C₃ * e ^ 2) ^ L * e ^ 13 * Real.log N ^ 8 := by
      have := mul_le_mul hP1 he13 zero_le_one (by linarith)
      have := mul_le_mul this hl8 zero_le_one (by positivity)
      linarith
    exact div_le_div_of_nonneg_right h1 hN0.le
  have hRm : (kalR N e s ℓ : ℝ) * refMargin (vIn 1 1) e (refK expSeqMeasure e expCoord ℓ)
      (kalU κ N e ℓ) ≤ 3 * kalCM * kalCR * kalCU κ * W := by
    calc _ ≤ (kalR N e s ℓ : ℝ) *
          (kalU κ N e ℓ * (kalCM * (C₃ ^ L * (3 * e)) * e ^ 10 * Real.log N ^ 5)) :=
          mul_le_mul_of_nonneg_left hmargin hR0
      _ = ((kalR N e s ℓ : ℝ) * kalU κ N e ℓ) *
          (kalCM * (C₃ ^ L * (3 * e)) * e ^ 10 * Real.log N ^ 5) := by ring
      _ ≤ (kalCU κ * kalCR * e ^ 2 * Real.log N ^ 3 * (kalC2 * e ^ 2) ^ L / N) *
          (kalCM * (C₃ ^ L * (3 * e)) * e ^ 10 * Real.log N ^ 5) :=
          mul_le_mul_of_nonneg_right hRu (by positivity)
      _ = 3 * kalCM * kalCR * kalCU κ *
          ((C₃ ^ L * (kalC2 * e ^ 2) ^ L) * e ^ 13 * Real.log N ^ 8 / N) := by ring
      _ = 3 * kalCM * kalCR * kalCU κ * W := by rw [hPM]
  have hE := kal_exp_R_le (e := e) hN0 s ℓ
  have hj := pow_jK_le hN1
  rw [kal_exp_lamG hN0, kal_exp_lamN hN0]
  have hN4 : (N : ℝ) ≤ (N : ℝ) ^ 4 := le_self_pow₀ hN1' (by norm_num)
  have hN3 : (N : ℝ) ≤ (N : ℝ) ^ 3 := le_self_pow₀ hN1' (by norm_num)
  have h14 : 1 / (N : ℝ) ^ 4 ≤ 1 / N := one_div_le_one_div_of_le hN0 hN4
  have hCK := CK_pos
  set A := (96 * KcIn + 2) * (1 + 2 * CK) with hA
  have hA0 : 0 ≤ A := by have := one_le_KcIn; rw [hA]; positivity
  have hRt : (kalR N e s ℓ : ℝ) * ((71 / 72 : ℝ) ^ jK N + CK * (1 / (N : ℝ) ^ 4) +
      CK * (1 / (N : ℝ) ^ 4)) ≤ A / N := by
    have h1 : (71 / 72 : ℝ) ^ jK N + CK * (1 / (N : ℝ) ^ 4) + CK * (1 / (N : ℝ) ^ 4) ≤
        (1 + 2 * CK) / (N : ℝ) ^ 4 := by
      have : (1 + 2 * CK) / (N : ℝ) ^ 4 = 1 / (N : ℝ) ^ 4 + CK * (1 / (N : ℝ) ^ 4) +
          CK * (1 / (N : ℝ) ^ 4) := by ring
      linarith
    calc _ ≤ ((96 * KcIn + 2) * N) * ((1 + 2 * CK) / (N : ℝ) ^ 4) :=
          mul_le_mul hR h1 (by positivity) (by have := one_le_KcIn; positivity)
      _ = A / (N : ℝ) ^ 3 := by rw [hA]; field_simp
      _ ≤ A / N := div_le_div_of_nonneg_left hA0 hN0 hN3
  have hAW : A / N ≤ A * W := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hW1 hA0
  have hsplit : (kalR N e s ℓ : ℝ) * (refMargin (vIn 1 1) e (refK expSeqMeasure e expCoord ℓ)
      (kalU κ N e ℓ) + (71 / 72 : ℝ) ^ jK N + CK * (1 / (N : ℝ) ^ 4) +
      CK * (1 / (N : ℝ) ^ 4)) = (kalR N e s ℓ : ℝ) * refMargin (vIn 1 1) e
      (refK expSeqMeasure e expCoord ℓ) (kalU κ N e ℓ) + (kalR N e s ℓ : ℝ) *
      ((71 / 72 : ℝ) ^ jK N + CK * (1 / (N : ℝ) ^ 4) + CK * (1 / (N : ℝ) ^ 4)) := by ring
  have hΔ : kalCΔ κ * W = W + A * W + 3 * kalCM * kalCR * kalCU κ * W := by
    unfold kalCΔ; rw [hA]; ring
  rw [hsplit, hΔ]
  linarith

/-- **The failure bound.**  With the parameter choices above,
`kepLowDelta ≤ L · kalCΔ κ · (c₂ C₃ e²)^L e¹³ (log N)⁸ / N + exp (-N/6) + CK / N²`. -/
theorem kal_delta_le (heps : kalEps ≤ e) {κ C₃ : ℝ} (heκ : 1 ≤ e * κ) (hC₃ : 1 ≤ C₃)
    (hK : ∀ ℓ, refK expSeqMeasure e expCoord ℓ ≤ C₃ ^ ℓ * Real.log (Real.exp 1 * e ^ 2))
    {N L : ℕ} (hlogN : 1 ≤ Real.log N) (hsN : kalS N e L ≤ N)
    (hu2 : ∀ ℓ < L, kalU κ N e ℓ ≤ 1 / 2) :
    kepLowDelta e N L (kalS N e L) (jK N) (kalU κ N e) (kalR N e (kalS N e L)) (kalLamG N)
        (kalLamN N) ≤
      L * (kalCΔ κ * ((kalC2 * C₃ * e ^ 2) ^ L * e ^ 13 * Real.log N ^ 8 / N)) +
        Real.exp (-((N : ℝ) / 6)) + CK * (1 / (N : ℝ) ^ 2) := by
  have hN0 : (0 : ℝ) < N := kal_N_pos (by linarith)
  have hs := kalS_le (N := N) heps (kalM_le_pow heps L)
  have hsum := Finset.sum_le_sum fun ℓ (hℓ : ℓ ∈ range L) =>
    kal_term_le heps heκ hC₃ hlogN (Finset.mem_range.1 hℓ) (hK ℓ) hs hsN
      (hu2 ℓ (Finset.mem_range.1 hℓ))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hS := kal_exp_s_le heps hN0 L
  unfold kalM at hS
  have hCK := CK_pos
  unfold kepLowDelta
  have := mul_le_mul_of_nonneg_left hS hCK.le
  linarith

/-! ## The top layer `L` and the exponent bookkeeping -/

theorem kalL_le {ν : ℝ} (hν1 : ν < 1) {N : ℕ} {e : ℝ} (hloge : 0 < Real.log e) :
    (kalL ν N e : ℝ) ≤ (1 - ν) * (Real.log N / (2 * Real.log e)) := by
  have := Real.log_natCast_nonneg N
  have : 0 ≤ 1 - ν := by linarith
  exact Nat.floor_le (by positivity)

theorem lt_kalL_add_one (ν : ℝ) (N : ℕ) (e : ℝ) :
    (1 - ν) * (Real.log N / (2 * Real.log e)) < (kalL ν N e : ℝ) + 1 :=
  Nat.lt_floor_add_one _

theorem one_le_kalL {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1 / 4) {N : ℕ} {e : ℝ}
    (hloge : 0 < Real.log e) (hr : Real.log e ≤ ν / 52 * Real.log N) : 1 ≤ kalL ν N e := by
  apply Nat.le_floor
  have hlogN : 0 < Real.log N := by nlinarith
  have h2 : 2 * Real.log e ≤ (1 - ν) * Real.log N := by nlinarith
  rw [Nat.cast_one, mul_div_assoc', le_div_iff₀ (by positivity), one_mul]
  exact h2

theorem kalL_le_log {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) {N : ℕ} {e : ℝ}
    (hloge : 1 ≤ Real.log e) : (kalL ν N e : ℝ) ≤ Real.log N := by
  have hl := Real.log_natCast_nonneg N
  have h1 := kalL_le (N := N) hν1 (by linarith : 0 < Real.log e)
  have h2 : Real.log N / (2 * Real.log e) ≤ Real.log N := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h3 : (1 - ν) * (Real.log N / (2 * Real.log e)) ≤ Real.log N / (2 * Real.log e) := by
    have : 0 ≤ Real.log N / (2 * Real.log e) := by positivity
    nlinarith
  linarith

/-- `(D e²)^L ≤ N^(1 - 3ν/4)` for `L ≤ (1 - ν) log N / (2 log e)` and
`log e ≥ 2 log D / ν`. -/
theorem kal_pow_le_rpow {ν D e : ℝ} {N L : ℕ} (hν0 : 0 < ν) (hν1 : ν < 1 / 4) (hD : 1 ≤ D)
    (he : 1 ≤ e) (hlogN : 0 < Real.log N) (hloge : 0 < Real.log e)
    (hL : (L : ℝ) ≤ (1 - ν) * (Real.log N / (2 * Real.log e)))
    (hDe : 2 * Real.log D / ν ≤ Real.log e) :
    (D * e ^ 2) ^ L ≤ (N : ℝ) ^ (1 - 3 * ν / 4) := by
  have hN := kal_N_pos hlogN
  have he0 : 0 < e := by linarith
  have hD0 : 0 < D := by linarith
  have hDe2 : 0 < D * e ^ 2 := by positivity
  have hc : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlog : Real.log (D * e ^ 2) = Real.log D + 2 * Real.log e := by
    rw [Real.log_mul hD0.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  rw [← Real.exp_log (pow_pos hDe2 L), Real.log_pow, hlog, Real.rpow_def_of_pos hN]
  apply Real.exp_le_exp.2
  set a := Real.log (N : ℝ)
  set b := Real.log e
  set c := Real.log D
  have h1 : (L : ℝ) * (c + 2 * b) ≤ (1 - ν) * (a / (2 * b)) * (c + 2 * b) :=
    mul_le_mul_of_nonneg_right hL (by positivity)
  have h2 : (1 - ν) * (a / (2 * b)) * (c + 2 * b) = (1 - ν) * a * (1 + c / (2 * b)) := by
    field_simp
    ring
  have h3 : c / (2 * b) ≤ ν / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have := (div_le_iff₀ hν0).1 hDe
    nlinarith
  have h4 : (1 - ν) * a * (1 + c / (2 * b)) ≤ (1 - ν) * a * (1 + ν / 4) := by
    have : 0 ≤ (1 - ν) * a := mul_nonneg (by linarith) hlogN.le
    exact mul_le_mul_of_nonneg_left (by linarith) this
  have h5 : (1 - ν) * a * (1 + ν / 4) ≤ a * (1 - 3 * ν / 4) := by
    nlinarith [mul_nonneg hlogN.le (sq_nonneg ν)]
  have e1 : ((L : ℕ) : ℝ) * (c + 2 * b) = (L : ℝ) * (c + 2 * b) := rfl
  linarith

theorem kal_rpow_combine {ν : ℝ} {N : ℕ} (hN : (0 : ℝ) < N) :
    (N : ℝ) ^ (ν / 4) * (N : ℝ) ^ (ν / 4) * (N : ℝ) ^ (1 - 3 * ν / 4) =
      N * ((N : ℝ) ^ (ν / 4))⁻¹ := by
  have e1 : (N : ℝ) * ((N : ℝ) ^ (ν / 4))⁻¹ = (N : ℝ) ^ (1 + -(ν / 4)) := by
    rw [Real.rpow_add hN, Real.rpow_one, Real.rpow_neg hN.le]
  rw [e1, ← Real.rpow_add hN, ← Real.rpow_add hN]
  congr 1
  ring

/-- The main term is at most `N^(-ν/4)`. -/
theorem kal_main_small {ν C W E Q x : ℝ} {N : ℕ} (hN : (0 : ℝ) < N)
    (hxQ : x ≤ Q) (hW0 : 0 ≤ W) (hW : W ≤ (N : ℝ) ^ (1 - 3 * ν / 4)) (hE0 : 0 ≤ E)
    (hE : E ≤ (N : ℝ) ^ (ν / 4)) (hC0 : 0 ≤ C)
    (hC : C * Q ^ 9 ≤ (N : ℝ) ^ (ν / 4)) :
    x * (C * (W * E * Q ^ 8 / N)) ≤ ((N : ℝ) ^ (ν / 4))⁻¹ := by
  calc x * (C * (W * E * Q ^ 8 / N)) ≤ Q * (C * (W * E * Q ^ 8 / N)) :=
        mul_le_mul_of_nonneg_right hxQ (by positivity)
    _ = C * Q ^ 9 * E * W / N := by ring
    _ ≤ (N : ℝ) ^ (ν / 4) * (N : ℝ) ^ (ν / 4) * (N : ℝ) ^ (1 - 3 * ν / 4) / N := by
        gcongr
    _ = ((N : ℝ) ^ (ν / 4))⁻¹ := by
        rw [kal_rpow_combine hN]
        field_simp

/-- The three pieces of the failure bound add up to at most `ν`. -/
theorem kal_delta_le_nu {ν Y : ℝ} {N : ℕ} (hν0 : 0 < ν) (hN1 : (1 : ℝ) ≤ N)
    (hY : Y ≤ ((N : ℝ) ^ (ν / 4))⁻¹) (hsmall : 3 / ν ≤ (N : ℝ) ^ (ν / 4))
    (hbig : (18 + 3 * CK) / ν ≤ N) :
    Y + Real.exp (-((N : ℝ) / 6)) + CK * (1 / (N : ℝ) ^ 2) ≤ ν := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hCK := CK_pos
  have h3 : (0 : ℝ) < 3 / ν := by positivity
  have hν3 : (3 / ν)⁻¹ = ν / 3 := by rw [inv_div]
  have h1 : ((N : ℝ) ^ (ν / 4))⁻¹ ≤ ν / 3 := by
    rw [← hν3]
    exact inv_anti₀ h3 hsmall
  have hb : 18 + 3 * CK ≤ N * ν := (div_le_iff₀ hν0).1 hbig
  have h2 : Real.exp (-((N : ℝ) / 6)) ≤ ν / 3 := by
    rw [Real.exp_neg, ← hν3]
    apply inv_anti₀ h3
    have := Real.add_one_le_exp ((N : ℝ) / 6)
    have : 3 / ν ≤ (N : ℝ) / 6 := by
      rw [div_le_div_iff₀ hν0 (by norm_num)]
      nlinarith
    linarith
  have h4 : CK * (1 / (N : ℝ) ^ 2) ≤ ν / 3 := by
    have hN2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := le_self_pow₀ hN1 (by norm_num)
    have : CK * (1 / (N : ℝ) ^ 2) ≤ CK * (1 / N) :=
      mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hN0 hN2) hCK.le
    have : CK * (1 / (N : ℝ)) ≤ ν / 3 := by
      rw [mul_one_div, div_le_iff₀ hN0]
      nlinarith
    linarith
  linarith

/-! ## The side conditions of `integral_epHeight_kKeys_ge` -/

/-- `s < N`. -/
theorem kalS_lt (heps : kalEps ≤ e) {ν : ℝ} (hν0 : 0 < ν) {N L : ℕ} (hN3 : 3 ≤ N)
    (hpolyS : 4 / θK * Real.log N ≤ (N : ℝ) ^ (ν / 4))
    (hM : (kalC2 * e ^ 2) ^ L ≤ (N : ℝ) ^ (1 - 3 * ν / 4)) : kalS N e L < N := by
  have hN3' : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < N := by linarith
  have hθ := θK_pos
  have hl := Real.log_natCast_nonneg N
  have hs := kalS_le (N := N) heps (kalM_le_pow heps L)
  have hM0 : 0 ≤ (kalC2 * e ^ 2) ^ L := by have := kalC2_pos; positivity
  have h1 : 2 / θK * (kalC2 * e ^ 2) ^ L * Real.log N =
      (4 / θK * Real.log N) * (kalC2 * e ^ 2) ^ L / 2 := by ring
  have h2 : (4 / θK * Real.log N) * (kalC2 * e ^ 2) ^ L ≤
      (N : ℝ) ^ (ν / 4) * (N : ℝ) ^ (1 - 3 * ν / 4) :=
    mul_le_mul hpolyS hM hM0 (by positivity)
  have h3 : (N : ℝ) ^ (ν / 4) * (N : ℝ) ^ (1 - 3 * ν / 4) ≤ N := by
    rw [← Real.rpow_add hN0]
    calc (N : ℝ) ^ (ν / 4 + (1 - 3 * ν / 4)) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = N := Real.rpow_one _
  have h4 : (kalS N e L : ℝ) < N := by linarith
  exact_mod_cast h4

/-- `u ℓ ≤ 1/2`. -/
theorem kalU_le_half (heps : kalEps ≤ e) {κ : ℝ} (hκ : 0 ≤ κ) {ν : ℝ} {N L ℓ : ℕ}
    (hℓ : ℓ < L) (hlogN : 1 ≤ Real.log N)
    (hpolyU : 2 * kalCU κ * Real.log N ^ 2 ≤ (N : ℝ) ^ (ν / 4))
    (he13 : e ^ 13 ≤ (N : ℝ) ^ (ν / 4))
    (hM : (kalC2 * e ^ 2) ^ L ≤ (N : ℝ) ^ (1 - 3 * ν / 4))
    (hsmall : 1 ≤ (N : ℝ) ^ (ν / 4)) : kalU κ N e ℓ ≤ 1 / 2 := by
  have he := one_le_of_kalEps_le heps
  have hN0 : (0 : ℝ) < N := kal_N_pos (by linarith)
  have hu := kalU_le heps hκ hlogN (kalM_le_pow_of_le (ℓ := ℓ + 1) heps hℓ)
  have hCU := kalCU_nonneg hκ
  have he2 : e ^ 2 ≤ e ^ 13 := pow_le_pow_right₀ he (by norm_num)
  have hM0 : 0 ≤ (kalC2 * e ^ 2) ^ L := by have := kalC2_pos; positivity
  have h1 : kalCU κ * e ^ 2 * Real.log N ^ 2 * (kalC2 * e ^ 2) ^ L / N ≤
      1 / 2 * ((2 * kalCU κ * Real.log N ^ 2) * e ^ 13 * (kalC2 * e ^ 2) ^ L / N) := by
    rw [show 1 / 2 * ((2 * kalCU κ * Real.log N ^ 2) * e ^ 13 * (kalC2 * e ^ 2) ^ L / N) =
      kalCU κ * e ^ 13 * Real.log N ^ 2 * (kalC2 * e ^ 2) ^ L / N by ring]
    gcongr
  have h2 : (2 * kalCU κ * Real.log N ^ 2) * e ^ 13 * (kalC2 * e ^ 2) ^ L / N ≤
      (N : ℝ) ^ (ν / 4) * (N : ℝ) ^ (ν / 4) * (N : ℝ) ^ (1 - 3 * ν / 4) / N := by
    gcongr
  have h2' : (N : ℝ) ^ (ν / 4) * (N : ℝ) ^ (ν / 4) * (N : ℝ) ^ (1 - 3 * ν / 4) / N =
      ((N : ℝ) ^ (ν / 4))⁻¹ := by
    rw [kal_rpow_combine hN0]
    field_simp
  have h3 : ((N : ℝ) ^ (ν / 4))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsmall
  linarith

/-- `s + λN m (ℓ + 1) ≤ d`. -/
theorem kalD_ge (heps : kalEps ≤ e) {N s L ℓ : ℕ} (hℓ : ℓ < L) :
    (s : ℝ) + kalLamN N * kalM e (ℓ + 1) ≤ kalD N e s L := by
  have hθ := θK_pos
  have hl := Real.log_natCast_nonneg N
  have hlam : 0 ≤ kalLamN N := by unfold kalLamN; positivity
  have hm := kalM_le_pow_of_le (ℓ := ℓ + 1) heps hℓ
  have h1 : kalLamN N * (kalC2 * e ^ 2) ^ L ≤ (⌈kalLamN N * (kalC2 * e ^ 2) ^ L⌉₊ : ℝ) :=
    Nat.le_ceil _
  have h2 : kalLamN N * kalM e (ℓ + 1) ≤ kalLamN N * (kalC2 * e ^ 2) ^ L :=
    mul_le_mul_of_nonneg_left hm hlam
  unfold kalD
  push_cast
  linarith

/-- The fixed-point condition `hΨ`. -/
theorem kalU_fixed (heps : kalEps ≤ e) {κ : ℝ} (hκ : 0 ≤ κ) {N : ℕ} (hlogN : 0 < Real.log N)
    {ℓ : ℕ} (hu1 : kalU κ N e ℓ ≤ 1) :
    ((kalT N e : ℝ) + 1 + 2 * (e + kalU κ N e ℓ)) * κ * kalG N e ℓ / N ≤ kalU κ N e ℓ := by
  have hN0 := kal_N_pos hlogN
  have hG : 0 ≤ kalG N e ℓ := (mul_pos (kalLamG_pos hlogN) (kalM_pos heps (ℓ + 1))).le
  have e1 : kalU κ N e ℓ = ((kalT N e : ℝ) + 3 + 2 * e) * κ * kalG N e ℓ / N := rfl
  have h1 : (kalT N e : ℝ) + 1 + 2 * (e + kalU κ N e ℓ) ≤ (kalT N e : ℝ) + 3 + 2 * e := by
    linarith
  calc ((kalT N e : ℝ) + 1 + 2 * (e + kalU κ N e ℓ)) * κ * kalG N e ℓ / N ≤
        ((kalT N e : ℝ) + 3 + 2 * e) * κ * kalG N e ℓ / N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hκ) hG) hN0.le
    _ = kalU κ N e ℓ := e1.symm

/-! ## The eventual regime -/

/-- The finitely many numerical conditions on `(N, e)` used by the lower bound, for a
margin `ν`, a local-count growth constant `C₃` and the Model K constant `κ`. -/
structure KalRegime (ν C₃ κ : ℝ) (N : ℕ) (e : ℝ) : Prop where
  hν0 : 0 < ν
  hν1 : ν < 1 / 4
  hC₃ : 1 ≤ C₃
  heps : kalEps ≤ e
  hK : ∀ ℓ, refK expSeqMeasure e expCoord ℓ ≤ C₃ ^ ℓ * Real.log (Real.exp 1 * e ^ 2)
  hN3 : 3 ≤ N
  hlogN : 1 ≤ Real.log N
  hloge : 1 ≤ Real.log e
  heκ : 1 ≤ e * κ
  hlogD : 2 * Real.log (kalC2 * C₃) / ν ≤ Real.log e
  heN : e ≤ (N : ℝ) ^ (ν / 52)
  hpolyS : 4 / θK * Real.log N ≤ (N : ℝ) ^ (ν / 4)
  hpolyU : 2 * kalCU κ * Real.log N ^ 2 ≤ (N : ℝ) ^ (ν / 4)
  hpolyΔ : kalCΔ κ * Real.log N ^ 9 ≤ (N : ℝ) ^ (ν / 4)
  hsmall : 3 / ν ≤ (N : ℝ) ^ (ν / 4)
  hbig : (18 + 3 * CK) / ν ≤ N

namespace KalRegime

variable {ν C₃ κ : ℝ} {N : ℕ}

theorem one_le_e (h : KalRegime ν C₃ κ N e) : 1 ≤ e := one_le_of_kalEps_le h.heps

theorem kappa_pos (h : KalRegime ν C₃ κ N e) : 0 < κ := by
  have := h.one_le_e
  have := h.heκ
  nlinarith

theorem N_pos (h : KalRegime ν C₃ κ N e) : (0 : ℝ) < N := kal_N_pos (by linarith [h.hlogN])

theorem log_e_le (h : KalRegime ν C₃ κ N e) : Real.log e ≤ ν / 52 * Real.log N := by
  have he0 : 0 < e := by linarith [h.one_le_e]
  have := Real.log_le_log he0 h.heN
  rwa [Real.log_rpow h.N_pos] at this

theorem e13_le (h : KalRegime ν C₃ κ N e) : e ^ 13 ≤ (N : ℝ) ^ (ν / 4) := by
  have he0 : 0 ≤ e := by linarith [h.one_le_e]
  calc e ^ 13 ≤ ((N : ℝ) ^ (ν / 52)) ^ 13 := pow_le_pow_left₀ he0 h.heN 13
    _ = (N : ℝ) ^ (ν / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h.N_pos.le]
      congr 1
      push_cast
      ring

theorem one_le_L (h : KalRegime ν C₃ κ N e) : 1 ≤ kalL ν N e :=
  one_le_kalL h.hν0 h.hν1 (by linarith [h.hloge]) h.log_e_le

theorem L_le (h : KalRegime ν C₃ κ N e) :
    (kalL ν N e : ℝ) ≤ (1 - ν) * (Real.log N / (2 * Real.log e)) :=
  kalL_le (by linarith [h.hν1]) (by linarith [h.hloge])

theorem pow_le (h : KalRegime ν C₃ κ N e) :
    (kalC2 * C₃ * e ^ 2) ^ kalL ν N e ≤ (N : ℝ) ^ (1 - 3 * ν / 4) := by
  have hD : 1 ≤ kalC2 * C₃ := by nlinarith [one_le_kalC2, h.hC₃]
  exact kal_pow_le_rpow h.hν0 h.hν1 hD h.one_le_e (by linarith [h.hlogN])
    (by linarith [h.hloge]) h.L_le h.hlogD

theorem M_le (h : KalRegime ν C₃ κ N e) :
    (kalC2 * e ^ 2) ^ kalL ν N e ≤ (N : ℝ) ^ (1 - 3 * ν / 4) := by
  have h0 : 0 ≤ kalC2 * e ^ 2 := mul_nonneg kalC2_pos.le (sq_nonneg e)
  have h1 : kalC2 * e ^ 2 ≤ kalC2 * C₃ * e ^ 2 := by
    have : kalC2 * e ^ 2 * 1 ≤ kalC2 * e ^ 2 * C₃ := mul_le_mul_of_nonneg_left h.hC₃ h0
    linarith
  exact (pow_le_pow_left₀ h0 h1 _).trans h.pow_le

theorem s_lt (h : KalRegime ν C₃ κ N e) : kalS N e (kalL ν N e) < N :=
  kalS_lt h.heps h.hν0 h.hN3 h.hpolyS h.M_le

theorem u_half (h : KalRegime ν C₃ κ N e) {ℓ : ℕ} (hℓ : ℓ < kalL ν N e) :
    kalU κ N e ℓ ≤ 1 / 2 := by
  have h1 : (1 : ℝ) ≤ 3 / ν := by
    rw [le_div_iff₀ h.hν0]
    linarith [h.hν1]
  exact kalU_le_half h.heps h.kappa_pos.le hℓ h.hlogN h.hpolyU h.e13_le h.M_le
    (h1.trans h.hsmall)

theorem u_pos (h : KalRegime ν C₃ κ N e) (ℓ : ℕ) : 0 < kalU κ N e ℓ :=
  kalU_pos h.heps h.kappa_pos (by linarith [h.hlogN]) ℓ

/-- **The failure bound is at most `ν`.** -/
theorem delta_le (h : KalRegime ν C₃ κ N e) :
    kepLowDelta e N (kalL ν N e) (kalS N e (kalL ν N e)) (jK N) (kalU κ N e)
      (kalR N e (kalS N e (kalL ν N e))) (kalLamG N) (kalLamN N) ≤ ν := by
  have hδ := kal_delta_le h.heps h.heκ h.hC₃ h.hK h.hlogN h.s_lt.le (fun ℓ hℓ => h.u_half hℓ)
  have hC : 0 ≤ kalCΔ κ := by
    have := kalCM_pos
    have := kalCR_pos
    have := kalCU_nonneg h.kappa_pos.le
    have := CK_pos
    have := one_le_KcIn
    unfold kalCΔ
    positivity
  have hP0 : 0 ≤ (kalC2 * C₃ * e ^ 2) ^ kalL ν N e := by
    have := kalC2_pos
    have := h.hC₃
    have : 0 ≤ C₃ := by linarith
    positivity
  have hY := kal_main_small h.N_pos (kalL_le_log h.hν0 (by linarith [h.hν1]) h.hloge) hP0
    h.pow_le (pow_nonneg (by linarith [h.one_le_e]) 13) h.e13_le hC h.hpolyΔ
  have hN1 : (1 : ℝ) ≤ N := by
    have := h.hN3
    have : (3 : ℝ) ≤ N := by exact_mod_cast this
    linarith
  have := kal_delta_le_nu h.hν0 hN1 hY h.hsmall h.hbig
  linarith

end KalRegime

/-! ## The Model K constant -/

variable {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ}

/-- The Model K constant `κ = 2 (Lf / fmin³ + 1) fmax` is positive. -/
theorem kal_kappa_pos (hf : DensityK f A B fmin fmax Lf) :
    0 < 2 * (Lf / fmin ^ 3 + 1) * fmax := by
  have hA : A ∈ Set.Icc A B := ⟨le_rfl, hf.lt.le⟩
  have hB : B ∈ Set.Icc A B := ⟨hf.lt.le, le_rfl⟩
  have hfmin := hf.pos
  have hfmax : 0 < fmax := lt_of_lt_of_le hfmin ((hf.lower A hA).trans (hf.upper A hA))
  have hLf : 0 ≤ Lf := by
    have h := hf.lip A hA B hB
    have hAB : 0 < |A - B| := abs_pos.2 (sub_ne_zero.2 hf.lt.ne)
    have h0 : 0 ≤ Lf * |A - B| := (abs_nonneg _).trans h
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.1 hneg) hAB
    linarith
  positivity

/-! ## The lower bound -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Fixed-parameter lower bound.**  In the regime `KalRegime`, the expected ALG-PGM height
on `N` sorted Model K samples is at least `(1 - ν)² log N / (2 log e)`. -/
theorem integral_epHeight_kKeys_ge_of_regime (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {ν C₃ : ℝ} {N : ℕ} (h : KalRegime ν C₃ (2 * (Lf / fmin ^ 3 + 1) * fmax) N e) :
    (1 - ν) * (1 - ν) * (Real.log N / (2 * Real.log e)) ≤
      ∫ ω, (epHeight e (kKeys X N ω) N : ℝ) ∂P := by
  have hκ := h.kappa_pos
  have hmain := integral_epHeight_kKeys_ge hf hX hind h.heps (N := N) (L := kalL ν N e)
    (s := kalS N e (kalL ν N e)) (Tmax := kalT N e) (j := jK N)
    (d := kalD N e (kalS N e (kalL ν N e)) (kalL ν N e)) (u := kalU _ N e) (Gmax := kalG N e)
    (R := kalR N e (kalS N e (kalL ν N e))) (lamG := kalLamG N) (lamN := kalLamN N)
    h.one_le_L h.s_lt (fun ℓ hℓ => ⟨h.u_pos ℓ, h.u_half hℓ⟩)
    (fun ℓ _ => kalR_mul_ge h.heps N _ ℓ) le_rfl (fun ℓ _ => le_rfl)
    (fun ℓ hℓ => kalD_ge h.heps hℓ)
    (fun ℓ hℓ => kalU_fixed h.heps hκ.le (by linarith [h.hlogN])
      (by linarith [h.u_half hℓ]))
  have hδ := h.delta_le
  have hν1 := h.hν1
  have hloge := h.hloge
  have hl := Real.log_natCast_nonneg N
  have hLf := (lt_kalL_add_one ν N e).le
  have h0 : 0 ≤ (1 - ν) * (Real.log N / (2 * Real.log e)) := by
    have : 0 ≤ 1 - ν := by linarith
    have : 0 < Real.log e := by linarith
    positivity
  calc (1 - ν) * (1 - ν) * (Real.log N / (2 * Real.log e)) =
        ((1 - ν) * (Real.log N / (2 * Real.log e))) * (1 - ν) := by ring
    _ ≤ ((kalL ν N e : ℝ) + 1) * (1 - kepLowDelta e N (kalL ν N e) (kalS N e (kalL ν N e))
          (jK N) (kalU _ N e) (kalR N e (kalS N e (kalL ν N e))) (kalLamG N) (kalLamN N)) :=
        mul_le_mul hLf (by linarith) (by linarith) (by positivity)
    _ ≤ _ := hmain

/-- The regime conditions hold eventually along `n → ∞`, `ε → ∞`, `log ε / log n → 0`. -/
theorem eventually_kalRegime {C₃ κ eps₁ : ℝ} (hC₃ : 1 ≤ C₃) (hκ : 0 < κ)
    (hK : ∀ eps ≥ eps₁, ∀ ℓ,
      refK expSeqMeasure eps expCoord ℓ ≤ C₃ ^ ℓ * Real.log (Real.exp 1 * eps ^ 2))
    {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0))
    {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1 / 4) :
    ∀ᶠ k in atTop, KalRegime ν C₃ κ (n k) (ε k) := by
  have hL : Tendsto (fun k => Real.log (n k)) atTop atTop := Real.tendsto_log_atTop.comp hn
  have hν4 : 0 < ν / 4 := by linarith
  have hrp : Tendsto (fun k => (n k : ℝ) ^ (ν / 4)) atTop atTop :=
    (tendsto_rpow_atTop hν4).comp hn
  filter_upwards [hn.eventually_ge_atTop 3, hL.eventually_ge_atTop 1,
    hε.eventually_ge_atTop kalEps, hε.eventually_ge_atTop eps₁,
    hε.eventually_ge_atTop (Real.exp 1), hε.eventually_ge_atTop (1 / κ),
    hε.eventually_ge_atTop (Real.exp (2 * Real.log (kalC2 * C₃) / ν)),
    eventually_le_rpow_of_logRatio hn hε hεn (by linarith : (0 : ℝ) < ν / 52),
    hn.eventually (eventually_mul_log_pow_le_rpow (4 / θK) 1 hν4),
    hn.eventually (eventually_mul_log_pow_le_rpow (2 * kalCU κ) 2 hν4),
    hn.eventually (eventually_mul_log_pow_le_rpow (kalCΔ κ) 9 hν4),
    hrp.eventually_ge_atTop (3 / ν),
    hn.eventually_ge_atTop ((18 + 3 * CK) / ν)]
    with k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  refine ⟨hν0, hν1, hC₃, h3, hK _ h4, ?_, h2, ?_, ?_, ?_, h8, ?_, h10, h11, h12, h13⟩
  · exact_mod_cast h1
  · rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) h5
  · exact (div_le_iff₀ hκ).1 h6
  · have := Real.log_le_log (Real.exp_pos _) h7
    rwa [Real.log_exp] at this
  · simpa only [pow_one] using h9

/-- **Asymptotic lower bound for the Model K ALG-PGM height.**  Assume the local-count bound
`refK ℓ ≤ C₃^ℓ log (e · eps²)` for all large `eps`.  Along `n → ∞`, `ε → ∞` with
`log ε / log n → 0`, for every `ν ∈ (0, 1/4)`, eventually
`(1 - ν)² · log n / (2 log ε) ≤ E H`. -/
theorem integral_epHeight_kKeys_ge_asymp (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    (hK : ∃ C₃ ≥ 1, ∃ eps₁, ∀ eps ≥ eps₁, ∀ ℓ,
      refK expSeqMeasure eps expCoord ℓ ≤ C₃ ^ ℓ * Real.log (Real.exp 1 * eps ^ 2))
    {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0))
    {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1 / 4) :
    ∀ᶠ k in atTop, (1 - ν) * (1 - ν) * (Real.log (n k) / (2 * Real.log (ε k))) ≤
      ∫ ω, (epHeight (ε k) (kKeys X (n k) ω) (n k) : ℝ) ∂P := by
  obtain ⟨C₃, hC₃, eps₁, hK⟩ := hK
  filter_upwards [eventually_kalRegime hC₃ (kal_kappa_pos hf) hK hn hε hεn hν0 hν1] with k hk
  exact integral_epHeight_kKeys_ge_of_regime hf hX hind hk

end

end PGM
