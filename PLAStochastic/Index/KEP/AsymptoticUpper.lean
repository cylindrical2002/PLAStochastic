import PLAStochastic.Index.KEP.UpperBound
import PLAStochastic.Index.KEP.AsymptoticLower
import PLAStochastic.Index.KEP.LocalCountConstants

/-!
# Asymptotic upper bound for the Model K ALG-PGM height

Along `n → ∞`, `ε → ∞` with `log ε / log n → 0`, the fixed-parameter bound
`integral_epHeight_kKeys_le` gives, for every `ν ∈ (0, 1/4)`, eventually
`E H ≤ (1 + 3ν) log n / (2 log ε)` (`integral_epHeight_kKeys_le_asymp`).

For `N = n k`, `e = ε k`, `h₀ = log N / (2 log e)` and `m ℓ = kalM e ℓ`, the parameters are
those of `KEPAsympLower` (`L = kalL ν N e`, `j = jK N`, `Tmax = kalT N e`, `λG`, `λN`,
`Gmax = kalG N e`, `u = kalU κ N e`) with the target gap `gap₀ = ⌊m L / 2⌋₊` (`kauGap`) in place
of the cutoff `s`: `R = kalR N e gap₀`, `d = kalD N e gap₀ L`; the good-anchor depth is
`D = ⌈12 log N⌉₊` (`kauD`) and the horizon is `𝔥 = N - D` (`kauH`).

* The layer counts grow at least like `m ℓ ≥ (e² / (128 b))^ℓ` (`kalM_ge_pow`), so
  `N^(1 - 5ν/4) ≤ e² m L` (`kau_rpow_le_mul_kalM`).
* The reference failure bound `kepRefDelta` is the sum part of `kepLowDelta`; the per-layer
  estimate `kal_term_le` applies with `s = gap₀ ≤ kalS` (`kau_refDelta_le`), so
  `kepRefDelta ≤ N^(-ν/4) ≤ 1 / (16 KcIn)` and `kepTrialProb ≥ 1 / (8 KcIn)`.
* Hence `kepLayerUp ≤ 8 KcIn (4 N / m L + 2) + 4 + D + 1 ≤ N^(7ν/4)` (`KauRegime.layerUp_le`),
  and with `log q ≥ log e`, `E H ≤ (1 - ν) h₀ + (7ν/2) h₀ + 1 ≤ (1 + 3ν) h₀`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Topology

variable {e : ℝ}

/-! ## The lower growth of the reference layer counts -/

theorem one_le_bIn_one : 1 ≤ bIn 1 1 := by
  unfold bIn
  exact le_max_of_le_left (by norm_num)

/-- `m ℓ ≥ (e² / (128 b))^ℓ` from the lower bracket `e² / (128 b) ≤ segMean`. -/
theorem kalM_ge_pow (heps : kalEps ≤ e) : ∀ ℓ, (e ^ 2 / (128 * bIn 1 1)) ^ ℓ ≤ kalM e ℓ
  | 0 => by rw [kalM_zero, pow_zero]
  | ℓ + 1 => by
    have H := kalHyp heps
    have hb := one_le_bIn_one
    obtain ⟨-, -, hc, hlo, -⟩ := layerOK_all H.input H.hb H.hβ H.hvmin0 H.hvmin H.hKc H.heps ℓ
    have ih := kalM_ge_pow heps ℓ
    unfold kalM at ih ⊢
    rw [hc, pow_succ]
    exact mul_le_mul ih hlo (by positivity) (H.lcount_pos ℓ).le

/-- `N^(1 - 5ν/4) ≤ (e² / B)^(L + 1)` for `L + 1 ≥ (1 - ν) log N / (2 log e)` and
`log e ≥ 2 log B / ν`. -/
theorem kau_rpow_le_pow {ν B e : ℝ} {N L : ℕ} (hν0 : 0 < ν) (hν1 : ν < 1 / 4) (hB : 1 ≤ B)
    (he : 1 ≤ e) (hlogN : 0 < Real.log N) (hloge : 0 < Real.log e)
    (hL : (1 - ν) * (Real.log N / (2 * Real.log e)) ≤ (L : ℝ) + 1)
    (hBe : 2 * Real.log B / ν ≤ Real.log e) :
    (N : ℝ) ^ (1 - 5 * ν / 4) ≤ (e ^ 2 / B) ^ (L + 1) := by
  have hN := kal_N_pos hlogN
  have he0 : 0 < e := by linarith
  have hB0 : 0 < B := by linarith
  have hx : 0 < e ^ 2 / B := by positivity
  have hc : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlog : Real.log (e ^ 2 / B) = 2 * Real.log e - Real.log B := by
    rw [Real.log_div (by positivity) hB0.ne', Real.log_pow]
    push_cast
    ring
  rw [← Real.exp_log (pow_pos hx (L + 1)), Real.log_pow, hlog, Real.rpow_def_of_pos hN]
  apply Real.exp_le_exp.2
  set a := Real.log (N : ℝ)
  set b := Real.log e
  set c := Real.log B
  have h1 : c ≤ ν / 2 * b := by
    have := (div_le_iff₀ hν0).1 hBe
    nlinarith
  have h2 : 0 ≤ 2 * b - c := by nlinarith
  have h3 : (1 - ν) * (a / (2 * b)) * (2 * b - c) ≤ ((L : ℝ) + 1) * (2 * b - c) :=
    mul_le_mul_of_nonneg_right hL h2
  have h4 : (1 - ν) * (a / (2 * b)) * (2 * b - c) = (1 - ν) * a * (1 - c / (2 * b)) := by
    field_simp
  have h5 : c / (2 * b) ≤ ν / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h6 : (1 - ν) * a * (1 - ν / 4) ≤ (1 - ν) * a * (1 - c / (2 * b)) := by
    have : 0 ≤ (1 - ν) * a := mul_nonneg (by linarith) hlogN.le
    exact mul_le_mul_of_nonneg_left (by linarith) this
  have h7 : a * (1 - 5 * ν / 4) ≤ (1 - ν) * a * (1 - ν / 4) := by
    nlinarith [mul_nonneg hlogN.le (sq_nonneg ν)]
  have e1 : ((L + 1 : ℕ) : ℝ) = (L : ℝ) + 1 := by push_cast; ring
  rw [e1]
  linarith

/-- `N^(1 - 5ν/4) ≤ e² · m L`. -/
theorem kau_rpow_le_mul_kalM (heps : kalEps ≤ e) {ν : ℝ} {N L : ℕ} (hν0 : 0 < ν)
    (hν1 : ν < 1 / 4) (hlogN : 0 < Real.log N) (hloge : 0 < Real.log e)
    (hL : (1 - ν) * (Real.log N / (2 * Real.log e)) ≤ (L : ℝ) + 1)
    (hBe : 2 * Real.log (128 * bIn 1 1) / ν ≤ Real.log e) :
    (N : ℝ) ^ (1 - 5 * ν / 4) ≤ e ^ 2 * kalM e L := by
  have he := one_le_of_kalEps_le heps
  have hb := one_le_bIn_one
  have hB : (1 : ℝ) ≤ 128 * bIn 1 1 := by linarith
  have h1 := kau_rpow_le_pow hν0 hν1 hB he hlogN hloge hL hBe
  have h2 := kalM_ge_pow heps L
  have hm := kalM_pos heps L
  have hx : 0 ≤ e ^ 2 / (128 * bIn 1 1) := by positivity
  have h3 : e ^ 2 / (128 * bIn 1 1) ≤ e ^ 2 := div_le_self (by positivity) hB
  calc (N : ℝ) ^ (1 - 5 * ν / 4) ≤ (e ^ 2 / (128 * bIn 1 1)) ^ (L + 1) := h1
    _ = (e ^ 2 / (128 * bIn 1 1)) ^ L * (e ^ 2 / (128 * bIn 1 1)) := pow_succ _ _
    _ ≤ kalM e L * e ^ 2 := mul_le_mul h2 h3 hx hm.le
    _ = e ^ 2 * kalM e L := mul_comm _ _

/-! ## The parameter choices -/

/-- The target gap `gap₀ = ⌊m L / 2⌋₊`. -/
def kauGap (e : ℝ) (L : ℕ) : ℕ := ⌊kalM e L / 2⌋₊

/-- The good-anchor depth `D = ⌈12 log N⌉₊`. -/
def kauD (N : ℕ) : ℕ := ⌈12 * Real.log N⌉₊

/-- The horizon `𝔥 = N - D`. -/
def kauH (N : ℕ) : ℕ := N - kauD N

theorem kauGap_le_half (heps : kalEps ≤ e) (L : ℕ) : (kauGap e L : ℝ) ≤ kalM e L / 2 := by
  have := kalM_pos heps L
  exact Nat.floor_le (by positivity)

theorem kauGap_ge {L : ℕ} (h4 : 4 ≤ kalM e L) : kalM e L / 4 ≤ kauGap e L := by
  have := Nat.lt_floor_add_one (kalM e L / 2)
  unfold kauGap
  linarith

theorem one_le_kauGap {L : ℕ} (h4 : 4 ≤ kalM e L) : 1 ≤ kauGap e L := by
  have h1 := kauGap_ge h4
  have h2 : (1 : ℝ) ≤ kauGap e L := by linarith
  exact_mod_cast h2

theorem kauGap_le_kalS (heps : kalEps ≤ e) {N L : ℕ} (hlogN : 1 ≤ Real.log N) :
    kauGap e L ≤ kalS N e L := by
  have h1 := kauGap_le_half heps L
  have h2 := kalS_ge N e L
  have hm := kalM_pos heps L
  have hθ := θK_pos
  have hθ1 := θK_le_one
  have h3 : 2 ≤ 2 / θK := by rw [le_div_iff₀ hθ]; linarith
  have h4 : 2 * kalM e L ≤ 2 / θK * kalM e L := mul_le_mul_of_nonneg_right h3 hm.le
  have h5 : 2 / θK * kalM e L ≤ 2 / θK * kalM e L * Real.log N :=
    le_mul_of_one_le_right (by positivity) hlogN
  have h6 : (kauGap e L : ℝ) ≤ kalS N e L := by linarith
  exact_mod_cast h6

theorem one_le_kauD {N : ℕ} (hlogN : 0 < Real.log N) : 1 ≤ kauD N :=
  Nat.one_le_ceil_iff.2 (by positivity)

theorem kauD_le {N : ℕ} (hbig : 12 * Real.log N + 1 ≤ N) :
    kauD N ≤ N := by
  have h1 : (kauD N : ℝ) < 12 * Real.log N + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2 : (kauD N : ℝ) < N := by linarith
  exact_mod_cast h2.le

theorem sub_kauH {N : ℕ} (hD : kauD N ≤ N) : N - kauH N = kauD N := by
  unfold kauH
  omega

theorem kauH_le {N : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ kauD N) : kauH N ≤ N - 1 := by
  unfold kauH
  omega

theorem cast_sub_kauH {N : ℕ} (hD : kauD N ≤ N) : (N : ℝ) - kauH N = kauD N := by
  have h : kauH N ≤ N := Nat.sub_le _ _
  rw [← Nat.cast_sub h, sub_kauH hD]

theorem kau_exp_D_le {N : ℕ} (hN : (0 : ℝ) < N) :
    Real.exp (-((kauD N : ℝ) / 6)) ≤ 1 / (N : ℝ) ^ 2 := by
  have h1 : 12 * Real.log N ≤ (kauD N : ℝ) := Nat.le_ceil _
  rw [← kal_exp_neg_mul_log hN 2]
  apply Real.exp_le_exp.2
  push_cast
  linarith

theorem kau_goodAnchors_le {N : ℕ} (hN : 1 ≤ N) :
    (Renyi.orderLaw N (goodAnchors N (kauD N))ᶜ).toReal ≤ 2 / N := by
  have h := orderLaw_real_compl_goodAnchors_log_le hN (p := 1) (K := 12) (by norm_num)
  rw [Real.rpow_neg_one] at h
  rw [div_eq_mul_inv]
  exact h

/-! ## The reference failure bound -/

/-- **The reference failure bound** `kepRefDelta` (the sum part of `kepLowDelta`) for a cutoff
`s ≤ 2/θK (c₂ e²)^L log N + 1`, `s ≤ N`. -/
theorem kau_refDelta_le (heps : kalEps ≤ e) {κ C₃ : ℝ} (heκ : 1 ≤ e * κ) (hC₃ : 1 ≤ C₃)
    (hK : ∀ ℓ, refK expSeqMeasure e expCoord ℓ ≤ C₃ ^ ℓ * Real.log (Real.exp 1 * e ^ 2))
    {N L s : ℕ} (hlogN : 1 ≤ Real.log N)
    (hs : (s : ℝ) ≤ 2 / θK * (kalC2 * e ^ 2) ^ L * Real.log N + 1) (hsN : s ≤ N)
    (hu2 : ∀ ℓ < L, kalU κ N e ℓ ≤ 1 / 2) :
    kepRefDelta e L (jK N) (kalU κ N e) (kalR N e s) (kalLamG N) (kalLamN N) ≤
      L * (kalCΔ κ * ((kalC2 * C₃ * e ^ 2) ^ L * e ^ 13 * Real.log N ^ 8 / N)) := by
  have hsum := Finset.sum_le_sum fun ℓ (hℓ : ℓ ∈ range L) =>
    kal_term_le heps heκ hC₃ hlogN (Finset.mem_range.1 hℓ) (hK ℓ) hs hsN
      (hu2 ℓ (Finset.mem_range.1 hℓ))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  exact hsum

/-! ## The expected layer size -/

/-- The bound `kepLayerUp ≤ 8 KcIn (4 N / M + 2) + D + 5` in real variables. -/
theorem kau_layerUp_le_aux {h g p Q N P M Dr : ℝ} (hp : 1 / (8 * KcIn) ≤ p) (hM : 0 < M)
    (hg : M / 4 ≤ g) (hhN : h ≤ N) (hQ : 1 ≤ Q) (hP0 : 0 ≤ P) (hP : P ≤ 2 / N)
    (hN : 1 ≤ N) (hD : N - h ≤ Dr) :
    (h / g + 2) / p + (N / Q + 1) * P + (N - h) / Q + 1 ≤
      8 * KcIn * (4 * (N / M) + 2) + Dr + 5 := by
  have hK := one_le_KcIn
  have hK8 : 0 < 8 * KcIn := by positivity
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hg0 : 0 < g := lt_of_lt_of_le (by positivity) hg
  have hN0 : 0 < N := by linarith
  have hNM : 0 ≤ N / M := by positivity
  have h1 : h / g ≤ 4 * (N / M) := by
    rw [div_le_iff₀ hg0]
    calc h ≤ N := hhN
      _ = 4 * (N / M) * (M / 4) := by field_simp
      _ ≤ 4 * (N / M) * g := mul_le_mul_of_nonneg_left hg (by positivity)
  have hp8 : 1 ≤ 8 * KcIn * p := by
    rw [div_le_iff₀ hK8] at hp
    linarith
  have h2 : (h / g + 2) / p ≤ 8 * KcIn * (4 * (N / M) + 2) := by
    rw [div_le_iff₀ hp0]
    have : 0 ≤ 4 * (N / M) + 2 := by positivity
    nlinarith
  have h3 : (N / Q + 1) * P ≤ 4 := by
    have hNQ : N / Q ≤ N := div_le_self hN0.le hQ
    have hA : (N / Q + 1) * P ≤ (N + 1) * (2 / N) :=
      mul_le_mul (by linarith) hP hP0 (by positivity)
    have hB : (N + 1) * (2 / N) = 2 + 2 / N := by field_simp
    have hC : 2 / N ≤ 2 := by rw [div_le_iff₀ hN0]; linarith
    linarith
  have h4 : (N - h) / Q ≤ Dr := by
    have h0 : 0 ≤ N - h := by linarith
    exact (div_le_self h0 hQ).trans hD
  linarith

/-! ## The final arithmetic -/

/-- From `E H ≤ L + log U / log q + 1`, `L ≤ (1 - ν) h₀`, `U ≤ N^(7ν/4)` and `q ≥ e`:
`E H ≤ (1 + 3ν) h₀`. -/
theorem kau_height_arith {ν E U q : ℝ} {N L : ℕ} (hν0 : 0 < ν) (he : 1 ≤ e)
    (hloge : 1 ≤ Real.log e) (hlogeN : Real.log e ≤ ν / 52 * Real.log N)
    (hE : E ≤ L + Real.log U / Real.log q + 1)
    (hL : (L : ℝ) ≤ (1 - ν) * (Real.log N / (2 * Real.log e)))
    (hU0 : 0 < U) (hU : U ≤ (N : ℝ) ^ (7 * ν / 4)) (hq : e ≤ q) :
    E ≤ (1 + 3 * ν) * (Real.log N / (2 * Real.log e)) := by
  have he0 : 0 < e := by linarith
  have hlogN : 0 < Real.log N := by nlinarith
  have hN0 := kal_N_pos hlogN
  have hlogU : Real.log U ≤ 7 * ν / 4 * Real.log N := by
    have := Real.log_le_log hU0 hU
    rwa [Real.log_rpow hN0] at this
  have hlq : Real.log e ≤ Real.log q := Real.log_le_log he0 hq
  have h1 : Real.log U / Real.log q ≤ 7 * ν / 4 * Real.log N / Real.log q :=
    div_le_div_of_nonneg_right hlogU (by linarith)
  have h2 : 7 * ν / 4 * Real.log N / Real.log q ≤ 7 * ν / 4 * Real.log N / Real.log e :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) hlq
  have h3 : 7 * ν / 4 * Real.log N / Real.log e =
      7 * ν / 2 * (Real.log N / (2 * Real.log e)) := by
    field_simp
    ring
  have h4 : 26 ≤ ν * (Real.log N / (2 * Real.log e)) := by
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith
  nlinarith

/-! ## The eventual regime -/

/-- The numerical conditions of the lower bound (`KalRegime`) together with the two further
conditions used by the upper bound. -/
structure KauRegime (ν C₃ κ : ℝ) (N : ℕ) (e : ℝ) : Prop extends KalRegime ν C₃ κ N e where
  hlogB : 2 * Real.log (128 * bIn 1 1) / ν ≤ Real.log e
  hpolyL : (48 * KcIn + 18) * Real.log N ≤ (N : ℝ) ^ (ν / 4)

namespace KauRegime

variable {ν C₃ κ : ℝ} {N : ℕ}

theorem N_one_le (h : KauRegime ν C₃ κ N e) : (1 : ℝ) ≤ N := by
  have := h.hN3
  have : (3 : ℝ) ≤ N := by exact_mod_cast this
  linarith

theorem e2_le (h : KauRegime ν C₃ κ N e) : e ^ 2 ≤ (N : ℝ) ^ (ν / 26) := by
  have he0 : 0 ≤ e := by linarith [h.one_le_e]
  calc e ^ 2 ≤ ((N : ℝ) ^ (ν / 52)) ^ 2 := pow_le_pow_left₀ he0 h.heN 2
    _ = (N : ℝ) ^ (ν / 26) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h.N_pos.le]
      congr 1
      push_cast
      ring

theorem four_le_rpow (h : KauRegime ν C₃ κ N e) : 4 ≤ (N : ℝ) ^ (ν / 4) := by
  have h1 : (12 : ℝ) ≤ 3 / ν := by
    rw [le_div_iff₀ h.hν0]
    linarith [h.hν1]
  linarith [h.hsmall]

theorem Kc_le_rpow (h : KauRegime ν C₃ κ N e) : 16 * KcIn ≤ (N : ℝ) ^ (ν / 4) := by
  have hK := one_le_KcIn
  have hl := h.hlogN
  have : 48 * KcIn + 18 ≤ (48 * KcIn + 18) * Real.log N := le_mul_of_one_le_right (by positivity) hl
  linarith [h.hpolyL]

theorem rpow_le_N (h : KauRegime ν C₃ κ N e) : (N : ℝ) ^ (ν / 4) ≤ N := by
  calc (N : ℝ) ^ (ν / 4) ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h.N_one_le (by linarith [h.hν1])
    _ = N := Real.rpow_one _

theorem rpow_le_mul_M (h : KauRegime ν C₃ κ N e) :
    (N : ℝ) ^ (1 - 5 * ν / 4) ≤ e ^ 2 * kalM e (kalL ν N e) :=
  kau_rpow_le_mul_kalM h.heps h.hν0 h.hν1 (by linarith [h.hlogN]) (by linarith [h.hloge])
    (lt_kalL_add_one ν N e).le h.hlogB

theorem four_le_M (h : KauRegime ν C₃ κ N e) : 4 ≤ kalM e (kalL ν N e) := by
  have he := h.one_le_e
  have hN0 := h.N_pos
  have he2 : 0 < e ^ 2 := by positivity
  have h1 : 4 * e ^ 2 ≤ (N : ℝ) ^ (ν / 4) * (N : ℝ) ^ (ν / 26) :=
    mul_le_mul h.four_le_rpow h.e2_le he2.le (by positivity)
  have h2 : (N : ℝ) ^ (ν / 4) * (N : ℝ) ^ (ν / 26) ≤ (N : ℝ) ^ (1 - 5 * ν / 4) := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le h.N_one_le (by linarith [h.hν1])
  have h3 := h.rpow_le_mul_M
  have h4 : e ^ 2 * 4 ≤ e ^ 2 * kalM e (kalL ν N e) := by linarith
  exact le_of_mul_le_mul_left h4 he2

theorem N_div_M_le (h : KauRegime ν C₃ κ N e) :
    (N : ℝ) / kalM e (kalL ν N e) ≤ e ^ 2 * (N : ℝ) ^ (5 * ν / 4) := by
  have hN0 := h.N_pos
  have hm := kalM_pos h.heps (kalL ν N e)
  have e1 : (N : ℝ) = (N : ℝ) ^ (1 - 5 * ν / 4) * (N : ℝ) ^ (5 * ν / 4) := by
    rw [← Real.rpow_add hN0]
    norm_num
  rw [div_le_iff₀ hm]
  calc (N : ℝ) = (N : ℝ) ^ (1 - 5 * ν / 4) * (N : ℝ) ^ (5 * ν / 4) := e1
    _ ≤ e ^ 2 * kalM e (kalL ν N e) * (N : ℝ) ^ (5 * ν / 4) :=
        mul_le_mul_of_nonneg_right h.rpow_le_mul_M (by positivity)
    _ = e ^ 2 * (N : ℝ) ^ (5 * ν / 4) * kalM e (kalL ν N e) := by ring

theorem one_le_gap (h : KauRegime ν C₃ κ N e) : 1 ≤ kauGap e (kalL ν N e) :=
  one_le_kauGap h.four_le_M

theorem gap_le_S (h : KauRegime ν C₃ κ N e) : kauGap e (kalL ν N e) ≤ kalS N e (kalL ν N e) :=
  kauGap_le_kalS h.heps h.hlogN

theorem gap_le (h : KauRegime ν C₃ κ N e) :
    (kauGap e (kalL ν N e) : ℝ) ≤ 2 / θK * (kalC2 * e ^ 2) ^ kalL ν N e * Real.log N + 1 := by
  have h1 : (kauGap e (kalL ν N e) : ℝ) ≤ kalS N e (kalL ν N e) := by exact_mod_cast h.gap_le_S
  exact h1.trans (kalS_le h.heps (kalM_le_pow h.heps _))

theorem gap_le_N (h : KauRegime ν C₃ κ N e) : kauGap e (kalL ν N e) ≤ N :=
  h.gap_le_S.trans h.s_lt.le

theorem D_le (h : KauRegime ν C₃ κ N e) : kauD N ≤ N := by
  have hK := one_le_KcIn
  have hl := h.hlogN
  have h1 : 12 * Real.log N + 1 ≤ (48 * KcIn + 18) * Real.log N := by nlinarith
  exact kauD_le (by linarith [h.hpolyL, h.rpow_le_N])

/-- **The reference failure bound is at most `1 / (16 KcIn)`.** -/
theorem refDelta_le (h : KauRegime ν C₃ κ N e) :
    kepRefDelta e (kalL ν N e) (jK N) (kalU κ N e) (kalR N e (kauGap e (kalL ν N e)))
      (kalLamG N) (kalLamN N) ≤ 1 / (16 * KcIn) := by
  have hδ := kau_refDelta_le h.heps h.heκ h.hC₃ h.hK h.hlogN h.gap_le h.gap_le_N
    (fun ℓ hℓ => h.u_half hℓ)
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
  have hK := one_le_KcIn
  have h16 : ((N : ℝ) ^ (ν / 4))⁻¹ ≤ 1 / (16 * KcIn) := by
    rw [one_div]
    exact inv_anti₀ (by positivity) h.Kc_le_rpow
  linarith

/-- **The trial success probability is at least `1 / (8 KcIn)`.** -/
theorem trialProb_ge (h : KauRegime ν C₃ κ N e) :
    1 / (8 * KcIn) ≤ kepTrialProb e N (kalL ν N e) (kauH N) (jK N) (kalU κ N e)
      (kalR N e (kauGap e (kalL ν N e))) (kalLamG N) (kalLamN N) := by
  have hδ := h.refDelta_le
  have hK := one_le_KcIn
  have hN0 := h.N_pos
  have hE := kau_exp_D_le hN0
  have hN2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := le_self_pow₀ h.N_one_le (by norm_num)
  have h16 : 1 / (N : ℝ) ^ 2 ≤ 1 / (16 * KcIn) :=
    one_div_le_one_div_of_le (by positivity) (h.Kc_le_rpow.trans (h.rpow_le_N.trans hN2))
  have e1 : 1 / (4 * KcIn) - 1 / (16 * KcIn) - 1 / (16 * KcIn) = 1 / (8 * KcIn) := by
    field_simp
    ring
  unfold kepTrialProb
  rw [sub_kauH h.D_le]
  linarith

/-- **The expected layer size is at most `N^(7ν/4)`.** -/
theorem layerUp_le (h : KauRegime ν C₃ κ N e) :
    kepLayerUp e N (kalL ν N e) (kauH N) (kauGap e (kalL ν N e)) (kauD N) (jK N) (kalU κ N e)
      (kalR N e (kauGap e (kalL ν N e))) (kalLamG N) (kalLamN N) ≤ (N : ℝ) ^ (7 * ν / 4) := by
  have hK := one_le_KcIn
  have hN0 := h.N_pos
  have hN1 := h.N_one_le
  have he := h.one_le_e
  have hl := h.hlogN
  have hq1 : (1 : ℝ) ≤ ((⌊2 * e⌋₊ : ℝ) + 1) ^ kalL ν N e :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ⌊2 * e⌋₊)])
  have hm := kalM_pos h.heps (kalL ν N e)
  have hH : (kauH N : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N (kauD N)
  have hP0 : 0 ≤ (Renyi.orderLaw N (goodAnchors N (kauD N))ᶜ).toReal := ENNReal.toReal_nonneg
  have hA := kau_layerUp_le_aux h.trialProb_ge hm (kauGap_ge h.four_le_M) hH hq1 hP0
    (kau_goodAnchors_le (by exact_mod_cast hN1)) hN1 (cast_sub_kauH h.D_le).le
  have hD : (kauD N : ℝ) ≤ 12 * Real.log N + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hX := h.N_div_M_le
  have hX1 : 1 ≤ e ^ 2 * (N : ℝ) ^ (5 * ν / 4) := by
    have : 1 ≤ e ^ 2 := one_le_pow₀ he
    have : 1 ≤ (N : ℝ) ^ (5 * ν / 4) := Real.one_le_rpow hN1 (by linarith [h.hν0])
    nlinarith
  set X := e ^ 2 * (N : ℝ) ^ (5 * ν / 4) with hXdef
  have h1 : 8 * KcIn * (4 * ((N : ℝ) / kalM e (kalL ν N e)) + 2) + kauD N + 5 ≤
      X * ((48 * KcIn + 18) * Real.log N) := by
    have : 8 * KcIn * (4 * ((N : ℝ) / kalM e (kalL ν N e)) + 2) ≤ 8 * KcIn * (4 * X + 2) := by
      gcongr
    have hXL : 1 ≤ X * Real.log N := by nlinarith
    have hKX : KcIn * X ≤ KcIn * X * Real.log N :=
      le_mul_of_one_le_right (by positivity) hl
    have hKXL : KcIn ≤ KcIn * (X * Real.log N) := le_mul_of_one_le_right (by positivity) hXL
    have hLX : Real.log N ≤ X * Real.log N := le_mul_of_one_le_left (by positivity) hX1
    have e1 : X * ((48 * KcIn + 18) * Real.log N) =
        32 * (KcIn * X * Real.log N) + 16 * (KcIn * (X * Real.log N)) +
          12 * (X * Real.log N) + 6 * (X * Real.log N) := by ring
    rw [e1]
    linarith
  have h2 : X * ((48 * KcIn + 18) * Real.log N) ≤
      (N : ℝ) ^ (ν / 26) * (N : ℝ) ^ (5 * ν / 4) * (N : ℝ) ^ (ν / 4) := by
    rw [hXdef]
    gcongr
    · exact h.e2_le
    · exact h.hpolyL
  have h3 : (N : ℝ) ^ (ν / 26) * (N : ℝ) ^ (5 * ν / 4) * (N : ℝ) ^ (ν / 4) ≤
      (N : ℝ) ^ (7 * ν / 4) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [h.hν0])
  unfold kepLayerUp
  linarith

theorem layerUp_pos (h : KauRegime ν C₃ κ N e) :
    0 < kepLayerUp e N (kalL ν N e) (kauH N) (kauGap e (kalL ν N e)) (kauD N) (jK N)
      (kalU κ N e) (kalR N e (kauGap e (kalL ν N e))) (kalLamG N) (kalLamN N) := by
  have hK := one_le_KcIn
  have hp : 0 < kepTrialProb e N (kalL ν N e) (kauH N) (jK N) (kalU κ N e)
      (kalR N e (kauGap e (kalL ν N e))) (kalLamG N) (kalLamN N) :=
    lt_of_lt_of_le (by positivity) h.trialProb_ge
  have hq : (0 : ℝ) < ((⌊2 * e⌋₊ : ℝ) + 1) ^ kalL ν N e := by positivity
  have hP0 : 0 ≤ (Renyi.orderLaw N (goodAnchors N (kauD N))ᶜ).toReal := ENNReal.toReal_nonneg
  have hH : (kauH N : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N (kauD N)
  have h1 : 0 ≤ ((kauH N : ℝ) / kauGap e (kalL ν N e) + 2) /
      kepTrialProb e N (kalL ν N e) (kauH N) (jK N) (kalU κ N e)
      (kalR N e (kauGap e (kalL ν N e))) (kalLamG N) (kalLamN N) := by positivity
  have h2 : 0 ≤ ((N : ℝ) / ((⌊2 * e⌋₊ : ℝ) + 1) ^ kalL ν N e + 1) *
      (Renyi.orderLaw N (goodAnchors N (kauD N))ᶜ).toReal := by positivity
  have h3 : 0 ≤ ((N : ℝ) - kauH N) / ((⌊2 * e⌋₊ : ℝ) + 1) ^ kalL ν N e :=
    div_nonneg (by linarith) hq.le
  unfold kepLayerUp
  linarith

end KauRegime

/-! ## The upper bound -/

variable {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Fixed-parameter upper bound.**  In the regime `KauRegime`, the expected ALG-PGM height
on `N` sorted Model K samples is at most `(1 + 3ν) log N / (2 log e)`. -/
theorem integral_epHeight_kKeys_le_of_regime (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {ν C₃ : ℝ} {N : ℕ} (h : KauRegime ν C₃ (2 * (Lf / fmin ^ 3 + 1) * fmax) N e) :
    ∫ ω, (epHeight e (kKeys X N ω) N : ℝ) ∂P ≤
      (1 + 3 * ν) * (Real.log N / (2 * Real.log e)) := by
  have hκ := h.kappa_pos
  have hN : 1 ≤ N := by have := h.hN3; omega
  have hmain := integral_epHeight_kKeys_le hf hX hind h.heps (N := N) (L := kalL ν N e)
    (𝔥 := kauH N) (gap₀ := kauGap e (kalL ν N e)) (D := kauD N) (Tmax := kalT N e) (j := jK N)
    (d := kalD N e (kauGap e (kalL ν N e)) (kalL ν N e)) (u := kalU _ N e) (Gmax := kalG N e)
    (R := kalR N e (kauGap e (kalL ν N e))) (lamG := kalLamG N) (lamN := kalLamN N)
    hN (kauH_le hN (one_le_kauD (by linarith [h.hlogN]))) h.one_le_gap
    (by have := kauGap_le_half h.heps (kalL ν N e); unfold kalM at this; linarith)
    (sub_kauH h.D_le).ge (fun ℓ hℓ => ⟨h.u_pos ℓ, h.u_half hℓ⟩)
    (fun ℓ _ => kalR_mul_ge h.heps N _ ℓ) le_rfl (fun ℓ _ => le_rfl)
    (fun ℓ hℓ => kalD_ge h.heps hℓ)
    (fun ℓ hℓ => kalU_fixed h.heps hκ.le (by linarith [h.hlogN])
      (by linarith [h.u_half hℓ]))
    (lt_of_lt_of_le (by have := one_le_KcIn; positivity) h.trialProb_ge)
  have hq : e ≤ (⌊2 * e⌋₊ : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (2 * e)
    linarith [h.one_le_e]
  exact kau_height_arith h.hν0 h.one_le_e h.hloge h.log_e_le hmain h.L_le h.layerUp_pos
    h.layerUp_le hq

/-- The regime conditions hold eventually along `n → ∞`, `ε → ∞`, `log ε / log n → 0`. -/
theorem eventually_kauRegime {C₃ κ eps₁ : ℝ} (hC₃ : 1 ≤ C₃) (hκ : 0 < κ)
    (hK : ∀ eps ≥ eps₁, ∀ ℓ,
      refK expSeqMeasure eps expCoord ℓ ≤ C₃ ^ ℓ * Real.log (Real.exp 1 * eps ^ 2))
    {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0))
    {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1 / 4) :
    ∀ᶠ k in atTop, KauRegime ν C₃ κ (n k) (ε k) := by
  have hν4 : 0 < ν / 4 := by linarith
  filter_upwards [eventually_kalRegime hC₃ hκ hK hn hε hεn hν0 hν1,
    hε.eventually_ge_atTop (Real.exp (2 * Real.log (128 * bIn 1 1) / ν)),
    hn.eventually (eventually_mul_log_pow_le_rpow (48 * KcIn + 18) 1 hν4)] with k h1 h2 h3
  refine ⟨h1, ?_, ?_⟩
  · have := Real.log_le_log (Real.exp_pos _) h2
    rwa [Real.log_exp] at this
  · simpa only [pow_one] using h3

/-- **Asymptotic upper bound for the Model K ALG-PGM height.**  Along `n → ∞`, `ε → ∞` with
`log ε / log n → 0`, for every `ν ∈ (0, 1/4)`, eventually
`E H ≤ (1 + 3ν) · log n / (2 log ε)`. -/
theorem integral_epHeight_kKeys_le_asymp (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0))
    {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1 / 4) :
    ∀ᶠ k in atTop, ∫ ω, (epHeight (ε k) (kKeys X (n k) ω) (n k) : ℝ) ∂P ≤
      (1 + 3 * ν) * (Real.log (n k) / (2 * Real.log (ε k))) := by
  obtain ⟨C₃, hC₃, eps₁, hK⟩ := refK_expCoord_le
  filter_upwards [eventually_kauRegime hC₃ (kal_kappa_pos hf) hK hn hε hεn hν0 hν1] with k hk
  exact integral_epHeight_kKeys_le_of_regime hf hX hind hk

end

end PGM
