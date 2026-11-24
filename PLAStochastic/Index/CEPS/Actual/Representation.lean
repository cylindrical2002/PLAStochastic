import PLAStochastic.Index.CEPS.Actual.Certificate

/-!
# P-CEPS WP8: the exact marked representation (E)

`research/2026-10-02-lean-ceps/blueprint-CS.md` §2.1, lemma S-1. For a gap law with a bounded
density on `(0, ∞)`, `ε > 0`, `T < ∞` a.s., `E T < ∞` and `Re t ≥ 0`, with `m = ⌊2ε⌋`:

`E e^{-t S_T} = φ(t)^{m+1} - (1 - φ(t)) ∫_{(-1, ∞)} J_t(μ) dμ`   (`CepsGapDensity.ceps_exact_marked_rep`),

`J_t = e^{tl} H_t² 𝔘` (`cepsActualPair`), and the domination `‖J_t(μ)‖ ≤ ‖J_0(μ)‖`
(`norm_cepsActualPair_le`), `∫ ‖J_0‖ = E T - m - 1` (`integral_norm_cepsActualPair_zero`).

Route: the telescoping identity (P4) reduces `E e^{-tS_T}` to `∑_k E[e^{-tS_k}; T > k]`. For
`k ≤ m` these are `φ^k`; for `k > m` the certificate decomposition and the exact certificate integral
write them as `∫ ∑_{i+L+r=k} (L-w) k_L e^{-t((1+μ)k-l)} h_i h_r dμ` (`cepsLayerSum`). Pointwise in
`μ > -1` the layer sums are the Cauchy product of the series `e^{tl} H_t`, `𝔘`, `H_t`
(`hasSum_cepsLayerSum`); the series in `k` is exchanged with the `μ`-integral using the `t = 0`
layer sums as a dominating family, whose integrals are `P(T > k) - 1{k ≤ m}`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

variable {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ} {D : ℝ}

/-! ## Short bridges vanish -/

/-- A bridge of `L ≤ 2ε` steps cannot rise by `2ε(1+μ)`: `k_L^{(μ)}(0, l) = 0`. -/
theorem CepsGapDensity.cepsBridgeDens_eq_zero_of_short (hf : CepsGapDensity ν f D) {eps : ℝ}
    {μ : ℝ} (hμ : -1 < μ) {n : ℕ} (hn : (n : ℝ) + 1 ≤ 2 * eps) :
    cepsBridgeDens ν f μ (2 * eps * (1 + μ)) (n + 1) = 0 := by
  unfold cepsBridgeDens
  rw [krDens_succ]
  refine (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [hf.ae_gapKeys_nonneg] with g hg
  unfold krKer
  have harg : (kWalk 0 (1 + μ) 1 g n + (1 + μ) - 2 * eps * (1 + μ)) / |(1 : ℝ)| ≤ 0 := by
    unfold kWalk
    rw [abs_one, div_one]
    have h1 : 0 < 1 + μ := by linarith
    have h2 := hg n
    nlinarith
  rw [abs_one, div_one] at harg ⊢
  rw [hf.eq_zero _ (by simpa using harg)]
  ring

/-! ## The triple terms -/

/-- The `(i, L, r)` term `(L - w) k_L(μ) e^{-t((1+μ)k - l)} h_i(μ) h_r(μ)`, `k = i + L + r`;
zero for `L = 0`. -/
def cepsTripleTerm (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ) (t : ℂ) (i L r : ℕ)
    (μ : ℝ) : ℂ :=
  if L = 0 then 0 else
    (((L : ℝ) - 2 * eps : ℝ) : ℂ) * cepsBridgeMul ν f eps L (cepsOuterMean ν t eps i r (i + L + r)) μ

/-- The survival probability `P_n(μ)` of the outer walk in `[0, 2ε(1+μ)]`. -/
def cepsOuterSurv (ν : ProbabilityMeasure ℝ) (eps μ : ℝ) (n : ℕ) : ℝ :=
  krSurv (Icc 0 (2 * eps * (1 + μ))) (ν : Measure ℝ) (-(1 + μ)) (-1) n 0

/-- The `t = 0` triple term, as a real number: `(L - w) k_L(μ) P_i(μ) P_r(μ)` for `L > 2ε`. -/
def cepsTripleReal (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ) (i L r : ℕ) (μ : ℝ) : ℝ :=
  if 2 * eps < L then
    ((L : ℝ) - 2 * eps) * cepsBridgeDens ν f μ (2 * eps * (1 + μ)) L *
      (cepsOuterSurv ν eps μ i * cepsOuterSurv ν eps μ r)
  else 0

theorem cepsStripTerm_zero (ν : ProbabilityMeasure ℝ) (μ l : ℝ) (n : ℕ) :
    cepsStripTerm ν 0 μ l n =
      (krSurv (Icc 0 l) (ν : Measure ℝ) (-(1 + μ)) (-1) n 0 : ℂ) := by
  unfold cepsStripTerm
  rw [krSurv_eq_integral measurableSet_Icc, ← integral_complex_ofReal]
  simp

theorem cepsOuterMean_zero (ν : ProbabilityMeasure ℝ) (eps : ℝ) (i r k : ℕ) (μ : ℝ) :
    cepsOuterMean ν 0 eps i r k μ =
      ((cepsOuterSurv ν eps μ i * cepsOuterSurv ν eps μ r : ℝ) : ℂ) := by
  rw [cepsOuterMean_eq, cepsStripTerm_zero, cepsStripTerm_zero]
  simp [cepsOuterSurv]

theorem CepsGapDensity.cepsTripleTerm_eq_zero (hf : CepsGapDensity ν f D) {eps : ℝ} (t : ℂ)
    {i L r : ℕ} (hL : (L : ℝ) ≤ 2 * eps) {μ : ℝ} (hμ : -1 < μ) :
    cepsTripleTerm ν f eps t i L r μ = 0 := by
  unfold cepsTripleTerm
  split_ifs with h0
  · rfl
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have hn : (n : ℝ) + 1 ≤ 2 * eps := by push_cast at hL; linarith
    simp [cepsBridgeMul, hf.cepsBridgeDens_eq_zero_of_short hμ hn]

theorem CepsGapDensity.integral_cepsTripleTerm (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) {t : ℂ} (ht : 0 ≤ t.re) (i : ℕ) {L : ℕ} (r : ℕ) (hL : 2 * eps < L) :
    ∫ μ in Ioi (-1 : ℝ), cepsTripleTerm ν f eps t i L r μ =
      ∫ g, ({g' : ℕ → ℝ | certOK eps (gapKeys g') (i + L + r) i (i + L)}.indicator
        (fun _ => (1 : ℂ)) g) * Complex.exp (-t * gapKeys g (i + L + r)) ∂(iidLaw ν) := by
  have hk : 2 * eps ≤ ((i + L + r : ℕ) : ℝ) := by
    push_cast
    linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i), (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hL0 : L ≠ 0 := by
    rintro rfl
    simp at hL
    linarith
  rw [hf.integral_cert_eq_perm heps hL t, integral_cepsPermInt ν heps hL ht,
    hf.integral_midAlive_mul heps hL (measurable_cepsOuterMean ν t eps i r (i + L + r))
      (norm_cepsOuterMean_le_one ν ht heps hk)]
  simp only [cepsTripleTerm, hL0, if_false]
  rw [integral_const_mul]
  rfl

theorem CepsGapDensity.integrableOn_cepsTripleTerm (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) {t : ℂ} (ht : 0 ≤ t.re) (i L r : ℕ) :
    IntegrableOn (cepsTripleTerm ν f eps t i L r) (Ioi (-1 : ℝ)) := by
  by_cases hL : 2 * eps < L
  · have hk : 2 * eps ≤ ((i + L + r : ℕ) : ℝ) := by
      push_cast
      linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i), (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
    have hL0 : L ≠ 0 := by
      rintro rfl
      simp at hL
      linarith
    have h := (hf.integrable_cepsBridgeMul heps hL (measurable_cepsOuterMean ν t eps i r (i + L + r))
      (norm_cepsOuterMean_le_one ν ht heps hk)).const_mul (((L : ℝ) - 2 * eps : ℝ) : ℂ)
    refine h.integrableOn.congr_fun (fun μ _ => ?_) measurableSet_Ioi
    simp only [cepsTripleTerm, hL0, if_false]
  · refine (integrableOn_zero).congr_fun (fun μ hμ => ?_) measurableSet_Ioi
    exact (hf.cepsTripleTerm_eq_zero t (not_lt.1 hL) hμ).symm

theorem CepsGapDensity.cepsTripleReal_nonneg (hf : CepsGapDensity ν f D) (eps : ℝ) (i L r : ℕ)
    (μ : ℝ) : 0 ≤ cepsTripleReal ν f eps i L r μ := by
  unfold cepsTripleReal
  split_ifs with hL
  · have h1 : 0 ≤ (L : ℝ) - 2 * eps := by linarith
    have h2 := hf.cepsBridgeDens_nonneg μ (2 * eps * (1 + μ)) L
    have h3 := krSurv_nonneg measurableSet_Icc ν (-(1 + μ)) (-1) i 0
      (J := Icc 0 (2 * eps * (1 + μ)))
    have h4 := krSurv_nonneg measurableSet_Icc ν (-(1 + μ)) (-1) r 0
      (J := Icc 0 (2 * eps * (1 + μ)))
    unfold cepsOuterSurv
    positivity
  · exact le_rfl

theorem CepsGapDensity.cepsTripleTerm_zero (hf : CepsGapDensity ν f D) {eps : ℝ} (heps : 0 < eps)
    (i L r : ℕ) {μ : ℝ} (hμ : -1 < μ) :
    cepsTripleTerm ν f eps 0 i L r μ = (cepsTripleReal ν f eps i L r μ : ℂ) := by
  by_cases hL : 2 * eps < L
  · have hL0 : L ≠ 0 := by
      rintro rfl
      simp at hL
      linarith
    simp only [cepsTripleTerm, cepsTripleReal, hL0, hL, if_false, if_true, cepsBridgeMul,
      cepsOuterMean_zero]
    push_cast
    ring
  · rw [hf.cepsTripleTerm_eq_zero 0 (not_lt.1 hL) hμ]
    simp [cepsTripleReal, hL]

theorem CepsGapDensity.norm_cepsTripleTerm_le (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) {t : ℂ} (ht : 0 ≤ t.re) (i L r : ℕ) {μ : ℝ} (hμ : -1 < μ) :
    ‖cepsTripleTerm ν f eps t i L r μ‖ ≤ cepsTripleReal ν f eps i L r μ := by
  by_cases hL : 2 * eps < L
  · have hL0 : L ≠ 0 := by
      rintro rfl
      simp at hL
      linarith
    simp only [cepsTripleTerm, cepsTripleReal, hL0, hL, if_false, if_true, cepsBridgeMul,
      cepsOuterMean_eq]
    have hk : 0 ≤ (1 + μ) * ((i + L + r : ℕ) : ℝ) - 2 * eps * (1 + μ) := by
      have : 2 * eps ≤ ((i + L + r : ℕ) : ℝ) := by
        push_cast
        linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i), (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
      nlinarith
    have hE := norm_cexp_neg_mul_le_one ht hk
    have hi := norm_cepsStripTerm_le ν ht μ (2 * eps * (1 + μ)) i
    have hr := norm_cepsStripTerm_le ν ht μ (2 * eps * (1 + μ)) r
    have hkL := hf.cepsBridgeDens_nonneg μ (2 * eps * (1 + μ)) L
    have hc : 0 ≤ (L : ℝ) - 2 * eps := by linarith
    have hsi := krSurv_nonneg measurableSet_Icc ν (-(1 + μ)) (-1) i 0
      (J := Icc 0 (2 * eps * (1 + μ)))
    have hsr := krSurv_nonneg measurableSet_Icc ν (-(1 + μ)) (-1) r 0
      (J := Icc 0 (2 * eps * (1 + μ)))
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg hkL]
    unfold cepsOuterSurv
    calc ((L : ℝ) - 2 * eps) * (cepsBridgeDens ν f μ (2 * eps * (1 + μ)) L *
          (‖cepsStripTerm ν t μ (2 * eps * (1 + μ)) i‖ * ‖cepsStripTerm ν t μ (2 * eps * (1 + μ)) r‖ *
            ‖Complex.exp (-t * (((1 + μ) * ((i + L + r : ℕ) : ℝ) - 2 * eps * (1 + μ) : ℝ) : ℂ))‖))
        ≤ ((L : ℝ) - 2 * eps) * (cepsBridgeDens ν f μ (2 * eps * (1 + μ)) L *
          (krSurv (Icc 0 (2 * eps * (1 + μ))) (ν : Measure ℝ) (-(1 + μ)) (-1) i 0 *
            krSurv (Icc 0 (2 * eps * (1 + μ))) (ν : Measure ℝ) (-(1 + μ)) (-1) r 0 * 1)) := by
          gcongr
      _ = _ := by ring
  · rw [hf.cepsTripleTerm_eq_zero t (not_lt.1 hL) hμ, norm_zero]
    exact hf.cepsTripleReal_nonneg eps i L r μ

theorem CepsGapDensity.integral_cepsTripleReal (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) (i : ℕ) {L : ℕ} (r : ℕ) (hL : 2 * eps < L) :
    ∫ μ in Ioi (-1 : ℝ), cepsTripleReal ν f eps i L r μ =
      (iidLaw ν).real {g' : ℕ → ℝ | certOK eps (gapKeys g') (i + L + r) i (i + L)} := by
  have h := hf.integral_cepsTripleTerm heps (t := 0) le_rfl i r hL
  rw [setIntegral_congr_fun measurableSet_Ioi fun μ hμ => hf.cepsTripleTerm_zero heps i L r hμ,
    integral_complex_ofReal] at h
  simp only [neg_zero, zero_mul, Complex.exp_zero, mul_one] at h
  rw [show (fun g => {g' : ℕ → ℝ | certOK eps (gapKeys g') (i + L + r) i (i + L)}.indicator
      (fun _ => (1 : ℂ)) g) = fun g => (({g' : ℕ → ℝ | certOK eps (gapKeys g') (i + L + r) i
        (i + L)}.indicator (fun _ => (1 : ℝ)) g : ℝ) : ℂ) from funext fun g => indicator_one_ofReal _ g,
    integral_complex_ofReal, integral_indicator (measurableSet_certOK eps _ i (i + L)),
    setIntegral_const, smul_eq_mul, mul_one] at h
  exact_mod_cast h

theorem CepsGapDensity.integrableOn_cepsTripleReal (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) (i L r : ℕ) :
    IntegrableOn (cepsTripleReal ν f eps i L r) (Ioi (-1 : ℝ)) := by
  have h : IntegrableOn (fun μ => (cepsTripleTerm ν f eps 0 i L r μ).re) (Ioi (-1 : ℝ)) :=
    (hf.integrableOn_cepsTripleTerm heps (t := 0) le_rfl i L r).re
  refine h.congr_fun (fun μ hμ => ?_) measurableSet_Ioi
  simp only [hf.cepsTripleTerm_zero heps i L r hμ, Complex.ofReal_re]

/-! ## Layer sums -/

/-- The layer sum `∑_{i + L + r = k} (triple term)`, as a sum over `j = i + L ≤ k` and `i ≤ j`. -/
def cepsLayerSum (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ) (t : ℂ) (k : ℕ) (μ : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (j + 1), cepsTripleTerm ν f eps t i (j - i) (k - j) μ

/-- The real `t = 0` layer sum. -/
def cepsLayerReal (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ) (k : ℕ) (μ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (j + 1), cepsTripleReal ν f eps i (j - i) (k - j) μ

theorem CepsGapDensity.integrableOn_cepsLayerSum (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) {t : ℂ} (ht : 0 ≤ t.re) (k : ℕ) :
    IntegrableOn (cepsLayerSum ν f eps t k) (Ioi (-1 : ℝ)) := by
  unfold cepsLayerSum
  exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ =>
    hf.integrableOn_cepsTripleTerm heps ht i (j - i) (k - j)

theorem CepsGapDensity.integrableOn_cepsLayerReal (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) (k : ℕ) :
    IntegrableOn (cepsLayerReal ν f eps k) (Ioi (-1 : ℝ)) := by
  unfold cepsLayerReal
  exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ =>
    hf.integrableOn_cepsTripleReal heps i (j - i) (k - j)

theorem CepsGapDensity.cepsLayerReal_nonneg (hf : CepsGapDensity ν f D) (eps : ℝ) (k : ℕ)
    (μ : ℝ) : 0 ≤ cepsLayerReal ν f eps k μ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hf.cepsTripleReal_nonneg eps _ _ _ μ

theorem CepsGapDensity.norm_cepsLayerSum_le (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) {t : ℂ} (ht : 0 ≤ t.re) (k : ℕ) {μ : ℝ} (hμ : -1 < μ) :
    ‖cepsLayerSum ν f eps t k μ‖ ≤ cepsLayerReal ν f eps k μ := by
  unfold cepsLayerSum cepsLayerReal
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact hf.norm_cepsTripleTerm_le heps ht i (j - i) (k - j) hμ

theorem CepsGapDensity.cepsLayerSum_zero (hf : CepsGapDensity ν f D) {eps : ℝ} (heps : 0 < eps)
    (k : ℕ) {μ : ℝ} (hμ : -1 < μ) :
    cepsLayerSum ν f eps 0 k μ = (cepsLayerReal ν f eps k μ : ℂ) := by
  unfold cepsLayerSum cepsLayerReal
  push_cast
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  exact hf.cepsTripleTerm_zero heps i (j - i) (k - j) hμ

/-! ## The layer identity -/

theorem two_mul_lt_of_floor_lt {eps : ℝ} {k : ℕ} (hk : ¬ k ≤ ⌊2 * eps⌋₊) :
    2 * eps < k := by
  have h1 := Nat.lt_floor_add_one (2 * eps)
  have h2 : ⌊2 * eps⌋₊ + 1 ≤ k := by omega
  have h3 : ((⌊2 * eps⌋₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast h2
  push_cast at h3
  linarith

theorem cast_le_two_mul_of_le_floor {eps : ℝ} (heps : 0 ≤ eps) {k L : ℕ} (hLk : L ≤ k)
    (hk : k ≤ ⌊2 * eps⌋₊) : (L : ℝ) ≤ 2 * eps := by
  have h1 : (L : ℝ) ≤ (⌊2 * eps⌋₊ : ℝ) := by exact_mod_cast hLk.trans hk
  exact h1.trans (Nat.floor_le (by positivity))

theorem indicator_mul_const_eq {α : Type*} (A : Set α) (F : α → ℂ) (g : α) :
    A.indicator F g = A.indicator (fun _ => (1 : ℂ)) g * F g := by
  by_cases h : g ∈ A
  · rw [indicator_of_mem h, indicator_of_mem h, one_mul]
  · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]

/-- **The layer identity.** `E[e^{-tS_k}; T > k] = 1{k ≤ m} φ(t)^k + ∫_{μ > -1} (layer sum)`. -/
theorem CepsGapDensity.cepsSurvLaplace_eq_layer (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) {t : ℂ} (ht : 0 ≤ t.re) (k : ℕ) :
    cepsSurvLaplace ν eps t k = (if k ≤ ⌊2 * eps⌋₊ then cepsLaplace ν t ^ k else 0) +
      ∫ μ in Ioi (-1 : ℝ), cepsLayerSum ν f eps t k μ := by
  by_cases hk : k ≤ ⌊2 * eps⌋₊
  · rw [if_pos hk, hf.cepsSurvLaplace_of_le heps.le ht hk]
    have h0 : ∀ μ ∈ Ioi (-1 : ℝ), cepsLayerSum ν f eps t k μ = 0 := fun μ hμ =>
      Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun i _ =>
        hf.cepsTripleTerm_eq_zero t (cast_le_two_mul_of_le_floor heps.le
          ((Nat.sub_le j i).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) hk) hμ
    rw [setIntegral_congr_fun measurableSet_Ioi h0, integral_zero, add_zero]
  rw [if_neg hk, zero_add]
  have hk2 := two_mul_lt_of_floor_lt hk
  have hint : Integrable (fun g : ℕ → ℝ => Complex.exp (-t * gapKeys g k)) (wordLaw ν ν ∅) := by
    rw [wordLaw_self]
    refine (integrable_const (1 : ℝ)).mono' (measurable_cexp_gapKeys t k).aestronglyMeasurable ?_
    filter_upwards [hf.ae_gapKeys_nonneg] with g hg
    exact norm_cexp_neg_mul_le_one ht (hg k)
  have hdec := cert_integral_indicator_eq_sum hf.absolutelyContinuous hf.absolutelyContinuous
    hf.measure_Iic_zero hf.measure_Iic_zero ∅ hk2 hint
  simp only [wordLaw_self] at hdec
  unfold cepsSurvLaplace survSet
  rw [hdec]
  -- the layer integral as a double sum of certificate integrals
  unfold cepsLayerSum
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ =>
    hf.integrableOn_cepsTripleTerm heps ht i (j - i) (k - j)]
  simp_rw [integral_finsetSum _ fun i _ => hf.integrableOn_cepsTripleTerm heps ht i _ _]
  -- the certificate pairs as a double sum
  set Y : ℕ × ℕ → ℂ := fun ij => ∫ g, {g' : ℕ → ℝ | certOK eps (gapKeys g') k ij.1 ij.2}.indicator
    (fun g => Complex.exp (-t * gapKeys g k)) g ∂(iidLaw ν) with hY
  set P : ℕ × ℕ → Prop := fun ij => ij.1 < ij.2 ∧ 2 * eps < (ij.2 : ℝ) - ij.1 with hP
  have hcp : certPairs eps k = (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter P := rfl
  rw [hcp, Finset.sum_filter, Finset.sum_product, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : j + 1 ≤ k + 1)) ?_]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - i := by rw [Nat.cast_sub hij]
    by_cases hL : 2 * eps < ((j - i : ℕ) : ℝ)
    · have hPij : P (i, j) := by
        refine ⟨?_, by rw [← hcast]; exact hL⟩
        by_contra h
        have : j - i = 0 := by omega
        rw [this] at hL
        simp at hL
        linarith
      rw [if_pos hPij, hf.integral_cepsTripleTerm heps ht i (k - j) hL]
      have e1 : i + (j - i) + (k - j) = k := by omega
      have e2 : i + (j - i) = j := by omega
      rw [e1, e2]
      exact integral_congr_ae (Eventually.of_forall fun g =>
        indicator_mul_const_eq _ (fun g => Complex.exp (-t * gapKeys g k)) g)
    · have hPij : ¬ P (i, j) := fun h => hL (by rw [hcast]; exact h.2)
      rw [if_neg hPij]
      refine (setIntegral_eq_zero_of_forall_eq_zero fun μ hμ => ?_).symm
      exact hf.cepsTripleTerm_eq_zero t (not_lt.1 hL) hμ
  · intro i _ hi
    have : j < i := by
      have := Finset.mem_range.not.1 hi
      omega
    rw [if_neg fun h => by have := h.1; simp at this; omega]

/-! ## The Cauchy product -/

/-- `e^{-qn} h_n(μ)` at `q = t(1+μ)`, `l = 2ε(1+μ)`. -/
def cepsHSeq (ν : ProbabilityMeasure ℝ) (t : ℂ) (eps μ : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (-(t * ((1 + μ : ℝ) : ℂ)) * n) * cepsStripTerm ν t μ (2 * eps * (1 + μ)) n

/-- The terms of `𝔘`: zero at `0`, then `(n - w) e^{-qn} k_n(μ)`. -/
def cepsUSeq (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (t : ℂ) (eps μ : ℝ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => (((n : ℝ) + 1 - 2 * eps : ℝ) : ℂ) * Complex.exp (-(t * ((1 + μ : ℝ) : ℂ)) * ((n : ℂ) + 1)) *
      cepsBridgeDens ν f μ (2 * eps * (1 + μ)) (n + 1)

theorem cepsTripleTerm_eq_mul (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ) (t : ℂ)
    (i L r : ℕ) (μ : ℝ) :
    Complex.exp (t * ((2 * eps * (1 + μ) : ℝ) : ℂ)) * cepsHSeq ν t eps μ i *
        cepsUSeq ν f t eps μ L * cepsHSeq ν t eps μ r = cepsTripleTerm ν f eps t i L r μ := by
  cases L with
  | zero => simp [cepsUSeq, cepsTripleTerm]
  | succ n =>
    simp only [cepsUSeq, cepsTripleTerm, Nat.succ_ne_zero, if_false, cepsBridgeMul,
      cepsOuterMean_eq, cepsHSeq]
    have hexp : Complex.exp (t * ((2 * eps * (1 + μ) : ℝ) : ℂ)) *
        Complex.exp (-(t * ((1 + μ : ℝ) : ℂ)) * (i : ℂ)) *
        Complex.exp (-(t * ((1 + μ : ℝ) : ℂ)) * ((n : ℂ) + 1)) *
        Complex.exp (-(t * ((1 + μ : ℝ) : ℂ)) * (r : ℂ)) =
        Complex.exp (-t * (((1 + μ) * ((i + (n + 1) + r : ℕ) : ℝ) - 2 * eps * (1 + μ) : ℝ) : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← hexp]
    push_cast
    ring

/-- **The layer sums are the Cauchy product** `∑_k (layer sum)_k = e^{tl} H_t² 𝔘 = J_t(μ)`. -/
theorem CepsGapDensity.hasSum_cepsLayerSum (hf : CepsGapDensity ν f D) {eps : ℝ}
    {t : ℂ} (ht : 0 ≤ t.re) {μ : ℝ} (hμ : -1 < μ) :
    HasSum (fun k => cepsLayerSum ν f eps t k μ) (cepsActualPair ν f eps t μ) := by
  set q : ℂ := t * ((1 + μ : ℝ) : ℂ) with hq
  set l : ℝ := 2 * eps * (1 + μ) with hl
  have hq0 : 0 ≤ q.re := by
    rw [hq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg ht (by linarith)
  set a : ℕ → ℂ := fun i => Complex.exp (t * (l : ℂ)) * cepsHSeq ν t eps μ i with ha
  set b : ℕ → ℂ := cepsUSeq ν f t eps μ with hb
  set c : ℕ → ℂ := cepsHSeq ν t eps μ with hc
  have hcs : Summable fun r => ‖c r‖ := hf.summable_cepsStripTerm ht hq0 μ l
  have has : Summable fun i => ‖a i‖ := by
    simp only [ha, norm_mul]
    exact hcs.mul_left _
  have hbs1 : Summable fun n => ‖b (n + 1)‖ := hf.summable_cepsMarkedBridge hq0 (2 * eps) μ l
  have hbs : Summable fun L => ‖b L‖ := (summable_nat_add_iff 1).1 hbs1
  have hds := summable_norm_sum_mul_antidiagonal_of_summable_norm has hbs
  have h1 := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm has hbs
  have h2 := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hds hcs
  have hEs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hds hcs).of_norm
  have hE : ∀ k, ∑ kl ∈ Finset.antidiagonal k,
      (∑ ij ∈ Finset.antidiagonal kl.1, a ij.1 * b ij.2) * c kl.2 = cepsLayerSum ν f eps t k μ := by
    intro k
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← cepsTripleTerm_eq_mul]
  have hJ : cepsActualPair ν f eps t μ = (∑' i, a i) * (∑' L, b L) * ∑' r, c r := by
    have hsa : ∑' i, a i = Complex.exp (t * (l : ℂ)) *
        cepsStripEntrance ν t μ q l := by
      rw [ha, tsum_mul_left]
      rfl
    have hsb : ∑' L, b L = cepsMarkedBridge ν f (2 * eps) μ q l := by
      rw [tsum_eq_zero_add' hbs1.of_norm]
      simp only [hb, cepsUSeq, zero_add]
      rfl
    have hsc : ∑' r, c r = cepsStripEntrance ν t μ q l := rfl
    rw [hsa, hsb, hsc]
    unfold cepsActualPair
    ring
  rw [hJ, h1, h2]
  simp only [hE] at hEs ⊢
  exact hEs.hasSum

/-! ## The dominating layers -/

theorem cepsSurvLaplace_zero (ν : ProbabilityMeasure ℝ) (eps : ℝ) (k : ℕ) :
    cepsSurvLaplace ν eps 0 k = ((iidLaw ν).real (survSet eps k) : ℂ) := by
  unfold cepsSurvLaplace
  simp only [neg_zero, zero_mul, Complex.exp_zero]
  rw [show (fun g => (survSet eps k).indicator (fun _ : ℕ → ℝ => (1 : ℂ)) g) =
      fun g => (((survSet eps k).indicator (fun _ => (1 : ℝ)) g : ℝ) : ℂ) from
    funext fun g => indicator_one_ofReal _ g, integral_complex_ofReal,
    integral_indicator (measurableSet_survSet eps k), setIntegral_const, smul_eq_mul, mul_one]

theorem cepsLaplace_zero (ν : ProbabilityMeasure ℝ) : cepsLaplace ν 0 = 1 := by
  simp [cepsLaplace]

/-- The `t = 0` layers integrate to `P(T > k) - 1{k ≤ m}`. -/
theorem CepsGapDensity.integral_cepsLayerReal (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) (k : ℕ) :
    ∫ μ in Ioi (-1 : ℝ), cepsLayerReal ν f eps k μ =
      (iidLaw ν).real (survSet eps k) - (if k ≤ ⌊2 * eps⌋₊ then 1 else 0) := by
  have h := hf.cepsSurvLaplace_eq_layer heps (t := 0) le_rfl k
  rw [cepsSurvLaplace_zero, cepsLaplace_zero, one_pow,
    setIntegral_congr_fun measurableSet_Ioi fun μ hμ => hf.cepsLayerSum_zero heps k hμ,
    integral_complex_ofReal] at h
  have h' : ((iidLaw ν).real (survSet eps k) : ℂ) =
      (((if k ≤ ⌊2 * eps⌋₊ then 1 else 0 : ℝ) + ∫ μ in Ioi (-1 : ℝ), cepsLayerReal ν f eps k μ : ℝ) :
        ℂ) := by
    rw [h]
    split_ifs <;> push_cast <;> ring
  have h'' := Complex.ofReal_injective h'
  linarith

theorem CepsGapDensity.summable_integral_cepsLayerReal (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) (hfin : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤)
    (hT : Integrable (fun g => ((gapSegLen eps g).toNat : ℝ)) (iidLaw ν)) :
    Summable (fun k => ∫ μ in Ioi (-1 : ℝ), cepsLayerReal ν f eps k μ) ∧
      ∑' k, ∫ μ in Ioi (-1 : ℝ), cepsLayerReal ν f eps k μ =
        lawC eps ν - ((⌊2 * eps⌋₊ : ℝ) + 1) := by
  obtain ⟨hP, hPsum⟩ := summable_measureReal_survSet hfin hT
  have hI : Summable (fun k : ℕ => (if k ≤ ⌊2 * eps⌋₊ then (1 : ℝ) else 0)) :=
    summable_of_ne_finset_zero (s := Finset.range (⌊2 * eps⌋₊ + 1)) fun k hk => by
      rw [if_neg]
      intro h
      exact hk (Finset.mem_range.2 (Nat.lt_succ_of_le h))
  have hIsum : ∑' k : ℕ, (if k ≤ ⌊2 * eps⌋₊ then (1 : ℝ) else 0) = (⌊2 * eps⌋₊ : ℝ) + 1 := by
    rw [tsum_eq_sum (s := Finset.range (⌊2 * eps⌋₊ + 1)) fun k hk => by
      rw [if_neg]
      intro h
      exact hk (Finset.mem_range.2 (Nat.lt_succ_of_le h))]
    rw [Finset.sum_congr rfl fun k hk => if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]
    simp
  simp_rw [hf.integral_cepsLayerReal heps]
  refine ⟨hP.sub hI, ?_⟩
  rw [hP.tsum_sub hI, hPsum, hIsum]

/-- For `μ > -1`, the `t = 0` pair is the sum of the real layers. -/
theorem CepsGapDensity.cepsActualPair_zero_eq (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) {μ : ℝ} (hμ : -1 < μ) :
    Summable (fun k => cepsLayerReal ν f eps k μ) ∧
      cepsActualPair ν f eps 0 μ = ((∑' k, cepsLayerReal ν f eps k μ : ℝ) : ℂ) := by
  have h := hf.hasSum_cepsLayerSum (eps := eps) (t := 0) le_rfl hμ
  simp only [hf.cepsLayerSum_zero heps _ hμ] at h
  have hs : Summable (fun k => cepsLayerReal ν f eps k μ) := Complex.summable_ofReal.1 h.summable
  refine ⟨hs, ?_⟩
  rw [← h.tsum_eq, Complex.ofReal_tsum]

theorem CepsGapDensity.cepsActualPair_eq_zero_of_le (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) (t : ℂ) {μ : ℝ} (hμ : μ ≤ -1) : cepsActualPair ν f eps t μ = 0 := by
  unfold cepsActualPair cepsMarkedBridge
  simp [hf.cepsBridgeDens_eq_zero_of_le heps hμ]

/-! ## Domination -/

/-- **Domination by the unmarked pair**: `‖J_t(μ)‖ ≤ ‖J_0(μ)‖` for `Re t ≥ 0`. -/
theorem CepsGapDensity.norm_cepsActualPair_le (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) {t : ℂ} (ht : 0 ≤ t.re) (μ : ℝ) :
    ‖cepsActualPair ν f eps t μ‖ ≤ ‖cepsActualPair ν f eps 0 μ‖ := by
  rcases le_or_gt μ (-1) with hμ | hμ
  · rw [hf.cepsActualPair_eq_zero_of_le heps t hμ, norm_zero]
    exact norm_nonneg _
  obtain ⟨hs, h0⟩ := hf.cepsActualPair_zero_eq heps hμ
  have hns : Summable fun k => ‖cepsLayerSum ν f eps t k μ‖ :=
    hs.of_nonneg_of_le (fun k => norm_nonneg _) fun k => hf.norm_cepsLayerSum_le heps ht k hμ
  rw [← (hf.hasSum_cepsLayerSum ht hμ).tsum_eq, h0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg fun k => hf.cepsLayerReal_nonneg eps k μ)]
  exact (norm_tsum_le_tsum_norm hns).trans
    (hns.tsum_le_tsum (fun k => hf.norm_cepsLayerSum_le heps ht k hμ) hs)

theorem CepsGapDensity.norm_cepsActualPair_zero_eq (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) (μ : ℝ) :
    ‖cepsActualPair ν f eps 0 μ‖ = (Ioi (-1 : ℝ)).indicator
      (fun μ => ∑' k, cepsLayerReal ν f eps k μ) μ := by
  rcases le_or_gt μ (-1) with hμ | hμ
  · rw [hf.cepsActualPair_eq_zero_of_le heps 0 hμ, norm_zero,
      indicator_of_notMem (fun h : μ ∈ Ioi (-1 : ℝ) => by simp at h; linarith)]
  obtain ⟨-, h0⟩ := hf.cepsActualPair_zero_eq heps hμ
  rw [indicator_of_mem (show μ ∈ Ioi (-1 : ℝ) from hμ), h0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg fun k => hf.cepsLayerReal_nonneg eps k μ)]

theorem CepsGapDensity.lintegral_cepsLayer_ne_top (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) (hfin : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤)
    (hT : Integrable (fun g => ((gapSegLen eps g).toNat : ℝ)) (iidLaw ν)) :
    ∑' k, ∫⁻ μ in Ioi (-1 : ℝ), ENNReal.ofReal (cepsLayerReal ν f eps k μ) ≠ ⊤ := by
  obtain ⟨hsum, -⟩ := hf.summable_integral_cepsLayerReal heps hfin hT
  have e : ∀ k, ∫⁻ μ in Ioi (-1 : ℝ), ENNReal.ofReal (cepsLayerReal ν f eps k μ) =
      ENNReal.ofReal (∫ μ in Ioi (-1 : ℝ), cepsLayerReal ν f eps k μ) := fun k =>
    (ofReal_integral_eq_lintegral_ofReal (hf.integrableOn_cepsLayerReal heps k)
      (Eventually.of_forall fun μ => hf.cepsLayerReal_nonneg eps k μ)).symm
  simp_rw [e]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => integral_nonneg fun μ =>
    hf.cepsLayerReal_nonneg eps k μ) hsum]
  exact ENNReal.ofReal_ne_top

/-- `∫_{μ > -1} ‖J_0‖ = E T - m - 1`, `m = ⌊2ε⌋`. -/
theorem CepsGapDensity.integral_norm_cepsActualPair_zero (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) (hfin : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤)
    (hT : Integrable (fun g => ((gapSegLen eps g).toNat : ℝ)) (iidLaw ν)) :
    ∫ μ in Ioi (-1 : ℝ), ‖cepsActualPair ν f eps 0 μ‖ = lawC eps ν - ((⌊2 * eps⌋₊ : ℝ) + 1) := by
  obtain ⟨hsum, hval⟩ := hf.summable_integral_cepsLayerReal heps hfin hT
  rw [setIntegral_congr_fun measurableSet_Ioi fun μ hμ => by
    rw [hf.norm_cepsActualPair_zero_eq heps μ, indicator_of_mem hμ], ← hval]
  refine integral_tsum (fun k => (hf.integrableOn_cepsLayerReal heps k).aestronglyMeasurable) ?_
  have e : ∀ k, ∫⁻ μ in Ioi (-1 : ℝ), ‖cepsLayerReal ν f eps k μ‖ₑ =
      ∫⁻ μ in Ioi (-1 : ℝ), ENNReal.ofReal (cepsLayerReal ν f eps k μ) := fun k =>
    lintegral_congr fun μ => by
      rw [Real.enorm_eq_ofReal (hf.cepsLayerReal_nonneg eps k μ)]
  simp_rw [e]
  exact hf.lintegral_cepsLayer_ne_top heps hfin hT

theorem CepsGapDensity.integrableOn_norm_cepsActualPair_zero (hf : CepsGapDensity ν f D)
    {eps : ℝ} (heps : 0 < eps) (hfin : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤)
    (hT : Integrable (fun g => ((gapSegLen eps g).toNat : ℝ)) (iidLaw ν)) :
    IntegrableOn (fun μ => ‖cepsActualPair ν f eps 0 μ‖) (Ioi (-1 : ℝ)) := by
  have hm : AEStronglyMeasurable (fun μ => ∑' k, cepsLayerReal ν f eps k μ)
      (volume.restrict (Ioi (-1 : ℝ))) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N μ =>
      ∑ k ∈ Finset.range N, cepsLayerReal ν f eps k μ)
      (fun N => (integrable_finsetSum _ fun k _ =>
        hf.integrableOn_cepsLayerReal heps k).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with μ hμ
    exact (hf.cepsActualPair_zero_eq heps hμ).1.hasSum.tendsto_sum_nat
  have hint : IntegrableOn (fun μ => ∑' k, cepsLayerReal ν f eps k μ) (Ioi (-1 : ℝ)) := by
    refine ⟨hm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun μ =>
      tsum_nonneg fun k => hf.cepsLayerReal_nonneg eps k μ)]
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 (hf.lintegral_cepsLayer_ne_top heps hfin hT))
    have e : ∫⁻ μ in Ioi (-1 : ℝ), ENNReal.ofReal (∑' k, cepsLayerReal ν f eps k μ) =
        ∫⁻ μ in Ioi (-1 : ℝ), ∑' k, ENNReal.ofReal (cepsLayerReal ν f eps k μ) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with μ hμ
      exact ENNReal.ofReal_tsum_of_nonneg (fun k => hf.cepsLayerReal_nonneg eps k μ)
        (hf.cepsActualPair_zero_eq heps hμ).1
    rw [e, lintegral_tsum fun k => (hf.integrableOn_cepsLayerReal heps k).aemeasurable.ennreal_ofReal]
  refine hint.congr_fun (fun μ hμ => ?_) measurableSet_Ioi
  rw [hf.norm_cepsActualPair_zero_eq heps μ, indicator_of_mem hμ]

/-! ## The exact marked representation (E) -/

/-- **Theorem (E).** For a gap law with a bounded density on `(0, ∞)`, `ε > 0`, `T < ∞` a.s.,
`E T < ∞` and `Re t ≥ 0`:
`E e^{-tS_T} = φ(t)^{⌊2ε⌋+1} - (1 - φ(t)) ∫_{(-1,∞)} J_t(μ) dμ`. -/
theorem CepsGapDensity.ceps_exact_marked_rep (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) (hfin : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤)
    (hT : Integrable (fun g => ((gapSegLen eps g).toNat : ℝ)) (iidLaw ν)) {t : ℂ}
    (ht : 0 ≤ t.re) :
    ∫ g, Complex.exp (-t * stopSum eps g) ∂(iidLaw ν) =
      cepsLaplace ν t ^ (⌊2 * eps⌋₊ + 1) -
        (1 - cepsLaplace ν t) * ∫ μ in Ioi (-1 : ℝ), cepsActualPair ν f eps t μ := by
  obtain ⟨hsumS, htel⟩ := hf.ceps_telescope hfin hT ht
  set m := ⌊2 * eps⌋₊ with hm
  set φ := cepsLaplace ν t with hφ
  set I : ℕ → ℂ := fun k => ∫ μ in Ioi (-1 : ℝ), cepsLayerSum ν f eps t k μ with hIdef
  have hlayer := hf.cepsSurvLaplace_eq_layer heps ht
  have hfinite : Summable (fun k : ℕ => (if k ≤ m then φ ^ k else 0)) :=
    summable_of_ne_finset_zero (s := Finset.range (m + 1)) fun k hk => by
      rw [if_neg]
      intro h
      exact hk (Finset.mem_range.2 (Nat.lt_succ_of_le h))
  have hI : Summable I := by
    have e : I = fun k => cepsSurvLaplace ν eps t k - (if k ≤ m then φ ^ k else 0) := by
      funext k
      rw [hlayer k]
      ring
    rw [e]
    exact hsumS.of_norm.sub hfinite
  have hfsum : ∑' k : ℕ, (if k ≤ m then φ ^ k else 0) = ∑ k ∈ Finset.range (m + 1), φ ^ k := by
    rw [tsum_eq_sum (s := Finset.range (m + 1)) fun k hk => by
      rw [if_neg]
      intro h
      exact hk (Finset.mem_range.2 (Nat.lt_succ_of_le h))]
    exact Finset.sum_congr rfl fun k hk => if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
  have hS : ∑' k, cepsSurvLaplace ν eps t k = ∑ k ∈ Finset.range (m + 1), φ ^ k + ∑' k, I k := by
    rw [tsum_congr hlayer, hfinite.tsum_add hI, hfsum]
  -- exchange of the layer series with the integral
  have hexch : ∫ μ in Ioi (-1 : ℝ), ∑' k, cepsLayerSum ν f eps t k μ = ∑' k, I k := by
    refine integral_tsum (fun k => (hf.integrableOn_cepsLayerSum heps ht k).aestronglyMeasurable)
      ?_
    refine ne_top_of_le_ne_top (hf.lintegral_cepsLayer_ne_top heps hfin hT)
      (ENNReal.tsum_le_tsum fun k => ?_)
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with μ hμ
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hf.norm_cepsLayerSum_le heps ht k hμ)
  have hpt : ∫ μ in Ioi (-1 : ℝ), ∑' k, cepsLayerSum ν f eps t k μ =
      ∫ μ in Ioi (-1 : ℝ), cepsActualPair ν f eps t μ :=
    setIntegral_congr_fun measurableSet_Ioi fun μ hμ =>
      (hf.hasSum_cepsLayerSum ht hμ).tsum_eq
  rw [htel, hS, ← hexch, hpt]
  have hgeom := geom_sum_mul_neg φ (m + 1)
  linear_combination (-1 : ℂ) * hgeom

/-- **Theorem (E), domination part**: `J_t` is integrable on `(-1, ∞)` and
`∫ ‖J_t‖ ≤ ∫ ‖J_0‖ = E T - ⌊2ε⌋ - 1`. -/
theorem CepsGapDensity.ceps_exact_marked_rep_domination (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) (hfin : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤)
    (hT : Integrable (fun g => ((gapSegLen eps g).toNat : ℝ)) (iidLaw ν)) {t : ℂ}
    (ht : 0 ≤ t.re) :
    IntegrableOn (cepsActualPair ν f eps t) (Ioi (-1 : ℝ)) ∧
      ∫ μ in Ioi (-1 : ℝ), ‖cepsActualPair ν f eps t μ‖ ≤
        ∫ μ in Ioi (-1 : ℝ), ‖cepsActualPair ν f eps 0 μ‖ ∧
      ∫ μ in Ioi (-1 : ℝ), ‖cepsActualPair ν f eps 0 μ‖ = lawC eps ν - ((⌊2 * eps⌋₊ : ℝ) + 1) := by
  have h0 := hf.integrableOn_norm_cepsActualPair_zero heps hfin hT
  have hm : AEStronglyMeasurable (cepsActualPair ν f eps t) (volume.restrict (Ioi (-1 : ℝ))) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N μ =>
      ∑ k ∈ Finset.range N, cepsLayerSum ν f eps t k μ)
      (fun N => (integrable_finsetSum _ fun k _ =>
        hf.integrableOn_cepsLayerSum heps ht k).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with μ hμ
    exact (hf.hasSum_cepsLayerSum ht hμ).tendsto_sum_nat
  have hint : IntegrableOn (cepsActualPair ν f eps t) (Ioi (-1 : ℝ)) :=
    h0.mono' hm (Eventually.of_forall fun μ => hf.norm_cepsActualPair_le heps ht μ)
  refine ⟨hint, integral_mono hint.norm h0 fun μ => hf.norm_cepsActualPair_le heps ht μ,
    hf.integral_norm_cepsActualPair_zero heps hfin hT⟩

end

end PGM
