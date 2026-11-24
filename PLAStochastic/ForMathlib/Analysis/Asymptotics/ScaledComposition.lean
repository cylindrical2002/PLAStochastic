import PLAStochastic.ForMathlib.Analysis.Asymptotics.SeriesApprox
import PLAStochastic.ForMathlib.Analysis.Calculus.TaylorBound

/-!
# Composing an expansion with a rescaled argument

Let `F ≈ ∑_{j ≤ N} hʲ g_j(ω / s)` with smooth `g_j : ℝ → ℂ` whose derivatives grow
polynomially, and let the scale have the expansion `s ≈ ∑_{k ≤ N} hᵏ c_k` with `c₀ > 0`. Taylor
expansion of `g_j` around `ω / c₀` and expansion of `1/s` give

`F = ∑_{k ≤ N} hᵏ Φ_k(ω) + O(h^{N+1} (1 + |ω|)^{d+N+1})`,

uniformly in `ω ∈ ℝ` and in all data with the same bounds (`norm_sub_sum_lowCompCoeff_le`).
`Φ_k = lowCompCoeff g c ω k` is the `k`-th coefficient of the power series

`∑_j Xʲ ∑_m g_j⁽ᵐ⁾(ω/c₀)/m! · (ω (S⁻¹ - c₀⁻¹))ᵐ`,  `S = ∑ c_k Xᵏ`,

a finite combination of derivatives of the `g_j` at `ω / c₀`, powers of `ω`, and polynomials in
`1/c₀, c₁, …, c_k` (`invTail`). It is linear in the derivative values
(`norm_lowCompCoeff_le`).
-/

namespace PGM

noncomputable section

open PowerSeries Finset

/-- The tail `(∑ c_k Xᵏ)⁻¹ - c₀⁻¹` of the inverse scale series. -/
def invTail (c : ℕ → ℝ) : PowerSeries ℂ :=
  (PowerSeries.mk fun k => (c k : ℂ))⁻¹ - C ((c 0 : ℂ)⁻¹)

/-- The composed series truncated to order `N` in `j` and `m`. -/
def compSeries (g : ℕ → ℝ → ℂ) (c : ℕ → ℝ) (ω : ℝ) (N : ℕ) : PowerSeries ℂ :=
  ∑ j ∈ range (N + 1), X ^ j * ∑ m ∈ range (N + 1),
    C ((m.factorial : ℂ)⁻¹ * iteratedDeriv m (g j) (ω / c 0)) * (C (ω : ℂ) * invTail c) ^ m

/-- The composed coefficient `Φ_k(ω)`. -/
def lowCompCoeff (g : ℕ → ℝ → ℂ) (c : ℕ → ℝ) (ω : ℝ) (k : ℕ) : ℂ :=
  coeff k (compSeries g c ω k)

theorem constantCoeff_invTail (c : ℕ → ℝ) : constantCoeff (invTail c) = 0 := by
  simp [invTail]

theorem coeff_compTerm_eq_zero (a ω : ℂ) (c : ℕ → ℝ) {j m k : ℕ} (h : k < j + m) :
    coeff k (X ^ j * (C a * (C ω * invTail c) ^ m)) = 0 := by
  obtain ⟨T, hT⟩ := X_dvd_iff.mpr (constantCoeff_invTail c)
  have e : X ^ j * (C a * (C ω * invTail c) ^ m) = X ^ (j + m) * (C a * (C ω * T) ^ m) := by
    rw [hT, pow_add, mul_pow, mul_pow, mul_pow]
    ring
  rw [e, coeff_X_pow_mul', if_neg (by omega)]

/-- The `k`-th coefficient only reads the terms `j, m ≤ k`. -/
theorem coeff_compSeries_eq (g : ℕ → ℝ → ℂ) (c : ℕ → ℝ) (ω : ℝ) {k N : ℕ} (hk : k ≤ N) :
    coeff k (compSeries g c ω N) = ∑ j ∈ range (k + 1), ∑ m ∈ range (k + 1),
      coeff k (X ^ j * (C ((m.factorial : ℂ)⁻¹ * iteratedDeriv m (g j) (ω / c 0)) *
        (C (ω : ℂ) * invTail c) ^ m)) := by
  have hsub : range (k + 1) ⊆ range (N + 1) := range_subset_range.mpr (by omega)
  simp only [compSeries, map_sum, mul_sum]
  rw [← sum_subset hsub fun j _ hj => sum_eq_zero fun m _ =>
    coeff_compTerm_eq_zero _ _ c (by simp at hj; omega)]
  refine sum_congr rfl fun j hj => ?_
  exact (sum_subset hsub fun m _ hm => coeff_compTerm_eq_zero _ _ c (by simp at hm; omega)).symm

theorem coeff_compSeries_eq_lowCompCoeff (g : ℕ → ℝ → ℂ) (c : ℕ → ℝ) (ω : ℝ) {k N : ℕ}
    (hk : k ≤ N) : coeff k (compSeries g c ω N) = lowCompCoeff g c ω k := by
  rw [lowCompCoeff, coeff_compSeries_eq g c ω hk, coeff_compSeries_eq g c ω le_rfl]

theorem truncEval_compSeries (g : ℕ → ℝ → ℂ) (c : ℕ → ℝ) (ω : ℝ) (N : ℕ) (h : ℝ) :
    truncEval (compSeries g c ω N) N h =
      ∑ k ∈ range (N + 1), (h : ℂ) ^ k * lowCompCoeff g c ω k := by
  refine sum_congr rfl fun k hk => ?_
  rw [coeff_compSeries_eq_lowCompCoeff g c ω (Nat.lt_succ_iff.mp (mem_range.mp hk)), mul_comm]

/-! ## The inverse scale -/

theorem truncEval_mk_ofReal (c : ℕ → ℝ) (N : ℕ) (h : ℝ) :
    truncEval (PowerSeries.mk fun k => (c k : ℂ)) N h =
      ((∑ k ∈ range (N + 1), h ^ k * c k : ℝ) : ℂ) := by
  simp only [truncEval, coeff_mk]
  push_cast
  exact sum_congr rfl fun k _ => mul_comm _ _

/-- The tail of the inverse scale is approximated by `invTail`, with a constant depending only
on `N`, `c_lo`, `B`, `K₁`. -/
theorem exists_seriesApprox_invTail (N : ℕ) {c_lo B K₁ : ℝ} (hclo : 0 < c_lo) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (c : ℕ → ℝ) (s h : ℝ), c_lo ≤ c 0 → (∀ k ≤ N, |c k| ≤ B) →
      0 ≤ h → h ≤ 1 → c_lo / 2 ≤ s →
      |s - ∑ k ∈ range (N + 1), h ^ k * c k| ≤ K₁ * h ^ (N + 1) →
      SeriesApprox ((s : ℂ)⁻¹ - (c 0 : ℂ)⁻¹) (invTail c) N h κ := by
  set Le : ℝ := (((N : ℝ) + 1) * (1 + |B| / c_lo)) ^ N / c_lo with hLe
  set Ks : ℝ := max |B| |K₁| with hKs
  refine ⟨Le + 3 * ((N : ℝ) + 2) ^ 2 * Ks * Le / (c_lo / 2) + c_lo⁻¹, by positivity,
    fun c s h hc0 hcB h0 h1 hslo hs => ?_⟩
  have hcB' : ∀ k ≤ N, ‖((c k : ℂ))‖ ≤ |B| := fun k hk => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (hcB k hk).trans (le_abs_self B)
  have hS : SeriesApprox (s : ℂ) (PowerSeries.mk fun k => (c k : ℂ)) N h Ks := by
    refine ⟨fun k hk => ?_, ?_⟩
    · rw [coeff_mk]
      exact (hcB' k hk).trans (le_max_left _ _)
    · rw [truncEval_mk_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      refine hs.trans ?_
      gcongr
      exact (le_abs_self K₁).trans (le_max_right _ _)
  have hc0pos : 0 < c 0 := hclo.trans_le hc0
  have hinv := norm_coeff_inv_mk_le (c := fun k => (c k : ℂ)) (N := N) hclo
    (by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0pos]; exact hc0) hcB'
  have hspos : 0 < s := (half_pos hclo).trans_le hslo
  have hI := hS.inv h0 h1 (half_pos hclo)
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos]; exact hslo)
    (by simp only [constantCoeff_mk]; exact_mod_cast hc0pos.ne') hinv
  have hT := hI.sub_const h0 ((c 0 : ℂ)⁻¹)
  refine hT.mono h0 (add_le_add le_rfl ?_)
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0pos]
  exact inv_anti₀ hclo hc0

/-! ## The polynomial part -/

/-- The truncated Taylor polynomials composed with the approximated tail of `1/s` are
approximated by `compSeries`, given bounds `A` on the derivatives at `ω / c₀`. -/
theorem seriesApprox_compSeries (g : ℕ → ℝ → ℂ) (c : ℕ → ℝ) (ω : ℝ) {N : ℕ} {s h κ A : ℝ}
    (h0 : 0 ≤ h) (h1 : h ≤ 1)
    (hY : SeriesApprox ((s : ℂ)⁻¹ - (c 0 : ℂ)⁻¹) (invTail c) N h κ)
    (hA : ∀ j ≤ N, ∀ m ≤ N, ‖iteratedDeriv m (g j) (ω / c 0)‖ ≤ A) :
    SeriesApprox (∑ j ∈ range (N + 1), (h : ℂ) ^ j * ∑ m ∈ range (N + 1),
        ((m.factorial : ℂ)⁻¹ * iteratedDeriv m (g j) (ω / c 0)) *
          ((ω : ℂ) * ((s : ℂ)⁻¹ - (c 0 : ℂ)⁻¹)) ^ m)
      (compSeries g c ω N) N h
      (((N : ℝ) + 1) ^ 2 * (3 * ((N : ℝ) + 2) ^ 2) * A *
        (3 * ((N : ℝ) + 2) ^ 2 * max κ 1) ^ N * (1 + |ω|) ^ N) := by
  have hκ := hY.nonneg
  have hW1 : (1 : ℝ) ≤ 1 + |ω| := by linarith [abs_nonneg ω]
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _) 0 (Nat.zero_le _))
  have hN3 : (1 : ℝ) ≤ 3 * ((N : ℝ) + 2) ^ 2 := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hm1 : (1 : ℝ) ≤ max κ 1 := le_max_right _ _
  set q : ℝ := 3 * ((N : ℝ) + 2) ^ 2 * max κ 1 with hq
  have hq1 : 1 ≤ q := by nlinarith
  have hYω : SeriesApprox ((ω : ℂ) * ((s : ℂ)⁻¹ - (c 0 : ℂ)⁻¹)) (C (ω : ℂ) * invTail c) N h
      ((1 + |ω|) * max κ 1) := by
    refine (hY.const_mul (ω : ℂ)).mono h0 ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (by linarith) (le_max_left _ _) hκ (by positivity)
  have hinner : ∀ j ∈ range (N + 1), SeriesApprox
      (∑ m ∈ range (N + 1), ((m.factorial : ℂ)⁻¹ * iteratedDeriv m (g j) (ω / c 0)) *
          ((ω : ℂ) * ((s : ℂ)⁻¹ - (c 0 : ℂ)⁻¹)) ^ m)
      (∑ m ∈ range (N + 1), C ((m.factorial : ℂ)⁻¹ * iteratedDeriv m (g j) (ω / c 0)) *
          (C (ω : ℂ) * invTail c) ^ m) N h
      (((N : ℝ) + 1) * A * q ^ N * (1 + |ω|) ^ N) := by
    intro j hj
    have hj' : j ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hs := seriesApprox_sum (range (N + 1)) fun m _ =>
      (hYω.pow h0 h1 m).const_mul ((m.factorial : ℂ)⁻¹ * iteratedDeriv m (g j) (ω / c 0))
    refine hs.mono h0 ?_
    calc ∑ m ∈ range (N + 1), ‖(m.factorial : ℂ)⁻¹ * iteratedDeriv m (g j) (ω / c 0)‖ *
          (3 * ((N : ℝ) + 2) ^ 2 * ((1 + |ω|) * max κ 1)) ^ m
        ≤ ∑ _m ∈ range (N + 1), A * (q ^ N * (1 + |ω|) ^ N) := by
          refine sum_le_sum fun m hm => ?_
          have hm' : m ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hm)
          refine mul_le_mul ?_ ?_ (by positivity) hA0
          · rw [norm_mul, norm_inv, Complex.norm_natCast]
            have hf : (1 : ℝ) ≤ (m.factorial : ℝ) := by
              exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
            calc (m.factorial : ℝ)⁻¹ * ‖iteratedDeriv m (g j) (ω / c 0)‖
                ≤ 1 * ‖iteratedDeriv m (g j) (ω / c 0)‖ :=
                  mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hf) (norm_nonneg _)
              _ ≤ A := by rw [one_mul]; exact hA j hj' m hm'
          · have e : 3 * ((N : ℝ) + 2) ^ 2 * ((1 + |ω|) * max κ 1) = q * (1 + |ω|) := by
              rw [hq]; ring
            rw [e, ← mul_pow]
            exact pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hq1 hW1) hm'
      _ = ((N : ℝ) + 1) * A * q ^ N * (1 + |ω|) ^ N := by
          rw [sum_const, card_range, nsmul_eq_mul]
          push_cast
          ring
  have hC : 0 ≤ ((N : ℝ) + 1) * A * q ^ N * (1 + |ω|) ^ N := by positivity
  have houter := seriesApprox_sum (range (N + 1)) fun j hj =>
    (seriesApprox_X_pow j N h0 h1).mul (hinner j hj) h0 h1
  unfold compSeries
  refine houter.mono h0 (le_of_eq ?_)
  rw [sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

/-! ## The Taylor step -/

theorem norm_sub_taylorSum_le {g : ℝ → ℂ} {N d : ℕ} {B : ℝ} (hg : ContDiff ℝ (N + 1) g)
    (hgB : ∀ x, ‖iteratedDeriv (N + 1) g x‖ ≤ B * (1 + |x|) ^ d) (x₀ x : ℝ) :
    ‖g x - ∑ m ∈ range (N + 1), ((m.factorial : ℂ)⁻¹ * iteratedDeriv m g x₀) *
        ((x - x₀ : ℝ) : ℂ) ^ m‖ ≤ B * (1 + |x₀| + |x - x₀|) ^ d * |x - x₀| ^ (N + 1) := by
  have hB : 0 ≤ B := by
    have h1 := (norm_nonneg _).trans (hgB 0)
    have h2 : 0 < (1 + |(0 : ℝ)|) ^ d := by positivity
    exact nonneg_of_mul_nonneg_left h1 h2
  have hT := norm_sub_taylor_le (N + 1) (f := g) (by exact_mod_cast hg) x₀ x
    (L := B * (1 + |x₀| + |x - x₀|) ^ d) fun t ht => by
      refine (hgB t).trans (mul_le_mul_of_nonneg_left ?_ hB)
      have h1 : |t| ≤ |x₀| + |x - x₀| := by
        have := Set.abs_sub_left_of_mem_uIcc ht
        have h2 : |t| ≤ |x₀| + |t - x₀| := by
          have := abs_add_le x₀ (t - x₀)
          rwa [add_sub_cancel] at this
        linarith
      exact pow_le_pow_left₀ (by positivity) (by linarith) d
  have e : ∑ m ∈ range (N + 1), ((m.factorial : ℝ)⁻¹ * (x - x₀) ^ m) • iteratedDeriv m g x₀ =
      ∑ m ∈ range (N + 1), ((m.factorial : ℂ)⁻¹ * iteratedDeriv m g x₀) *
        ((x - x₀ : ℝ) : ℂ) ^ m := by
    refine sum_congr rfl fun m _ => ?_
    rw [Complex.real_smul]
    push_cast
    ring
  rwa [e] at hT

/-! ## The composition theorem -/

theorem one_add_mul_le_mul (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    1 + a * x ≤ (1 + a) * (1 + x) := by nlinarith

/-- **Composition of a rescaled expansion.** Constants depend only on `N`, `d`, `c_lo`, `B`,
`K₁`, `K₂`. -/
theorem norm_sub_sum_lowCompCoeff_le (N d : ℕ) {c_lo B K₁ K₂ : ℝ} (hclo : 0 < c_lo) :
    ∃ h₀ K : ℝ, 0 < h₀ ∧ ∀ (c : ℕ → ℝ) (g : ℕ → ℝ → ℂ) (ω s h : ℝ) (F : ℂ),
      c_lo ≤ c 0 → (∀ k ≤ N, |c k| ≤ B) → (∀ j ≤ N, ContDiff ℝ (N + 1) (g j)) →
      (∀ j ≤ N, ∀ m ≤ N + 1, ∀ x, ‖iteratedDeriv m (g j) x‖ ≤ B * (1 + |x|) ^ d) →
      0 < h → h ≤ h₀ → |s - ∑ k ∈ range (N + 1), h ^ k * c k| ≤ K₁ * h ^ (N + 1) →
      ‖F - ∑ j ∈ range (N + 1), (h : ℂ) ^ j * g j (ω / s)‖ ≤
        K₂ * h ^ (N + 1) * (1 + |ω / s|) ^ d →
      ‖F - ∑ k ∈ range (N + 1), (h : ℂ) ^ k * lowCompCoeff g c ω k‖ ≤
        K * h ^ (N + 1) * (1 + |ω|) ^ (d + N + 1) := by
  obtain ⟨κ, hκ0, hκ⟩ := exists_seriesApprox_invTail N (B := B) (K₁ := K₁) hclo
  set κ₄ : ℝ := |K₁| + ((N : ℝ) + 1) * |B| with hκ₄
  have hκ₄0 : 0 ≤ κ₄ := by positivity
  set κ₅ : ℝ := 2 * κ₄ / c_lo ^ 2 with hκ₅
  set κ₆ : ℝ := 1 + c_lo⁻¹ + κ₅ with hκ₆
  set q : ℝ := 3 * ((N : ℝ) + 2) ^ 2 * max κ 1 with hq
  refine ⟨min 1 (c_lo / (2 * (κ₄ + 1))),
    ((N : ℝ) + 1) ^ 2 * (3 * ((N : ℝ) + 2) ^ 2) * (|B| * (1 + c_lo⁻¹) ^ d) * q ^ N +
      ((N : ℝ) + 1) * |B| * κ₆ ^ d * κ₅ ^ (N + 1) + |K₂| * (1 + 2 / c_lo) ^ d,
    lt_min one_pos (by positivity), fun c g ω s h F hc0 hcB hg hgB hh0 hh₀ hs hF => ?_⟩
  have hh1 : h ≤ 1 := hh₀.trans (min_le_left _ _)
  have hh2 : h ≤ c_lo / (2 * (κ₄ + 1)) := hh₀.trans (min_le_right _ _)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hcB 0 (Nat.zero_le _))
  have hc0pos : 0 < c 0 := hclo.trans_le hc0
  have hhN : h ^ (N + 1) ≤ h := by
    calc h ^ (N + 1) ≤ h ^ 1 := pow_le_pow_of_le_one hh0.le hh1 (by omega)
      _ = h := pow_one h
  -- the scale is close to `c₀`
  have hsc : |s - c 0| ≤ κ₄ * h := by
    have e : s - c 0 = (s - ∑ k ∈ range (N + 1), h ^ k * c k) +
        ∑ k ∈ range N, h ^ (k + 1) * c (k + 1) := by
      rw [sum_range_succ', pow_zero, one_mul]
      ring
    have h2 : |∑ k ∈ range N, h ^ (k + 1) * c (k + 1)| ≤ N * |B| * h := by
      calc |∑ k ∈ range N, h ^ (k + 1) * c (k + 1)|
          ≤ ∑ k ∈ range N, |h ^ (k + 1) * c (k + 1)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ range N, |B| * h := by
            refine sum_le_sum fun k hk => ?_
            have hk' : k + 1 ≤ N := mem_range.mp hk
            rw [abs_mul, abs_of_nonneg (by positivity)]
            calc h ^ (k + 1) * |c (k + 1)| ≤ h * |B| := by
                  refine mul_le_mul ?_ ((hcB (k + 1) hk').trans (le_abs_self B))
                    (abs_nonneg _) hh0.le
                  calc h ^ (k + 1) ≤ h ^ 1 := pow_le_pow_of_le_one hh0.le hh1 (by omega)
                    _ = h := pow_one h
              _ = |B| * h := mul_comm _ _
        _ = N * |B| * h := by rw [sum_const, card_range, nsmul_eq_mul]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h1 : K₁ * h ^ (N + 1) ≤ |K₁| * h := by
      calc K₁ * h ^ (N + 1) ≤ |K₁| * h ^ (N + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self K₁) (by positivity)
        _ ≤ |K₁| * h := mul_le_mul_of_nonneg_left hhN (abs_nonneg _)
    have h3 : ((N : ℝ) + 1) * |B| * h = N * |B| * h + |B| * h := by ring
    have h4 : 0 ≤ |B| * h := by positivity
    have h5 : κ₄ * h = |K₁| * h + ((N : ℝ) + 1) * |B| * h := by rw [hκ₄]; ring
    linarith
  have hslo : c_lo / 2 ≤ s := by
    have h3 : κ₄ * h ≤ c_lo / 2 := by
      calc κ₄ * h ≤ κ₄ * (c_lo / (2 * (κ₄ + 1))) := mul_le_mul_of_nonneg_left hh2 hκ₄0
        _ ≤ c_lo / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
            calc κ₄ * c_lo * 2 ≤ κ₄ * c_lo * 2 + 2 * c_lo := by linarith
              _ = c_lo * (2 * (κ₄ + 1)) := by ring
    have := (abs_le.mp hsc).1
    linarith
  have hspos : 0 < s := (half_pos hclo).trans_le hslo
  have hY := hκ c s h hc0 hcB hh0.le hh1 hslo hs
  set W : ℝ := 1 + |ω| with hW
  have hW1 : 1 ≤ W := by rw [hW]; linarith [abs_nonneg ω]
  have hωW : |ω| ≤ W := by rw [hW]; linarith
  -- elementary bounds on the arguments
  have hx0 : |ω / c 0| ≤ c_lo⁻¹ * |ω| := by
    rw [abs_div, abs_of_pos hc0pos, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hclo hc0) (abs_nonneg _)
  have hxs : |ω / s| ≤ 2 / c_lo * |ω| := by
    rw [abs_div, abs_of_pos hspos, div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [show 2 / c_lo = (c_lo / 2)⁻¹ by field_simp]
    exact inv_anti₀ (half_pos hclo) hslo
  have hxx : |ω / s - ω / c 0| ≤ κ₅ * W * h := by
    have e : ω / s - ω / c 0 = ω * (c 0 - s) / (s * c 0) := by
      field_simp
    rw [e, abs_div, abs_mul, abs_of_pos (mul_pos hspos hc0pos), abs_sub_comm]
    rw [div_le_iff₀ (mul_pos hspos hc0pos)]
    have hsc' : c_lo / 2 * c_lo ≤ s * c 0 := mul_le_mul hslo hc0 hclo.le hspos.le
    have hk5 : κ₅ * (c_lo / 2 * c_lo) = κ₄ := by rw [hκ₅]; field_simp
    calc |ω| * |s - c 0| ≤ W * (κ₄ * h) :=
          mul_le_mul hωW hsc (abs_nonneg _) (by positivity)
      _ = κ₅ * W * h * (c_lo / 2 * c_lo) := by rw [← hk5]; ring
      _ ≤ κ₅ * W * h * (s * c 0) := by gcongr
  -- the polynomial part
  have hA : ∀ j ≤ N, ∀ m ≤ N, ‖iteratedDeriv m (g j) (ω / c 0)‖ ≤
      |B| * (1 + c_lo⁻¹) ^ d * W ^ d := by
    intro j hj m hm
    refine (hgB j hj m (by omega) _).trans ?_
    rw [abs_of_nonneg hB0, mul_assoc, ← mul_pow]
    gcongr
    calc 1 + |ω / c 0| ≤ 1 + c_lo⁻¹ * |ω| := by linarith
      _ ≤ (1 + c_lo⁻¹) * W :=
          one_add_mul_le_mul _ _ (inv_nonneg.mpr hclo.le) (abs_nonneg ω)
  have hM := seriesApprox_compSeries g c ω hh0.le hh1 hY hA
  set T : ℕ → ℂ := fun j => ∑ m ∈ range (N + 1),
    ((m.factorial : ℂ)⁻¹ * iteratedDeriv m (g j) (ω / c 0)) *
      ((ω : ℂ) * ((s : ℂ)⁻¹ - (c 0 : ℂ)⁻¹)) ^ m with hT
  -- the Taylor step
  have hcast : (((ω / s - ω / c 0 : ℝ)) : ℂ) = (ω : ℂ) * ((s : ℂ)⁻¹ - (c 0 : ℂ)⁻¹) := by
    push_cast
    ring
  have hTay : ∀ j ∈ range (N + 1), ‖g j (ω / s) - T j‖ ≤
      |B| * κ₆ ^ d * κ₅ ^ (N + 1) * W ^ (d + N + 1) * h ^ (N + 1) := by
    intro j hj
    have hj' : j ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have h1 := norm_sub_taylorSum_le (hg j hj') (hgB j hj' (N + 1) le_rfl) (ω / c 0) (ω / s)
    rw [hcast] at h1
    refine h1.trans ?_
    have hb1 : 1 + |ω / c 0| + |ω / s - ω / c 0| ≤ κ₆ * W := by
      have h5 : κ₅ * W * h ≤ κ₅ * W := mul_le_of_le_one_right (by positivity) hh1
      have h6 : c_lo⁻¹ * |ω| ≤ c_lo⁻¹ * W :=
        mul_le_mul_of_nonneg_left hωW (inv_nonneg.mpr hclo.le)
      have h7 : κ₆ * W = W + c_lo⁻¹ * W + κ₅ * W := by rw [hκ₆]; ring
      linarith
    calc B * (1 + |ω / c 0| + |ω / s - ω / c 0|) ^ d * |ω / s - ω / c 0| ^ (N + 1)
        ≤ |B| * (κ₆ * W) ^ d * (κ₅ * W * h) ^ (N + 1) := by
          rw [abs_of_nonneg hB0]
          gcongr
      _ = |B| * κ₆ ^ d * κ₅ ^ (N + 1) * W ^ (d + N + 1) * h ^ (N + 1) := by ring_nf
  have E2 : ‖∑ j ∈ range (N + 1), (h : ℂ) ^ j * g j (ω / s) -
      ∑ j ∈ range (N + 1), (h : ℂ) ^ j * T j‖ ≤
      ((N : ℝ) + 1) * |B| * κ₆ ^ d * κ₅ ^ (N + 1) * W ^ (d + N + 1) * h ^ (N + 1) := by
    rw [← sum_sub_distrib]
    calc ‖∑ j ∈ range (N + 1), ((h : ℂ) ^ j * g j (ω / s) - (h : ℂ) ^ j * T j)‖
        ≤ ∑ j ∈ range (N + 1), ‖(h : ℂ) ^ j * g j (ω / s) - (h : ℂ) ^ j * T j‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j ∈ range (N + 1), |B| * κ₆ ^ d * κ₅ ^ (N + 1) * W ^ (d + N + 1) * h ^ (N + 1) := by
          refine sum_le_sum fun j hj => ?_
          rw [← mul_sub, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hh0]
          calc h ^ j * ‖g j (ω / s) - T j‖ ≤ 1 * ‖g j (ω / s) - T j‖ :=
                mul_le_mul_of_nonneg_right (pow_le_one₀ hh0.le hh1) (norm_nonneg _)
            _ ≤ _ := by rw [one_mul]; exact hTay j hj
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have E1 : ‖F - ∑ j ∈ range (N + 1), (h : ℂ) ^ j * g j (ω / s)‖ ≤
      |K₂| * (1 + 2 / c_lo) ^ d * W ^ (d + N + 1) * h ^ (N + 1) := by
    refine hF.trans ?_
    have hb : 1 + |ω / s| ≤ (1 + 2 / c_lo) * W := by
      have := one_add_mul_le_mul (2 / c_lo) |ω| (by positivity) (abs_nonneg ω)
      rw [hW]
      linarith
    calc K₂ * h ^ (N + 1) * (1 + |ω / s|) ^ d
        ≤ |K₂| * h ^ (N + 1) * ((1 + 2 / c_lo) * W) ^ d := by
          gcongr
          · exact le_abs_self K₂
      _ ≤ |K₂| * h ^ (N + 1) * ((1 + 2 / c_lo) ^ d * W ^ (d + N + 1)) := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hW1 (by omega)) (by positivity)) (by positivity)
      _ = _ := by ring
  have E3 : ‖∑ j ∈ range (N + 1), (h : ℂ) ^ j * T j - truncEval (compSeries g c ω N) N h‖ ≤
      ((N : ℝ) + 1) ^ 2 * (3 * ((N : ℝ) + 2) ^ 2) * (|B| * (1 + c_lo⁻¹) ^ d) * q ^ N *
        W ^ (d + N + 1) * h ^ (N + 1) := by
    refine hM.2.trans ?_
    have hWp : W ^ d * W ^ N ≤ W ^ (d + N + 1) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hW1 (by omega)
    have h0' : 0 ≤ ((N : ℝ) + 1) ^ 2 * (3 * ((N : ℝ) + 2) ^ 2) * (|B| * (1 + c_lo⁻¹) ^ d) *
        q ^ N := by positivity
    calc ((N : ℝ) + 1) ^ 2 * (3 * ((N : ℝ) + 2) ^ 2) * (|B| * (1 + c_lo⁻¹) ^ d * W ^ d) *
          (3 * ((N : ℝ) + 2) ^ 2 * max κ 1) ^ N * (1 + |ω|) ^ N * h ^ (N + 1)
        = ((N : ℝ) + 1) ^ 2 * (3 * ((N : ℝ) + 2) ^ 2) * (|B| * (1 + c_lo⁻¹) ^ d) * q ^ N *
            (W ^ d * W ^ N) * h ^ (N + 1) := by rw [hq, hW]; ring
      _ ≤ _ := by gcongr
  rw [← truncEval_compSeries]
  have e : F - truncEval (compSeries g c ω N) N h =
      (F - ∑ j ∈ range (N + 1), (h : ℂ) ^ j * g j (ω / s)) +
      (∑ j ∈ range (N + 1), (h : ℂ) ^ j * g j (ω / s) - ∑ j ∈ range (N + 1), (h : ℂ) ^ j * T j) +
      (∑ j ∈ range (N + 1), (h : ℂ) ^ j * T j - truncEval (compSeries g c ω N) N h) := by ring
  rw [e]
  refine ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans ?_
  have := add_le_add (add_le_add E1 E2) E3
  refine this.trans (le_of_eq ?_)
  rw [hW]
  ring

/-- **Coefficient bound.** The composed coefficient is linear in the derivative values at
`ω / c₀`: if these are at most `A`, then `‖Φ_k(ω)‖ ≤ κ A (1 + |ω|)ᵏ`. -/
theorem norm_lowCompCoeff_le (k : ℕ) {c_lo B : ℝ} (hclo : 0 < c_lo) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (c : ℕ → ℝ) (g : ℕ → ℝ → ℂ) (ω A : ℝ), c_lo ≤ c 0 →
      (∀ i ≤ k, |c i| ≤ B) → (∀ j ≤ k, ∀ m ≤ k, ‖iteratedDeriv m (g j) (ω / c 0)‖ ≤ A) →
      ‖lowCompCoeff g c ω k‖ ≤ κ * A * (1 + |ω|) ^ k := by
  obtain ⟨κ, hκ0, hκ⟩ := exists_seriesApprox_invTail k (B := B) (K₁ := 0) hclo
  refine ⟨((k : ℝ) + 1) ^ 2 * (3 * ((k : ℝ) + 2) ^ 2) * (3 * ((k : ℝ) + 2) ^ 2 * max κ 1) ^ k,
    by positivity, fun c g ω A hc0 hcB hA => ?_⟩
  have hc0pos : 0 < c 0 := hclo.trans_le hc0
  have hY := hκ c (c 0) 0 hc0 hcB le_rfl zero_le_one (by linarith) (by
    rw [sum_range_succ']
    simp)
  have hM := seriesApprox_compSeries g c ω le_rfl zero_le_one hY hA
  refine (hM.1 k le_rfl).trans (le_of_eq ?_)
  ring

end

end PGM
