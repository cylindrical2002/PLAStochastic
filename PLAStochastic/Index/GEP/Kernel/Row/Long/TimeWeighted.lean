import PLAStochastic.Index.GEP.Kernel.Row.Long.Decomposition

/-!
# WP4 kernel rows: small exponential time weights (for `KernelPhi`)

Source: `influence-lipschitz.md` §6: the weighted-Lipschitz output reward only multiplies each
segment of length `n` by `exp(K η n / w²)`; with `η` below a fixed fraction of the killed
spectral-gap constant, all row, pin, long-kernel and jump sums hold unchanged.

This file gives the exponentially weighted versions of the Green sums of `GEPKernelRowGreen`
and of the (long) display of `GEPKernelRowLong`, for weights `e^{ε n / w²}` with
`0 ≤ ε ≤ krKappa/16` (sums) resp. `0 ≤ ε ≤ krEps` (long display):

* `kr_expw_sum_le`: generic — a nonnegative sequence with partial sums `≤ S` and geometric
  large-time bound `F(T₀+j) ≤ C r^j` has weighted partial sums
  `≤ e^{3ε}(S + C/(1 - r e^{ε/w²}))`;
* `sum_expw_krSurv_bdry_le`, `sum_expw_krDens_bdry_row_le`, `sum_expw_krDens_bdry_pin_le`,
  `sum_expw_weighted_krDens_bdry_pin_le`: the four Green sums with weights, same orders
  (`(1+A) w`, `(1+A)(1 + log w)`, `(1+A)²/√w`, `(1+A)² w`) and the factor `e^{3ε}`;
* `krLong_decomposition_expw`: the (long) display for `∑ e^{ε n/w²} q_n(b, ·)`.

All constants remain class constants; the `A`-loss stays polynomial.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {J : Set ℝ} {β a : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}

/-! ## Elementary -/

/-- `e^x ≤ 1 + 2x` on `[0, 1]`. -/
theorem kr_exp_le_one_add_two_mul {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + 2 * x := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  have := (abs_le.1 h).2
  nlinarith

/-- `(1 - x)/2 ≤ 1 - √x` on `[0, 1]`. -/
theorem kr_one_sub_sqrt_ge {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (1 - x) / 2 ≤ 1 - Real.sqrt x := by
  have hs := Real.sqrt_nonneg x
  have hs1 : Real.sqrt x ≤ 1 := Real.sqrt_le_one.2 h1
  have hsq := Real.sq_sqrt h0
  nlinarith

/-- `j r^j ≤ 1/(1 - r)`. -/
theorem kr_mul_pow_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (j : ℕ) :
    (j : ℝ) * r ^ j ≤ 1 / (1 - r) := by
  have e : (j : ℝ) * r ^ j = ∑ _i ∈ Finset.range j, r ^ j := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [e]
  exact (Finset.sum_le_sum fun i hi =>
    pow_le_pow_of_le_one h0 h1.le (Finset.mem_range.1 hi).le).trans (kr_geom_sum_le h0 h1 j)

/-! ## The generic weighted sum -/

/-- A nonnegative sequence with partial sums `≤ S` and `F(T₀ + j) ≤ C r^j`, `T₀ + s ≤ 3w²`,
has weighted partial sums `∑ e^{ε (n+s)/w²} F n ≤ e^{3ε} (S + C/(1 - r e^{ε/w²}))`. -/
theorem kr_expw_sum_le {F : ℕ → ℝ} (hF : ∀ n, 0 ≤ F n) {S C r ε w : ℝ} (T₀ s : ℕ)
    (hS : ∀ N, ∑ n ∈ Finset.range N, F n ≤ S) (hlarge : ∀ j, F (T₀ + j) ≤ C * r ^ j)
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hε : 0 ≤ ε) (hw : 0 < w) (hT : ((T₀ + s : ℕ) : ℝ) ≤ 3 * w ^ 2)
    (hgeom : r * Real.exp (ε / w ^ 2) < 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, Real.exp (ε * ((n + s : ℕ) : ℝ) / w ^ 2) * F n ≤
      Real.exp (3 * ε) * (S + C / (1 - r * Real.exp (ε / w ^ 2))) := by
  have hF' : ∀ n, 0 ≤ Real.exp (ε * ((n + s : ℕ) : ℝ) / w ^ 2) * F n :=
    fun n => mul_nonneg (Real.exp_pos _).le (hF n)
  have hw2 : 0 < w ^ 2 := by positivity
  have hTε : ε * ((T₀ + s : ℕ) : ℝ) / w ^ 2 ≤ 3 * ε := by
    calc ε * ((T₀ + s : ℕ) : ℝ) / w ^ 2 ≤ ε * (3 * w ^ 2) / w ^ 2 := by gcongr
      _ = 3 * ε := by field_simp
  refine (kr_sum_split hF' T₀ N).trans ?_
  have h1 : ∑ n ∈ Finset.range T₀, Real.exp (ε * ((n + s : ℕ) : ℝ) / w ^ 2) * F n ≤
      Real.exp (3 * ε) * S := by
    have hb : ∀ n ∈ Finset.range T₀,
        Real.exp (ε * ((n + s : ℕ) : ℝ) / w ^ 2) * F n ≤ Real.exp (3 * ε) * F n := fun n hn => by
      refine mul_le_mul_of_nonneg_right ?_ (hF n)
      rw [Real.exp_le_exp]
      have hn' : ((n + s : ℕ) : ℝ) ≤ ((T₀ + s : ℕ) : ℝ) := by
        exact_mod_cast (by have := Finset.mem_range.1 hn; omega : n + s ≤ T₀ + s)
      calc ε * ((n + s : ℕ) : ℝ) / w ^ 2 ≤ ε * ((T₀ + s : ℕ) : ℝ) / w ^ 2 := by gcongr
        _ ≤ 3 * ε := hTε
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hS T₀) (Real.exp_pos _).le
  have h2 : ∑ j ∈ Finset.range (N - T₀),
      Real.exp (ε * ((T₀ + j + s : ℕ) : ℝ) / w ^ 2) * F (T₀ + j) ≤
        Real.exp (3 * ε) * (C / (1 - r * Real.exp (ε / w ^ 2))) := by
    have hb : ∀ j ∈ Finset.range (N - T₀),
        Real.exp (ε * ((T₀ + j + s : ℕ) : ℝ) / w ^ 2) * F (T₀ + j) ≤
          Real.exp (3 * ε) * C * (r * Real.exp (ε / w ^ 2)) ^ j := fun j _ => by
      have hωj : Real.exp (ε * ((T₀ + j + s : ℕ) : ℝ) / w ^ 2) ≤
          Real.exp (3 * ε) * Real.exp (ε / w ^ 2) ^ j := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
        have e : ε * ((T₀ + j + s : ℕ) : ℝ) / w ^ 2 =
            ε * ((T₀ + s : ℕ) : ℝ) / w ^ 2 + j * (ε / w ^ 2) := by
          push_cast
          ring
        rw [e]
        linarith
      calc Real.exp (ε * ((T₀ + j + s : ℕ) : ℝ) / w ^ 2) * F (T₀ + j)
          ≤ (Real.exp (3 * ε) * Real.exp (ε / w ^ 2) ^ j) * (C * r ^ j) :=
            mul_le_mul hωj (hlarge j) (hF _) (by positivity)
        _ = Real.exp (3 * ε) * C * (r * Real.exp (ε / w ^ 2)) ^ j := by rw [mul_pow]; ring
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    calc C * ∑ j ∈ Finset.range (N - T₀), (r * Real.exp (ε / w ^ 2)) ^ j
        ≤ C * (1 / (1 - r * Real.exp (ε / w ^ 2))) :=
          mul_le_mul_of_nonneg_left (kr_geom_sum_le (by positivity) hgeom _) hC
      _ = C / (1 - r * Real.exp (ε / w ^ 2)) := by ring
  calc _ ≤ Real.exp (3 * ε) * S + Real.exp (3 * ε) * (C / (1 - r * Real.exp (ε / w ^ 2))) :=
        add_le_add h1 h2
    _ = _ := by ring

/-! ## The weighted geometric factors -/

/-- The admissible weight bound `ε₀ = min(κ/32, (1 - ρ)/12)`. -/
def krEps (D vlo vhi : ℝ) : ℝ :=
  min (krKappa D vlo vhi / 32) ((1 - kBVClassRho D vlo vhi) / 12)

namespace KrBand

variable {ν}

theorem kappa_le_one {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') : krKappa D vlo vhi ≤ 1 :=
  krKappa_le_one H.hD H.hθ H.hvlo H.hvhi H.hν

theorem krEps_pos {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') : 0 < krEps D vlo vhi := by
  have h1 := H.kappa_pos
  have h2 := H.classConsts.2.1
  unfold krEps
  exact lt_min (by positivity) (by linarith)

theorem krEps_le_kappa {θ vlo vhi K L w A a' : ℝ}
    (_H : KrBand D θ vlo vhi K L ν f w A a β a') : krEps D vlo vhi ≤ krKappa D vlo vhi / 32 :=
  min_le_left _ _

theorem krEps_le_rho {θ vlo vhi K L w A a' : ℝ}
    (_H : KrBand D θ vlo vhi K L ν f w A a β a') :
    krEps D vlo vhi ≤ (1 - kBVClassRho D vlo vhi) / 12 :=
  min_le_right _ _

theorem sqrt_lam_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') :
    Real.sqrt (krLam D vlo vhi w) ≤ 1 - krKappa D vlo vhi / (2 * w ^ 2) := by
  linarith [H.one_sub_sqrt_lam]

/-- `e^{ε/w²} ≤ 1 + 2ε/w²` for `0 ≤ ε ≤ 1`. -/
theorem exp_eps_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1) :
    Real.exp (ε / w ^ 2) ≤ 1 + 2 * ε / w ^ 2 := by
  have hw := H.hw
  have hw2 : 1 ≤ w ^ 2 := one_le_pow₀ hw
  have h := kr_exp_le_one_add_two_mul (x := ε / w ^ 2) (by positivity)
    (by rw [div_le_one (by positivity)]; exact hε.trans hw2)
  refine h.trans (le_of_eq ?_)
  ring

/-- `√λ e^{ε/w²} ≤ 1 - κ/(4w²)` for `0 ≤ ε ≤ κ/16`. -/
theorem expw_factor {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ krKappa D vlo vhi / 16) :
    Real.sqrt (krLam D vlo vhi w) * Real.exp (ε / w ^ 2) ≤ 1 - krKappa D vlo vhi / (4 * w ^ 2) := by
  have hw0 := H.hw0
  have hκ := H.kappa_pos
  have hκ1 := H.kappa_le_one
  have h1 := H.sqrt_lam_le
  have h2 := H.exp_eps_le hε0 (by linarith)
  have h10 : 0 ≤ 1 - krKappa D vlo vhi / (2 * w ^ 2) := H.sqrt_lam_nonneg.trans h1
  calc Real.sqrt (krLam D vlo vhi w) * Real.exp (ε / w ^ 2)
      ≤ (1 - krKappa D vlo vhi / (2 * w ^ 2)) * (1 + 2 * ε / w ^ 2) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le h10
    _ ≤ 1 - krKappa D vlo vhi / (4 * w ^ 2) := by
        have e : 1 - krKappa D vlo vhi / (4 * w ^ 2) -
            (1 - krKappa D vlo vhi / (2 * w ^ 2)) * (1 + 2 * ε / w ^ 2) =
            (krKappa D vlo vhi - 8 * ε) / (4 * w ^ 2) + krKappa D vlo vhi * ε / w ^ 4 := by
          field_simp
          ring
        have : 0 ≤ (krKappa D vlo vhi - 8 * ε) / (4 * w ^ 2) + krKappa D vlo vhi * ε / w ^ 4 :=
          add_nonneg (div_nonneg (by linarith) (by positivity)) (by positivity)
        linarith

theorem expw_factor_lt_one {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ krKappa D vlo vhi / 16) :
    Real.sqrt (krLam D vlo vhi w) * Real.exp (ε / w ^ 2) < 1 := by
  have := H.expw_factor hε0 hε
  have hκ := H.kappa_pos
  have hw0 := H.hw0
  have : 0 < krKappa D vlo vhi / (4 * w ^ 2) := by positivity
  linarith

/-- `1/(1 - √λ e^{ε/w²}) ≤ 4 w²/κ`. -/
theorem inv_expw_factor {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ krKappa D vlo vhi / 16) :
    1 / (1 - Real.sqrt (krLam D vlo vhi w) * Real.exp (ε / w ^ 2)) ≤
      4 * w ^ 2 / krKappa D vlo vhi := by
  have h := H.expw_factor hε0 hε
  have hκ := H.kappa_pos
  have hw0 := H.hw0
  have hpos : 0 < krKappa D vlo vhi / (4 * w ^ 2) := by positivity
  calc 1 / (1 - Real.sqrt (krLam D vlo vhi w) * Real.exp (ε / w ^ 2))
      ≤ 1 / (krKappa D vlo vhi / (4 * w ^ 2)) := one_div_le_one_div_of_le hpos (by linarith)
    _ = 4 * w ^ 2 / krKappa D vlo vhi := by rw [one_div_div]

/-- `√√λ ≤ 1 - κ/(4w²)`. -/
theorem sqrt_sqrt_lam_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') :
    Real.sqrt (Real.sqrt (krLam D vlo vhi w)) ≤ 1 - krKappa D vlo vhi / (4 * w ^ 2) := by
  have h := kr_one_sub_sqrt_ge H.sqrt_lam_nonneg H.sqrt_lam_lt_one.le
  have h2 := H.one_sub_sqrt_lam
  have e : krKappa D vlo vhi / (4 * w ^ 2) = krKappa D vlo vhi / (2 * w ^ 2) / 2 := by ring
  rw [e]
  linarith

/-- `√√λ e^{ε/w²} ≤ 1 - κ/(8w²)` for `0 ≤ ε ≤ κ/16`. -/
theorem expw_factor' {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ krKappa D vlo vhi / 16) :
    Real.sqrt (Real.sqrt (krLam D vlo vhi w)) * Real.exp (ε / w ^ 2) ≤
      1 - krKappa D vlo vhi / (8 * w ^ 2) := by
  have hw0 := H.hw0
  have hκ := H.kappa_pos
  have hκ1 := H.kappa_le_one
  have h1 := H.sqrt_sqrt_lam_le
  have h2 := H.exp_eps_le hε0 (by linarith)
  have h10 : 0 ≤ 1 - krKappa D vlo vhi / (4 * w ^ 2) := (Real.sqrt_nonneg _).trans h1
  calc Real.sqrt (Real.sqrt (krLam D vlo vhi w)) * Real.exp (ε / w ^ 2)
      ≤ (1 - krKappa D vlo vhi / (4 * w ^ 2)) * (1 + 2 * ε / w ^ 2) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le h10
    _ ≤ 1 - krKappa D vlo vhi / (8 * w ^ 2) := by
        have e : 1 - krKappa D vlo vhi / (8 * w ^ 2) -
            (1 - krKappa D vlo vhi / (4 * w ^ 2)) * (1 + 2 * ε / w ^ 2) =
            (krKappa D vlo vhi - 16 * ε) / (8 * w ^ 2) + krKappa D vlo vhi * ε / (2 * w ^ 4) := by
          field_simp
          ring
        have : 0 ≤ (krKappa D vlo vhi - 16 * ε) / (8 * w ^ 2) +
            krKappa D vlo vhi * ε / (2 * w ^ 4) :=
          add_nonneg (div_nonneg (by linarith) (by positivity)) (by positivity)
        linarith

theorem expw_factor'_lt_one {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ krKappa D vlo vhi / 16) :
    Real.sqrt (Real.sqrt (krLam D vlo vhi w)) * Real.exp (ε / w ^ 2) < 1 := by
  have := H.expw_factor' hε0 hε
  have hκ := H.kappa_pos
  have hw0 := H.hw0
  have : 0 < krKappa D vlo vhi / (8 * w ^ 2) := by positivity
  linarith

/-- `1/(1 - √√λ e^{ε/w²}) ≤ 8 w²/κ`. -/
theorem inv_expw_factor' {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ krKappa D vlo vhi / 16) :
    1 / (1 - Real.sqrt (Real.sqrt (krLam D vlo vhi w)) * Real.exp (ε / w ^ 2)) ≤
      8 * w ^ 2 / krKappa D vlo vhi := by
  have h := H.expw_factor' hε0 hε
  have hκ := H.kappa_pos
  have hw0 := H.hw0
  have hpos : 0 < krKappa D vlo vhi / (8 * w ^ 2) := by positivity
  calc 1 / (1 - Real.sqrt (Real.sqrt (krLam D vlo vhi w)) * Real.exp (ε / w ^ 2))
      ≤ 1 / (krKappa D vlo vhi / (8 * w ^ 2)) := one_div_le_one_div_of_le hpos (by linarith)
    _ = 8 * w ^ 2 / krKappa D vlo vhi := by rw [one_div_div]

theorem two_T_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') :
    ((2 * krT w - 1 + 1 : ℕ) : ℝ) ≤ 3 * w ^ 2 := by
  have := H.hT1
  rw [Nat.sub_add_cancel (by omega)]
  push_cast
  have := H.hTw
  nlinarith [sq_nonneg w]

theorem two_T_index {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (j : ℕ) :
    2 * krT w - 1 + j + 1 = krT w + j + krT w := by
  have := H.hT1
  omega

end KrBand

/-! ## The four weighted Green sums -/

/-- **Weighted boundary survival sum**:
`∑_{n<N} e^{ε n/w²} s_n(b) ≤ e^{3ε} (C^O + 4 C₃/κ) (1 + A) w`. -/
theorem sum_expw_krSurv_bdry_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi / 16) (N : ℕ) :
    ∑ n ∈ Finset.range N, Real.exp (ε * n / w ^ 2) * krSurv (Icc 0 w) (ν : Measure ℝ) β a' n b ≤
      Real.exp (3 * ε) *
        ((krCO D K L vlo vhi + 4 * krC₃ D K L / krKappa D vlo vhi) * (1 + A) * w) := by
  have hw0 := H.hw0
  have hA := H.hA
  have hκ := H.kappa_pos
  have hC3 : 0 ≤ krC₃ D K L := Real.sqrt_nonneg _
  have h := kr_expw_sum_le (F := fun n => krSurv (Icc 0 w) (ν : Measure ℝ) β a' n b)
    (fun n => krSurv_nonneg H.hJ ν β a' n b) (krT w) 0 (fun N => sum_krSurv_bdry_le ν H hb N)
    (C := krC₃ D K L * (1 + A) / w) (r := Real.sqrt (krLam D vlo vhi w))
    (fun j => (krSurv_bdry_large ν H hb H.hT1 H.hTw H.hwT j).trans (le_of_eq (by ring)))
    (by positivity) H.sqrt_lam_nonneg hε0 hw0
    (by rw [Nat.add_zero]; nlinarith [H.hTw, sq_nonneg w]) (H.expw_factor_lt_one hε0 hε) N
  simp only [Nat.add_zero] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  have hinv := H.inv_expw_factor hε0 hε
  calc krCO D K L vlo vhi * (1 + A) * w +
        krC₃ D K L * (1 + A) / w / (1 - Real.sqrt (krLam D vlo vhi w) * Real.exp (ε / w ^ 2))
      = krCO D K L vlo vhi * (1 + A) * w + krC₃ D K L * (1 + A) / w *
          (1 / (1 - Real.sqrt (krLam D vlo vhi w) * Real.exp (ε / w ^ 2))) := by ring
    _ ≤ krCO D K L vlo vhi * (1 + A) * w + krC₃ D K L * (1 + A) / w *
          (4 * w ^ 2 / krKappa D vlo vhi) := by gcongr
    _ = (krCO D K L vlo vhi + 4 * krC₃ D K L / krKappa D vlo vhi) * (1 + A) * w := by
        field_simp

/-- **Weighted boundary row sum**:
`∑_{n<N} e^{ε (n+1)/w²} q_{n+1}(b, z) ≤ e^{3ε} (C^G + 4 C₄/κ) (1 + A)(1 + log w)`. -/
theorem sum_expw_krDens_bdry_row_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w) (z : ℝ)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi / 16) (N : ℕ) :
    ∑ n ∈ Finset.range N, Real.exp (ε * ((n + 1 : ℕ) : ℝ) / w ^ 2) *
        krDens (Icc 0 w) ν f β a' (n + 1) b z ≤
      Real.exp (3 * ε) * ((krCG D K L vlo vhi + 4 * krC₄ D K L / krKappa D vlo vhi) * (1 + A) *
        (1 + Real.log w)) := by
  have hw0 := H.hw0
  have hA := H.hA
  have hκ := H.kappa_pos
  have hC4 : 0 ≤ krC₄ D K L := Real.sqrt_nonneg _
  have hlog : 0 ≤ Real.log w := Real.log_nonneg H.hw
  have h := kr_expw_sum_le (F := fun n => krDens (Icc 0 w) ν f β a' (n + 1) b z)
    (fun n => krDens_nonneg ν H.hf0 (n + 1) b z) (2 * krT w - 1) 1
    (fun N => sum_krDens_bdry_row_le ν H hb z N)
    (C := krC₄ D K L * (1 + A) / w ^ 2) (r := Real.sqrt (krLam D vlo vhi w))
    (fun j => by
      show krDens (Icc 0 w) ν f β a' (2 * krT w - 1 + j + 1) b z ≤ _
      rw [H.two_T_index j]
      exact (krDens_bdry_row_large ν H hb H.hT1 H.hTw H.hwT j z).trans (le_of_eq (by ring)))
    (by positivity) H.sqrt_lam_nonneg hε0 hw0 H.two_T_le (H.expw_factor_lt_one hε0 hε) N
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  have hinv := H.inv_expw_factor hε0 hε
  calc krCG D K L vlo vhi * (1 + A) * (1 + Real.log w) +
        krC₄ D K L * (1 + A) / w ^ 2 /
          (1 - Real.sqrt (krLam D vlo vhi w) * Real.exp (ε / w ^ 2))
      = krCG D K L vlo vhi * (1 + A) * (1 + Real.log w) + krC₄ D K L * (1 + A) / w ^ 2 *
          (1 / (1 - Real.sqrt (krLam D vlo vhi w) * Real.exp (ε / w ^ 2))) := by ring
    _ ≤ krCG D K L vlo vhi * (1 + A) * (1 + Real.log w) + krC₄ D K L * (1 + A) / w ^ 2 *
          (4 * w ^ 2 / krKappa D vlo vhi) := by gcongr
    _ = krCG D K L vlo vhi * (1 + A) * (1 + Real.log w) +
          4 * krC₄ D K L / krKappa D vlo vhi * (1 + A) * 1 := by
        field_simp
    _ ≤ krCG D K L vlo vhi * (1 + A) * (1 + Real.log w) +
          4 * krC₄ D K L / krKappa D vlo vhi * (1 + A) * (1 + Real.log w) := by
        gcongr
        linarith
    _ = _ := by ring

/-- **Weighted opposite-side pin sum**:
`∑_{n<N} e^{ε (n+1)/w²} q_{n+1}(b, b') ≤ e^{3ε} (C^P + 12 C₂/κ) (1 + A)²/√w`. -/
theorem sum_expw_krDens_bdry_pin_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (hAw : A ≤ w) {b b' : ℝ} (hb : b = 0 ∨ b = w)
    (hb' : b' = 0 ∨ b' = w) (hbb : b ≠ b')
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi / 16) (N : ℕ) :
    ∑ n ∈ Finset.range N, Real.exp (ε * ((n + 1 : ℕ) : ℝ) / w ^ 2) *
        krDens (Icc 0 w) ν f β a' (n + 1) b b' ≤
      Real.exp (3 * ε) * ((krCP D θ K L vlo vhi + 12 * krC₂ D K L / krKappa D vlo vhi) *
        (1 + A) ^ 2 / Real.sqrt w) := by
  have hw0 := H.hw0
  have hw := H.hw
  have hA := H.hA
  have hκ := H.kappa_pos
  have hC := krC₂_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.2 hw0
  have hsww : Real.sqrt w ≤ w := by
    rw [Real.sqrt_le_left hw0.le]
    nlinarith
  have h := kr_expw_sum_le (F := fun n => krDens (Icc 0 w) ν f β a' (n + 1) b b')
    (fun n => krDens_nonneg ν H.hf0 (n + 1) b b') (2 * krT w - 1) 1
    (fun N => sum_krDens_bdry_pin_le ν H hAw hb hb' hbb N)
    (C := 3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3) (r := Real.sqrt (krLam D vlo vhi w))
    (fun j => by
      show krDens (Icc 0 w) ν f β a' (2 * krT w - 1 + j + 1) b b' ≤ _
      rw [H.two_T_index j]
      exact (krDens_bdry_pin_large ν H hb hb' H.hT1 H.hTw H.hwT j).trans (le_of_eq (by ring)))
    (by positivity) H.sqrt_lam_nonneg hε0 hw0 H.two_T_le (H.expw_factor_lt_one hε0 hε) N
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  have hinv := H.inv_expw_factor hε0 hε
  have hCP : 0 ≤ krCP D θ K L vlo vhi := by
    have := sum_krDens_bdry_pin_le ν H hAw hb hb' hbb 0
    simp only [Finset.range_zero, Finset.sum_empty] at this
    have hpos : 0 < (1 + A) ^ 2 / Real.sqrt w := by positivity
    by_contra hneg
    push Not at hneg
    have : krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w < 0 := by
      rw [mul_div_assoc]
      exact mul_neg_of_neg_of_pos hneg hpos
    linarith
  calc krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w +
        3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3 /
          (1 - Real.sqrt (krLam D vlo vhi w) * Real.exp (ε / w ^ 2))
      = krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w + 3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3 *
          (1 / (1 - Real.sqrt (krLam D vlo vhi w) * Real.exp (ε / w ^ 2))) := by ring
    _ ≤ krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w + 3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3 *
          (4 * w ^ 2 / krKappa D vlo vhi) := by gcongr
    _ = krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w +
          12 * krC₂ D K L / krKappa D vlo vhi * (1 + A) ^ 2 * (1 / w) := by
        field_simp
        ring
    _ ≤ krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w +
          12 * krC₂ D K L / krKappa D vlo vhi * (1 + A) ^ 2 * (1 / Real.sqrt w) := by
        gcongr
    _ = _ := by ring

/-- **Weighted length-weighted pin sum**:
`∑_{n<N} e^{ε (n+1)/w²} (n + 1 + w) q_{n+1}(b, b') ≤ e^{3ε} (C^B + 264 C₂/κ²) (1 + A)² w`. -/
theorem sum_expw_weighted_krDens_bdry_pin_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b b' : ℝ} (hb : b = 0 ∨ b = w)
    (hb' : b' = 0 ∨ b' = w)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi / 16) (N : ℕ) :
    ∑ n ∈ Finset.range N, Real.exp (ε * ((n + 1 : ℕ) : ℝ) / w ^ 2) *
        (((n : ℝ) + 1 + w) * krDens (Icc 0 w) ν f β a' (n + 1) b b') ≤
      Real.exp (3 * ε) * ((krCB D K L vlo vhi + 264 * krC₂ D K L / krKappa D vlo vhi ^ 2) *
        (1 + A) ^ 2 * w) := by
  have hw0 := H.hw0
  have hw := H.hw
  have hA := H.hA
  have hκ := H.kappa_pos
  have hκ1 := H.kappa_le_one
  have hC := krC₂_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  set r₁ := Real.sqrt (Real.sqrt (krLam D vlo vhi w)) with hr₁
  have hr₁0 : 0 ≤ r₁ := Real.sqrt_nonneg _
  have hr₁1 : r₁ < 1 := by
    have := H.expw_factor' (ε := 0) le_rfl (by positivity)
    simp only [zero_div, Real.exp_zero, mul_one] at this
    have : 0 < krKappa D vlo vhi / (8 * w ^ 2) := by positivity
    linarith
  have hr₁sq : r₁ ^ 2 = Real.sqrt (krLam D vlo vhi w) := Real.sq_sqrt H.sqrt_lam_nonneg
  -- `(2T + j + w) √λ^j ≤ (11 w²/κ) r₁^j`
  have hlarge : ∀ j : ℕ, (((2 * krT w - 1 + j : ℕ) : ℝ) + 1 + w) *
      krDens (Icc 0 w) ν f β a' (2 * krT w - 1 + j + 1) b b' ≤
        33 * krC₂ D K L * (1 + A) ^ 2 / (krKappa D vlo vhi * w) * r₁ ^ j := fun j => by
    rw [H.two_T_index j]
    have hT := H.hT1
    have e : (((2 * krT w - 1 + j : ℕ) : ℝ) + 1 + w) = 2 * (krT w : ℝ) + j + w := by
      rw [Nat.cast_add, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [e]
    have hq := krDens_bdry_pin_large ν H hb hb' H.hT1 H.hTw H.hwT j
    have hsplit : Real.sqrt (krLam D vlo vhi w) ^ j = r₁ ^ j * r₁ ^ j := by
      rw [← hr₁sq, ← pow_mul, ← pow_add, two_mul]
    have hj : (j : ℝ) * r₁ ^ j ≤ 8 * w ^ 2 / krKappa D vlo vhi := by
      refine (kr_mul_pow_le hr₁0 hr₁1 j).trans ?_
      have := H.inv_expw_factor' (ε := 0) le_rfl (by positivity)
      simpa only [zero_div, Real.exp_zero, mul_one] using this
    have hr₁j : r₁ ^ j ≤ 1 := pow_le_one₀ hr₁0 hr₁1.le
    have hTw : 2 * (krT w : ℝ) + w ≤ 3 * w ^ 2 := by nlinarith [H.hTw, sq_nonneg w]
    have hfront : (2 * (krT w : ℝ) + j + w) * r₁ ^ j ≤ 11 * w ^ 2 / krKappa D vlo vhi := by
      have h1 : (2 * (krT w : ℝ) + w) * r₁ ^ j ≤ 3 * w ^ 2 := by
        calc (2 * (krT w : ℝ) + w) * r₁ ^ j ≤ (3 * w ^ 2) * 1 :=
              mul_le_mul hTw hr₁j (pow_nonneg hr₁0 _) (by positivity)
          _ = 3 * w ^ 2 := mul_one _
      have h2 : 3 * w ^ 2 ≤ 3 * w ^ 2 / krKappa D vlo vhi := by
        rw [le_div_iff₀ hκ]
        nlinarith [sq_nonneg w]
      have e2 : (2 * (krT w : ℝ) + j + w) * r₁ ^ j =
          (2 * (krT w : ℝ) + w) * r₁ ^ j + j * r₁ ^ j := by ring
      rw [e2]
      have : 3 * w ^ 2 / krKappa D vlo vhi + 8 * w ^ 2 / krKappa D vlo vhi =
          11 * w ^ 2 / krKappa D vlo vhi := by ring
      linarith
    calc (2 * (krT w : ℝ) + j + w) * krDens (Icc 0 w) ν f β a' (krT w + j + krT w) b b'
        ≤ (2 * (krT w : ℝ) + j + w) *
          (3 * krC₂ D K L * (1 + A) ^ 2 * Real.sqrt (krLam D vlo vhi w) ^ j / w ^ 3) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = ((2 * (krT w : ℝ) + j + w) * r₁ ^ j) * (3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3) *
          r₁ ^ j := by rw [hsplit]; ring
      _ ≤ (11 * w ^ 2 / krKappa D vlo vhi) * (3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3) *
          r₁ ^ j := by gcongr
      _ = 33 * krC₂ D K L * (1 + A) ^ 2 / (krKappa D vlo vhi * w) * r₁ ^ j := by
          field_simp
          ring
  have h := kr_expw_sum_le
    (F := fun n => ((n : ℝ) + 1 + w) * krDens (Icc 0 w) ν f β a' (n + 1) b b')
    (fun n => mul_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      (krDens_nonneg ν H.hf0 (n + 1) b b'))
    (2 * krT w - 1) 1 (fun N => sum_weighted_krDens_bdry_pin_le ν H hb hb' N)
    (C := 33 * krC₂ D K L * (1 + A) ^ 2 / (krKappa D vlo vhi * w)) (r := r₁) hlarge
    (by positivity) hr₁0 hε0 hw0 H.two_T_le (H.expw_factor'_lt_one hε0 hε) N
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  have hinv := H.inv_expw_factor' hε0 hε
  calc krCB D K L vlo vhi * (1 + A) ^ 2 * w +
        33 * krC₂ D K L * (1 + A) ^ 2 / (krKappa D vlo vhi * w) / (1 - r₁ * Real.exp (ε / w ^ 2))
      = krCB D K L vlo vhi * (1 + A) ^ 2 * w +
          33 * krC₂ D K L * (1 + A) ^ 2 / (krKappa D vlo vhi * w) *
            (1 / (1 - r₁ * Real.exp (ε / w ^ 2))) := by ring
    _ ≤ krCB D K L vlo vhi * (1 + A) ^ 2 * w +
          33 * krC₂ D K L * (1 + A) ^ 2 / (krKappa D vlo vhi * w) *
            (8 * w ^ 2 / krKappa D vlo vhi) := by gcongr
    _ = (krCB D K L vlo vhi + 264 * krC₂ D K L / krKappa D vlo vhi ^ 2) * (1 + A) ^ 2 * w := by
        field_simp
        ring

/-! ## The weighted (long) display -/

/-- Scaling a pointwise decomposition by a nonnegative weight. -/
theorem kr_scale_decomposition {w : ℝ} {g r : ℝ → ℂ} {q : ℝ → ℝ} {V Lc Rc ω : ℝ} (hω : 0 ≤ ω)
    (hg : Measurable g) (hr : Measurable r) (hs : ∀ x, x ∉ Icc 0 w → g x = 0 ∧ r x = 0)
    (hsum : ∀ z, (q z : ℂ) = g z + r z) (hvar : eVariationOn g univ ≤ ENNReal.ofReal V)
    (hlip : ∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖g x - g y‖ ≤ Lc * |x - y|)
    (hrem : ∀ x, ‖r x‖ ≤ Rc) :
    Measurable (fun x => (ω : ℂ) * g x) ∧ Measurable (fun x => (ω : ℂ) * r x) ∧
      (∀ x, x ∉ Icc 0 w → (ω : ℂ) * g x = 0 ∧ (ω : ℂ) * r x = 0) ∧
      (∀ z, ((ω * q z : ℝ) : ℂ) = (ω : ℂ) * g z + (ω : ℂ) * r z) ∧
      eVariationOn (fun x => (ω : ℂ) * g x) univ ≤ ENNReal.ofReal (ω * V) ∧
      (∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖(ω : ℂ) * g x - (ω : ℂ) * g y‖ ≤ (ω * Lc) * |x - y|) ∧
      (∀ x, ‖(ω : ℂ) * r x‖ ≤ ω * Rc) := by
  have hnorm : ‖(ω : ℂ)‖ = ω := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hω]
  refine ⟨measurable_const.mul hg, measurable_const.mul hr, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [(hs x hx).1, (hs x hx).2, mul_zero]
    exact ⟨rfl, rfl⟩
  · intro z
    rw [Complex.ofReal_mul, hsum z, mul_add]
  · have hl : LipschitzWith (Real.toNNReal ω) (fun z : ℂ => (ω : ℂ) * z) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, hnorm, Real.coe_toNNReal _ hω]
    have h := (hl.lipschitzOnWith (s := univ)).comp_eVariationOn_le (mapsTo_univ g univ)
    refine h.trans ?_
    rw [ENNReal.ofReal_mul hω]
    exact mul_le_mul' le_rfl hvar
  · intro x hx y hy
    rw [← mul_sub, norm_mul, hnorm, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hlip x hx y hy) hω
  · intro x
    rw [norm_mul, hnorm]
    exact mul_le_mul_of_nonneg_left (hrem x) hω

variable {ν}

/-- The weight against the variation term: `e^{ε n/w²} krVarTermGen ρ n ≤ e^{3ε} krVarTermGen (ρ-ε) n`. -/
theorem KrBand.expw_varTerm {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {ε : ℝ} (hε0 : 0 ≤ ε) (ρ : ℝ) (n : ℕ) :
    Real.exp (ε * n / w ^ 2) * krVarTermGen ρ w n ≤
      Real.exp (3 * ε) * krVarTermGen (ρ - ε) w n := by
  have hw0 := H.hw0
  have hTw := H.hTw
  have h3T : ε * (3 * (krT w : ℝ)) / w ^ 2 ≤ 3 * ε := by
    calc ε * (3 * (krT w : ℝ)) / w ^ 2 ≤ ε * (3 * w ^ 2) / w ^ 2 := by gcongr
      _ = 3 * ε := by field_simp
  unfold krVarTermGen
  by_cases h3 : 3 * krT w ≤ n
  · rw [if_pos h3, if_pos h3]
    have hn : (n : ℝ) = 3 * (krT w : ℝ) + ((n - 3 * krT w : ℕ) : ℝ) := by
      rw [Nat.cast_sub h3]
      push_cast
      ring
    have hsplit : Real.exp (ε * n / w ^ 2) =
        Real.exp (ε * (3 * (krT w : ℝ)) / w ^ 2) * Real.exp (ε / w ^ 2) ^ (n - 3 * krT w) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, hn]
      congr 1
      ring
    have hprod : Real.exp (ε / w ^ 2) ^ (n - 3 * krT w) * Real.exp (-(ρ / w ^ 2)) ^ (n - 3 * krT w) =
        Real.exp (-((ρ - ε) / w ^ 2)) ^ (n - 3 * krT w) := by
      rw [← mul_pow, ← Real.exp_add]
      congr 2
      ring
    rw [hsplit]
    calc Real.exp (ε * (3 * (krT w : ℝ)) / w ^ 2) * Real.exp (ε / w ^ 2) ^ (n - 3 * krT w) *
          (Real.sqrt 6 * Real.exp (-(ρ / w ^ 2)) ^ (n - 3 * krT w) / w ^ 2)
        = Real.exp (ε * (3 * (krT w : ℝ)) / w ^ 2) *
          (Real.sqrt 6 * (Real.exp (ε / w ^ 2) ^ (n - 3 * krT w) *
            Real.exp (-(ρ / w ^ 2)) ^ (n - 3 * krT w)) / w ^ 2) := by ring
      _ = Real.exp (ε * (3 * (krT w : ℝ)) / w ^ 2) *
          (Real.sqrt 6 * Real.exp (-((ρ - ε) / w ^ 2)) ^ (n - 3 * krT w) / w ^ 2) := by
          rw [hprod]
      _ ≤ Real.exp (3 * ε) *
          (Real.sqrt 6 * Real.exp (-((ρ - ε) / w ^ 2)) ^ (n - 3 * krT w) / w ^ 2) := by
          gcongr
  · rw [if_neg h3, if_neg h3]
    have hn : (n : ℝ) ≤ 3 * (krT w : ℝ) := by
      have : n ≤ 3 * krT w := by omega
      exact_mod_cast this
    have : Real.exp (ε * n / w ^ 2) ≤ Real.exp (3 * ε) := by
      rw [Real.exp_le_exp]
      calc ε * n / w ^ 2 ≤ ε * (3 * (krT w : ℝ)) / w ^ 2 := by gcongr
        _ ≤ 3 * ε := h3T
    exact mul_le_mul_of_nonneg_right this
      (div_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (krFourthRoot_nonneg _)))

/-- The weight against the remainder power:
`e^{ε n/w²} ρ^{⌊n/3⌋-1} ≤ e^{5ε} (ρ e^{3ε/w²})^{⌊n/3⌋-1}`. -/
theorem kr_expw_rho {ε w ρ : ℝ} (hε0 : 0 ≤ ε) (hw : 1 ≤ w) (hρ0 : 0 ≤ ρ) (n : ℕ) :
    Real.exp (ε * n / w ^ 2) * ρ ^ (n / 3 - 1) ≤
      Real.exp (5 * ε) * (ρ * Real.exp (3 * ε / w ^ 2)) ^ (n / 3 - 1) := by
  have hw0 : 0 < w := by linarith
  have hw2 : 1 ≤ w ^ 2 := one_le_pow₀ hw
  have hnq : (n : ℝ) ≤ 3 * ((n / 3 - 1 : ℕ) : ℝ) + 5 := by
    have : n ≤ 3 * (n / 3 - 1) + 5 := by omega
    exact_mod_cast this
  have hexp : Real.exp (ε * n / w ^ 2) ≤
      Real.exp (5 * ε) * Real.exp (3 * ε / w ^ 2) ^ (n / 3 - 1) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
    have h1 : ε * n / w ^ 2 ≤ ε * (3 * ((n / 3 - 1 : ℕ) : ℝ) + 5) / w ^ 2 := by gcongr
    have h2 : ε * (3 * ((n / 3 - 1 : ℕ) : ℝ) + 5) / w ^ 2 =
        5 * ε / w ^ 2 + ((n / 3 - 1 : ℕ) : ℝ) * (3 * ε / w ^ 2) := by ring
    have h3 : 5 * ε / w ^ 2 ≤ 5 * ε := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  calc Real.exp (ε * n / w ^ 2) * ρ ^ (n / 3 - 1)
      ≤ (Real.exp (5 * ε) * Real.exp (3 * ε / w ^ 2) ^ (n / 3 - 1)) * ρ ^ (n / 3 - 1) :=
        mul_le_mul_of_nonneg_right hexp (pow_nonneg hρ0 _)
    _ = Real.exp (5 * ε) * (ρ * Real.exp (3 * ε / w ^ 2)) ^ (n / 3 - 1) := by
        rw [mul_pow]
        ring

/-- `ρ e^{3ε/w²} ≤ (1 + ρ)/2` for `0 ≤ ε ≤ ε₀`. -/
theorem KrBand.rho_expw_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ krEps D vlo vhi) :
    kBVClassRho D vlo vhi * Real.exp (3 * ε / w ^ 2) ≤ (1 + kBVClassRho D vlo vhi) / 2 := by
  have hcc := H.classConsts
  have hκ1 := H.kappa_le_one
  have hε1 := hε.trans H.krEps_le_kappa
  have hε2 := hε.trans H.krEps_le_rho
  have hw := H.hw
  have hw2 : 1 ≤ w ^ 2 := one_le_pow₀ hw
  have h := H.exp_eps_le (ε := 3 * ε) (by linarith) (by linarith)
  have hρ1 := hcc.2.1
  have hρ0 := hcc.1
  have h6 : 2 * (3 * ε) / w ^ 2 ≤ 6 * ε := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc kBVClassRho D vlo vhi * Real.exp (3 * ε / w ^ 2)
      ≤ kBVClassRho D vlo vhi * (1 + 2 * (3 * ε) / w ^ 2) :=
        mul_le_mul_of_nonneg_left h hρ0
    _ ≤ kBVClassRho D vlo vhi * (1 + 6 * ε) := by gcongr
    _ = kBVClassRho D vlo vhi + kBVClassRho D vlo vhi * (6 * ε) := by ring
    _ ≤ kBVClassRho D vlo vhi + 1 * (6 * ε) := by gcongr
    _ ≤ (1 + kBVClassRho D vlo vhi) / 2 := by linarith

variable (ν)

/-- **(long), weighted**: for `0 ≤ ε ≤ ε₀`, `∑_{i<M} e^{ε (P+1+i)/w²} q_{P+1+i}(b, ·) = G + R` with
`V(G) ≤ 2 e^{3ε} krCV (1+A) (√w/P^{1/4} + 1)`, the same Lipschitz scale times `2D`,
`‖R‖_∞ ≤ 2 e^{5ε} krCR (1+A) ((1+ρ)/2)^{⌊P/3⌋-1}`, and the opposite-endpoint trace
`‖G(b')‖ ≤ e^{3ε} (C^P + 12 C₂/κ)(1+A)²/√w + 2 e^{5ε} krCR (1+A) ((1+ρ)/2)^{⌊P/3⌋-1}`. -/
theorem krLong_decomposition_expw {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {P : ℕ} (hP : 12 ≤ P) (M : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krEps D vlo vhi) :
    ∃ G R : ℝ → ℂ, Measurable G ∧ Measurable R ∧
      (∀ x, x ∉ Icc 0 w → G x = 0 ∧ R x = 0) ∧
      (∀ z, ((∑ i ∈ Finset.range M, Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) *
        krDens (Icc 0 w) ν f β a' (P + 1 + i) b z : ℝ) : ℂ) = G z + R z) ∧
      eVariationOn G univ ≤ ENNReal.ofReal (2 * Real.exp (3 * ε) * krCV D K L vlo vhi * (1 + A) *
        (Real.sqrt w / krFourthRoot P + 1)) ∧
      (∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖G x - G y‖ ≤
        (2 * D * (2 * Real.exp (3 * ε) * krCV D K L vlo vhi * (1 + A) *
          (Real.sqrt w / krFourthRoot P + 1))) * |x - y|) ∧
      (∀ x, ‖R x‖ ≤ 2 * Real.exp (5 * ε) * krCR D K L vlo vhi * (1 + A) *
        ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1)) ∧
      (∀ b', (b' = 0 ∨ b' = w) → b ≠ b' → A ≤ w →
        ‖G b'‖ ≤ Real.exp (3 * ε) * ((krCP D θ K L vlo vhi + 12 * krC₂ D K L / krKappa D vlo vhi) *
          (1 + A) ^ 2 / Real.sqrt w) +
          2 * Real.exp (5 * ε) * krCR D K L vlo vhi * (1 + A) *
            ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1)) := by
  have hw0 := H.hw0
  have hw := H.hw
  have hA := H.hA
  have hcc := H.classConsts
  have hC := krC₂_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  have hD0 := H.hD0
  have hεκ : ε ≤ krKappa D vlo vhi / 16 := by
    have := hε.trans H.krEps_le_kappa
    have := H.kappa_pos
    linarith
  set ω : ℕ → ℝ := fun i => Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) with hω_def
  have hω0 : ∀ i, 0 ≤ ω i := fun i => (Real.exp_pos _).le
  -- per-row decompositions, scaled
  have hdec : ∀ i : ℕ, ∃ g r : ℝ → ℂ, Measurable g ∧ Measurable r ∧
      (∀ x, x ∉ Icc 0 w → g x = 0 ∧ r x = 0) ∧
      (∀ z, ((ω i * krDens (Icc 0 w) ν f β a' (P + 1 + i) b z : ℝ) : ℂ) = g z + r z) ∧
      eVariationOn g univ ≤ ENNReal.ofReal (ω i * (kBVClassVarConst D vlo vhi *
        Real.sqrt (krC₂ D K L) * (1 + A) * krVarTerm D vlo vhi w (P + 1 + i))) ∧
      (∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖g x - g y‖ ≤
        (ω i * (2 * D * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
          krVarTerm D vlo vhi w (P + 1 + i)))) * |x - y|) ∧
      (∀ x, ‖r x‖ ≤ ω i * (Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
        Real.sqrt (3 * krC₂ D K L) * (1 + A) * kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1)))) := by
    intro i
    obtain ⟨g, r, hg, hr, hs, hsum, hvar, hlip, hrem⟩ :=
      krDens_row_decomposition ν H hb (n := P + 1 + i) (by omega)
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
      kr_scale_decomposition (hω0 i) hg hr hs hsum hvar hlip hrem
    exact ⟨_, _, h1, h2, h3, h4, h5, h6, h7⟩
  choose g r hg hr hs hsum hvar hlip hrem using hdec
  have hV0 : ∀ i, 0 ≤ ω i * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
      krVarTerm D vlo vhi w (P + 1 + i)) := fun i =>
    mul_nonneg (hω0 i) (mul_nonneg (mul_nonneg (mul_nonneg hcc.2.2.2.2.le (Real.sqrt_nonneg _))
      (by linarith)) (krVarTerm_nonneg hw0 _))
  obtain ⟨hGm, hRm, hGRs, hGR, hGvar, hGlip, hRsup⟩ :=
    kr_sum_decomposition (w := w)
      (q := fun i z => ω i * krDens (Icc 0 w) ν f β a' (P + 1 + i) b z)
      hg hr hs hsum hV0 hvar hlip hrem M
  -- the variation sum
  have hrate := hcc.2.2.1
  have hrate' : ε ≤ kBVClassRate D vlo vhi / 2 := by
    have := hε.trans H.krEps_le_kappa
    unfold kBVClassRate
    unfold krKappa at this
    linarith
  have hρε : 0 < kBVClassRate D vlo vhi - ε := by linarith
  have hVsum : ∑ i ∈ Finset.range M, ω i * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) *
      (1 + A) * krVarTerm D vlo vhi w (P + 1 + i)) ≤
      2 * Real.exp (3 * ε) * krCV D K L vlo vhi * (1 + A) * (Real.sqrt w / krFourthRoot P + 1) := by
    have hterm : ∀ i ∈ Finset.range M, ω i * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) *
        (1 + A) * krVarTerm D vlo vhi w (P + 1 + i)) ≤
        (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) * Real.exp (3 * ε)) *
          krVarTermGen (kBVClassRate D vlo vhi - ε) w (P + 1 + i) := fun i _ => by
      have := H.expw_varTerm hε0 (kBVClassRate D vlo vhi) (P + 1 + i)
      have e : ω i * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
          krVarTerm D vlo vhi w (P + 1 + i)) =
          (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A)) *
            (Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) *
              krVarTermGen (kBVClassRate D vlo vhi) w (P + 1 + i)) := by
        simp only [hω_def, krVarTerm]
        ring
      rw [e, mul_assoc _ (Real.exp (3 * ε))]
      exact mul_le_mul_of_nonneg_left this
        (mul_nonneg (mul_nonneg hcc.2.2.2.2.le (Real.sqrt_nonneg _)) (by linarith))
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hs := kr_sum_krVarTermGen_le hρε hw
      (by linarith [H.rate_le_one, one_le_pow₀ (n := 2) hw]) (by omega : 1 ≤ P) M
    have hq0 : 0 ≤ Real.sqrt w / krFourthRoot P :=
      div_nonneg (Real.sqrt_nonneg _) (krFourthRoot_nonneg _)
    have hinv : 2 * Real.sqrt 6 / (kBVClassRate D vlo vhi - ε) ≤
        4 * Real.sqrt 6 / kBVClassRate D vlo vhi := by
      rw [div_le_div_iff₀ hρε hrate]
      nlinarith [Real.sqrt_nonneg 6]
    have hs' : 16 * Real.sqrt w / krFourthRoot P + 2 * Real.sqrt 6 / (kBVClassRate D vlo vhi - ε) ≤
        2 * ((16 + 2 * Real.sqrt 6 / kBVClassRate D vlo vhi) * (Real.sqrt w / krFourthRoot P + 1)) := by
      have h2 : 0 ≤ 2 * Real.sqrt 6 / kBVClassRate D vlo vhi := by positivity
      have hcx := mul_nonneg h2 hq0
      have e1 : 16 * Real.sqrt w / krFourthRoot P = 16 * (Real.sqrt w / krFourthRoot P) := by ring
      have e2 : 2 * ((16 + 2 * Real.sqrt 6 / kBVClassRate D vlo vhi) *
          (Real.sqrt w / krFourthRoot P + 1)) =
          32 * (Real.sqrt w / krFourthRoot P) + 32 +
            2 * (2 * Real.sqrt 6 / kBVClassRate D vlo vhi * (Real.sqrt w / krFourthRoot P)) +
            2 * (2 * Real.sqrt 6 / kBVClassRate D vlo vhi) := by ring
      have e3 : 4 * Real.sqrt 6 / kBVClassRate D vlo vhi =
          2 * (2 * Real.sqrt 6 / kBVClassRate D vlo vhi) := by ring
      rw [e1, e2]
      rw [e3] at hinv
      linarith
    calc kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) * Real.exp (3 * ε) *
          ∑ i ∈ Finset.range M, krVarTermGen (kBVClassRate D vlo vhi - ε) w (P + 1 + i)
        ≤ kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) * Real.exp (3 * ε) *
          (2 * ((16 + 2 * Real.sqrt 6 / kBVClassRate D vlo vhi) *
            (Real.sqrt w / krFourthRoot P + 1))) :=
          mul_le_mul_of_nonneg_left (hs.trans hs')
            (mul_nonneg (mul_nonneg (mul_nonneg hcc.2.2.2.2.le (Real.sqrt_nonneg _))
              (by linarith)) (Real.exp_pos _).le)
      _ = _ := by unfold krCV; ring
  -- the remainder sum
  set ρ' := kBVClassRho D vlo vhi * Real.exp (3 * ε / w ^ 2) with hρ'_def
  have hρ'0 : 0 ≤ ρ' := mul_nonneg hcc.1 (Real.exp_pos _).le
  have hρ'le := H.rho_expw_le hε0 hε
  have hρ'1 : ρ' < 1 := by linarith [hcc.2.1]
  have hRsum : ∑ i ∈ Finset.range M, ω i * (Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
      Real.sqrt (3 * krC₂ D K L) * (1 + A) * kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1))) ≤
      2 * Real.exp (5 * ε) * krCR D K L vlo vhi * (1 + A) *
        ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1) := by
    set Cr := Real.sqrt (2 * D) * kBVClassRemConst D vlo vhi * Real.sqrt (3 * krC₂ D K L) * (1 + A)
      with hCr_def
    have hCr0 : 0 ≤ Cr :=
      mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hcc.2.2.2.1.le)
        (Real.sqrt_nonneg _)) (by linarith)
    have hterm : ∀ i ∈ Finset.range M, ω i * (Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
        Real.sqrt (3 * krC₂ D K L) * (1 + A) * kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1))) ≤
        (Cr * Real.exp (5 * ε)) * ρ' ^ ((P + 1 + i) / 3 - 1) := fun i _ => by
      have := kr_expw_rho (ε := ε) (w := w) hε0 hw hcc.1 (P + 1 + i)
      have e : ω i * (Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
          Real.sqrt (3 * krC₂ D K L) * (1 + A) * kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1))) =
          Cr * (Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) *
            kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1)) := by
        simp only [hω_def, hCr_def]
        ring
      rw [e]
      refine (mul_le_mul_of_nonneg_left this hCr0).trans (le_of_eq ?_)
      rw [hρ'_def]
      ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hsum := kr_sum_rho_pow_le hρ'0 hρ'1 (by omega : 3 ≤ P) M
    have hpow : ρ' ^ (P / 3 - 1) ≤ ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1) :=
      pow_le_pow_left₀ hρ'0 hρ'le _
    have hhalf : 0 < (1 - kBVClassRho D vlo vhi) / 2 := by linarith [hcc.2.1]
    have hinv : 1 / (1 - ρ') ≤ 1 / ((1 - kBVClassRho D vlo vhi) / 2) :=
      one_div_le_one_div_of_le hhalf (by linarith)
    have hgeom : 3 * ρ' ^ (P / 3 - 1) / (1 - ρ') ≤
        3 * ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1) / ((1 - kBVClassRho D vlo vhi) / 2) := by
      have hρ1' : 0 ≤ (1 + kBVClassRho D vlo vhi) / 2 := by linarith [hcc.1]
      exact div_le_div₀ (mul_nonneg (by norm_num) (pow_nonneg hρ1' _)) (by gcongr) hhalf
        (by linarith)
    calc Cr * Real.exp (5 * ε) * ∑ i ∈ Finset.range M, ρ' ^ ((P + 1 + i) / 3 - 1)
        ≤ Cr * Real.exp (5 * ε) *
          (3 * ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1) / ((1 - kBVClassRho D vlo vhi) / 2)) :=
          mul_le_mul_of_nonneg_left (hsum.trans hgeom) (mul_nonneg hCr0 (Real.exp_pos _).le)
      _ = _ := by
          simp only [hCr_def]
          unfold krCR
          field_simp
  refine ⟨_, _, hGm, hRm, hGRs, hGR, hGvar.trans (ENNReal.ofReal_le_ofReal hVsum), ?_,
    fun x => (hRsup x).trans hRsum, ?_⟩
  · intro x hx y hy
    refine (hGlip x hx y hy).trans ?_
    have e : ∑ i ∈ Finset.range M, ω i * (2 * D * (kBVClassVarConst D vlo vhi *
        Real.sqrt (krC₂ D K L) * (1 + A) * krVarTerm D vlo vhi w (P + 1 + i))) =
        2 * D * ∑ i ∈ Finset.range M, ω i * (kBVClassVarConst D vlo vhi *
          Real.sqrt (krC₂ D K L) * (1 + A) * krVarTerm D vlo vhi w (P + 1 + i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hVsum (by linarith)) (abs_nonneg _)
  · -- the opposite-endpoint trace
    intro b' hb' hbb hAw
    have hGb : (∑ i ∈ Finset.range M, g i b') =
        ((∑ i ∈ Finset.range M, ω i * krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' : ℝ) : ℂ) -
          ∑ i ∈ Finset.range M, r i b' := by
      rw [hGR b']; ring
    have hpin : ∑ i ∈ Finset.range M, ω i * krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' ≤
        Real.exp (3 * ε) * ((krCP D θ K L vlo vhi + 12 * krC₂ D K L / krKappa D vlo vhi) *
          (1 + A) ^ 2 / Real.sqrt w) := by
      refine le_trans ?_ (sum_expw_krDens_bdry_pin_le ν H hAw hb hb' hbb hε0 hεκ (P + M))
      rw [Finset.sum_range_add]
      have e : ∑ i ∈ Finset.range M, ω i * krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' =
          ∑ i ∈ Finset.range M, Real.exp (ε * ((P + i + 1 : ℕ) : ℝ) / w ^ 2) *
            krDens (Icc 0 w) ν f β a' (P + i + 1) b b' :=
        Finset.sum_congr rfl fun i _ => by
          simp only [hω_def]
          rw [show P + 1 + i = P + i + 1 by omega]
      rw [e]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun n _ =>
        mul_nonneg (Real.exp_pos _).le (krDens_nonneg ν H.hf0 (n + 1) b b'))
    have hpin0 : 0 ≤ ∑ i ∈ Finset.range M, ω i * krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hω0 i) (krDens_nonneg ν H.hf0 _ _ _)
    calc ‖∑ i ∈ Finset.range M, g i b'‖
        ≤ ‖((∑ i ∈ Finset.range M, ω i * krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' : ℝ) : ℂ)‖ +
          ‖∑ i ∈ Finset.range M, r i b'‖ := by rw [hGb]; exact norm_sub_le _ _
      _ ≤ _ := by
          refine add_le_add ?_ ((hRsup b').trans hRsum)
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpin0]
          exact hpin

end

end PGM
