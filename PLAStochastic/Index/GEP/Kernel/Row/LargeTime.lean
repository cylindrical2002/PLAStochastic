import PLAStochastic.Index.GEP.Kernel.Row.MediumTime

/-!
# WP4 kernel rows: large-time bounds from the killed `L²` gap

Source: `influence-lipschitz.md` §3: "for `n ≥ w²`, first run a fixed proportion of `w²` steps,
then use the killed-kernel `L²` spectral gap".  With `T ≈ w²` (any `T` with `1 ≤ T ≤ w² ≤ 2T`)
and `λ = 1 - κ/w²` the class-uniform killed `L²` contraction factor,

* `krDens_add_krRow`: the pointwise three-block identity
  `q_{m+j+k}(y₀, z) = ∫ q_m(y₀, y) (P^j q_k(·, z))(y) dy` (`m, k ≥ 1`, `j ≥ 0`);
* `sq_krDens_add_krRow_le`: Cauchy–Schwarz + gap:
  `q_{m+j+k}(y₀,z)² ≤ ‖q_m(y₀,·)‖₂² λ^j ‖q_k(·,z)‖₂²`;
* `krSurv_bdry_large`: `s_{T+j}(b) ≤ √(3 C₂) (1 + A) (√λ)^j / w`;
* `krDens_bdry_row_large`: `q_{T+j+T}(b, z) ≤ C₄ (1 + A) (√λ)^j / w²`;
* `krDens_bdry_pin_large`: `q_{T+j+T}(b, b') ≤ 3 C₂ (1 + A)² (√λ)^j / w³` for boundary `b, b'`.

The exponential rate is the actual killed gap `krKappa = killGapConst (killCnu D vlo vhi) (1/2)`
from `GEPKillGap`, class-uniform and chosen before the law.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {J : Set ℝ} {β a : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}

/-! ## The gap constants -/

/-- The killed `L²` gap constant `κ` of the class (slope window `|a| ≥ 1/2`). -/
def krKappa (D vlo vhi : ℝ) : ℝ := killGapConst (killCnu D vlo vhi) (1 / 2)

/-- The killed `L²` contraction factor `λ = 1 - κ / w²`. -/
def krLam (D vlo vhi w : ℝ) : ℝ := 1 - krKappa D vlo vhi / w ^ 2

theorem krKappa_pos {vlo vhi : ℝ} (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    0 < krKappa D vlo vhi :=
  killGapConst_pos (killCnu_pos hD hvlo hvhi) (by norm_num)

theorem krKappa_le_one {θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) :
    krKappa D vlo vhi ≤ 1 := by
  have hcle : killCnu D vlo vhi ≤ 1 := by
    have h := kill_regLaw_charFun_gap hD hθ hvlo hν (a := 1) (by norm_num) 1
    have h0 : 0 ≤ ‖charFun (ν : Measure ℝ) (1 * 1)‖ ^ 2 := sq_nonneg _
    simp only [one_pow, min_self, mul_one] at h h0
    linarith
  unfold krKappa killGapConst
  have hmin : min (Real.pi ^ 2 * (1 / 2) ^ 2 / 4) 1 ≤ 1 := min_le_right _ _
  have hmin0 : 0 ≤ min (Real.pi ^ 2 * (1 / 2) ^ 2 / 4) 1 := le_min (by positivity) zero_le_one
  have hc0 : 0 ≤ killCnu D vlo vhi := (killCnu_pos hD hvlo hvhi).le
  calc killCnu D vlo vhi * min (Real.pi ^ 2 * (1 / 2) ^ 2 / 4) 1 / 2 ≤ 1 * 1 / 2 := by gcongr
    _ ≤ 1 := by norm_num

theorem krLam_nonneg {θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) {w : ℝ}
    (hw : 1 ≤ w) : 0 ≤ krLam D vlo vhi w := by
  unfold krLam
  have h1 := krKappa_le_one hD hθ hvlo hvhi hν
  have h2 : krKappa D vlo vhi / w ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact h1.trans (by nlinarith)
  linarith

theorem krLam_lt_one {vlo vhi : ℝ} (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {w : ℝ}
    (hw : 1 ≤ w) : krLam D vlo vhi w < 1 := by
  unfold krLam
  have := krKappa_pos hD hvlo hvhi
  have : 0 < krKappa D vlo vhi / w ^ 2 := by positivity
  linarith

/-- `1 - √λ ≥ κ / (2 w²)`, so geometric sums in `√λ` cost at most `2 w² / κ`. -/
theorem one_sub_sqrt_krLam_ge {θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) {w : ℝ}
    (hw : 1 ≤ w) : krKappa D vlo vhi / (2 * w ^ 2) ≤ 1 - Real.sqrt (krLam D vlo vhi w) := by
  have hl0 := krLam_nonneg hD hθ hvlo hvhi hν hw
  have hl1 := (krLam_lt_one hD hvlo hvhi hw).le
  have hx : krLam D vlo vhi w = 1 - krKappa D vlo vhi / w ^ 2 := rfl
  set x := krKappa D vlo vhi / w ^ 2 with hxdef
  have hx0 : 0 ≤ x := by positivity [krKappa_pos hD hvlo hvhi]
  have hx1 : x ≤ 1 := by rw [hx] at hl0; linarith
  have hs : Real.sqrt (krLam D vlo vhi w) ≤ 1 - x / 2 := by
    rw [Real.sqrt_le_left (by linarith), hx]
    nlinarith
  have e : krKappa D vlo vhi / (2 * w ^ 2) = x / 2 := by rw [hxdef]; ring
  rw [e]
  linarith

/-! ## Squares and square roots -/

theorem kr_le_of_sq_le {x y : ℝ} (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y :=
  (abs_le_of_sq_le_sq' h hy).2

theorem kr_sqrt_pow_sq {l : ℝ} (hl : 0 ≤ l) (j : ℕ) : (Real.sqrt l ^ j) ^ 2 = l ^ j := by
  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hl]

namespace KrBand

variable {ν} {θ vlo vhi K L w A a' : ℝ}

theorem ha₁' (H : KrBand D θ vlo vhi K L ν f w A a β a') : 1 / 2 ≤ |a'| := by
  rw [H.habs]; exact H.ha₁

theorem lam_nonneg (H : KrBand D θ vlo vhi K L ν f w A a β a') : 0 ≤ krLam D vlo vhi w :=
  krLam_nonneg H.hD H.hθ H.hvlo H.hvhi H.hν H.hw

theorem lam_lt_one (H : KrBand D θ vlo vhi K L ν f w A a β a') : krLam D vlo vhi w < 1 :=
  krLam_lt_one H.hD H.hvlo H.hvhi H.hw

theorem kappa_pos (H : KrBand D θ vlo vhi K L ν f w A a β a') : 0 < krKappa D vlo vhi :=
  krKappa_pos H.hD H.hvlo H.hvhi

/-- The killed `L²` contraction of the band row, in the `Icc 0 w` form. -/
theorem gap_pow (H : KrBand D θ vlo vhi K L ν f w A a β a') {φ : ℝ → ℝ} (hφ : Measurable φ)
    {M : ℝ} (hM : ∀ y, |φ y| ≤ M) (n : ℕ) :
    ∫ y, krRow (Icc 0 w) (ν : Measure ℝ) β a' n φ y ^ 2 ≤
      krLam D vlo vhi w ^ n * ∫ y, (Icc 0 w).indicator φ y ^ 2 := by
  have h := integral_krRow_sq_le_gap_pow H.hD H.hθ H.hvlo H.hvhi H.hν (α := 0) (β := β) H.hw
    H.ha₁' hφ hM n
  rw [zero_add] at h
  exact h

end KrBand

/-! ## The three-block identity with a row in the middle -/

/-- `q_{m+1+j+(k+1)}(y₀, z) = ∫ q_{m+1}(y₀, y) · (P^j q_{k+1}(·, z))(y) dy`, pointwise. -/
theorem krDens_add_krRow (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) (ha : a ≠ 0)
    (m j k : ℕ) (y₀ z : ℝ) :
    krDens J ν f β a (m + 1 + j + (k + 1)) y₀ z =
      ∫ y, krDens J ν f β a (m + 1) y₀ y *
        krRow J (ν : Measure ℝ) β a j (fun y' => krDens J ν f β a (k + 1) y' z) y := by
  cases j with
  | zero =>
    rw [Nat.add_zero, krDens_add ν hJ hJfin hf hf0 hfD hν ha m k y₀ z]
    congr 1
    funext y
    rw [krRow_zero]
    by_cases hy : y ∈ J
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy, krDens_eq_zero_of_left_notMem ν hy]
  | succ j =>
    have e : m + 1 + (j + 1) + (k + 1) = m + 1 + (j + k + 1 + 1) := by omega
    rw [e, krDens_add ν hJ hJfin hf hf0 hfD hν ha m (j + k + 1) y₀ z]
    congr 1
    funext y
    rw [show j + k + 1 + 1 = j + 1 + (k + 1) by omega,
      krDens_add ν hJ hJfin hf hf0 hfD hν ha j k y z,
      krRow_succ_eq_integral_krDens ν hJ hJfin hf hf0 hfD hν ha j
        (measurable_krDens_left ν hJ hf β a (k + 1) z) (M := D / |a|)
        (fun y' => abs_krDens_le ν hf0 hfD (k + 1) y' z) y]

/-- **Cauchy–Schwarz + gap**: `q_{m+1+j+(k+1)}(y₀,z)² ≤ ‖q_{m+1}(y₀,·)‖₂² · λ^j · ‖q_{k+1}(·,z)‖₂²`. -/
theorem sq_krDens_add_krRow_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (m j k : ℕ) (y₀ z : ℝ) :
    krDens (Icc 0 w) ν f β a' (m + 1 + j + (k + 1)) y₀ z ^ 2 ≤
      (∫ y, krDens (Icc 0 w) ν f β a' (m + 1) y₀ y ^ 2) *
        (krLam D vlo vhi w ^ j * ∫ y, krDens (Icc 0 w) ν f β a' (k + 1) y z ^ 2) := by
  have hφ : Measurable (fun y' => krDens (Icc 0 w) ν f β a' (k + 1) y' z) :=
    measurable_krDens_left ν H.hJ H.hf β a' (k + 1) z
  have hM : ∀ y, |krDens (Icc 0 w) ν f β a' (k + 1) y z| ≤ D / |a'| :=
    fun y => abs_krDens_le ν H.hf0 H.hfD (k + 1) y z
  have hφ0 : ∀ y, 0 ≤ krDens (Icc 0 w) ν f β a' (k + 1) y z :=
    fun y => krDens_nonneg ν H.hf0 _ _ _
  rw [krDens_add_krRow ν H.hJ H.hJfin H.hf H.hf0 H.hfD H.hνf H.ha' m j k y₀ z]
  have hF : Measurable (fun y => krDens (Icc 0 w) ν f β a' (m + 1) y₀ y) :=
    measurable_krDens_right ν H.hJ H.hf β a' (m + 1) y₀
  have hG : Measurable (krRow (Icc 0 w) (ν : Measure ℝ) β a' j
      (fun y' => krDens (Icc 0 w) ν f β a' (k + 1) y' z)) :=
    measurable_krRow H.hJ ν β a' j hφ hM
  have hF2 : Integrable (fun y => krDens (Icc 0 w) ν f β a' (m + 1) y₀ y ^ 2) :=
    kr_integrable_sq_of_bdd H.hJ H.hJfin hF
      (fun _ hy => krDens_eq_zero_of_right_notMem ν hy _ _) (abs_krDens_le ν H.hf0 H.hfD _ _)
  have hG2 : Integrable (fun y => krRow (Icc 0 w) (ν : Measure ℝ) β a' j
      (fun y' => krDens (Icc 0 w) ν f β a' (k + 1) y' z) y ^ 2) :=
    kr_integrable_sq_of_bdd H.hJ H.hJfin hG (fun _ hy => krRow_eq_zero_of_notMem hy)
      (abs_krRow_le H.hJ ν β a' j hφ hM)
  refine (kr_cauchy_schwarz hF hG (fun _ => krDens_nonneg ν H.hf0 _ _ _)
    (fun y => krRow_nonneg H.hJ ν β a' j hφ hM hφ0 y) hF2 hG2).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (integral_nonneg fun _ => sq_nonneg _)
  have h := H.gap_pow hφ hM j
  have e : (Icc 0 w).indicator (fun y' => krDens (Icc 0 w) ν f β a' (k + 1) y' z) =
      fun y' => krDens (Icc 0 w) ν f β a' (k + 1) y' z := by
    refine indicator_eq_self.2 fun y hy => ?_
    by_contra hyJ
    exact hy (krDens_eq_zero_of_left_notMem ν hyJ _ _)
  rw [e] at h
  exact h

/-! ## The `T ≈ w²` block -/

/-- `T √T ≥ w³ / 3` when `w² ≤ 2 T` and `w ≥ 1`. -/
theorem kr_T_cube {w : ℝ} (hw : 1 ≤ w) {T : ℕ} (hwT : w ^ 2 ≤ 2 * T) :
    w ^ 3 / 3 ≤ (T : ℝ) * Real.sqrt T := by
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw
  have hs : 2 * w / 3 ≤ Real.sqrt T := by
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  calc w ^ 3 / 3 = (w ^ 2 / 2) * (2 * w / 3) := by ring
    _ ≤ (T : ℝ) * Real.sqrt T := mul_le_mul (by linarith) hs (by positivity) hT0

/-- Boundary row `L²` norm at time `T`: `∫ q_T(b, y)² dy ≤ 3 C₂ (1 + A)² / w³`. -/
theorem integral_sq_krDens_bdry_T {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {T : ℕ} (hT : 1 ≤ T) (hTw : (T : ℝ) ≤ w ^ 2) (hwT : w ^ 2 ≤ 2 * T) :
    ∫ y, krDens (Icc 0 w) ν f β a' T b y ^ 2 ≤ 3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3 := by
  refine (integral_sq_krDens_bdry_medium ν H hb hT hTw).trans ?_
  have hc := kr_T_cube H.hw hwT
  have hw0 := H.hw0
  have hC := krC₂_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  have hA := H.hA
  calc krC₂ D K L * (1 + A) ^ 2 / (T * Real.sqrt T)
      ≤ krC₂ D K L * (1 + A) ^ 2 / (w ^ 3 / 3) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hc
    _ = 3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3 := by field_simp

/-- Sup of the time-`T` kernel from any starting point: `q_T(y, z) ≤ 4 (L + D) / w`. -/
theorem krDens_T_sup {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {T : ℕ} (hT : 1 ≤ T)
    (hwT : w ^ 2 ≤ 2 * T) (y z : ℝ) :
    krDens (Icc 0 w) ν f β a' T y z ≤ 4 * (L + D) / w := by
  have hw0 := H.hw0
  have hw := H.hw
  have hD0 := H.hD0
  have hL0 := H.hL0
  by_cases hT2 : T ≤ 2
  · refine (H.krDens_le_two_D T y z).trans ?_
    have hT2' : (T : ℝ) ≤ 2 := by exact_mod_cast hT2
    have hw2 : w ≤ 2 := by nlinarith
    rw [le_div_iff₀ hw0]
    nlinarith
  · have hT3 : 3 ≤ T := by omega
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
    have hk2 : 2 ≤ k := by omega
    refine (H.krDens_le_free_two hk2 y z).trans ?_
    have hk' : w ^ 2 / 4 ≤ (k : ℝ) := by
      have : ((k + 1 : ℕ) : ℝ) = k + 1 := by push_cast; ring
      rw [this] at hwT
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      nlinarith
    have hs : w / 2 ≤ Real.sqrt k := by
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith
    have hk0 : 0 < Real.sqrt k := lt_of_lt_of_le (by positivity) hs
    rw [div_le_div_iff₀ hk0 hw0]
    nlinarith

/-! ## Large-time boundary survival -/

/-- The mass of the band indicator: `∫ 1_{[0,w]}(y)² dy = w`. -/
theorem kr_integral_band_indicator_sq {w : ℝ} (hw : 0 ≤ w) :
    ∫ y, (Icc (0 : ℝ) w).indicator (fun _ => (1 : ℝ)) y ^ 2 = w := by
  have e : ∀ y, (Icc (0 : ℝ) w).indicator (fun _ => (1 : ℝ)) y ^ 2 =
      (Icc (0 : ℝ) w).indicator (fun _ => (1 : ℝ)) y := by
    intro y
    by_cases hy : y ∈ Icc (0 : ℝ) w <;> simp [hy]
  simp_rw [e]
  rw [integral_indicator_const (1 : ℝ) measurableSet_Icc, smul_eq_mul, mul_one,
    Real.volume_real_Icc_of_le hw, sub_zero]

/-- Large-time constant `C₃ = √(3 C₂)`. -/
def krC₃ (D K L : ℝ) : ℝ := Real.sqrt (3 * krC₂ D K L)

/-- **Large-time boundary survival**: `s_{T+j}(b)² ≤ 3 C₂ (1 + A)² λ^j / w²`. -/
theorem sq_krSurv_bdry_large {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {T : ℕ} (hT : 1 ≤ T) (hTw : (T : ℝ) ≤ w ^ 2) (hwT : w ^ 2 ≤ 2 * T) (j : ℕ) :
    krSurv (Icc 0 w) (ν : Measure ℝ) β a' (T + j) b ^ 2 ≤
      3 * krC₂ D K L * (1 + A) ^ 2 * krLam D vlo vhi w ^ j / w ^ 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
  have hw0 := H.hw0
  have hA := H.hA
  have hC := krC₂_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  have hφ : Measurable (krSurv (Icc 0 w) (ν : Measure ℝ) β a' j) := measurable_krSurv H.hJ ν β a' j
  have hM : ∀ y, |krSurv (Icc 0 w) (ν : Measure ℝ) β a' j y| ≤ 1 := fun y =>
    abs_krRow_le H.hJ ν β a' j measurable_const (M := 1) (fun _ => by simp) y
  have e : krSurv (Icc 0 w) (ν : Measure ℝ) β a' (t + 1 + j) b =
      ∫ y, krDens (Icc 0 w) ν f β a' (t + 1) b y * krSurv (Icc 0 w) (ν : Measure ℝ) β a' j y := by
    show krRow (Icc 0 w) (ν : Measure ℝ) β a' (t + 1 + j) (fun _ => (1 : ℝ)) b = _
    rw [krRow_add]
    exact krRow_succ_eq_integral_krDens ν H.hJ H.hJfin H.hf H.hf0 H.hfD H.hνf H.ha' t hφ hM b
  rw [e]
  have hF : Measurable (fun y => krDens (Icc 0 w) ν f β a' (t + 1) b y) :=
    measurable_krDens_right ν H.hJ H.hf β a' (t + 1) b
  have hF2 : Integrable (fun y => krDens (Icc 0 w) ν f β a' (t + 1) b y ^ 2) :=
    kr_integrable_sq_of_bdd H.hJ H.hJfin hF
      (fun _ hy => krDens_eq_zero_of_right_notMem ν hy _ _) (abs_krDens_le ν H.hf0 H.hfD _ _)
  have hG2 : Integrable (fun y => krSurv (Icc 0 w) (ν : Measure ℝ) β a' j y ^ 2) :=
    kr_integrable_sq_of_bdd H.hJ H.hJfin hφ (fun _ hy => krRow_eq_zero_of_notMem hy) hM
  refine (kr_cauchy_schwarz hF hφ (fun _ => krDens_nonneg ν H.hf0 _ _ _)
    (fun y => krSurv_nonneg H.hJ ν β a' j y) hF2 hG2).trans ?_
  have h1 := integral_sq_krDens_bdry_T ν H hb hT hTw hwT
  have h2 : ∫ y, krSurv (Icc 0 w) (ν : Measure ℝ) β a' j y ^ 2 ≤ krLam D vlo vhi w ^ j * w := by
    have := H.gap_pow (φ := fun _ => (1 : ℝ)) measurable_const (M := 1) (fun _ => by simp) j
    rw [kr_integral_band_indicator_sq hw0.le] at this
    exact this
  have hl := H.lam_nonneg
  calc (∫ y, krDens (Icc 0 w) ν f β a' (t + 1) b y ^ 2) *
        ∫ y, krSurv (Icc 0 w) (ν : Measure ℝ) β a' j y ^ 2
      ≤ (3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3) * (krLam D vlo vhi w ^ j * w) :=
        mul_le_mul h1 h2 (integral_nonneg fun _ => sq_nonneg _) (by positivity)
    _ = 3 * krC₂ D K L * (1 + A) ^ 2 * krLam D vlo vhi w ^ j / w ^ 2 := by
        field_simp

/-- **Large-time boundary survival**: `s_{T+j}(b) ≤ C₃ (1 + A) (√λ)^j / w`. -/
theorem krSurv_bdry_large {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {T : ℕ} (hT : 1 ≤ T) (hTw : (T : ℝ) ≤ w ^ 2) (hwT : w ^ 2 ≤ 2 * T) (j : ℕ) :
    krSurv (Icc 0 w) (ν : Measure ℝ) β a' (T + j) b ≤
      krC₃ D K L * (1 + A) * Real.sqrt (krLam D vlo vhi w) ^ j / w := by
  have hw0 := H.hw0
  have hA := H.hA
  have hC := krC₂_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  refine kr_le_of_sq_le (by unfold krC₃; positivity) ?_
  refine (sq_krSurv_bdry_large ν H hb hT hTw hwT j).trans (le_of_eq ?_)
  unfold krC₃
  rw [div_pow, mul_pow, mul_pow, kr_sqrt_pow_sq H.lam_nonneg, Real.sq_sqrt (by positivity)]

/-! ## Large-time boundary row sup -/

/-- Large-time row constant `C₄ = √(12 C₂ (L + D))`. -/
def krC₄ (D K L : ℝ) : ℝ := Real.sqrt (12 * krC₂ D K L * (L + D))

/-- **Large-time boundary row**: `q_{T+j+T}(b, z)² ≤ 12 C₂ (L + D) (1 + A)² λ^j / w⁴`. -/
theorem sq_krDens_bdry_row_large {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {T : ℕ} (hT : 1 ≤ T) (hTw : (T : ℝ) ≤ w ^ 2) (hwT : w ^ 2 ≤ 2 * T) (j : ℕ) (z : ℝ) :
    krDens (Icc 0 w) ν f β a' (T + j + T) b z ^ 2 ≤
      12 * krC₂ D K L * (L + D) * (1 + A) ^ 2 * krLam D vlo vhi w ^ j / w ^ 4 := by
  obtain ⟨t, rfl⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
  have hw0 := H.hw0
  have hA := H.hA
  have hC := krC₂_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  have hLD : 0 ≤ L + D := by linarith [H.hL0, H.hD0]
  refine (sq_krDens_add_krRow_le ν H t j t b z).trans ?_
  have h1 := integral_sq_krDens_bdry_T ν H hb hT hTw hwT
  have h3 : ∫ y, krDens (Icc 0 w) ν f β a' (t + 1) y z ^ 2 ≤ 4 * (L + D) / w := by
    have hint : Integrable (fun y => krDens (Icc 0 w) ν f β a' (t + 1) y z) :=
      kr_integrable_krDens_left ν H.hJ H.hJfin H.hf H.hf0 H.hfD (t + 1) z
    have hint2 : Integrable (fun y => krDens (Icc 0 w) ν f β a' (t + 1) y z ^ 2) :=
      kr_integrable_sq_of_bdd H.hJ H.hJfin (measurable_krDens_left ν H.hJ H.hf β a' (t + 1) z)
        (fun _ hy => krDens_eq_zero_of_left_notMem ν hy _ _)
        (fun y => abs_krDens_le ν H.hf0 H.hfD (t + 1) y z)
    calc ∫ y, krDens (Icc 0 w) ν f β a' (t + 1) y z ^ 2
        ≤ ∫ y, 4 * (L + D) / w * krDens (Icc 0 w) ν f β a' (t + 1) y z := by
          refine integral_mono hint2 (hint.const_mul _) fun y => ?_
          rw [sq]
          exact mul_le_mul_of_nonneg_right (krDens_T_sup ν H hT hwT y z)
            (krDens_nonneg ν H.hf0 _ _ _)
      _ = 4 * (L + D) / w * krSurv (Icc 0 w) (ν : Measure ℝ) (-β) (-a') (t + 1) z := by
          rw [integral_const_mul, integral_krDens_left ν H.hJ H.hJfin H.hf H.hf0 H.hfD H.hνf H.ha']
      _ ≤ 4 * (L + D) / w * 1 :=
          mul_le_mul_of_nonneg_left (krSurv_le_one H.hJ ν _ _ _ _) (by positivity)
      _ = 4 * (L + D) / w := mul_one _
  have hl := H.lam_nonneg
  calc (∫ y, krDens (Icc 0 w) ν f β a' (t + 1) b y ^ 2) *
        (krLam D vlo vhi w ^ j * ∫ y, krDens (Icc 0 w) ν f β a' (t + 1) y z ^ 2)
      ≤ (3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3) * (krLam D vlo vhi w ^ j * (4 * (L + D) / w)) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_left h3 (by positivity))
          (mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)) (by positivity)
    _ = 12 * krC₂ D K L * (L + D) * (1 + A) ^ 2 * krLam D vlo vhi w ^ j / w ^ 4 := by
        field_simp
        ring

/-- **Large-time boundary row**: `q_{T+j+T}(b, z) ≤ C₄ (1 + A) (√λ)^j / w²`. -/
theorem krDens_bdry_row_large {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {T : ℕ} (hT : 1 ≤ T) (hTw : (T : ℝ) ≤ w ^ 2) (hwT : w ^ 2 ≤ 2 * T) (j : ℕ) (z : ℝ) :
    krDens (Icc 0 w) ν f β a' (T + j + T) b z ≤
      krC₄ D K L * (1 + A) * Real.sqrt (krLam D vlo vhi w) ^ j / w ^ 2 := by
  have hw0 := H.hw0
  have hA := H.hA
  have hC := krC₂_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  have hLD : 0 ≤ L + D := by linarith [H.hL0, H.hD0]
  refine kr_le_of_sq_le (by unfold krC₄; positivity) ?_
  refine (sq_krDens_bdry_row_large ν H hb hT hTw hwT j z).trans (le_of_eq ?_)
  unfold krC₄
  rw [div_pow, mul_pow, mul_pow, kr_sqrt_pow_sq H.lam_nonneg, Real.sq_sqrt (by positivity)]
  ring

/-! ## Large-time boundary-to-boundary pin -/

/-- **Large-time pin**: `q_{T+j+T}(b, b')² ≤ 9 C₂² (1 + A)⁴ λ^j / w⁶` for boundary `b, b'`. -/
theorem sq_krDens_bdry_pin_large {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b b' : ℝ} (hb : b = 0 ∨ b = w)
    (hb' : b' = 0 ∨ b' = w)
    {T : ℕ} (hT : 1 ≤ T) (hTw : (T : ℝ) ≤ w ^ 2) (hwT : w ^ 2 ≤ 2 * T) (j : ℕ) :
    krDens (Icc 0 w) ν f β a' (T + j + T) b b' ^ 2 ≤
      (3 * krC₂ D K L * (1 + A) ^ 2) ^ 2 * krLam D vlo vhi w ^ j / w ^ 6 := by
  obtain ⟨t, rfl⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
  have hw0 := H.hw0
  have hA := H.hA
  have hC := krC₂_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  refine (sq_krDens_add_krRow_le ν H t j t b b').trans ?_
  have h1 := integral_sq_krDens_bdry_T ν H hb hT hTw hwT
  have h3 : ∫ y, krDens (Icc 0 w) ν f β a' (t + 1) y b' ^ 2 ≤
      3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3 := by
    have := integral_sq_krDens_bdry_T ν H.rev hb' hT hTw hwT
    simp_rw [← krDens_symm ν H.hJ H.hJfin H.hf H.hf0 H.hfD H.hνf H.ha' t _ b'] at this
    exact this
  have hl := H.lam_nonneg
  calc (∫ y, krDens (Icc 0 w) ν f β a' (t + 1) b y ^ 2) *
        (krLam D vlo vhi w ^ j * ∫ y, krDens (Icc 0 w) ν f β a' (t + 1) y b' ^ 2)
      ≤ (3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3) *
          (krLam D vlo vhi w ^ j * (3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3)) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_left h3 (by positivity))
          (mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)) (by positivity)
    _ = (3 * krC₂ D K L * (1 + A) ^ 2) ^ 2 * krLam D vlo vhi w ^ j / w ^ 6 := by
        field_simp

/-- **Large-time pin**: `q_{T+j+T}(b, b') ≤ 3 C₂ (1 + A)² (√λ)^j / w³` for boundary `b, b'`. -/
theorem krDens_bdry_pin_large {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b b' : ℝ} (hb : b = 0 ∨ b = w)
    (hb' : b' = 0 ∨ b' = w)
    {T : ℕ} (hT : 1 ≤ T) (hTw : (T : ℝ) ≤ w ^ 2) (hwT : w ^ 2 ≤ 2 * T) (j : ℕ) :
    krDens (Icc 0 w) ν f β a' (T + j + T) b b' ≤
      3 * krC₂ D K L * (1 + A) ^ 2 * Real.sqrt (krLam D vlo vhi w) ^ j / w ^ 3 := by
  have hw0 := H.hw0
  have hA := H.hA
  have hC := krC₂_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  refine kr_le_of_sq_le (by positivity) ?_
  refine (sq_krDens_bdry_pin_large ν H hb hb' hT hTw hwT j).trans (le_of_eq ?_)
  simp only [div_pow, mul_pow, kr_sqrt_pow_sq H.lam_nonneg]
  ring

end

end PGM
