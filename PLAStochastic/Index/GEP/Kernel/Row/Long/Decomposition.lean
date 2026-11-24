import PLAStochastic.Index.GEP.Kernel.Row.Long.KilledBV
import PLAStochastic.Index.GEP.Kernel.BV.PointwiseDecomposition

/-!
# WP4 kernel rows: the (long) display — pointwise decomposition and summation

Source: `influence-lipschitz.md` §3, (long): for long rows `n ≥ n₀`,
`∑_{n ≥ n₀} q_n(b, ·) = g + r` with `V(g) + Lip(g|_{[0,w]}) ≤ K (1+A)^p w^{1/4}` and
`‖r‖_∞ ≤ K (1+A)^p e^{-c w}`; at the opposite endpoint the trace of `g` is controlled by
(pin) and the uniform remainder.

This file uses the pointwise decomposition `kBV_regLaw_pointwise_decomposition` of the
`GEPKernelBV*` modules (developed separately, compiled) for the actual kernel `krDens`:

* `krDens_pointwise_decomposition`: `q_{m+1+(k+1)}(b, ·) = g + r` pointwise, `g` of variation
  `≤ kBVVarBudget … k ‖q_{m+1}(b,·)‖₂`, Lipschitz on `[0, w]` with constant
  `2D · kBVVarBudget …`, and `‖r‖_∞ ≤ √(2D) · kBVRemBudget … k ‖q_{m+1}(b,·)‖₂`;
* `krDens_row_decomposition`: for a boundary row `q_n(b, ·)`, `n ≥ 13`, with the split
  `m + 1 = min(⌊n/3⌋, T)`, `T = ⌈w²/2⌉`: explicit budgets
  `V ≤ Cᵛ (1+A) (4√w/(n n^{1/4}) + [n ≥ 3T] e^{-ρ(n-T-1)/w²}/w²)`,
  `‖r‖_∞ ≤ Cʳ (1+A) √(1-c)^{⌊n/3⌋-1}`;
* `krLong_decomposition`: the sum over `n ∈ [P+1, P+1+M)` of boundary rows, `P ≥ 12`:
  `∑ q_n(b, ·) = G + R` with `V(G) ≤ krCV (1+A) (√w / P^{1/4} + 1)`,
  `Lip(G|_{[0,w]}) ≤ 2D · krCV (1+A) (√w / P^{1/4} + 1)`,
  `‖R‖_∞ ≤ krCR (1+A) √(1-c)^{⌊P/3⌋-1}`, and the opposite-endpoint trace
  `‖G(b')‖ ≤ ∑ q_n(b, b') + ‖R‖_∞ ≤ krCP (1+A)²/√w + krCR (1+A) √(1-c)^{⌊P/3⌋-1}`.

With `P = ⌊w/4⌋` this is (long): `√w / P^{1/4} ≍ w^{1/4}` and `√(1-c)^{P/3} = e^{-c' w}`.
All constants depend only on `(D, θ, vlo, vhi)` through `K, L` and the class gap constants.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {J : Set ℝ} {β a : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}

/-! ## Elementary: fourth roots and the tail `∑ n^{-5/4}` -/

/-- `x^{1/4}` as `√√x`. -/
def krFourthRoot (x : ℝ) : ℝ := Real.sqrt (Real.sqrt x)

theorem krFourthRoot_nonneg (x : ℝ) : 0 ≤ krFourthRoot x := Real.sqrt_nonneg _

theorem krFourthRoot_pos {x : ℝ} (hx : 0 < x) : 0 < krFourthRoot x :=
  Real.sqrt_pos.2 (Real.sqrt_pos.2 hx)

theorem krFourthRoot_pow_four {x : ℝ} (hx : 0 ≤ x) : krFourthRoot x ^ 4 = x := by
  unfold krFourthRoot
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hx]

theorem krFourthRoot_sq (x : ℝ) : krFourthRoot x ^ 2 = Real.sqrt x := by
  unfold krFourthRoot
  exact Real.sq_sqrt (Real.sqrt_nonneg _)

theorem krFourthRoot_le_krFourthRoot {x y : ℝ} (h : x ≤ y) : krFourthRoot x ≤ krFourthRoot y :=
  Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)

/-- `1/(n n^{1/4}) ≤ 4 ((n-1)^{-1/4} - n^{-1/4})` for `n ≥ 2`. -/
theorem kr_telescope_54 {n : ℝ} (hn : 2 ≤ n) :
    1 / (n * krFourthRoot n) ≤ 4 / krFourthRoot (n - 1) - 4 / krFourthRoot n := by
  obtain ⟨u, hu_def⟩ : ∃ u, u = krFourthRoot n := ⟨_, rfl⟩
  obtain ⟨v, hv_def⟩ : ∃ v, v = krFourthRoot (n - 1) := ⟨_, rfl⟩
  have hu : 0 < u := hu_def ▸ krFourthRoot_pos (by linarith)
  have hv : 0 < v := hv_def ▸ krFourthRoot_pos (by linarith)
  have hvu : v ≤ u := hv_def ▸ hu_def ▸ krFourthRoot_le_krFourthRoot (by linarith)
  have hu4 : u ^ 4 = n := hu_def ▸ krFourthRoot_pow_four (by linarith)
  have hv4 : v ^ 4 = n - 1 := hv_def ▸ krFourthRoot_pow_four (by linarith)
  have hdiff : (u - v) * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) = 1 := by nlinarith
  have hsum : u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3 ≤ 4 * u ^ 3 := by
    have h1 : u ^ 2 * v ≤ u ^ 3 := by nlinarith [sq_nonneg u]
    have h2 : u * v ^ 2 ≤ u ^ 3 := by nlinarith [mul_pos hu hv]
    have h3 : v ^ 3 ≤ u ^ 3 := by
      have := pow_le_pow_left₀ hv.le hvu 3
      linarith
    linarith
  have huv : 0 ≤ u - v := by linarith
  have hkey : 1 ≤ (u - v) * (4 * u ^ 3) := by
    calc (1 : ℝ) = (u - v) * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) := hdiff.symm
      _ ≤ (u - v) * (4 * u ^ 3) := mul_le_mul_of_nonneg_left hsum huv
  have hkey' : v ≤ 4 * u ^ 4 * (u - v) := by nlinarith
  rw [← hu_def, ← hv_def, ← hu4]
  have e : 4 / v - 4 / u - 1 / (u ^ 4 * u) = (4 * u ^ 4 * (u - v) - v) / (u ^ 5 * v) := by
    field_simp
  have : 0 ≤ 4 / v - 4 / u - 1 / (u ^ 4 * u) := by
    rw [e]
    exact div_nonneg (by linarith) (by positivity)
  linarith

/-- `∑_{i < M} 1/((P+1+i) (P+1+i)^{1/4}) ≤ 4 / P^{1/4}` for `P ≥ 1`. -/
theorem kr_sum_inv_pow54_le {P : ℕ} (hP : 1 ≤ P) (M : ℕ) :
    ∑ i ∈ Finset.range M,
        1 / (((P + 1 + i : ℕ) : ℝ) * krFourthRoot ((P + 1 + i : ℕ) : ℝ)) ≤
      4 / krFourthRoot P := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have key : ∀ M : ℕ, ∑ i ∈ Finset.range M,
      1 / (((P + 1 + i : ℕ) : ℝ) * krFourthRoot ((P + 1 + i : ℕ) : ℝ)) ≤
        4 / krFourthRoot P - 4 / krFourthRoot ((P + M : ℕ) : ℝ) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ]
      have ht := kr_telescope_54 (n := ((P + 1 + M : ℕ) : ℝ)) (by
        have : (2 : ℝ) ≤ ((P + 1 + M : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ P + 1 + M)
        exact this)
      have e1 : ((P + 1 + M : ℕ) : ℝ) - 1 = ((P + M : ℕ) : ℝ) := by push_cast; ring
      have e2 : ((P + (M + 1) : ℕ) : ℝ) = ((P + 1 + M : ℕ) : ℝ) := by push_cast; ring
      rw [e1] at ht
      rw [e2]
      linarith
  refine (key M).trans ?_
  have : 0 ≤ 4 / krFourthRoot ((P + M : ℕ) : ℝ) := by
    exact div_nonneg (by norm_num) (krFourthRoot_nonneg _)
  linarith

/-- `x/2 ≤ 1 - e^{-x}` for `0 ≤ x ≤ 1`. -/
theorem kr_one_sub_exp_ge {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x / 2 ≤ 1 - Real.exp (-x) := by
  have h := Real.add_one_le_exp x
  have hpos : 0 < Real.exp x := Real.exp_pos x
  rw [Real.exp_neg]
  have : (Real.exp x)⁻¹ ≤ 1 / (x + 1) := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by linarith) h
  have h2 : 1 / (x + 1) ≤ 1 - x / 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- Geometric tail of `e^{-ρ j / w²}`: `∑_{j<N} e^{-ρ/w²}^j ≤ 2 w²/ρ` for `0 < ρ ≤ w²`. -/
theorem kr_exp_geom_sum_le {ρ w : ℝ} (hρ : 0 < ρ) (hw : 0 < w) (hρw : ρ ≤ w ^ 2) (N : ℕ) :
    ∑ j ∈ Finset.range N, Real.exp (-(ρ / w ^ 2)) ^ j ≤ 2 * w ^ 2 / ρ := by
  have hx0 : 0 ≤ ρ / w ^ 2 := by positivity
  have hx1 : ρ / w ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact hρw
  have hr0 : 0 ≤ Real.exp (-(ρ / w ^ 2)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(ρ / w ^ 2)) < 1 := by
    have : 0 < ρ / w ^ 2 := by positivity
    have h := Real.exp_lt_exp.2 (show -(ρ / w ^ 2) < 0 by linarith)
    rwa [Real.exp_zero] at h
  refine (kr_geom_sum_le hr0 hr1 N).trans ?_
  have hg := kr_one_sub_exp_ge hx0 hx1
  have hpos : 0 < 1 - Real.exp (-(ρ / w ^ 2)) := by linarith
  rw [div_le_div_iff₀ hpos hρ]
  have : ρ / w ^ 2 / 2 * (2 * w ^ 2) = ρ := by field_simp
  nlinarith

/-! ## Pointwise decomposition of a long row -/

/-- The class constants of the BV modules are nonnegative / less than one. -/
theorem KrBand.classConsts {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') :
    0 ≤ kBVClassRho D vlo vhi ∧ kBVClassRho D vlo vhi < 1 ∧
      0 < kBVClassRate D vlo vhi ∧ 0 < kBVClassRemConst D vlo vhi ∧
      0 < kBVClassVarConst D vlo vhi :=
  kBVClass_constants H.hD H.hvlo H.hvhi

theorem kBVVarBudget_nonneg {vlo vhi w : ℝ} (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    (n : ℕ) {N : ℝ} (hN : 0 ≤ N) : 0 ≤ kBVVarBudget D vlo vhi w n N := by
  unfold kBVVarBudget
  have hc := kBVClass_constants hD hvlo hvhi
  exact mul_nonneg (mul_nonneg (mul_nonneg hc.2.2.2.2.le (Real.sqrt_nonneg _))
    (Real.exp_pos _).le) hN

theorem kBVRemBudget_nonneg {vlo vhi w : ℝ} (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    (n : ℕ) {N : ℝ} (hN : 0 ≤ N) : 0 ≤ kBVRemBudget D vlo vhi w n N := by
  unfold kBVRemBudget
  have hc := kBVClass_constants hD hvlo hvhi
  exact mul_nonneg (mul_nonneg
    (mul_nonneg (div_nonneg hc.2.2.2.1.le (Real.sqrt_nonneg _)) (pow_nonneg hc.1 _))
    (Real.exp_pos _).le) hN

/-- **(long), pointwise, per row**: `q_{m+1+(k+1)}(b, ·) = g + r` on all of `ℝ`, with `g`
of variation `≤ kBVVarBudget … k N`, Lipschitz on `[0, w]` with constant `2D · kBVVarBudget`,
and `‖r‖_∞ ≤ √(2D) · kBVRemBudget … k N`, where `N = ‖q_{m+1}(b, ·)‖₂`. -/
theorem krDens_pointwise_decomposition {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (m k : ℕ) (hk : 8 ≤ k) (b : ℝ) :
    ∃ g r : ℝ → ℂ, Measurable g ∧ Measurable r ∧
      (∀ x, x ∉ Icc 0 w → g x = 0 ∧ r x = 0) ∧
      (∀ z, (krDens (Icc 0 w) ν f β a' (m + 1 + (k + 1)) b z : ℂ) = g z + r z) ∧
      eVariationOn g univ ≤ ENNReal.ofReal (kBVVarBudget D vlo vhi w k
        (Real.sqrt (∫ y, krDens (Icc 0 w) ν f β a' (m + 1) b y ^ 2))) ∧
      (∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖g x - g y‖ ≤
        (2 * D * kBVVarBudget D vlo vhi w k
          (Real.sqrt (∫ y, krDens (Icc 0 w) ν f β a' (m + 1) b y ^ 2))) * |x - y|) ∧
      (∀ x, ‖r x‖ ≤ Real.sqrt (2 * D) * kBVRemBudget D vlo vhi w k
        (Real.sqrt (∫ y, krDens (Icc 0 w) ν f β a' (m + 1) b y ^ 2))) := by
  have hJ := H.hJ
  have hJfin := H.hJfin
  set u : ℝ → ℝ := fun y => krDens (Icc 0 w) ν f β a' (m + 1) b y with hu_def
  have hu : Measurable u := measurable_krDens_right ν hJ H.hf β a' (m + 1) b
  have husupp : ∀ y, y ∉ Icc 0 w → u y = 0 := fun _ hy => krDens_eq_zero_of_right_notMem ν hy _ _
  have huM : ∀ y, |u y| ≤ D / |a'| := fun y => abs_krDens_le ν H.hf0 H.hfD (m + 1) b y
  have h2 : MemLp (fun y => (u y : ℂ)) 2 := kr_memLp_two_ofReal hJ hJfin hu husupp huM
  have huc : Measurable (fun y => (u y : ℂ)) := Complex.measurable_ofReal.comp hu
  have hsuppc : ∀ x, x ∉ Icc (0 : ℝ) (0 + w) → (u x : ℂ) = 0 := fun x hx => by
    rw [zero_add] at hx
    rw [husupp x hx, Complex.ofReal_zero]
  have ha' : 1 / 2 ≤ |-a'| := by rw [abs_neg]; exact H.ha₁'
  obtain ⟨g, r, hg, _, _, hr, _, _, hs, hsum, hvar, hlip, hrem⟩ :=
    kBV_regLaw_pointwise_decomposition H.hD H.hθ H.hvlo H.hν (-β) (α := 0)
      ha' H.hw huc h2 hsuppc k hk
  simp only [zero_add] at hs hsum hlip
  -- the `L²` norm of the input row
  have hN : ‖h2.toLp (fun y => (u y : ℂ))‖ =
      Real.sqrt (∫ y, krDens (Icc 0 w) ν f β a' (m + 1) b y ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), kBV_toLp_norm_sq, kBVNormSq_ofReal]
  rw [hN] at hvar hlip hrem
  -- identify the iterate with the shifted kernel
  have hind : (fun y => (u y : ℂ)) = fun x => (((Icc 0 w).indicator u x : ℝ) : ℂ) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) w
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, husupp x hx]
  have hiter : ∀ z, ((kStep (Icc 0 w) (ν : Measure ℝ) (-β) (-a'))^[k + 1]
      (fun y => (u y : ℂ))) z = (krDens (Icc 0 w) ν f β a' (m + 1 + (k + 1)) b z : ℂ) := by
    intro z
    rw [hind, kStep_iterate_ofReal (ν : Measure ℝ) (k + 1) u]
    rw [congrFun (krDens_shift_eq_krRow ν hJ hJfin H.hf H.hf0 H.hfD H.hνf H.ha' m (k + 1) b) z]
  -- constants: `D / |a'| ≤ 2 D`
  have hDa : D / |-a'| ≤ 2 * D := by
    rw [abs_neg, div_le_iff₀ (abs_pos.2 H.ha')]
    have := H.ha₁'
    nlinarith [H.hD0]
  have hN0 : 0 ≤ Real.sqrt (∫ y, krDens (Icc 0 w) ν f β a' (m + 1) b y ^ 2) := Real.sqrt_nonneg _
  have hV0 := kBVVarBudget_nonneg (w := w) H.hD H.hvlo H.hvhi k hN0
  have hR0 := kBVRemBudget_nonneg (w := w) H.hD H.hvlo H.hvhi k hN0
  refine ⟨g, r, hg, hr, hs, fun z => by rw [← hiter z, hsum z], hvar, ?_, ?_⟩
  · intro x hx y hy
    refine (hlip x hx y hy).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDa hV0) (abs_nonneg _)
  · intro x
    refine (hrem x).trans ?_
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hDa) hR0

/-! ## The split of a long row and the explicit budgets -/

/-- The length `m + 1 = min(⌊n/3⌋, T)` of the initial `L²` segment of a long row. -/
def krSplit (w : ℝ) (n : ℕ) : ℕ := min (n / 3) (krT w)

theorem kr_split_nat {w : ℝ} (hw : 1 ≤ w) {n : ℕ} (hn : 13 ≤ n) :
    1 ≤ krSplit w n ∧ krSplit w n ≤ n / 3 ∧ 8 ≤ n - krSplit w n - 1 ∧
      krSplit w n - 1 + 1 + (n - krSplit w n - 1 + 1) = n ∧
      n / 3 - 1 ≤ (n - krSplit w n - 1) / 2 ∧ n - 3 * krT w ≤ n - krSplit w n - 1 := by
  have hT := krT_pos hw
  unfold krSplit
  omega

/-- The variation term of one long row with decay rate `ρ`:
`[n < 3T] 4√w/(n n^{1/4}) + [n ≥ 3T] √6 e^{-ρ/w²}^{n-3T} / w²`. -/
def krVarTermGen (ρ w : ℝ) (n : ℕ) : ℝ :=
  if 3 * krT w ≤ n then Real.sqrt 6 * Real.exp (-(ρ / w ^ 2)) ^ (n - 3 * krT w) / w ^ 2
  else 4 * Real.sqrt w / ((n : ℝ) * krFourthRoot n)

/-- The variation term of one long row at the class rate. -/
def krVarTerm (D vlo vhi w : ℝ) (n : ℕ) : ℝ := krVarTermGen (kBVClassRate D vlo vhi) w n

theorem krVarTermGen_nonneg {ρ w : ℝ} (hw : 0 < w) (n : ℕ) : 0 ≤ krVarTermGen ρ w n := by
  unfold krVarTermGen
  split_ifs
  · positivity
  · exact div_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (krFourthRoot_nonneg _))

theorem krVarTerm_nonneg {vlo vhi w : ℝ} (hw : 0 < w) (n : ℕ) : 0 ≤ krVarTerm D vlo vhi w n :=
  krVarTermGen_nonneg hw n

theorem krVarTermGen_le_add {ρ w : ℝ} (hw : 0 < w) (n : ℕ) :
    krVarTermGen ρ w n ≤ 4 * Real.sqrt w / ((n : ℝ) * krFourthRoot n) +
      if 3 * krT w ≤ n then Real.sqrt 6 * Real.exp (-(ρ / w ^ 2)) ^ (n - 3 * krT w) / w ^ 2
      else 0 := by
  have h1 : 0 ≤ 4 * Real.sqrt w / ((n : ℝ) * krFourthRoot n) :=
    div_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (krFourthRoot_nonneg _))
  unfold krVarTermGen
  split_ifs
  · linarith
  · simp

namespace KrBand

variable {ν}

/-- The `L²` input of the split: `∫ q_s(b,·)² ≤ 3 C₂ (1+A)²`, and
`(w/k) ∫ q_s(b,·)² ≤ [n < 3T] 16 C₂ (1+A)² w/(n² √n) + [n ≥ 3T] 6 C₂ (1+A)²/w⁴`. -/
theorem split_L2 {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {n : ℕ} (hn : 13 ≤ n) :
    (∫ y, krDens (Icc 0 w) ν f β a' (krSplit w n) b y ^ 2) ≤ 3 * krC₂ D K L * (1 + A) ^ 2 ∧
      w / ((n - krSplit w n - 1 : ℕ) : ℝ) * ∫ y, krDens (Icc 0 w) ν f β a' (krSplit w n) b y ^ 2 ≤
        if 3 * krT w ≤ n then 6 * krC₂ D K L * (1 + A) ^ 2 / w ^ 4
        else 16 * krC₂ D K L * (1 + A) ^ 2 * w / ((n : ℝ) ^ 2 * Real.sqrt n) := by
  have hw := H.hw
  have hw0 := H.hw0
  have hA := H.hA
  have hC := krC₂_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  obtain ⟨hs1, hs3, hk8, -, -, -⟩ := kr_split_nat hw hn
  have hI0 : 0 ≤ ∫ y, krDens (Icc 0 w) ν f β a' (krSplit w n) b y ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hk0 : (0 : ℝ) < ((n - krSplit w n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < _)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  by_cases h3 : 3 * krT w ≤ n
  · -- `s = T`
    have hsT : krSplit w n = krT w := by unfold krSplit; exact Nat.min_eq_right (by omega)
    rw [if_pos h3, hsT]
    rw [hsT] at hk0 hI0
    have hI := integral_sq_krDens_bdry_T ν H hb H.hT1 H.hTw H.hwT
    have hw3 : 1 ≤ w ^ 3 := one_le_pow₀ hw
    refine ⟨hI.trans ?_, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hC) (sq_nonneg (1 + A))]
    · -- `k ≥ w²/2`
      have hk1 : w ^ 2 ≤ 2 * (krT w : ℝ) := H.hwT
      have hk2 : (2 * krT w - 1 : ℝ) ≤ ((n - krT w - 1 : ℕ) : ℝ) := by
        have : 2 * krT w - 1 ≤ n - krT w - 1 := by omega
        have h' : ((2 * krT w - 1 : ℕ) : ℝ) ≤ ((n - krT w - 1 : ℕ) : ℝ) := by exact_mod_cast this
        have e : ((2 * krT w - 1 : ℕ) : ℝ) = 2 * (krT w : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        linarith
      have hk8' : (8 : ℝ) ≤ ((n - krT w - 1 : ℕ) : ℝ) := by exact_mod_cast (hsT ▸ hk8)
      have hkw : w ^ 2 / 2 ≤ ((n - krT w - 1 : ℕ) : ℝ) := by linarith
      have hwk : w / ((n - krT w - 1 : ℕ) : ℝ) ≤ 2 / w := by
        rw [div_le_div_iff₀ hk0 hw0]
        nlinarith
      calc w / ((n - krT w - 1 : ℕ) : ℝ) * ∫ y, krDens (Icc 0 w) ν f β a' (krT w) b y ^ 2
          ≤ 2 / w * (3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3) :=
            mul_le_mul hwk hI hI0 (by positivity)
        _ = 6 * krC₂ D K L * (1 + A) ^ 2 / w ^ 4 := by field_simp; ring
  · -- `s = ⌊n/3⌋`
    have hs : krSplit w n = n / 3 := by unfold krSplit; exact Nat.min_eq_left (by omega)
    rw [if_neg h3, hs]
    rw [hs] at hk0 hI0
    have hsw : ((n / 3 : ℕ) : ℝ) ≤ w ^ 2 := by
      have : ((n / 3 : ℕ) : ℝ) ≤ (krT w : ℝ) := by exact_mod_cast (by omega : n / 3 ≤ krT w)
      exact this.trans H.hTw
    have hI := integral_sq_krDens_bdry_medium ν H hb (n := n / 3) (by omega) hsw
    have hs0 : (1 : ℝ) ≤ ((n / 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n / 3)
    have hss : 1 ≤ ((n / 3 : ℕ) : ℝ) * Real.sqrt ((n / 3 : ℕ) : ℝ) :=
      one_le_mul_of_one_le_of_one_le hs0 (Real.one_le_sqrt.2 hs0)
    refine ⟨hI.trans ?_, ?_⟩
    · rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg hC (sq_nonneg (1 + A))]
    · -- `s ≥ n/4`, `k ≥ n/2`
      have hs4 : (n : ℝ) / 4 ≤ ((n / 3 : ℕ) : ℝ) := by
        have : n ≤ 4 * (n / 3) := by omega
        have h' : (n : ℝ) ≤ 4 * ((n / 3 : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      have hk2 : (n : ℝ) / 2 ≤ ((n - n / 3 - 1 : ℕ) : ℝ) := by
        have : n ≤ 2 * (n - n / 3 - 1) := by omega
        have h' : (n : ℝ) ≤ 2 * ((n - n / 3 - 1 : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      have hsq4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hsqs : Real.sqrt n / 2 ≤ Real.sqrt ((n / 3 : ℕ) : ℝ) := by
        have := Real.sqrt_le_sqrt hs4
        rwa [Real.sqrt_div (by positivity), hsq4] at this
      have hsss : (n : ℝ) * Real.sqrt n / 8 ≤ ((n / 3 : ℕ) : ℝ) * Real.sqrt ((n / 3 : ℕ) : ℝ) := by
        have h1 : 0 ≤ Real.sqrt n / 2 := by positivity
        calc (n : ℝ) * Real.sqrt n / 8 = (n / 4) * (Real.sqrt n / 2) := by ring
          _ ≤ ((n / 3 : ℕ) : ℝ) * Real.sqrt ((n / 3 : ℕ) : ℝ) :=
            mul_le_mul hs4 hsqs h1 (by positivity)
      have hsn0 : 0 < (n : ℝ) * Real.sqrt n := by positivity
      have hI' : (∫ y, krDens (Icc 0 w) ν f β a' (n / 3) b y ^ 2) ≤
          8 * krC₂ D K L * (1 + A) ^ 2 / ((n : ℝ) * Real.sqrt n) := by
        refine hI.trans ?_
        rw [div_le_div_iff₀ (by positivity) hsn0]
        have := mul_le_mul_of_nonneg_left hsss (mul_nonneg hC (sq_nonneg (1 + A)))
        nlinarith
      have hwk : w / ((n - n / 3 - 1 : ℕ) : ℝ) ≤ 2 * w / n := by
        rw [div_le_div_iff₀ hk0 hn0]
        nlinarith
      calc w / ((n - n / 3 - 1 : ℕ) : ℝ) * ∫ y, krDens (Icc 0 w) ν f β a' (n / 3) b y ^ 2
          ≤ 2 * w / n * (8 * krC₂ D K L * (1 + A) ^ 2 / ((n : ℝ) * Real.sqrt n)) :=
            mul_le_mul hwk hI' hI0 (by positivity)
        _ = 16 * krC₂ D K L * (1 + A) ^ 2 * w / ((n : ℝ) ^ 2 * Real.sqrt n) := by
            field_simp
            ring

/-- The variation budget of a long boundary row: `≤ C^V √C₂ (1+A) krVarTerm n`. -/
theorem varBudget_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {n : ℕ} (hn : 13 ≤ n) :
    kBVVarBudget D vlo vhi w (n - krSplit w n - 1)
        (Real.sqrt (∫ y, krDens (Icc 0 w) ν f β a' (krSplit w n) b y ^ 2)) ≤
      kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
        krVarTerm D vlo vhi w n := by
  have hw := H.hw
  have hw0 := H.hw0
  have hA := H.hA
  have hC := krC₂_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  have hcc := H.classConsts
  obtain ⟨hs1, hs3, hk8, -, -, hk3⟩ := kr_split_nat hw hn
  obtain ⟨-, hX⟩ := H.split_L2 hb hn
  set I := ∫ y, krDens (Icc 0 w) ν f β a' (krSplit w n) b y ^ 2 with hI_def
  set k := n - krSplit w n - 1 with hk_def
  have hI0 : 0 ≤ I := integral_nonneg fun _ => sq_nonneg _
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hwk0 : 0 ≤ w / (k : ℝ) := by positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hrate := hcc.2.2.1
  have hexp : Real.exp (-(kBVClassRate D vlo vhi * k / w ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ kBVClassRate D vlo vhi * k / w ^ 2 := by positivity
    linarith
  have hVC := hcc.2.2.2.2
  have hnf : 0 < (n : ℝ) * krFourthRoot n := mul_pos hn0 (krFourthRoot_pos hn0)
  have hprod : Real.sqrt (w / k) * Real.sqrt I = Real.sqrt (w / k * I) := (Real.sqrt_mul hwk0 I).symm
  have hV : kBVVarBudget D vlo vhi w k (Real.sqrt I) =
      kBVClassVarConst D vlo vhi * Real.sqrt (w / k * I) *
        Real.exp (-(kBVClassRate D vlo vhi * k / w ^ 2)) := by
    unfold kBVVarBudget
    rw [← hprod]
    ring
  rw [hV]
  unfold krVarTerm krVarTermGen
  by_cases h3 : 3 * krT w ≤ n
  · rw [if_pos h3] at hX ⊢
    -- `√(w/k · I) ≤ √6 √C₂ (1+A) / w²`
    have hY : Real.sqrt (w / k * I) ≤ Real.sqrt 6 * Real.sqrt (krC₂ D K L) * (1 + A) / w ^ 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      refine hX.trans (le_of_eq ?_)
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hC]
      ring
    -- `e^{-ρ k/w²} = r^k ≤ r^{n - 3T}`
    have hr0 : 0 ≤ Real.exp (-(kBVClassRate D vlo vhi / w ^ 2)) := (Real.exp_pos _).le
    have hr1 : Real.exp (-(kBVClassRate D vlo vhi / w ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ kBVClassRate D vlo vhi / w ^ 2 := div_nonneg hrate.le (by positivity)
      linarith
    have hE : Real.exp (-(kBVClassRate D vlo vhi * k / w ^ 2)) =
        Real.exp (-(kBVClassRate D vlo vhi / w ^ 2)) ^ k := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hE' : Real.exp (-(kBVClassRate D vlo vhi / w ^ 2)) ^ k ≤
        Real.exp (-(kBVClassRate D vlo vhi / w ^ 2)) ^ (n - 3 * krT w) :=
      pow_le_pow_of_le_one hr0 hr1 hk3
    have h1 : 0 ≤ 4 * Real.sqrt w / ((n : ℝ) * krFourthRoot n) :=
      div_nonneg (by positivity) hnf.le
    calc kBVClassVarConst D vlo vhi * Real.sqrt (w / k * I) *
          Real.exp (-(kBVClassRate D vlo vhi * k / w ^ 2))
        ≤ kBVClassVarConst D vlo vhi * (Real.sqrt 6 * Real.sqrt (krC₂ D K L) * (1 + A) / w ^ 2) *
          Real.exp (-(kBVClassRate D vlo vhi / w ^ 2)) ^ (n - 3 * krT w) := by
          rw [hE]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hY hcc.2.2.2.2.le) hE'
            (pow_nonneg hr0 _) (mul_nonneg hVC.le (by positivity))
      _ = kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
          (Real.sqrt 6 * Real.exp (-(kBVClassRate D vlo vhi / w ^ 2)) ^ (n - 3 * krT w) /
            w ^ 2) := by ring
  · rw [if_neg h3] at hX ⊢
    have hY : Real.sqrt (w / k * I) ≤
        4 * Real.sqrt (krC₂ D K L) * (1 + A) * Real.sqrt w / ((n : ℝ) * krFourthRoot n) := by
      rw [Real.sqrt_le_left (div_nonneg (by positivity) hnf.le)]
      refine hX.trans (le_of_eq ?_)
      rw [div_pow, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hC, Real.sq_sqrt hw0.le,
        krFourthRoot_sq]
      ring
    calc kBVClassVarConst D vlo vhi * Real.sqrt (w / k * I) *
          Real.exp (-(kBVClassRate D vlo vhi * k / w ^ 2))
        ≤ kBVClassVarConst D vlo vhi *
          (4 * Real.sqrt (krC₂ D K L) * (1 + A) * Real.sqrt w / ((n : ℝ) * krFourthRoot n)) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hY hcc.2.2.2.2.le) hexp (Real.exp_pos _).le
            (mul_nonneg hVC.le (div_nonneg (by positivity) hnf.le))
      _ = kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
          (4 * Real.sqrt w / ((n : ℝ) * krFourthRoot n)) := by ring

/-- The remainder budget of a long boundary row: `≤ C^R √(3 C₂) (1+A) ρ^{⌊n/3⌋-1}`. -/
theorem remBudget_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {n : ℕ} (hn : 13 ≤ n) :
    kBVRemBudget D vlo vhi w (n - krSplit w n - 1)
        (Real.sqrt (∫ y, krDens (Icc 0 w) ν f β a' (krSplit w n) b y ^ 2)) ≤
      kBVClassRemConst D vlo vhi * Real.sqrt (3 * krC₂ D K L) * (1 + A) *
        kBVClassRho D vlo vhi ^ (n / 3 - 1) := by
  have hw := H.hw
  have hA := H.hA
  have hC := krC₂_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  have hcc := H.classConsts
  obtain ⟨hs1, hs3, hk8, -, hk2, -⟩ := kr_split_nat hw hn
  obtain ⟨hI3, -⟩ := H.split_L2 hb hn
  set I := ∫ y, krDens (Icc 0 w) ν f β a' (krSplit w n) b y ^ 2 with hI_def
  set k := n - krSplit w n - 1 with hk_def
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hrate := hcc.2.2.1
  have hexp : Real.exp (-(kBVClassRate D vlo vhi * k / w ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ kBVClassRate D vlo vhi * k / w ^ 2 := by positivity
    linarith
  have hN : Real.sqrt I ≤ Real.sqrt (3 * krC₂ D K L) * (1 + A) := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
    exact hI3
  have hdiv : kBVClassRemConst D vlo vhi / Real.sqrt k ≤ kBVClassRemConst D vlo vhi :=
    div_le_self hcc.2.2.2.1.le (Real.one_le_sqrt.2 hk1)
  have hρ : kBVClassRho D vlo vhi ^ (k / 2) ≤ kBVClassRho D vlo vhi ^ (n / 3 - 1) :=
    pow_le_pow_of_le_one hcc.1 hcc.2.1.le hk2
  unfold kBVRemBudget
  calc kBVClassRemConst D vlo vhi / Real.sqrt k * kBVClassRho D vlo vhi ^ (k / 2) *
        Real.exp (-(kBVClassRate D vlo vhi * k / w ^ 2)) * Real.sqrt I
      ≤ kBVClassRemConst D vlo vhi * kBVClassRho D vlo vhi ^ (n / 3 - 1) * 1 *
        (Real.sqrt (3 * krC₂ D K L) * (1 + A)) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul hdiv hρ (pow_nonneg hcc.1 _) hcc.2.2.2.1.le)
          hexp (Real.exp_pos _).le ?_) hN (Real.sqrt_nonneg _) ?_
        · exact mul_nonneg hcc.2.2.2.1.le (pow_nonneg hcc.1 _)
        · exact mul_nonneg (mul_nonneg hcc.2.2.2.1.le (pow_nonneg hcc.1 _)) zero_le_one
    _ = _ := by ring

end KrBand

/-- **(long), per boundary row, explicit budgets**: for `n ≥ 13`, `q_n(b, ·) = g + r` with
`V(g) ≤ C^V √C₂ (1+A) krVarTerm n`, `Lip(g|_{[0,w]}) ≤ 2D · C^V √C₂ (1+A) krVarTerm n`, and
`‖r‖_∞ ≤ √(2D) C^R √(3C₂) (1+A) ρ^{⌊n/3⌋-1}`. -/
theorem krDens_row_decomposition {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {n : ℕ} (hn : 13 ≤ n) :
    ∃ g r : ℝ → ℂ, Measurable g ∧ Measurable r ∧
      (∀ x, x ∉ Icc 0 w → g x = 0 ∧ r x = 0) ∧
      (∀ z, (krDens (Icc 0 w) ν f β a' n b z : ℂ) = g z + r z) ∧
      eVariationOn g univ ≤ ENNReal.ofReal (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) *
        (1 + A) * krVarTerm D vlo vhi w n) ∧
      (∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖g x - g y‖ ≤
        (2 * D * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
          krVarTerm D vlo vhi w n)) * |x - y|) ∧
      (∀ x, ‖r x‖ ≤ Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi * Real.sqrt (3 * krC₂ D K L) *
        (1 + A) * kBVClassRho D vlo vhi ^ (n / 3 - 1))) := by
  obtain ⟨hs1, -, hk8, hsplit, -, -⟩ := kr_split_nat H.hw hn
  obtain ⟨g, r, hg, hr, hs, hsum, hvar, hlip, hrem⟩ :=
    krDens_pointwise_decomposition ν H (krSplit w n - 1) (n - krSplit w n - 1) hk8 b
  have hs1' : krSplit w n - 1 + 1 = krSplit w n := by omega
  rw [hsplit] at hsum
  rw [hs1'] at hvar hlip hrem
  have hVB := H.varBudget_le hb hn
  have hRB := H.remBudget_le hb hn
  refine ⟨g, r, hg, hr, hs, hsum, hvar.trans (ENNReal.ofReal_le_ofReal hVB), ?_, ?_⟩
  · intro x hx y hy
    refine (hlip x hx y hy).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hVB (by linarith [H.hD0]))
      (abs_nonneg _)
  · intro x
    exact (hrem x).trans (mul_le_mul_of_nonneg_left hRB (Real.sqrt_nonneg _))

/-! ## Finite sums of decompositions -/

theorem kr_eVariationOn_sum_le {g : ℕ → ℝ → ℂ} {V : ℕ → ℝ} (hV : ∀ i, 0 ≤ V i)
    (hvar : ∀ i, eVariationOn (g i) univ ≤ ENNReal.ofReal (V i)) (M : ℕ) :
    eVariationOn (fun x => ∑ i ∈ Finset.range M, g i x) univ ≤
      ENNReal.ofReal (∑ i ∈ Finset.range M, V i) := by
  induction M with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, ENNReal.ofReal_zero]
    exact le_of_eq ((eVariationOn.eq_zero_iff _).2 fun _ _ _ _ => edist_self _)
  | succ M ih =>
    simp only [Finset.sum_range_succ]
    rw [ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => hV i) (hV M)]
    exact (kBV_variation_add_le (fun x => ∑ i ∈ Finset.range M, g i x) (g M) univ).trans
      (add_le_add ih (hvar M))

/-- Finite sums of pointwise decompositions: measurability, support, identity, variation,
Lipschitz constant, and uniform remainder all add. -/
theorem kr_sum_decomposition {w : ℝ} {g r : ℕ → ℝ → ℂ} {q : ℕ → ℝ → ℝ} {V Lc Rc : ℕ → ℝ}
    (hg : ∀ i, Measurable (g i)) (hr : ∀ i, Measurable (r i))
    (hs : ∀ i x, x ∉ Icc 0 w → g i x = 0 ∧ r i x = 0)
    (hsum : ∀ i z, (q i z : ℂ) = g i z + r i z)
    (hV : ∀ i, 0 ≤ V i) (hvar : ∀ i, eVariationOn (g i) univ ≤ ENNReal.ofReal (V i))
    (hlip : ∀ i, ∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖g i x - g i y‖ ≤ Lc i * |x - y|)
    (hrem : ∀ i x, ‖r i x‖ ≤ Rc i) (M : ℕ) :
    Measurable (fun x => ∑ i ∈ Finset.range M, g i x) ∧
      Measurable (fun x => ∑ i ∈ Finset.range M, r i x) ∧
      (∀ x, x ∉ Icc 0 w →
        (∑ i ∈ Finset.range M, g i x) = 0 ∧ (∑ i ∈ Finset.range M, r i x) = 0) ∧
      (∀ z, ((∑ i ∈ Finset.range M, q i z : ℝ) : ℂ) =
        (∑ i ∈ Finset.range M, g i z) + ∑ i ∈ Finset.range M, r i z) ∧
      eVariationOn (fun x => ∑ i ∈ Finset.range M, g i x) univ ≤
        ENNReal.ofReal (∑ i ∈ Finset.range M, V i) ∧
      (∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w,
        ‖(∑ i ∈ Finset.range M, g i x) - ∑ i ∈ Finset.range M, g i y‖ ≤
          (∑ i ∈ Finset.range M, Lc i) * |x - y|) ∧
      (∀ x, ‖∑ i ∈ Finset.range M, r i x‖ ≤ ∑ i ∈ Finset.range M, Rc i) := by
  refine ⟨Finset.measurable_sum _ fun i _ => hg i, Finset.measurable_sum _ fun i _ => hr i,
    ?_, ?_, kr_eVariationOn_sum_le hV hvar M, ?_, ?_⟩
  · intro x hx
    exact ⟨Finset.sum_eq_zero fun i _ => (hs i x hx).1, Finset.sum_eq_zero fun i _ => (hs i x hx).2⟩
  · intro z
    rw [Complex.ofReal_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hsum i z
  · intro x hx y hy
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hlip i x hx y hy)
  · intro x
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hrem i x)

/-! ## Sums of the budgets -/

variable {ν}

theorem KrBand.rate_le_one {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') : kBVClassRate D vlo vhi ≤ 1 := by
  have := krKappa_le_one H.hD H.hθ H.hvlo H.hvhi H.hν
  unfold kBVClassRate
  unfold krKappa at this
  linarith

/-- `∑_{i<M} krVarTermGen ρ (P+1+i) ≤ 16 √w / P^{1/4} + 2√6 / ρ` for `P ≥ 1`, `0 < ρ ≤ w²`. -/
theorem kr_sum_krVarTermGen_le {ρ w : ℝ} (hrate : 0 < ρ) (hw : 1 ≤ w) (hρw : ρ ≤ w ^ 2)
    {P : ℕ} (hP : 1 ≤ P) (M : ℕ) :
    ∑ i ∈ Finset.range M, krVarTermGen ρ w (P + 1 + i) ≤
      16 * Real.sqrt w / krFourthRoot P + 2 * Real.sqrt 6 / ρ := by
  have hw0 : 0 < w := by linarith
  refine (Finset.sum_le_sum fun i _ => krVarTermGen_le_add hw0 (P + 1 + i)).trans ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · have := kr_sum_inv_pow54_le hP M
    have e : ∀ i ∈ Finset.range M,
        4 * Real.sqrt w / (((P + 1 + i : ℕ) : ℝ) * krFourthRoot ((P + 1 + i : ℕ) : ℝ)) =
          4 * Real.sqrt w * (1 / (((P + 1 + i : ℕ) : ℝ) * krFourthRoot ((P + 1 + i : ℕ) : ℝ))) :=
      fun i _ => by ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    calc 4 * Real.sqrt w * ∑ i ∈ Finset.range M,
          1 / (((P + 1 + i : ℕ) : ℝ) * krFourthRoot ((P + 1 + i : ℕ) : ℝ))
        ≤ 4 * Real.sqrt w * (4 / krFourthRoot P) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 16 * Real.sqrt w / krFourthRoot P := by ring
  · -- the geometric part
    set r := Real.exp (-(ρ / w ^ 2)) with hr_def
    set F : ℕ → ℝ := fun n => if 3 * krT w ≤ n then Real.sqrt 6 * r ^ (n - 3 * krT w) / w ^ 2 else 0
      with hF_def
    have hF0 : ∀ n, 0 ≤ F n := fun n => by
      simp only [hF_def]
      split_ifs
      · positivity
      · exact le_refl 0
    have hgeom := kr_exp_geom_sum_le hrate hw0 hρw
    have h1 : ∑ i ∈ Finset.range M, F (P + 1 + i) ≤ ∑ n ∈ Finset.range (P + 1 + M), F n := by
      rw [Finset.sum_range_add]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun n _ => hF0 n)
    have h2 : ∑ n ∈ Finset.range (P + 1 + M), F n ≤
        ∑ j ∈ Finset.range (P + 1 + M - 3 * krT w), Real.sqrt 6 * r ^ j / w ^ 2 := by
      refine (kr_sum_split hF0 (3 * krT w) (P + 1 + M)).trans ?_
      have hz : ∑ n ∈ Finset.range (3 * krT w), F n = 0 :=
        Finset.sum_eq_zero fun n hn => by
          simp only [hF_def]
          rw [if_neg (by have := Finset.mem_range.1 hn; omega)]
      rw [hz, zero_add]
      refine le_of_eq (Finset.sum_congr rfl fun j _ => ?_)
      simp only [hF_def]
      rw [if_pos (by omega), Nat.add_sub_cancel_left]
    have h3 : ∑ j ∈ Finset.range (P + 1 + M - 3 * krT w), Real.sqrt 6 * r ^ j / w ^ 2 ≤
        Real.sqrt 6 / w ^ 2 * (2 * w ^ 2 / ρ) := by
      have e : ∀ j ∈ Finset.range (P + 1 + M - 3 * krT w),
          Real.sqrt 6 * r ^ j / w ^ 2 = Real.sqrt 6 / w ^ 2 * r ^ j := fun j _ => by ring
      rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hgeom _) (by positivity)
    refine (h1.trans (h2.trans h3)).trans (le_of_eq ?_)
    field_simp

/-- `∑_{i<M} krVarTerm (P+1+i) ≤ 16 √w / P^{1/4} + 2√6 / ρ_rate` for `P ≥ 1`. -/
theorem KrBand.sum_krVarTerm_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {P : ℕ} (hP : 1 ≤ P) (M : ℕ) :
    ∑ i ∈ Finset.range M, krVarTerm D vlo vhi w (P + 1 + i) ≤
      16 * Real.sqrt w / krFourthRoot P + 2 * Real.sqrt 6 / kBVClassRate D vlo vhi :=
  kr_sum_krVarTermGen_le H.classConsts.2.2.1 H.hw (H.rate_le_one.trans (one_le_pow₀ H.hw)) hP M

/-- `∑_{i<M} ρ^{⌊(P+1+i)/3⌋-1} ≤ 3 ρ^{⌊P/3⌋-1} / (1-ρ)` for `P ≥ 3`, `0 ≤ ρ < 1`. -/
theorem kr_sum_rho_pow_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) {P : ℕ} (hP : 3 ≤ P) (M : ℕ) :
    ∑ i ∈ Finset.range M, ρ ^ ((P + 1 + i) / 3 - 1) ≤ 3 * ρ ^ (P / 3 - 1) / (1 - ρ) := by
  have hterm : ∀ i, ρ ^ ((P + 1 + i) / 3 - 1) ≤ ρ ^ (P / 3 - 1) * ρ ^ (i / 3) := fun i => by
    rw [← pow_add]
    exact pow_le_pow_of_le_one h0 h1.le (by omega)
  have hgroup : ∀ N : ℕ, ∑ i ∈ Finset.range (3 * N), ρ ^ (i / 3) = 3 * ∑ j ∈ Finset.range N, ρ ^ j := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show 3 * (N + 1) = 3 * N + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, Finset.sum_range_succ,
        show (3 * N) / 3 = N by omega, show (3 * N + 1) / 3 = N by omega,
        show (3 * N + 1 + 1) / 3 = N by omega]
      ring
  have hsub : ∑ i ∈ Finset.range M, ρ ^ (i / 3) ≤ ∑ i ∈ Finset.range (3 * M), ρ ^ (i / 3) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      fun i _ _ => pow_nonneg h0 _
  calc ∑ i ∈ Finset.range M, ρ ^ ((P + 1 + i) / 3 - 1)
      ≤ ∑ i ∈ Finset.range M, ρ ^ (P / 3 - 1) * ρ ^ (i / 3) := Finset.sum_le_sum fun i _ => hterm i
    _ = ρ ^ (P / 3 - 1) * ∑ i ∈ Finset.range M, ρ ^ (i / 3) := by rw [Finset.mul_sum]
    _ ≤ ρ ^ (P / 3 - 1) * (3 * ∑ j ∈ Finset.range M, ρ ^ j) := by
        rw [← hgroup]
        exact mul_le_mul_of_nonneg_left hsub (pow_nonneg h0 _)
    _ ≤ ρ ^ (P / 3 - 1) * (3 * (1 / (1 - ρ))) := by
        gcongr
        exact kr_geom_sum_le h0 h1 M
    _ = 3 * ρ ^ (P / 3 - 1) / (1 - ρ) := by ring

/-! ## The (long) display -/

/-- Variation constant of (long): `C^V √C₂ (16 + 2√6/ρ_rate)`. -/
def krCV (D K L vlo vhi : ℝ) : ℝ :=
  kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) *
    (16 + 2 * Real.sqrt 6 / kBVClassRate D vlo vhi)

/-- Remainder constant of (long): `3 √(2D) C^R √(3 C₂) / (1 - ρ)`. -/
def krCR (D K L vlo vhi : ℝ) : ℝ :=
  3 * Real.sqrt (2 * D) * kBVClassRemConst D vlo vhi * Real.sqrt (3 * krC₂ D K L) /
    (1 - kBVClassRho D vlo vhi)

theorem KrBand.krCV_nonneg {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') : 0 ≤ krCV D K L vlo vhi := by
  have hcc := H.classConsts
  unfold krCV
  have : 0 ≤ 2 * Real.sqrt 6 / kBVClassRate D vlo vhi := by
    exact div_nonneg (by positivity) hcc.2.2.1.le
  exact mul_nonneg (mul_nonneg hcc.2.2.2.2.le (Real.sqrt_nonneg _)) (by linarith)

theorem KrBand.krCR_nonneg {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') : 0 ≤ krCR D K L vlo vhi := by
  have hcc := H.classConsts
  unfold krCR
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    hcc.2.2.2.1.le) (Real.sqrt_nonneg _)) (by linarith [hcc.2.1])

variable (ν)

/-- **(long)**: for a boundary point `b`, `P ≥ 12`, and any `M`,
`∑_{i<M} q_{P+1+i}(b, ·) = G + R` on `ℝ` with `G, R` measurable, supported in `[0, w]`,
`V(G) ≤ krCV (1+A) (√w / P^{1/4} + 1)`, `Lip(G|_{[0,w]}) ≤ 2D krCV (1+A) (√w / P^{1/4} + 1)`,
`‖R‖_∞ ≤ krCR (1+A) ρ^{⌊P/3⌋-1}` (`ρ = √(1 - c) < 1`), and at the opposite endpoint `b'`
(for `A ≤ w`) the trace `‖G(b')‖ ≤ krCP (1+A)²/√w + krCR (1+A) ρ^{⌊P/3⌋-1}`.
With `P = ⌊w/4⌋ ≥ 12`: `√w / P^{1/4} ≤ 2 w^{1/4}` and `ρ^{⌊P/3⌋-1} ≤ ρ^{-3} e^{-(w/12) log(1/ρ)}`. -/
theorem krLong_decomposition {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {P : ℕ} (hP : 12 ≤ P) (M : ℕ) :
    ∃ G R : ℝ → ℂ, Measurable G ∧ Measurable R ∧
      (∀ x, x ∉ Icc 0 w → G x = 0 ∧ R x = 0) ∧
      (∀ z, ((∑ i ∈ Finset.range M, krDens (Icc 0 w) ν f β a' (P + 1 + i) b z : ℝ) : ℂ) =
        G z + R z) ∧
      eVariationOn G univ ≤ ENNReal.ofReal (krCV D K L vlo vhi * (1 + A) *
        (Real.sqrt w / krFourthRoot P + 1)) ∧
      (∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖G x - G y‖ ≤
        (2 * D * (krCV D K L vlo vhi * (1 + A) * (Real.sqrt w / krFourthRoot P + 1))) * |x - y|) ∧
      (∀ x, ‖R x‖ ≤ krCR D K L vlo vhi * (1 + A) * kBVClassRho D vlo vhi ^ (P / 3 - 1)) ∧
      (∀ b', (b' = 0 ∨ b' = w) → b ≠ b' → A ≤ w →
        ‖G b'‖ ≤ krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w +
          krCR D K L vlo vhi * (1 + A) * kBVClassRho D vlo vhi ^ (P / 3 - 1)) := by
  have hw0 := H.hw0
  have hA := H.hA
  have hcc := H.classConsts
  have hC := krC₂_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  have hD0 := H.hD0
  -- choose the per-row decompositions
  have hdec : ∀ i : ℕ, ∃ g r : ℝ → ℂ, Measurable g ∧ Measurable r ∧
      (∀ x, x ∉ Icc 0 w → g x = 0 ∧ r x = 0) ∧
      (∀ z, (krDens (Icc 0 w) ν f β a' (P + 1 + i) b z : ℂ) = g z + r z) ∧
      eVariationOn g univ ≤ ENNReal.ofReal (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) *
        (1 + A) * krVarTerm D vlo vhi w (P + 1 + i)) ∧
      (∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖g x - g y‖ ≤
        (2 * D * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
          krVarTerm D vlo vhi w (P + 1 + i))) * |x - y|) ∧
      (∀ x, ‖r x‖ ≤ Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
        Real.sqrt (3 * krC₂ D K L) * (1 + A) * kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1))) :=
    fun i => krDens_row_decomposition ν H hb (n := P + 1 + i) (by omega)
  choose g r hg hr hs hsum hvar hlip hrem using hdec
  have hV0 : ∀ i, 0 ≤ kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
      krVarTerm D vlo vhi w (P + 1 + i) := fun i =>
    mul_nonneg (mul_nonneg (mul_nonneg hcc.2.2.2.2.le (Real.sqrt_nonneg _)) (by linarith))
      (krVarTerm_nonneg hw0 _)
  obtain ⟨hGm, hRm, hGRs, hGR, hGvar, hGlip, hRsup⟩ :=
    kr_sum_decomposition (w := w) (q := fun i z => krDens (Icc 0 w) ν f β a' (P + 1 + i) b z)
      hg hr hs hsum hV0 hvar hlip hrem M
  -- the variation / Lipschitz sum
  have hVsum : ∑ i ∈ Finset.range M, kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) *
      (1 + A) * krVarTerm D vlo vhi w (P + 1 + i) ≤
      krCV D K L vlo vhi * (1 + A) * (Real.sqrt w / krFourthRoot P + 1) := by
    rw [← Finset.mul_sum]
    have hs := H.sum_krVarTerm_le (by omega : 1 ≤ P) M
    have hq0 : 0 ≤ Real.sqrt w / krFourthRoot P := div_nonneg (Real.sqrt_nonneg _) (krFourthRoot_nonneg _)
    have hr0 : 0 ≤ 2 * Real.sqrt 6 / kBVClassRate D vlo vhi := div_nonneg (by positivity) hcc.2.2.1.le
    have hs' : 16 * Real.sqrt w / krFourthRoot P + 2 * Real.sqrt 6 / kBVClassRate D vlo vhi ≤
        (16 + 2 * Real.sqrt 6 / kBVClassRate D vlo vhi) * (Real.sqrt w / krFourthRoot P + 1) := by
      have : 16 * Real.sqrt w / krFourthRoot P = 16 * (Real.sqrt w / krFourthRoot P) := by ring
      rw [this]
      nlinarith
    calc kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
          ∑ i ∈ Finset.range M, krVarTerm D vlo vhi w (P + 1 + i)
        ≤ kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
          ((16 + 2 * Real.sqrt 6 / kBVClassRate D vlo vhi) *
            (Real.sqrt w / krFourthRoot P + 1)) :=
          mul_le_mul_of_nonneg_left (hs.trans hs')
            (mul_nonneg (mul_nonneg hcc.2.2.2.2.le (Real.sqrt_nonneg _)) (by linarith))
      _ = _ := by unfold krCV; ring
  -- the remainder sum
  have hRsum : ∑ i ∈ Finset.range M, Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
      Real.sqrt (3 * krC₂ D K L) * (1 + A) * kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1)) ≤
      krCR D K L vlo vhi * (1 + A) * kBVClassRho D vlo vhi ^ (P / 3 - 1) := by
    have e : ∀ i ∈ Finset.range M, Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
        Real.sqrt (3 * krC₂ D K L) * (1 + A) * kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1)) =
        (Real.sqrt (2 * D) * kBVClassRemConst D vlo vhi * Real.sqrt (3 * krC₂ D K L) * (1 + A)) *
          kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1) := fun i _ => by ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    have hsum := kr_sum_rho_pow_le hcc.1 hcc.2.1 (by omega : 3 ≤ P) M
    have hpos : 0 < 1 - kBVClassRho D vlo vhi := by linarith [hcc.2.1]
    calc (Real.sqrt (2 * D) * kBVClassRemConst D vlo vhi * Real.sqrt (3 * krC₂ D K L) * (1 + A)) *
          ∑ i ∈ Finset.range M, kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1)
        ≤ (Real.sqrt (2 * D) * kBVClassRemConst D vlo vhi * Real.sqrt (3 * krC₂ D K L) * (1 + A)) *
          (3 * kBVClassRho D vlo vhi ^ (P / 3 - 1) / (1 - kBVClassRho D vlo vhi)) :=
          mul_le_mul_of_nonneg_left hsum
            (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hcc.2.2.2.1.le)
              (Real.sqrt_nonneg _)) (by linarith))
      _ = _ := by unfold krCR; field_simp
  refine ⟨_, _, hGm, hRm, hGRs, hGR, hGvar.trans (ENNReal.ofReal_le_ofReal hVsum), ?_,
    fun x => (hRsup x).trans hRsum, ?_⟩
  · intro x hx y hy
    refine (hGlip x hx y hy).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hVsum (by linarith)) (abs_nonneg _)
  · -- the opposite-endpoint trace
    intro b' hb' hbb hAw
    have hGb : (∑ i ∈ Finset.range M, g i b') =
        ((∑ i ∈ Finset.range M, krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' : ℝ) : ℂ) -
          ∑ i ∈ Finset.range M, r i b' := by
      rw [hGR b']; ring
    have hpin : ∑ i ∈ Finset.range M, krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' ≤
        krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w := by
      refine le_trans ?_ (sum_krDens_bdry_pin_le ν H hAw hb hb' hbb (P + M))
      rw [Finset.sum_range_add]
      have e : ∑ i ∈ Finset.range M, krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' =
          ∑ i ∈ Finset.range M, krDens (Icc 0 w) ν f β a' (P + i + 1) b b' :=
        Finset.sum_congr rfl fun i _ => by rw [show P + 1 + i = P + i + 1 by omega]
      rw [e]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun n _ =>
        krDens_nonneg ν H.hf0 (n + 1) b b')
    have hpin0 : 0 ≤ ∑ i ∈ Finset.range M, krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' :=
      Finset.sum_nonneg fun i _ => krDens_nonneg ν H.hf0 _ _ _
    calc ‖∑ i ∈ Finset.range M, g i b'‖
        ≤ ‖((∑ i ∈ Finset.range M, krDens (Icc 0 w) ν f β a' (P + 1 + i) b b' : ℝ) : ℂ)‖ +
          ‖∑ i ∈ Finset.range M, r i b'‖ := by rw [hGb]; exact norm_sub_le _ _
      _ ≤ krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w +
          krCR D K L vlo vhi * (1 + A) * kBVClassRho D vlo vhi ^ (P / 3 - 1) := by
          refine add_le_add ?_ ((hRsup b').trans hRsum)
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpin0]
          exact hpin

end

end PGM
