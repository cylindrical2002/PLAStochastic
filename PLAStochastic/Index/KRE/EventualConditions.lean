import PLAStochastic.Index.GRE.LogLogTheta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Eventual side conditions for the Model K rank-equispaced height

Along sequences `n → ∞`, `ε → ∞` with `log ε = o(log n)`, the explicit choices
`j = ⌈4 log n / log (72/71)⌉₊` (`jK`) and
`Dn = (n / (9 · 10⁸ Λ j² ε³ log n))^(1/3)` (`DnK`) satisfy every finite side condition of
the Model K bridge eventually (`KRE_eventually`), the upper height expression is
`O(log log n)` (`KRE_UK_le_loglog`), and under RE-LOWER `log ε ≤ D (log n)^(1-η)` the
lower-bound side conditions hold eventually and the lower expression is
`Ω(log log n)` (`KRE_lower_eventually`, `KRE_LoK_ge_loglog`).
-/

namespace PGM

noncomputable section

open Filter Topology

/-! ## The window multiplicity `j = ⌈4 log n / log (72/71)⌉₊` -/

/-- The window multiplicity used for `n` keys. -/
def jK (n : ℕ) : ℕ := ⌈4 * Real.log n / Real.log (72 / 71)⌉₊

theorem log_72_71_pos : 0 < Real.log (72 / 71 : ℝ) := Real.log_pos (by norm_num)

/-- `(71/72)^(jK n) ≤ 1 / n⁴`. -/
theorem pow_jK_le {n : ℕ} (hn : 1 ≤ n) : (71 / 72 : ℝ) ^ jK n ≤ 1 / (n : ℝ) ^ 4 := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := log_72_71_pos
  have ht : 4 * Real.log n / Real.log (72 / 71) ≤ (jK n : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ hc] at ht
  have hexp : Real.exp (-(4 * Real.log n)) = 1 / (n : ℝ) ^ 4 := by
    rw [Real.exp_neg, one_div]
    congr 1
    rw [show (4 : ℝ) * Real.log n = ((4 : ℕ) : ℝ) * Real.log n by norm_num,
      Real.exp_nat_mul, Real.exp_log hN]
  have hlog : Real.log (71 / 72 : ℝ) = -Real.log (72 / 71) := by
    rw [← Real.log_inv]; norm_num
  rw [← hexp, ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), hlog]
  apply Real.exp_le_exp.2
  linarith

/-- The union-bound mass of the window bad event: `(2n+1)² (71/72)^(jK n) ≤ 9 / n²`. -/
theorem windowMass_jK_le {n : ℕ} (hn : 1 ≤ n) :
    ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (71 / 72 : ℝ) ^ jK n ≤ 9 / (n : ℝ) ^ 2 := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hsq : ((2 * n + 1 : ℕ) : ℝ) ^ 2 ≤ 9 * (n : ℝ) ^ 2 := by
    push_cast
    have : 2 * (n : ℝ) + 1 ≤ 3 * n := by linarith
    calc (2 * (n : ℝ) + 1) ^ 2 ≤ (3 * n) ^ 2 := by gcongr
      _ = 9 * (n : ℝ) ^ 2 := by ring
  calc ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (71 / 72 : ℝ) ^ jK n ≤ 9 * (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 4) :=
        mul_le_mul hsq (pow_jK_le hn) (by positivity) (by positivity)
    _ = 9 / (n : ℝ) ^ 2 := by field_simp

theorem one_le_jK {n : ℕ} (hn : 2 ≤ n) : 1 ≤ jK n := by
  have hN : (1 : ℝ) < n := by exact_mod_cast hn
  exact Nat.one_le_ceil_iff.2 (div_pos (mul_pos (by norm_num) (Real.log_pos hN)) log_72_71_pos)

/-- The constant of `jK n ≤ CjK log n`. -/
def CjK : ℝ := 4 / Real.log (72 / 71) + 1

theorem one_le_CjK : 1 ≤ CjK := by
  have := log_72_71_pos
  unfold CjK
  have : 0 ≤ 4 / Real.log (72 / 71) := by positivity
  linarith

/-- `jK n ≤ CjK log n` once `log n ≥ 1`. -/
theorem jK_le {n : ℕ} (hL : 1 ≤ Real.log n) : (jK n : ℝ) ≤ CjK * Real.log n := by
  have hc := log_72_71_pos
  have h0 : 0 ≤ 4 * Real.log n / Real.log (72 / 71) := by positivity
  have h1 : (jK n : ℝ) < 4 * Real.log n / Real.log (72 / 71) + 1 := Nat.ceil_lt_add_one h0
  have h2 : 4 * Real.log n / Real.log (72 / 71) = 4 / Real.log (72 / 71) * Real.log n := by ring
  unfold CjK
  nlinarith

/-! ## The noise/curvature threshold `Dn` and the layer constants -/

/-- The noise/curvature threshold `Dn = (n / (9 · 10⁸ Λ j² ε³ log n))^(1/3)`. -/
def DnK (Λ : ℝ) (n : ℕ) (ε : ℝ) : ℝ :=
  ((n : ℝ) / (9 * 10 ^ 8 * Λ * (jK n : ℝ) ^ 2 * ε ^ 3 * Real.log n)) ^ (1 / 3 : ℝ)

/-- Layer-side noise entry `c₁ = ε² / (409600 log n)`. -/
def c₁K (n : ℕ) (ε : ℝ) : ℝ := ε ^ 2 / (409600 * Real.log n)

/-- Layer-side curvature entry `c₂ = √(ε / (16 Λ))`. -/
def c₂K (Λ ε : ℝ) : ℝ := Real.sqrt (ε / (16 * Λ))

/-- Layer-side span entry `c₃ = 1 / (8 Λ)`. -/
def c₃K (Λ : ℝ) : ℝ := 1 / (8 * Λ)

theorem DnK_nonneg {Λ : ℝ} (hΛ : 0 ≤ Λ) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ DnK Λ n ε := by
  have := Real.log_natCast_nonneg n
  unfold DnK
  positivity

/-- `Dn³ = n / (9 · 10⁸ Λ j² ε³ log n)`. -/
theorem DnK_cube {Λ : ℝ} (hΛ : 0 ≤ Λ) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    DnK Λ n ε ^ 3 = (n : ℝ) / (9 * 10 ^ 8 * Λ * (jK n : ℝ) ^ 2 * ε ^ 3 * Real.log n) := by
  have := Real.log_natCast_nonneg n
  have hb : 0 ≤ (n : ℝ) / (9 * 10 ^ 8 * Λ * (jK n : ℝ) ^ 2 * ε ^ 3 * Real.log n) := by
    positivity
  unfold DnK
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
  norm_num

/-- **N2.** `9 · 10⁸ Λ j² Dn³ ε³ log n ≤ n`. -/
theorem KRE_N2 {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ} {e : ℝ} (hN : 2 ≤ N) (he : 0 < e) :
    9 * 10 ^ 8 * Λ * (jK N : ℝ) ^ 2 * DnK Λ N e ^ 3 * e ^ 3 * Real.log N ≤ N := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hL := Real.log_pos hN1
  have hj : (1 : ℝ) ≤ jK N := by exact_mod_cast one_le_jK hN
  have hX : 0 < 9 * 10 ^ 8 * Λ * (jK N : ℝ) ^ 2 * e ^ 3 * Real.log N := by positivity
  have e1 : 9 * 10 ^ 8 * Λ * (jK N : ℝ) ^ 2 * DnK Λ N e ^ 3 * e ^ 3 * Real.log N =
      (9 * 10 ^ 8 * Λ * (jK N : ℝ) ^ 2 * e ^ 3 * Real.log N) * DnK Λ N e ^ 3 := by ring
  rw [e1, DnK_cube hΛ.le N he.le, mul_div_cancel₀ _ hX.ne']

/-- **N1.** `16 Λ Dn³ ε³ log n ≤ n`. -/
theorem KRE_N1 {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ} {e : ℝ} (hN : 2 ≤ N) (he : 0 < e) :
    16 * Λ * DnK Λ N e ^ 3 * e ^ 3 * Real.log N ≤ N := by
  have hL := Real.log_natCast_nonneg N
  have hj : (1 : ℝ) ≤ jK N := by exact_mod_cast one_le_jK hN
  have hD := DnK_nonneg hΛ.le N he.le
  have h16 : (16 : ℝ) ≤ 9 * 10 ^ 8 * (jK N : ℝ) ^ 2 := by nlinarith
  have hY : 0 ≤ Λ * DnK Λ N e ^ 3 * e ^ 3 * Real.log N := by positivity
  calc 16 * Λ * DnK Λ N e ^ 3 * e ^ 3 * Real.log N =
        16 * (Λ * DnK Λ N e ^ 3 * e ^ 3 * Real.log N) := by ring
    _ ≤ 9 * 10 ^ 8 * (jK N : ℝ) ^ 2 * (Λ * DnK Λ N e ^ 3 * e ^ 3 * Real.log N) :=
        mul_le_mul_of_nonneg_right h16 hY
    _ = 9 * 10 ^ 8 * Λ * (jK N : ℝ) ^ 2 * DnK Λ N e ^ 3 * e ^ 3 * Real.log N := by ring
    _ ≤ N := KRE_N2 hΛ hN he

/-- `(ε Dn)³ = n / (9 · 10⁸ Λ j² log n)`: the product `ε Dn` does not depend on `ε`. -/
theorem mul_DnK_cube {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ} {e : ℝ} (hN : 2 ≤ N) (he : 0 < e) :
    (e * DnK Λ N e) ^ 3 = (N : ℝ) / (9 * 10 ^ 8 * Λ * (jK N : ℝ) ^ 2 * Real.log N) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hL := Real.log_pos hN1
  have hj : (1 : ℝ) ≤ jK N := by exact_mod_cast one_le_jK hN
  rw [mul_pow, DnK_cube hΛ.le N he.le]
  have : (0 : ℝ) < jK N := by linarith
  field_simp

/-- `A ≤ ε Dn` whenever `A³ · 9 · 10⁸ Λ j² log n ≤ n`. -/
theorem le_mul_DnK {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ} {e A : ℝ} (hN : 2 ≤ N) (he : 0 < e)
    (h : A ^ 3 * (9 * 10 ^ 8 * Λ * (jK N : ℝ) ^ 2 * Real.log N) ≤ N) :
    A ≤ e * DnK Λ N e := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hL := Real.log_pos hN1
  have hj : (1 : ℝ) ≤ jK N := by exact_mod_cast one_le_jK hN
  have hX : 0 < 9 * 10 ^ 8 * Λ * (jK N : ℝ) ^ 2 * Real.log N := by positivity
  have hD := DnK_nonneg hΛ.le N he.le
  apply le_of_pow_le_pow_left₀ three_ne_zero (by positivity)
  rw [mul_DnK_cube hΛ hN he, le_div_iff₀ hX]
  exact h

/-! ## The curvature-regime conditions for fixed parameters -/

/-- The polylog constant of the conditions `C1`, `C2`, `R1`. -/
def KpolyK (Λ : ℝ) : ℝ := 819200 ^ 3 * (9 * 10 ^ 8) * Λ * CjK ^ 2

/-- The polylog constant of the condition `R2`. -/
def KpolyK₂ (Λ : ℝ) : ℝ := 819200 ^ 5 * (9 * 10 ^ 8) ^ 2 * Λ * CjK ^ 4

/-- `819200 log n ≤ ε Dn` once `KpolyK Λ (log n)⁶ ≤ n`. -/
theorem KRE_mul_DnK_ge {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ} {e : ℝ} (hN : 2 ≤ N) (he : 0 < e)
    (hL1 : 1 ≤ Real.log N) (hpoly : KpolyK Λ * Real.log N ^ 6 ≤ N) :
    819200 * Real.log N ≤ e * DnK Λ N e := by
  apply le_mul_DnK hΛ hN he
  have hj := jK_le hL1
  have hj0 : (0 : ℝ) ≤ jK N := Nat.cast_nonneg _
  have hL0 : 0 ≤ Real.log N := by linarith
  calc (819200 * Real.log N) ^ 3 * (9 * 10 ^ 8 * Λ * (jK N : ℝ) ^ 2 * Real.log N) ≤
        (819200 * Real.log N) ^ 3 * (9 * 10 ^ 8 * Λ * (CjK * Real.log N) ^ 2 * Real.log N) := by
        gcongr
    _ = KpolyK Λ * Real.log N ^ 6 := by unfold KpolyK; ring
    _ ≤ N := hpoly

/-- **C1.** `640 log n ≤ ε Dn`. -/
theorem KRE_C1 {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ} {e : ℝ} (hN : 2 ≤ N) (he : 0 < e)
    (hL1 : 1 ≤ Real.log N) (hpoly : KpolyK Λ * Real.log N ^ 6 ≤ N) :
    640 * Real.log N ≤ e * DnK Λ N e := by
  have := KRE_mul_DnK_ge hΛ hN he hL1 hpoly
  linarith

/-- **C2.** `8 Λ log n ≤ n`. -/
theorem KRE_C2 {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ} (hL1 : 1 ≤ Real.log N)
    (hpoly : KpolyK Λ * Real.log N ^ 6 ≤ N) : 8 * Λ * Real.log N ≤ N := by
  have h1 : Real.log N ≤ Real.log N ^ 6 := le_self_pow₀ hL1 (by norm_num)
  have hC : 1 ≤ CjK ^ 2 := one_le_pow₀ one_le_CjK
  have h2 : 8 * Λ ≤ KpolyK Λ := by
    unfold KpolyK
    nlinarith
  have h3 : 0 ≤ Real.log N := by linarith
  have h4 : 0 ≤ KpolyK Λ := by linarith
  calc 8 * Λ * Real.log N ≤ KpolyK Λ * Real.log N ^ 6 := by gcongr
    _ ≤ N := hpoly

/-- **R1.** `1 ≤ (c₁ / 2) Dn`. -/
theorem KRE_R1 {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ} {e : ℝ} (hN : 2 ≤ N) (he : 1 ≤ e)
    (hL1 : 1 ≤ Real.log N) (hpoly : KpolyK Λ * Real.log N ^ 6 ≤ N) :
    1 ≤ c₁K N e / 2 * DnK Λ N e := by
  have he0 : 0 < e := by linarith
  have h := KRE_mul_DnK_ge hΛ hN he0 hL1 hpoly
  have hD := DnK_nonneg hΛ.le N he0.le
  have hL0 : 0 < Real.log N := by linarith
  have e1 : c₁K N e / 2 * DnK Λ N e = e * (e * DnK Λ N e) / (819200 * Real.log N) := by
    unfold c₁K; field_simp; ring
  rw [e1, le_div_iff₀ (by positivity), one_mul]
  have : e * DnK Λ N e ≤ e * (e * DnK Λ N e) := le_mul_of_one_le_left (by positivity) he
  linarith

/-- `(c₂ / 2)² = ε / (64 Λ)`. -/
theorem c₂K_half_sq {Λ : ℝ} (hΛ : 0 < Λ) {e : ℝ} (he : 0 ≤ e) :
    (c₂K Λ e / 2) ^ 2 = e / (64 * Λ) := by
  rw [div_pow, c₂K, Real.sq_sqrt (by positivity)]
  field_simp
  ring

/-- **R2.** `64 (c₂ / 2)² n ≤ (c₁ / 2)⁵ Dn⁶`. -/
theorem KRE_R2 {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ} {e : ℝ} (hN : 2 ≤ N) (he : 1 ≤ e)
    (hL1 : 1 ≤ Real.log N) (hpoly : KpolyK₂ Λ * Real.log N ^ 11 ≤ N) :
    64 * (c₂K Λ e / 2) ^ 2 * N ≤ (c₁K N e / 2) ^ 5 * DnK Λ N e ^ 6 := by
  have he0 : 0 < e := by linarith
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hL0 : 0 < Real.log N := by linarith
  have hj1 : (1 : ℝ) ≤ jK N := by exact_mod_cast one_le_jK hN
  have hj0 : (0 : ℝ) < jK N := by linarith
  have hj := jK_le hL1
  set L := Real.log N with hLdef
  set j : ℝ := (jK N : ℝ) with hjdef
  have hH : 819200 ^ 5 * (9 * 10 ^ 8) ^ 2 * Λ * j ^ 4 * L ^ 7 ≤ e ^ 3 * N := by
    have he3 : 1 ≤ e ^ 3 := one_le_pow₀ he
    calc 819200 ^ 5 * (9 * 10 ^ 8) ^ 2 * Λ * j ^ 4 * L ^ 7 ≤
          819200 ^ 5 * (9 * 10 ^ 8) ^ 2 * Λ * (CjK * L) ^ 4 * L ^ 7 := by gcongr
      _ = KpolyK₂ Λ * L ^ 11 := by unfold KpolyK₂; ring
      _ ≤ N := hpoly
      _ = 1 * N := (one_mul _).symm
      _ ≤ e ^ 3 * N := by gcongr
  have hl : 64 * (c₂K Λ e / 2) ^ 2 * N = e * N / Λ := by
    rw [c₂K_half_sq hΛ he0.le]; field_simp
  have hr : (c₁K N e / 2) ^ 5 * DnK Λ N e ^ 6 =
      e ^ 4 * (N : ℝ) ^ 2 / (819200 ^ 5 * (9 * 10 ^ 8) ^ 2 * Λ ^ 2 * j ^ 4 * L ^ 7) := by
    rw [show DnK Λ N e ^ 6 = (DnK Λ N e ^ 3) ^ 2 by ring, DnK_cube hΛ.le N he0.le]
    unfold c₁K
    rw [← hLdef, ← hjdef]
    field_simp
    ring
  rw [hl, hr, div_le_div_iff₀ hΛ (by positivity)]
  calc e * N * (819200 ^ 5 * (9 * 10 ^ 8) ^ 2 * Λ ^ 2 * j ^ 4 * L ^ 7) =
        (819200 ^ 5 * (9 * 10 ^ 8) ^ 2 * Λ * j ^ 4 * L ^ 7) * (e * N * Λ) := by ring
    _ ≤ (e ^ 3 * N) * (e * N * Λ) := mul_le_mul_of_nonneg_right hH (by positivity)
    _ = e ^ 4 * (N : ℝ) ^ 2 * Λ := by ring

/-! ## The height expressions -/

/-- The upper height expression of the Model K bridge at concentration level `t`. -/
def UK (Λ : ℝ) (n : ℕ) (ε : ℝ) (t : ℕ) : ℝ :=
  Real.logb 2 (Real.log n / Real.log (ε ^ 2 / (4 * 514))) +
    Real.logb 2 (2 * (514 * (4 * ((t : ℝ) + 1) / (aRE / 4)) + ((t : ℝ) + 1))) +
    Real.logb 2 (Real.log n) +
    Real.logb 2 (max (3 * max 1 (16 / (c₂K Λ ε / 2) ^ 2)) (4 / (c₃K Λ / 2)) + 1) + 8

/-- The lower height expression of the Model K bridge. -/
def LoK (n : ℕ) (ε : ℝ) : ℝ :=
  Real.logb 2 (Real.log n / (2 * Real.log (2 / (aRE / 4) * ε ^ 2)))

/-- The constant inside the second logarithm of `UK`. -/
def KUK : ℝ := 2 * (8224 / aRE + 1) * (4 / cRE + 2)

theorem one_le_KUK : 1 ≤ KUK := by
  have ha := aRE_pos
  have hc := cRE_pos
  have h1 : 0 ≤ 8224 / aRE := by positivity
  have h2 : 0 ≤ 4 / cRE := by positivity
  unfold KUK
  have h3 : 1 ≤ 8224 / aRE + 1 := by linarith
  have h4 : 2 ≤ 4 / cRE + 2 := by linarith
  calc (1 : ℝ) ≤ 2 * 1 * 2 := by norm_num
    _ ≤ 2 * (8224 / aRE + 1) * (4 / cRE + 2) := by gcongr

/-- The bound for the argument of the fourth logarithm of `UK`. -/
def MUK (Λ : ℝ) : ℝ := max (3 * max 1 (1024 * Λ)) (64 * Λ) + 1

/-- The constant of the upper `log log n` bound. -/
def CUK (Λ : ℝ) : ℝ :=
  (2 + Real.log KUK) / Real.log 2 + (Real.logb 2 (MUK Λ) + 8) + 1 / Real.log 2

/-- `UK Λ n ε (tRE n) ≤ CUK Λ · log log n` for fixed parameters. -/
theorem UK_tRE_le {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ} {e : ℝ} (hN : 1 ≤ N)
    (hLL : 1 ≤ Real.log (Real.log N)) (he : 1 ≤ e) (hq : Real.exp 1 ≤ e ^ 2 / (4 * 514)) :
    UK Λ N e (tRE N) ≤ CUK Λ * Real.log (Real.log N) := by
  set L := Real.log N
  have hL0 := log_pos_of_loglog hN hLL
  have hL1 : 1 ≤ L := by
    have := Real.log_le_sub_one_of_pos hL0
    linarith
  have ha := aRE_pos
  have hc := cRE_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he0 : 0 < e := by linarith
  have hlogq : 1 ≤ Real.log (e ^ 2 / (4 * 514)) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hq
  have hT1 : Real.logb 2 (L / Real.log (e ^ 2 / (4 * 514))) ≤ Real.logb 2 L :=
    Real.logb_le_logb_of_le (by norm_num) (div_pos hL0 (by linarith)) (div_le_self hL0.le hlogq)
  have ht := tRE_succ_le hL1
  have ht0 : (0 : ℝ) ≤ tRE N := Nat.cast_nonneg _
  have he2 : 2 * (514 * (4 * ((tRE N : ℝ) + 1) / (aRE / 4)) + ((tRE N : ℝ) + 1)) =
      2 * (8224 / aRE + 1) * ((tRE N : ℝ) + 1) := by field_simp; ring
  have hT2 : Real.logb 2 (2 * (514 * (4 * ((tRE N : ℝ) + 1) / (aRE / 4)) + ((tRE N : ℝ) + 1))) ≤
      Real.logb 2 (KUK * L) := by
    rw [he2]
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    have : 2 * (8224 / aRE + 1) * ((tRE N : ℝ) + 1) ≤
        2 * (8224 / aRE + 1) * ((4 / cRE + 2) * L) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    calc _ ≤ _ := this
      _ = KUK * L := by unfold KUK; ring
  have hc2 : 16 / (c₂K Λ e / 2) ^ 2 ≤ 1024 * Λ := by
    rw [c₂K_half_sq hΛ he0.le, show 16 / (e / (64 * Λ)) = 1024 * Λ / e by field_simp; ring]
    exact div_le_self (by positivity) he
  have hc3 : 4 / (c₃K Λ / 2) = 64 * Λ := by unfold c₃K; field_simp; ring
  have hT4 : Real.logb 2 (max (3 * max 1 (16 / (c₂K Λ e / 2) ^ 2)) (4 / (c₃K Λ / 2)) + 1) ≤
      Real.logb 2 (MUK Λ) := by
    apply Real.logb_le_logb_of_le (by norm_num)
    · have : 3 ≤ 3 * max 1 (16 / (c₂K Λ e / 2) ^ 2) := by
        have := le_max_left 1 (16 / (c₂K Λ e / 2) ^ 2); linarith
      have := le_max_left (3 * max 1 (16 / (c₂K Λ e / 2) ^ 2)) (4 / (c₃K Λ / 2))
      linarith
    · unfold MUK
      rw [hc3]
      gcongr
  have hM : 0 ≤ Real.logb 2 (MUK Λ) := by
    apply Real.logb_nonneg (by norm_num)
    unfold MUK
    have : 3 ≤ 3 * max 1 (1024 * Λ) := by have := le_max_left 1 (1024 * Λ); linarith
    have := le_max_left (3 * max 1 (1024 * Λ)) (64 * Λ)
    linarith
  have hsum := logb_sum_le_mul_log one_le_KUK (by linarith : 0 ≤ Real.logb 2 (MUK Λ) + 8)
    hL0 hLL
  have hT3 : Real.logb 2 L = 1 / Real.log 2 * Real.log L := by
    rw [Real.logb]; ring
  unfold UK CUK
  have e3 : ((2 + Real.log KUK) / Real.log 2 + (Real.logb 2 (MUK Λ) + 8) + 1 / Real.log 2) *
      Real.log L = ((2 + Real.log KUK) / Real.log 2 + (Real.logb 2 (MUK Λ) + 8)) * Real.log L +
      1 / Real.log 2 * Real.log L := by ring
  rw [e3]
  linarith

/-- `LoK n ε ≥ (η / (2 log 2)) log log n` for fixed parameters. -/
theorem LoK_ge {N : ℕ} {e η D₁ : ℝ} (hN : 1 ≤ N) (hη : 0 < η) (hD₁ : 0 < D₁) (he : 1 ≤ e)
    (hLL : 1 ≤ Real.log (Real.log N))
    (hLL2 : 2 * Real.log (2 * D₁) / η ≤ Real.log (Real.log N))
    (hD' : Real.log (2 / (aRE / 4) * e ^ 2) ≤ D₁ * Real.log N ^ (1 - η)) :
    η / (2 * Real.log 2) * Real.log (Real.log N) ≤ LoK N e := by
  set L := Real.log N
  have hL0 := log_pos_of_loglog hN hLL
  have hL1 : 1 < L := by
    have := Real.log_le_sub_one_of_pos hL0
    linarith
  have ha := aRE_pos
  have ha1 := aRE_le_one
  have h8 : 8 ≤ 2 / (aRE / 4) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have he2 : 1 ≤ e ^ 2 := one_le_pow₀ he
  have hD'pos : 0 < Real.log (2 / (aRE / 4) * e ^ 2) := by
    apply Real.log_pos
    calc (1 : ℝ) < 8 * 1 := by norm_num
      _ ≤ 2 / (aRE / 4) * e ^ 2 := mul_le_mul h8 he2 (by norm_num) (by positivity)
  have hr := logb_ratio_ge hD₁ hD'pos hL1 hD'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk : 2 * Real.log (2 * D₁) ≤ Real.log L * η := (div_le_iff₀ hη).1 hLL2
  have hdiff : η / Real.log 2 * Real.log L - Real.log (2 * D₁) / Real.log 2 -
      η / (2 * Real.log 2) * Real.log L =
      (η * Real.log L - 2 * Real.log (2 * D₁)) / (2 * Real.log 2) := by
    field_simp; ring
  have hnn : 0 ≤ (η * Real.log L - 2 * Real.log (2 * D₁)) / (2 * Real.log 2) :=
    div_nonneg (by linarith) (by positivity)
  unfold LoK
  linarith

/-! ## The lower-bound side conditions for fixed parameters -/

/-- **L1.** `n^(1/4) ≤ Dn` once `ε ≤ n^(1/24)` and `9 · 10⁸ Λ CjK² (log n)³ ≤ n^(1/8)`. -/
theorem KRE_L1 {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ} {e : ℝ} (hN : 2 ≤ N) (he : 1 ≤ e)
    (hL1 : 1 ≤ Real.log N) (heN : e ≤ (N : ℝ) ^ (1 / 24 : ℝ))
    (hpoly : 9 * 10 ^ 8 * Λ * CjK ^ 2 * Real.log N ^ 3 ≤ (N : ℝ) ^ (1 / 8 : ℝ)) :
    Real.sqrt (Real.sqrt N) ≤ DnK Λ N e := by
  have he0 : 0 < e := by linarith
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hL0 : 0 < Real.log N := by linarith
  have hj1 : (1 : ℝ) ≤ jK N := by exact_mod_cast one_le_jK hN
  have hj := jK_le hL1
  have hj0 : (0 : ℝ) ≤ jK N := by linarith
  have he3 : e ^ 3 ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by
    calc e ^ 3 ≤ ((N : ℝ) ^ (1 / 24 : ℝ)) ^ 3 := pow_le_pow_left₀ he0.le heN 3
      _ = (N : ℝ) ^ (1 / 8 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hX : 9 * 10 ^ 8 * Λ * (jK N : ℝ) ^ 2 * e ^ 3 * Real.log N ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    calc 9 * 10 ^ 8 * Λ * (jK N : ℝ) ^ 2 * e ^ 3 * Real.log N ≤
          9 * 10 ^ 8 * Λ * (CjK * Real.log N) ^ 2 * e ^ 3 * Real.log N := by gcongr
      _ = (9 * 10 ^ 8 * Λ * CjK ^ 2 * Real.log N ^ 3) * e ^ 3 := by ring
      _ ≤ (N : ℝ) ^ (1 / 8 : ℝ) * (N : ℝ) ^ (1 / 8 : ℝ) :=
          mul_le_mul hpoly he3 (by positivity) (by positivity)
      _ = (N : ℝ) ^ (1 / 4 : ℝ) := by rw [← Real.rpow_add hN0]; norm_num
  have hX0 : 0 < 9 * 10 ^ 8 * Λ * (jK N : ℝ) ^ 2 * e ^ 3 * Real.log N := by positivity
  have hs : Real.sqrt (Real.sqrt N) = (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]; norm_num
  rw [hs]
  apply le_of_pow_le_pow_left₀ three_ne_zero (DnK_nonneg hΛ.le N he0.le)
  rw [DnK_cube hΛ.le N he0.le, le_div_iff₀ hX0]
  calc ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 3 * (9 * 10 ^ 8 * Λ * (jK N : ℝ) ^ 2 * e ^ 3 * Real.log N) ≤
        ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 3 * (N : ℝ) ^ (1 / 4 : ℝ) := by gcongr
    _ = (N : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]; norm_num

/-- The constant of the condition `L2`. -/
def KL2 : ℝ := 16 * (4 / cRE + 2) / aRE

/-- **L2.** `4 t / (aRE / 4) ≤ √n` for `t = tRE n`. -/
theorem KRE_L2 {N : ℕ} (hL1 : 1 ≤ Real.log N) (hpoly : KL2 * Real.log N ≤ Real.sqrt N) :
    4 * (tRE N : ℝ) / (aRE / 4) ≤ Real.sqrt N := by
  have ha := aRE_pos
  have ht := tRE_succ_le hL1
  calc 4 * (tRE N : ℝ) / (aRE / 4) = 16 / aRE * (tRE N : ℝ) := by field_simp; ring
    _ ≤ 16 / aRE * ((4 / cRE + 2) * Real.log N) := by gcongr; linarith
    _ = KL2 * Real.log N := by unfold KL2; ring
    _ ≤ _ := hpoly

/-! ## Eventual bounds along `n → ∞` -/

/-- `K (log x)^m ≤ x^s` for all large `x`. -/
theorem eventually_mul_log_pow_le_rpow (K : ℝ) (m : ℕ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, K * Real.log x ^ m ≤ x ^ s := by
  have h := (isLittleO_log_rpow_rpow_atTop (m : ℝ) hs).bound
    (show (0 : ℝ) < 1 / (|K| + 1) by positivity)
  filter_upwards [h, eventually_ge_atTop 1] with x hx hx1
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.rpow_natCast] at hx
  have hK : 0 < |K| + 1 := by positivity
  calc K * Real.log x ^ m ≤ |K| * Real.log x ^ m :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    _ ≤ (|K| + 1) * Real.log x ^ m := by gcongr; linarith
    _ ≤ (|K| + 1) * (1 / (|K| + 1) * x ^ s) := by gcongr
    _ = x ^ s := by field_simp

/-- From `log ε / log n → 0`: eventually `ε ≤ n^δ`, for every fixed `δ > 0`. -/
theorem eventually_le_rpow_of_logRatio {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0)) {δ : ℝ}
    (hδ : 0 < δ) : ∀ᶠ k in atTop, ε k ≤ (n k : ℝ) ^ δ := by
  filter_upwards [hn.eventually_ge_atTop 2, hε.eventually_ge_atTop 1,
    hεn.eventually (eventually_le_nhds hδ)] with k h1 h2 h3
  have hN : (0 : ℝ) < n k := by linarith
  have hL : 0 < Real.log (n k) := Real.log_pos (by linarith)
  have h4 : Real.log (ε k) ≤ δ * Real.log (n k) := (div_le_iff₀ hL).1 h3
  rw [← Real.log_le_log_iff (by linarith) (Real.rpow_pos_of_pos hN _), Real.log_rpow hN]
  exact h4

/-- RE-LOWER `log ε ≤ D (log n)^(1-η)` implies `log ε / log n → 0`. -/
theorem tendsto_logRatio_of_RE {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    {η D : ℝ} (hη0 : 0 < η)
    (hRE : ∀ᶠ k in atTop, Real.log (ε k) ≤ D * Real.log (n k) ^ (1 - η)) :
    Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0) := by
  have hL : Tendsto (fun k => Real.log (n k)) atTop atTop := Real.tendsto_log_atTop.comp hn
  have hup : Tendsto (fun k => D * Real.log (n k) ^ (-η)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hη0).comp hL).const_mul D
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hε.eventually_ge_atTop 1, hn.eventually_ge_atTop 1] with k h1 h2
    exact div_nonneg (Real.log_nonneg h1) (Real.log_nonneg h2)
  · filter_upwards [hRE, hL.eventually_gt_atTop 0] with k h1 h2
    have e1 : D * Real.log (n k) ^ (-η) = D * Real.log (n k) ^ (1 - η) / Real.log (n k) := by
      rw [mul_div_assoc, ← Real.rpow_sub_one h2.ne']
      congr 2
      ring
    rw [e1]
    exact div_le_div_of_nonneg_right h1 h2.le

/-- `exp 1 ≤ ε² / (4 · 514)` once `1 ≤ ε` and `4 · 514 · exp 1 ≤ ε`. -/
theorem exp_one_le_sq_div {e : ℝ} (he : 1 ≤ e) (he' : 4 * 514 * Real.exp 1 ≤ e) :
    Real.exp 1 ≤ e ^ 2 / (4 * 514) := by
  rw [le_div_iff₀ (by norm_num)]
  have : e ≤ e ^ 2 := by nlinarith
  linarith

/-- **The upper-regime side conditions** `E1–E4`, `N1`, `N2`, `C1`, `C2`, `R1–R3` hold
eventually along `n → ∞`, `ε → ∞`, `log ε = o(log n)`. -/
theorem KRE_eventually {Λ : ℝ} (hΛ : 0 < Λ) {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0)) :
    ∀ᶠ k in atTop,
      160000 ≤ n k ∧ epsZero 1 18 ≤ ε k / 2 ∧ 1 ≤ jK (n k) ∧ 1 ≤ ε k ∧
      16 * Λ * DnK Λ (n k) (ε k) ^ 3 * ε k ^ 3 * Real.log (n k) ≤ n k ∧
      9 * 10 ^ 8 * Λ * (jK (n k) : ℝ) ^ 2 * DnK Λ (n k) (ε k) ^ 3 * ε k ^ 3 *
        Real.log (n k) ≤ n k ∧
      640 * Real.log (n k) ≤ ε k * DnK Λ (n k) (ε k) ∧
      8 * Λ * Real.log (n k) ≤ n k ∧
      1 ≤ c₁K (n k) (ε k) / 2 * DnK Λ (n k) (ε k) ∧
      64 * (c₂K Λ (ε k) / 2) ^ 2 * n k ≤ (c₁K (n k) (ε k) / 2) ^ 5 * DnK Λ (n k) (ε k) ^ 6 ∧
      1 < ε k ^ 2 / (4 * 514) ∧ ε k ^ 2 / (4 * 514) ≤ n k := by
  have hL : Tendsto (fun k => Real.log (n k)) atTop atTop := Real.tendsto_log_atTop.comp hn
  filter_upwards [hn.eventually_ge_atTop 160000, hL.eventually_ge_atTop 1,
    hε.eventually_ge_atTop (max (2 * epsZero 1 18) (max 1 (4 * 514 * Real.exp 1))),
    hn.eventually (eventually_mul_log_pow_le_rpow (KpolyK Λ) 6 one_pos),
    hn.eventually (eventually_mul_log_pow_le_rpow (KpolyK₂ Λ) 11 one_pos),
    eventually_le_rpow_of_logRatio hn hε hεn (by norm_num : (0 : ℝ) < 1 / 2)]
    with k h1 h2 h3 h4 h5 h6
  rw [Real.rpow_one] at h4 h5
  have hN : 160000 ≤ n k := by exact_mod_cast h1
  have hN2 : 2 ≤ n k := by omega
  have he1 : 1 ≤ ε k := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h3)
  have he0 : 0 < ε k := by linarith
  have hez : 2 * epsZero 1 18 ≤ ε k := le_trans (le_max_left _ _) h3
  have heq : 4 * 514 * Real.exp 1 ≤ ε k :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h3)
  have hq := exp_one_le_sq_div he1 heq
  have hexp : 1 < Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hN0 : (0 : ℝ) ≤ n k := Nat.cast_nonneg _
  have hsq : ε k ^ 2 ≤ n k := by
    calc ε k ^ 2 ≤ ((n k : ℝ) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ he0.le h6 2
      _ = n k := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
  refine ⟨hN, by linarith, one_le_jK hN2, he1, KRE_N1 hΛ hN2 he0, KRE_N2 hΛ hN2 he0,
    KRE_C1 hΛ hN2 he0 h2 h4, KRE_C2 hΛ h2 h4, KRE_R1 hΛ hN2 he1 h2 h4,
    KRE_R2 hΛ hN2 he1 h2 h5, by linarith, ?_⟩
  have : ε k ^ 2 / (4 * 514) ≤ ε k ^ 2 := div_le_self (by positivity) (by norm_num)
  linarith

/-- **Upper height expression.**  Along `n → ∞`, `ε → ∞`, `UK Λ n ε (tRE n) = O(log log n)`. -/
theorem KRE_UK_le_loglog {Λ : ℝ} (hΛ : 0 < Λ) {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop) :
    ∃ C : ℝ, ∀ᶠ k in atTop,
      UK Λ (n k) (ε k) (tRE (n k)) ≤ C * Real.log (Real.log (n k)) := by
  refine ⟨CUK Λ, ?_⟩
  have hL : Tendsto (fun k => Real.log (n k)) atTop atTop := Real.tendsto_log_atTop.comp hn
  have hLL : Tendsto (fun k => Real.log (Real.log (n k))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  filter_upwards [hn.eventually_ge_atTop 1, hLL.eventually_ge_atTop 1,
    hε.eventually_ge_atTop (max 1 (4 * 514 * Real.exp 1))] with k h1 h2 h3
  have hn1 : 1 ≤ n k := by exact_mod_cast h1
  have he1 : 1 ≤ ε k := le_trans (le_max_left _ _) h3
  exact UK_tRE_le hΛ hn1 h2 he1 (exp_one_le_sq_div he1 (le_trans (le_max_right _ _) h3))

/-- **The lower-regime side conditions** `L1`, `L2` hold eventually under RE-LOWER. -/
theorem KRE_lower_eventually {Λ : ℝ} (hΛ : 0 < Λ) {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    {η D₀ : ℝ} (hη0 : 0 < η)
    (hRE : ∀ᶠ k in atTop, Real.log (ε k) ≤ D₀ * Real.log (n k) ^ (1 - η)) :
    ∀ᶠ k in atTop,
      Real.sqrt (Real.sqrt (n k)) ≤ DnK Λ (n k) (ε k) ∧
        4 * (tRE (n k) : ℝ) / (aRE / 4) ≤ Real.sqrt (n k) := by
  have hεn := tendsto_logRatio_of_RE hn hε hη0 hRE
  have hL : Tendsto (fun k => Real.log (n k)) atTop atTop := Real.tendsto_log_atTop.comp hn
  filter_upwards [hn.eventually_ge_atTop 2, hL.eventually_ge_atTop 1,
    hε.eventually_ge_atTop 1,
    eventually_le_rpow_of_logRatio hn hε hεn (by norm_num : (0 : ℝ) < 1 / 24),
    hn.eventually (eventually_mul_log_pow_le_rpow (9 * 10 ^ 8 * Λ * CjK ^ 2) 3
      (by norm_num : (0 : ℝ) < 1 / 8)),
    hn.eventually (eventually_mul_log_pow_le_rpow KL2 1 (by norm_num : (0 : ℝ) < 1 / 2))]
    with k h1 h2 h3 h4 h5 h6
  have hN2 : 2 ≤ n k := by exact_mod_cast h1
  rw [pow_one, ← Real.sqrt_eq_rpow] at h6
  exact ⟨KRE_L1 hΛ hN2 h3 h2 h4 h5, KRE_L2 h2 h6⟩

/-- **Lower height expression.**  Under RE-LOWER, `LoK n ε = Ω(log log n)`. -/
theorem KRE_LoK_ge_loglog {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    {η D₀ : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hD₀ : 0 < D₀)
    (hRE : ∀ᶠ k in atTop, Real.log (ε k) ≤ D₀ * Real.log (n k) ^ (1 - η)) :
    ∃ c > 0, ∀ᶠ k in atTop, c * Real.log (Real.log (n k)) ≤ LoK (n k) (ε k) := by
  have ha := aRE_pos
  have hL : Tendsto (fun k => Real.log (n k)) atTop atTop := Real.tendsto_log_atTop.comp hn
  have hLL : Tendsto (fun k => Real.log (Real.log (n k))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hpow : Tendsto (fun k => Real.log (n k) ^ (1 - η)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hL
  refine ⟨η / (2 * Real.log 2), by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity,
    ?_⟩
  filter_upwards [hn.eventually_ge_atTop 1, hLL.eventually_ge_atTop 1,
    hLL.eventually_ge_atTop (2 * Real.log (2 * (3 * D₀)) / η),
    hε.eventually_ge_atTop 1, hRE,
    hpow.eventually_ge_atTop (|Real.log (2 / (aRE / 4))| / D₀)] with k h1 h2 h3 h4 h5 h6
  have hn1 : 1 ≤ n k := by exact_mod_cast h1
  have he0 : 0 < ε k := by linarith
  have hD' : Real.log (2 / (aRE / 4) * ε k ^ 2) ≤ 3 * D₀ * Real.log (n k) ^ (1 - η) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have h7 : Real.log (2 / (aRE / 4)) ≤ D₀ * Real.log (n k) ^ (1 - η) := by
      have := (div_le_iff₀ hD₀).1 h6
      linarith [le_abs_self (Real.log (2 / (aRE / 4)))]
    push_cast
    linarith
  exact LoK_ge hn1 hη0 (by positivity) h4 h2 h3 hD'

end

end PGM
