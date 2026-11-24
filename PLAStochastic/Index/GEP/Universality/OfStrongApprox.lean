import PLAStochastic.Index.GEP.Universality.MainTerm

/-!
# WP5: `(SA) + Brownian side ⟹ (U)`

Blueprint `kmt-blueprint/main.tex` Theorem 8.7 and the deduction of `GEPUniversality`.
The rate obtained here is `β = 17/32` (the blueprint's `5/8` needs the sharper horizon
`n ≍ ε² log ε`; here `n ≤ ε^{5/2}` is used to keep the exponent bookkeeping short — any
`β > 1/2` is what `GEPUniversality` asks for).

* `single_law_bound`: for one law of the class and every `ε` above an explicit threshold,
  `d_γ(rawLaw ε ν, 𝒯) ≤ K ε^{-17/32}`, with `γ = min(r', θτ)/16` depending only on
  `(vlo, vhi, θτ)`;
* `universality_of_SA_lifetime`: `StrongApproxClass` for every class, together with a
  `LifetimeSide`, gives `GEPUniversality`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-! ## Elementary asymptotics -/

theorem log_le_mul_rpow {x : ℝ} (hx : 0 ≤ x) {a : ℝ} (ha : 0 < a) :
    Real.log x ≤ (1 / a) * x ^ a := by
  have := Real.log_le_rpow_div hx ha
  rw [div_eq_inv_mul] at this
  simpa [one_div] using this

theorem rpow_neg_one_le {ε : ℝ} (hε : 1 ≤ ε) : ε⁻¹ ≤ ε ^ (-(17 / 32 : ℝ)) := by
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hε (by norm_num)

theorem rpow_neg_two_le {ε : ℝ} (hε : 1 ≤ ε) : (ε ^ 2)⁻¹ ≤ ε ^ (-(17 / 32 : ℝ)) := by
  have h1 : (ε ^ 2)⁻¹ ≤ ε⁻¹ := by
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    nlinarith
  exact h1.trans (rpow_neg_one_le hε)

/-! ## Constants -/

/-- `γ = min(r', θτ) / 16`. -/
def saGamma (vlo vhi θτ : ℝ) : ℝ := min (rPrime vlo vhi) θτ / 16

/-- `L = 1/(8γ)`, so that `γ L = 1/8`. -/
def saL (vlo vhi θτ : ℝ) : ℝ := 1 / (8 * saGamma vlo vhi θτ)

/-- The `χ` constant: `χ ≤ K_χ n^{3/16}`. -/
def saKchi (KSA cB vhi : ℝ) : ℝ := Real.sqrt 8 * KSA + 192 / cB + 2 * Real.sqrt (48 * vhi)

/-- The horizon constant `A = L/vlo + 1`. -/
def saA (vlo vhi θτ : ℝ) : ℝ := saL vlo vhi θτ / vlo + 1

/-- The final constant of `single_law_bound`. -/
def saK (vlo vhi θτ Eτ KSA cB : ℝ) : ℝ :=
  kEndpoint vlo vhi + 2 * vhi * Real.exp (saGamma vlo vhi θτ) +
    Real.exp (saGamma vlo vhi θτ) * Eτ * (12 * saKchi KSA cB vhi / θτ + vhi) +
    7 * (vhi / saL vlo vhi θτ) ^ 2 * (saL vlo vhi θτ + 1) * Real.exp (saGamma vlo vhi θτ) +
    (2 * cTail / rPrime vlo vhi + 2 * Eτ / θτ)

theorem saGamma_pos {vlo vhi θτ : ℝ} (hvlo : 0 < vlo) (hvhi : 0 < vhi) (hθτ : 0 < θτ) :
    0 < saGamma vlo vhi θτ := by
  unfold saGamma
  have := rPrime_pos hvlo hvhi
  exact div_pos (lt_min this hθτ) (by norm_num)

theorem saL_pos {vlo vhi θτ : ℝ} (hvlo : 0 < vlo) (hvhi : 0 < vhi) (hθτ : 0 < θτ) :
    0 < saL vlo vhi θτ := by
  unfold saL; have := saGamma_pos hvlo hvhi hθτ; positivity

theorem saGamma_mul_saL {vlo vhi θτ : ℝ} (hvlo : 0 < vlo) (hvhi : 0 < vhi) (hθτ : 0 < θτ) :
    saGamma vlo vhi θτ * saL vlo vhi θτ = 1 / 8 := by
  have := saGamma_pos hvlo hvhi hθτ
  unfold saL; field_simp

/-! ## Numeric lemmas -/

/-- The horizon `n = ⌈L G log ε⌉` and its bounds. -/
theorem sa_horizon {L A vlo vhi eps v : ℝ} {n₀ : ℕ} (hL : 0 < L) (hvlo : 0 < vlo) (hvv : vlo ≤ v)
    (hvvhi : v ≤ vhi) (heps1 : 1 ≤ eps) (hlog1 : 1 ≤ Real.log eps)
    (hε₃ : (n₀ : ℝ) * vhi / L ≤ eps ^ 2) (hε₄ : 2 * vhi / L ≤ eps) (hε₅ : (4 * A) ^ 4 ≤ eps)
    (hA : A = L / vlo + 1) :
    let n := ⌈L * (eps ^ 2 / v) * Real.log eps⌉₊
    n₀ ≤ n ∧ L * eps ^ 2 / vhi ≤ n ∧ (n : ℝ) ≤ eps ^ ((5 : ℝ) / 2) ∧ ⌈eps⌉₊ ≤ n ∧
      L * (eps ^ 2 / v) * Real.log eps ≤ n ∧ (n : ℝ) < L * (eps ^ 2 / v) * Real.log eps + 1 := by
  intro n
  have hv0 : 0 < v := hvlo.trans_le hvv
  have hvhi : 0 < vhi := hv0.trans_le hvvhi
  have hepspos : 0 < eps := by linarith
  have hE : 0 < eps ^ 2 := by positivity
  have hnge : L * (eps ^ 2 / v) * Real.log eps ≤ n := Nat.le_ceil _
  have hnlt : (n : ℝ) < L * (eps ^ 2 / v) * Real.log eps + 1 := Nat.ceil_lt_add_one (by positivity)
  have hGlo : eps ^ 2 / vhi ≤ eps ^ 2 / v := by gcongr
  have hGhi : eps ^ 2 / v ≤ eps ^ 2 / vlo := by gcongr
  have hn_lo : L * eps ^ 2 / vhi ≤ n := by
    calc L * eps ^ 2 / vhi = L * (eps ^ 2 / vhi) * 1 := by ring
      _ ≤ L * (eps ^ 2 / v) * Real.log eps := by gcongr
      _ ≤ n := hnge
  have hn₀n : n₀ ≤ n := by
    have : (n₀ : ℝ) ≤ n := by
      have h1' : (n₀ : ℝ) ≤ L * eps ^ 2 / vhi := by
        rw [div_le_iff₀ hL] at hε₃
        rw [le_div_iff₀ hvhi]
        linarith
      exact h1'.trans hn_lo
    exact_mod_cast this
  have hA1 : 1 ≤ A := by
    have hLv : 0 ≤ L / vlo := by positivity
    rw [hA]; linarith
  have hε14 : 4 * A ≤ eps ^ ((1 : ℝ) / 4) := by
    have h0 : (0 : ℝ) ≤ 4 * A := by linarith
    calc 4 * A = ((4 * A) ^ 4) ^ ((1 : ℝ) / 4) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
      _ ≤ eps ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by positivity) hε₅ (by norm_num)
  have hlog4 : Real.log eps ≤ 4 * eps ^ ((1 : ℝ) / 4) := by
    have := Real.log_le_rpow_div hepspos.le (show (0 : ℝ) < 1 / 4 by norm_num)
    have e : eps ^ ((1 : ℝ) / 4) / (1 / 4) = 4 * eps ^ ((1 : ℝ) / 4) := by ring
    rw [e] at this; exact this
  have hn_hi : (n : ℝ) ≤ eps ^ ((5 : ℝ) / 2) := by
    have hε2log : 1 ≤ eps ^ 2 * Real.log eps := by nlinarith
    have h1 : (n : ℝ) ≤ A * eps ^ 2 * Real.log eps := by
      calc (n : ℝ) ≤ L * (eps ^ 2 / v) * Real.log eps + 1 := hnlt.le
        _ ≤ L * (eps ^ 2 / vlo) * Real.log eps + eps ^ 2 * Real.log eps := by gcongr
        _ = A * eps ^ 2 * Real.log eps := by rw [hA]; ring
    calc (n : ℝ) ≤ A * eps ^ 2 * Real.log eps := h1
      _ ≤ A * eps ^ 2 * (4 * eps ^ ((1 : ℝ) / 4)) := by gcongr
      _ = (4 * A) * (eps ^ 2 * eps ^ ((1 : ℝ) / 4)) := by ring
      _ ≤ eps ^ ((1 : ℝ) / 4) * (eps ^ 2 * eps ^ ((1 : ℝ) / 4)) := by gcongr
      _ = eps ^ ((5 : ℝ) / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hepspos, ← Real.rpow_add hepspos]; norm_num
  have hk₁n : ⌈eps⌉₊ ≤ n := by
    have hk₁ε' : (⌈eps⌉₊ : ℝ) < eps + 1 := Nat.ceil_lt_add_one hepspos.le
    have : (⌈eps⌉₊ : ℝ) ≤ n := by
      have h1' : (⌈eps⌉₊ : ℝ) ≤ 2 * eps := by linarith
      have h2' : 2 * eps ≤ L * eps ^ 2 / vhi := by
        rw [div_le_iff₀ hL] at hε₄
        rw [le_div_iff₀ hvhi]
        nlinarith
      exact (h1'.trans h2').trans hn_lo
    exact_mod_cast this
  exact ⟨hn₀n, hn_lo, hn_hi, hk₁n, hnge, hnlt⟩

/-- `χ = a + x_D + 2√v ρ ≤ K_χ ε^{15/32}`. -/
theorem sa_chi_le {n eps KSA cB v vhi : ℝ} (hn1 : 1 ≤ n) (heps1 : 1 ≤ eps)
    (hn_hi : n ≤ eps ^ ((5 : ℝ) / 2)) (hKSA : 0 ≤ KSA) (hcB : 0 < cB)
    (hvvhi : v ≤ vhi) :
    KSA * n ^ ((1 : ℝ) / 8) * Real.sqrt (Real.log n) + 24 * Real.log n / cB +
        2 * Real.sqrt v * Real.sqrt (6 * Real.log n) ≤
      saKchi KSA cB vhi * eps ^ ((15 : ℝ) / 32) := by
  have hnpos : 0 < n := by linarith
  have hepspos : 0 < eps := by linarith
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hn316 : n ^ ((3 : ℝ) / 16) ≤ eps ^ ((15 : ℝ) / 32) := by
    calc n ^ ((3 : ℝ) / 16) ≤ (eps ^ ((5 : ℝ) / 2)) ^ ((3 : ℝ) / 16) :=
          Real.rpow_le_rpow hnpos.le hn_hi (by norm_num)
      _ = eps ^ ((15 : ℝ) / 32) := by rw [← Real.rpow_mul hepspos.le]; norm_num
  have hlogn8 : Real.log n ≤ 8 * n ^ ((1 : ℝ) / 8) := by
    have := Real.log_le_rpow_div hnpos.le (show (0 : ℝ) < 1 / 8 by norm_num)
    have e : n ^ ((1 : ℝ) / 8) / (1 / 8) = 8 * n ^ ((1 : ℝ) / 8) := by ring
    rw [e] at this; exact this
  have hsqrtlogn : Real.sqrt (Real.log n) ≤ Real.sqrt 8 * n ^ ((1 : ℝ) / 16) := by
    calc Real.sqrt (Real.log n) ≤ Real.sqrt (8 * n ^ ((1 : ℝ) / 8)) := Real.sqrt_le_sqrt hlogn8
      _ = Real.sqrt 8 * n ^ ((1 : ℝ) / 16) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (n ^ ((1 : ℝ) / 8)),
            ← Real.rpow_mul hnpos.le]
          norm_num
  have hn18 : n ^ ((1 : ℝ) / 8) ≤ n ^ ((3 : ℝ) / 16) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hn116 : n ^ ((1 : ℝ) / 16) ≤ n ^ ((3 : ℝ) / 16) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hn18' : 0 ≤ n ^ ((1 : ℝ) / 8) := by positivity
  have ha' : KSA * n ^ ((1 : ℝ) / 8) * Real.sqrt (Real.log n) ≤
      Real.sqrt 8 * KSA * n ^ ((3 : ℝ) / 16) := by
    calc KSA * n ^ ((1 : ℝ) / 8) * Real.sqrt (Real.log n)
        ≤ KSA * n ^ ((1 : ℝ) / 8) * (Real.sqrt 8 * n ^ ((1 : ℝ) / 16)) :=
          mul_le_mul_of_nonneg_left hsqrtlogn (by positivity)
      _ = Real.sqrt 8 * KSA * (n ^ ((1 : ℝ) / 8) * n ^ ((1 : ℝ) / 16)) := by ring
      _ = Real.sqrt 8 * KSA * n ^ ((3 : ℝ) / 16) := by
          rw [← Real.rpow_add hnpos]; norm_num
  have hxD' : 24 * Real.log n / cB ≤ 192 / cB * n ^ ((3 : ℝ) / 16) := by
    calc 24 * Real.log n / cB = 24 / cB * Real.log n := by ring
      _ ≤ 24 / cB * (8 * n ^ ((1 : ℝ) / 8)) :=
          mul_le_mul_of_nonneg_left hlogn8 (by positivity)
      _ = 192 / cB * n ^ ((1 : ℝ) / 8) := by ring
      _ ≤ 192 / cB * n ^ ((3 : ℝ) / 16) := mul_le_mul_of_nonneg_left hn18 (by positivity)
  have hΓ' : 2 * Real.sqrt v * Real.sqrt (6 * Real.log n) ≤
      2 * Real.sqrt (48 * vhi) * n ^ ((3 : ℝ) / 16) := by
    have hsv : Real.sqrt v ≤ Real.sqrt vhi := Real.sqrt_le_sqrt hvvhi
    have hρ' : Real.sqrt (6 * Real.log n) ≤ Real.sqrt 48 * n ^ ((1 : ℝ) / 16) := by
      calc Real.sqrt (6 * Real.log n) = Real.sqrt 6 * Real.sqrt (Real.log n) :=
            Real.sqrt_mul (by norm_num) _
        _ ≤ Real.sqrt 6 * (Real.sqrt 8 * n ^ ((1 : ℝ) / 16)) :=
            mul_le_mul_of_nonneg_left hsqrtlogn (Real.sqrt_nonneg _)
        _ = Real.sqrt 48 * n ^ ((1 : ℝ) / 16) := by
            rw [← mul_assoc, ← Real.sqrt_mul (by norm_num)]; norm_num
    calc 2 * Real.sqrt v * Real.sqrt (6 * Real.log n)
        ≤ 2 * Real.sqrt vhi * (Real.sqrt 48 * n ^ ((1 : ℝ) / 16)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsv (by norm_num)) hρ' (Real.sqrt_nonneg _)
            (by positivity)
      _ = 2 * Real.sqrt (48 * vhi) * n ^ ((1 : ℝ) / 16) := by
          rw [Real.sqrt_mul (by norm_num)]; ring
      _ ≤ 2 * Real.sqrt (48 * vhi) * n ^ ((3 : ℝ) / 16) :=
          mul_le_mul_of_nonneg_left hn116 (by positivity)
  have hK0 : 0 ≤ saKchi KSA cB vhi := by
    unfold saKchi
    exact add_nonneg (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hKSA)
      (div_nonneg (by norm_num) hcB.le)) (by positivity)
  calc KSA * n ^ ((1 : ℝ) / 8) * Real.sqrt (Real.log n) + 24 * Real.log n / cB +
        2 * Real.sqrt v * Real.sqrt (6 * Real.log n)
      ≤ saKchi KSA cB vhi * n ^ ((3 : ℝ) / 16) := by
        unfold saKchi
        linarith only [ha', hxD', hΓ']
    _ ≤ saKchi KSA cB vhi * eps ^ ((15 : ℝ) / 32) := mul_le_mul_of_nonneg_left hn316 hK0

variable {vlo vhi κ₃ B θ D c₀ : ℝ} {ν : ProbabilityMeasure ℝ}

/-- The Bernstein input of the middle range at deviation level `√(3 k log n / c_B)`. -/
theorem sa_bernstein_input (h : UnivClass vlo vhi κ₃ B θ ν) (hθ : 0 < θ) {n k₁ : ℕ}
    (hn16 : 16 ≤ n) (hk₁ : 1 ≤ k₁) {eps : ℝ} (hk₁ε : eps ≤ k₁)
    (hBern243 : 243 * Real.log n / bernsteinRate θ B ≤ eps) :
    BernsteinInput ν k₁ n (24 * Real.log n / bernsteinRate θ B) (2 / (n : ℝ) ^ 3) := by
  have hB := h.B_pos
  set cB := bernsteinRate θ B with hcBdef
  have hcB : 0 < cB := bernsteinRate_pos hθ hB
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  intro k hkk₁ hkn
  have hk0 : (0 : ℝ) < k := by
    have : 1 ≤ k := hk₁.trans hkk₁
    exact_mod_cast this
  have hkε : eps ≤ k := hk₁ε.trans (by exact_mod_cast hkk₁)
  have hargpos : 0 < 3 / cB * k * Real.log n :=
    mul_pos (mul_pos (div_pos (by norm_num) hcB) hk0) hlogn
  obtain ⟨xB, hxBdef⟩ : ∃ xB : ℝ, xB = Real.sqrt (3 / cB * k * Real.log n) := ⟨_, rfl⟩
  have hxB2 : xB ^ 2 = 3 / cB * k * Real.log n := by
    rw [hxBdef]; exact Real.sq_sqrt hargpos.le
  have hxB0 : 0 < xB := by rw [hxBdef]; exact Real.sqrt_pos.2 hargpos
  have h5 : 3 * Real.log n / cB ≤ k := by
    have := hBern243.trans hkε
    rw [div_le_iff₀ hcB] at this ⊢
    linarith
  have h5' : 243 * Real.log n / cB ≤ k := hBern243.trans hkε
  refine ⟨xB, hxB0.le, ?_, ?_, ?_⟩
  · rw [hxBdef, Real.sqrt_le_left (by positivity)]
    have e : (k / 9 : ℝ) ^ 2 = k * (k / 81) := by ring
    rw [e, show 3 / cB * k * Real.log n = k * (3 * Real.log n / cB) by ring]
    refine mul_le_mul_of_nonneg_left ?_ hk0.le
    rw [div_le_iff₀ hcB] at h5'
    rw [div_le_div_iff₀ hcB (by norm_num)]
    linarith
  · have e : 8 * xB ^ 2 / k = 24 * Real.log n / cB := by
      rw [hxB2]; field_simp; ring
    exact e.le
  · have hbern := iid_maximal_bernstein hθ h.pos h.mean h.expMom' k (hk₁.trans hkk₁) hxB0
    refine hbern.trans ?_
    have hxBk : xB ^ 2 / k = 3 * Real.log n / cB := by rw [hxB2]; field_simp
    have hxBk' : xB ≤ k := by
      rw [hxBdef, Real.sqrt_le_left hk0.le]
      calc 3 / cB * k * Real.log n = k * (3 * Real.log n / cB) := by ring
        _ ≤ k * k := mul_le_mul_of_nonneg_left h5 hk0.le
        _ = k ^ 2 := by ring
    have hle : xB ^ 2 / k ≤ xB := by
      rw [div_le_iff₀ hk0, pow_two]
      exact mul_le_mul_of_nonneg_left hxBk' hxB0.le
    have hmin : cB * min (xB ^ 2 / k) xB = 3 * Real.log n := by
      rw [min_eq_left hle, hxBk]; field_simp
    rw [hmin]
    have : Real.exp (-(3 * Real.log n)) = 1 / (n : ℝ) ^ 3 := by
      rw [Real.exp_neg, show (3 : ℝ) * Real.log n = ((3 : ℕ) : ℝ) * Real.log n by norm_num,
        Real.exp_nat_mul, Real.exp_log hnpos, one_div]
    rw [this]; ring_nf; rfl

set_option maxHeartbeats 3000000 in
/-- The final numeric bound: `K_A/ε + mainBound ≤ K ε^{-17/32}`. -/
theorem sa_numeric {vlo vhi θτ Eτ KSA cB eps v γ L χ pfail : ℝ} {k₁ n : ℕ}
    (hγeq : γ = saGamma vlo vhi θτ) (hLeq : L = saL vlo vhi θτ)
    (hvlo : 0 < vlo) (hv0 : 0 < v) (hvvhi : v ≤ vhi) (heps1 : 1 ≤ eps) (hlog1 : 1 ≤ Real.log eps)
    (hγ : 0 < γ) (hL : 0 < L) (hγL : γ * L = 1 / 8) (hθτ : 0 < θτ) (hE0 : 0 ≤ Eτ)
    (h16γr : 16 * γ ≤ rPrime vlo vhi) (h16γτ : 16 * γ ≤ θτ) (hKSA : 0 ≤ KSA) (hcB : 0 < cB)
    (hn1 : (1 : ℝ) ≤ n) (hn_lo : L * eps ^ 2 / vhi ≤ n)
    (hnge : L * (eps ^ 2 / v) * Real.log eps ≤ n)
    (hnlt : (n : ℝ) < L * (eps ^ 2 / v) * Real.log eps + 1)
    (hk₁ : (k₁ : ℝ) ≤ 2 * eps) (hε₆ : 2 * vhi ≤ eps) (_hχ0 : 0 ≤ χ)
    (hχ : χ ≤ saKchi KSA cB vhi * eps ^ ((15 : ℝ) / 32)) (_hpf0 : 0 ≤ pfail)
    (hpfail : pfail ≤ 7 / (n : ℝ) ^ 2) :
    kEndpoint vlo vhi / eps + mainBound γ eps v vhi θτ Eτ (rPrime vlo vhi) χ pfail k₁ n ≤
      saK vlo vhi θτ Eτ KSA cB * eps ^ (-(17 / 32 : ℝ)) := by
  have hvhi : 0 < vhi := hv0.trans_le hvvhi
  have hr' := rPrime_pos hvlo hvhi
  have hepspos : 0 < eps := by linarith
  have hE : 0 < eps ^ 2 := by positivity
  have hlogε : Real.log eps ≤ eps := (Real.log_le_sub_one_of_pos hepspos).trans (by linarith)
  have hnpos : (0 : ℝ) < n := by linarith
  have hKχ0 : 0 ≤ saKchi KSA cB vhi := by
    unfold saKchi
    exact add_nonneg (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hKSA)
      (div_nonneg (by norm_num) hcB.le)) (by positivity)
  set e17 := eps ^ (-(17 / 32 : ℝ)) with he17
  have he17pos : 0 < e17 := by positivity
  have hinv1 : eps⁻¹ ≤ e17 := rpow_neg_one_le heps1
  have hinv2 : (eps ^ 2)⁻¹ ≤ e17 := rpow_neg_two_le heps1
  have hpow1532 : eps ^ ((15 : ℝ) / 32) / eps = e17 := by
    rw [he17, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hepspos]; norm_num
  -- endpoint
  have hT1 : kEndpoint vlo vhi / eps ≤ kEndpoint vlo vhi * e17 := by
    have hk0 : 0 ≤ kEndpoint vlo vhi := by
      unfold kEndpoint; exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hinv1 hk0
  -- piece (i)
  have hr₁le : (k₁ : ℝ) * v / eps ^ 2 ≤ 2 * vhi / eps := by
    have : (k₁ : ℝ) * v ≤ 2 * eps * vhi := mul_le_mul hk₁ hvvhi hv0.le (by positivity)
    rw [div_le_div_iff₀ hE hepspos]
    nlinarith
  have hr₁1 : (k₁ : ℝ) * v / eps ^ 2 ≤ 1 := by
    have : 2 * vhi / eps ≤ 1 := by rw [div_le_one hepspos]; exact hε₆
    linarith
  have hT2 : (k₁ : ℝ) * v / eps ^ 2 * Real.exp (γ * ((k₁ : ℝ) * v / eps ^ 2)) ≤
      2 * vhi * Real.exp γ * e17 := by
    have hr₁0 : 0 ≤ (k₁ : ℝ) * v / eps ^ 2 := by positivity
    have h1' : Real.exp (γ * ((k₁ : ℝ) * v / eps ^ 2)) ≤ Real.exp γ :=
      Real.exp_le_exp.2 (by nlinarith)
    calc (k₁ : ℝ) * v / eps ^ 2 * Real.exp (γ * ((k₁ : ℝ) * v / eps ^ 2))
        ≤ 2 * vhi / eps * Real.exp γ :=
          mul_le_mul hr₁le h1' (Real.exp_pos _).le (by positivity)
      _ = 2 * vhi * Real.exp γ * eps⁻¹ := by ring
      _ ≤ 2 * vhi * Real.exp γ * e17 := mul_le_mul_of_nonneg_left hinv1 (by positivity)
  -- piece (ii-a)
  have hT3 : Real.exp γ * Eτ * (12 * χ / (θτ * eps) + vhi / eps ^ 2) ≤
      Real.exp γ * Eτ * (12 * saKchi KSA cB vhi / θτ + vhi) * e17 := by
    have h1' : 12 * χ / (θτ * eps) ≤ 12 * saKchi KSA cB vhi / θτ * e17 := by
      calc 12 * χ / (θτ * eps) ≤ 12 * (saKchi KSA cB vhi * eps ^ ((15 : ℝ) / 32)) / (θτ * eps) := by
            gcongr
        _ = 12 * saKchi KSA cB vhi / θτ * (eps ^ ((15 : ℝ) / 32) / eps) := by
            field_simp
        _ = 12 * saKchi KSA cB vhi / θτ * e17 := by rw [hpow1532]
    have h2' : vhi / eps ^ 2 ≤ vhi * e17 := by
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hinv2 hvhi.le
    calc Real.exp γ * Eτ * (12 * χ / (θτ * eps) + vhi / eps ^ 2)
        ≤ Real.exp γ * Eτ * (12 * saKchi KSA cB vhi / θτ * e17 + vhi * e17) :=
          mul_le_mul_of_nonneg_left (add_le_add h1' h2') (by positivity)
      _ = Real.exp γ * Eτ * (12 * saKchi KSA cB vhi / θτ + vhi) * e17 := by ring
  -- piece (ii-b)
  set r₂ := ((n : ℝ) + 1) * v / eps ^ 2 with hr₂def
  have hpfail' : pfail ≤ 7 * (vhi / L) ^ 2 / eps ^ 4 := by
    refine hpfail.trans ?_
    have hpos' : 0 < L * eps ^ 2 / vhi := by positivity
    have h1' : (L * eps ^ 2 / vhi) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hpos'.le hn_lo 2
    have e : (L * eps ^ 2 / vhi) ^ 2 = eps ^ 4 / (vhi / L) ^ 2 := by field_simp
    rw [e] at h1'
    have hvL : 0 < (vhi / L) ^ 2 := by positivity
    rw [div_le_iff₀ hvL] at h1'
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [h1']
  have hr₂bound : r₂ ≤ L * Real.log eps + 2 * v / eps ^ 2 := by
    rw [hr₂def]
    have : ((n : ℝ) + 1) * v ≤ (L * (eps ^ 2 / v) * Real.log eps + 2) * v :=
      mul_le_mul_of_nonneg_right (by linarith) hv0.le
    calc ((n : ℝ) + 1) * v / eps ^ 2 ≤ (L * (eps ^ 2 / v) * Real.log eps + 2) * v / eps ^ 2 := by
          gcongr
      _ = L * Real.log eps + 2 * v / eps ^ 2 := by field_simp
  have h2v : 2 * v / eps ^ 2 ≤ 1 := by
    rw [div_le_one hE]
    have : 2 * v ≤ 2 * vhi := by linarith
    nlinarith
  have hr₂le : r₂ ≤ (L + 1) * eps := by
    calc r₂ ≤ L * Real.log eps + 1 := by linarith
      _ ≤ L * eps + eps := by
          have := mul_le_mul_of_nonneg_left hlogε hL.le
          linarith
      _ = (L + 1) * eps := by ring
  have hr₂ge : L * Real.log eps ≤ r₂ := by
    rw [hr₂def]
    have : L * (eps ^ 2 / v) * Real.log eps * v ≤ ((n : ℝ) + 1) * v :=
      mul_le_mul_of_nonneg_right (by linarith) hv0.le
    calc L * Real.log eps = L * (eps ^ 2 / v) * Real.log eps * v / eps ^ 2 := by
          field_simp
      _ ≤ ((n : ℝ) + 1) * v / eps ^ 2 := by gcongr
  have hexpr₂ : Real.exp (γ * r₂) ≤ Real.exp γ * eps ^ ((1 : ℝ) / 8) := by
    have h1' : γ * r₂ ≤ γ * (L * Real.log eps + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hγ.le
    have : γ * r₂ ≤ γ + (1 / 8) * Real.log eps := by
      have e : γ * (L * Real.log eps + 1) = γ * L * Real.log eps + γ := by ring
      rw [e, hγL] at h1'
      linarith
    calc Real.exp (γ * r₂) ≤ Real.exp (γ + (1 / 8) * Real.log eps) := Real.exp_le_exp.2 this
      _ = Real.exp γ * eps ^ ((1 : ℝ) / 8) := by
          rw [Real.exp_add, Real.rpow_def_of_pos hepspos, mul_comm (Real.log eps)]
  have hT4 : pfail * r₂ * Real.exp (γ * r₂) ≤
      7 * (vhi / L) ^ 2 * (L + 1) * Real.exp γ * e17 := by
    have hr₂0 : 0 ≤ r₂ := by rw [hr₂def]; positivity
    have hrate : eps ^ ((1 : ℝ) / 8) * eps / eps ^ 4 ≤ e17 := by
      have e : eps ^ ((1 : ℝ) / 8) * eps / eps ^ 4 = eps ^ (-(23 / 8 : ℝ)) := by
        calc eps ^ ((1 : ℝ) / 8) * eps / eps ^ 4
            = eps ^ ((1 : ℝ) / 8) * eps ^ (1 : ℝ) / eps ^ ((4 : ℕ) : ℝ) := by
              rw [Real.rpow_one, Real.rpow_natCast]
          _ = eps ^ ((1 : ℝ) / 8 + 1 - ((4 : ℕ) : ℝ)) := by
              rw [Real.rpow_sub hepspos, Real.rpow_add hepspos]
          _ = eps ^ (-(23 / 8 : ℝ)) := by norm_num
      rw [e, he17]
      exact Real.rpow_le_rpow_of_exponent_le heps1 (by norm_num)
    calc pfail * r₂ * Real.exp (γ * r₂)
        ≤ (7 * (vhi / L) ^ 2 / eps ^ 4) * ((L + 1) * eps) * (Real.exp γ * eps ^ ((1 : ℝ) / 8)) := by
          gcongr
      _ = 7 * (vhi / L) ^ 2 * (L + 1) * Real.exp γ * (eps ^ ((1 : ℝ) / 8) * eps / eps ^ 4) := by
          ring
      _ ≤ 7 * (vhi / L) ^ 2 * (L + 1) * Real.exp γ * e17 :=
          mul_le_mul_of_nonneg_left hrate (by positivity)
  -- piece (iii)
  have htailexp : ∀ c : ℝ, 16 * γ ≤ c → Real.exp (-(c * r₂ / 2)) ≤ e17 := by
    intro c hc
    have h1' : Real.log eps ≤ c * r₂ / 2 := by
      have : 8 * γ * (L * Real.log eps) ≤ c / 2 * r₂ := by
        have hh : 8 * γ ≤ c / 2 := by linarith
        exact mul_le_mul hh hr₂ge (by positivity) (by linarith)
      have e : 8 * γ * (L * Real.log eps) = Real.log eps := by
        rw [show 8 * γ * (L * Real.log eps) = 8 * (γ * L) * Real.log eps by ring, hγL]; ring
      linarith
    calc Real.exp (-(c * r₂ / 2)) ≤ Real.exp (-Real.log eps) := Real.exp_le_exp.2 (by linarith)
      _ = eps⁻¹ := by rw [Real.exp_neg, Real.exp_log hepspos]
      _ ≤ e17 := hinv1
  have hT5 : 2 * cTail / rPrime vlo vhi * Real.exp (-(rPrime vlo vhi * r₂ / 2)) +
      2 * Eτ / θτ * Real.exp (-(θτ * r₂ / 2)) ≤
      (2 * cTail / rPrime vlo vhi + 2 * Eτ / θτ) * e17 := by
    have h1' := htailexp (rPrime vlo vhi) h16γr
    have h2' := htailexp θτ h16γτ
    have hc0 : 0 ≤ 2 * cTail / rPrime vlo vhi := div_nonneg (by linarith [cTail_pos]) hr'.le
    have hE0' : 0 ≤ 2 * Eτ / θτ := div_nonneg (by linarith) hθτ.le
    calc 2 * cTail / rPrime vlo vhi * Real.exp (-(rPrime vlo vhi * r₂ / 2)) +
          2 * Eτ / θτ * Real.exp (-(θτ * r₂ / 2))
        ≤ 2 * cTail / rPrime vlo vhi * e17 + 2 * Eτ / θτ * e17 :=
          add_le_add (mul_le_mul_of_nonneg_left h1' hc0) (mul_le_mul_of_nonneg_left h2' hE0')
      _ = (2 * cTail / rPrime vlo vhi + 2 * Eτ / θτ) * e17 := by ring
  unfold mainBound saK
  rw [← hr₂def, ← hγeq, ← hLeq]
  linarith only [hT1, hT2, hT3, hT4, hT5]

/-! ## The single-law bound -/

set_option maxHeartbeats 1000000 in
/-- **The single-law bound**: `d_γ(rawLaw ε ν, 𝒯) ≤ K ε^{-17/32}` above an explicit threshold. -/
theorem single_law_bound (h : UnivClass vlo vhi κ₃ B θ ν) (hvlo : 0 < vlo) (hθ : 0 < θ)
    {𝒯 : Measure ℝ} {θτ Eτ : ℝ} (hL : LifetimeSide 𝒯 θτ Eτ)
    {KSA : ℝ} {n₀ : ℕ} (hKSA : 0 ≤ KSA) (hn₀ : 16 ≤ n₀)
    (hSAν : ∀ n : ℕ, n₀ ≤ n → HasSACoupling ν n
      (KSA * (n : ℝ) ^ ((1 : ℝ) / 8) * Real.sqrt (Real.log n)) ((n : ℝ) ^ (-(2 : ℝ))))
    {eps : ℝ} (hε₁ : epsZero vhi (univBeta vlo κ₃) ≤ eps) (hε₂ : Real.exp 1 ≤ eps)
    (hε₃ : (n₀ : ℝ) * vhi / saL vlo vhi θτ ≤ eps ^ 2) (hε₄ : 2 * vhi / saL vlo vhi θτ ≤ eps)
    (hε₅ : (4 * saA vlo vhi θτ) ^ 4 ≤ eps) (hε₆ : 2 * vhi ≤ eps)
    (hε₇ : (4 * saKchi KSA (bernsteinRate θ B) vhi) ^ 2 ≤ eps)
    (hε₈ : (1215 / bernsteinRate θ B) ^ 2 ≤ eps)
    (hε₉ : 2 * saGamma vlo vhi θτ * vhi / min (θ / 4) (θ ^ 2 / (16 * B)) ≤ eps) :
    dEtaL (saGamma vlo vhi θτ) (rawLaw eps ν) ⟨𝒯, hL.prob⟩ ≤
      ENNReal.ofReal (saK vlo vhi θτ Eτ KSA (bernsteinRate θ B) * eps ^ (-(17 / 32 : ℝ))) := by
  have hTprob := hL.prob
  have hθτ := hL.θpos
  have hv0 : 0 < lawVar ν := hvlo.trans_le h.var_ge
  have hvvlo : vlo ≤ lawVar ν := h.var_ge
  have hvvhi : lawVar ν ≤ vhi := h.var_le
  have hvhi : 0 < vhi := hv0.trans_le hvvhi
  have hB := h.B_pos
  have hγ := saGamma_pos hvlo hvhi hθτ
  have hLpos := saL_pos hvlo hvhi hθτ
  have hγL := saGamma_mul_saL hvlo hvhi hθτ
  have h16γr : 16 * saGamma vlo vhi θτ ≤ rPrime vlo vhi := by
    unfold saGamma; have := min_le_left (rPrime vlo vhi) θτ; linarith
  have h16γτ : 16 * saGamma vlo vhi θτ ≤ θτ := by
    unfold saGamma; have := min_le_right (rPrime vlo vhi) θτ; linarith
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans hε₁
  have hepspos : 0 < eps := by linarith
  have hE : 0 < eps ^ 2 := by positivity
  have hlog1 : 1 ≤ Real.log eps := by rw [Real.le_log_iff_exp_le hepspos]; exact hε₂
  have hcB : 0 < bernsteinRate θ B := bernsteinRate_pos hθ hB
  have hE0 : 0 ≤ Eτ := by
    have := hL.tail_le 0
    have := measureReal_nonneg (μ := 𝒯) (s := {t | (0 : ℝ) ≤ t})
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at *
    linarith
  -- the horizon
  obtain ⟨hn₀n, hn_lo, hn_hi, hk₁n, hnge, hnlt⟩ := sa_horizon (v := lawVar ν) hLpos hvlo hvvlo
    hvvhi heps1 hlog1 hε₃ hε₄ hε₅ rfl
  set n := ⌈saL vlo vhi θτ * (eps ^ 2 / lawVar ν) * Real.log eps⌉₊ with hndef
  have hn16 : 16 ≤ n := hn₀.trans hn₀n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := by linarith
  set k₁ := ⌈eps⌉₊ with hk₁def
  have hk₁ : 1 ≤ k₁ := Nat.one_le_iff_ne_zero.2 (by
    intro h0; have := Nat.ceil_eq_zero.1 h0; linarith)
  have hk₁ε : eps ≤ k₁ := Nat.le_ceil _
  have hk₁ε' : (k₁ : ℝ) < eps + 1 := Nat.ceil_lt_add_one hepspos.le
  -- the coupling
  obtain ⟨π, hπ, h1, h2, hSAπ⟩ := hSAν n hn₀n
  have hpSA : (n : ℝ) ^ (-(2 : ℝ)) = 1 / n ^ 2 := by
    rw [Real.rpow_neg hnpos.le, one_div, Real.rpow_two]
  -- Bernstein input
  have hlogn_le : Real.log n ≤ 5 * Real.sqrt eps := by
    have h1' : Real.log n ≤ (5 / 2) * Real.log eps := by
      calc Real.log n ≤ Real.log (eps ^ ((5 : ℝ) / 2)) := Real.log_le_log hnpos hn_hi
        _ = (5 / 2) * Real.log eps := Real.log_rpow hepspos _
    have h2' : Real.log eps ≤ 2 * Real.sqrt eps := by
      have := Real.log_le_rpow_div hepspos.le (show (0 : ℝ) < 1 / 2 by norm_num)
      rw [Real.sqrt_eq_rpow]
      have e : eps ^ ((1 : ℝ) / 2) / (1 / 2) = 2 * eps ^ ((1 : ℝ) / 2) := by ring
      rw [e] at this
      exact this
    linarith only [h1', h2']
  have hsqrtε : 1215 / bernsteinRate θ B ≤ Real.sqrt eps := by
    rw [Real.le_sqrt (by positivity) hepspos.le]; exact hε₈
  have hBern243 : 243 * Real.log n / bernsteinRate θ B ≤ eps := by
    have h1' : 243 * Real.log n ≤ 243 * (5 * Real.sqrt eps) :=
      mul_le_mul_of_nonneg_left hlogn_le (by norm_num)
    have h2' : 243 * (5 * Real.sqrt eps) / bernsteinRate θ B ≤ eps := by
      rw [div_le_iff₀ hcB]
      have h3 : 1215 ≤ Real.sqrt eps * bernsteinRate θ B := by
        rw [div_le_iff₀ hcB] at hsqrtε; linarith only [hsqrtε]
      have h4 : Real.sqrt eps * Real.sqrt eps = eps := Real.mul_self_sqrt hepspos.le
      have h5 := mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg eps)
      have e : Real.sqrt eps * (Real.sqrt eps * bernsteinRate θ B) = eps * bernsteinRate θ B := by
        rw [← mul_assoc, h4]
      rw [e] at h5
      linarith only [h5]
    calc 243 * Real.log n / bernsteinRate θ B ≤ 243 * (5 * Real.sqrt eps) / bernsteinRate θ B :=
          div_le_div_of_nonneg_right h1' hcB.le
      _ ≤ eps := h2'
  have hBern := sa_bernstein_input h hθ hn16 hk₁ hk₁ε hBern243
  -- the grid parameter and `χ`
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hρ : 0 < Real.sqrt (6 * Real.log n) := Real.sqrt_pos.2 (by positivity)
  have hρ2 : Real.sqrt (6 * Real.log n) ^ 2 = 6 * Real.log n := Real.sq_sqrt (by positivity)
  have hp₃ : 2 * (n : ℝ) * Real.exp (-Real.sqrt (6 * Real.log n) ^ 2 / 2) = 2 / (n : ℝ) ^ 2 := by
    rw [hρ2, show -(6 * Real.log n) / 2 = -(((3 : ℕ) : ℝ) * Real.log n) by push_cast; ring,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log hnpos]
    field_simp
  have hχ := sa_chi_le (n := n) hn1 heps1 hn_hi hKSA hcB hvvhi
  have hKχ0 : 0 ≤ saKchi KSA (bernsteinRate θ B) vhi := by
    unfold saKchi
    exact add_nonneg (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hKSA)
      (div_nonneg (by norm_num) hcB.le)) (by positivity)
  have hχ4 : KSA * (n : ℝ) ^ ((1 : ℝ) / 8) * Real.sqrt (Real.log n) +
      24 * Real.log n / bernsteinRate θ B +
      2 * Real.sqrt (lawVar ν) * Real.sqrt (6 * Real.log n) ≤ eps / 4 := by
    have h1' : 4 * saKchi KSA (bernsteinRate θ B) vhi ≤ Real.sqrt eps := by
      rw [Real.le_sqrt (by positivity) hepspos.le]; exact hε₇
    have h2' : Real.sqrt eps ≤ eps ^ ((17 : ℝ) / 32) := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le heps1 (by norm_num)
    have e : eps = eps ^ ((17 : ℝ) / 32) * eps ^ ((15 : ℝ) / 32) := by
      rw [← Real.rpow_add hepspos]; norm_num
    have h3' : saKchi KSA (bernsteinRate θ B) vhi * eps ^ ((15 : ℝ) / 32) ≤ eps / 4 := by
      calc saKchi KSA (bernsteinRate θ B) vhi * eps ^ ((15 : ℝ) / 32)
          = (4 * saKchi KSA (bernsteinRate θ B) vhi) * eps ^ ((15 : ℝ) / 32) / 4 := by ring
        _ ≤ eps ^ ((17 : ℝ) / 32) * eps ^ ((15 : ℝ) / 32) / 4 := by
            gcongr
            exact h1'.trans h2'
        _ = eps / 4 := by rw [← e]
    exact hχ.trans h3'
  -- (E2)
  have hmin : 0 < min (θ / 4) (θ ^ 2 / (16 * B)) := lt_min (by positivity) (by positivity)
  have hE2 : 2 * saGamma vlo vhi θτ * vhi / eps ^ 2 ≤ min (θ / 4) (θ ^ 2 / (16 * B)) := by
    rw [div_le_iff₀ hE]
    rw [div_le_iff₀ hmin] at hε₉
    have : eps ≤ eps ^ 2 := by nlinarith
    nlinarith [hmin]
  -- the two terms
  have hend := endpoint_term_le h hvlo hθ hε₁ hγ h16γr hE2
  have hmain := main_term_le h hvlo hε₁ hL hγ (by linarith) (by linarith) h1 h2 hk₁ hk₁n
    (by positivity) (by positivity) hSAπ (by positivity) (by positivity) hBern hρ hχ4
  rw [rawLaw_eq_lawPM]
  refine (dEtaL_triangle _ _ (lawPM (iidLaw ν) (measurable_rawV eps ν)) _).trans ?_
  refine (add_le_add hend hmain).trans ?_
  -- the numeric bound
  have hpf0 : 0 ≤ (n : ℝ) ^ (-(2 : ℝ)) + 2 / (n : ℝ) ^ 3 + 2 / (n : ℝ) ^ 3 +
      2 * n * Real.exp (-Real.sqrt (6 * Real.log n) ^ 2 / 2) := by positivity
  have hpfail : (n : ℝ) ^ (-(2 : ℝ)) + 2 / (n : ℝ) ^ 3 + 2 / (n : ℝ) ^ 3 +
      2 * n * Real.exp (-Real.sqrt (6 * Real.log n) ^ 2 / 2) ≤ 7 / (n : ℝ) ^ 2 := by
    rw [hp₃, hpSA]
    have : 2 / (n : ℝ) ^ 3 ≤ 2 / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_right₀ hn1 (by norm_num))
    have e : (1 : ℝ) / n ^ 2 + 2 / n ^ 2 + 2 / n ^ 2 + 2 / n ^ 2 = 7 / n ^ 2 := by ring
    linarith
  have hnum := sa_numeric (k₁ := k₁) (n := n) rfl rfl hvlo hv0 hvvhi heps1 hlog1 hγ hLpos hγL hθτ
    hE0 h16γr
    h16γτ hKSA hcB hn1 hn_lo hnge hnlt (by linarith) hε₆ (by positivity) hχ hpf0 hpfail
  have hmb0 : 0 ≤ mainBound (saGamma vlo vhi θτ) eps (lawVar ν) vhi θτ Eτ (rPrime vlo vhi)
      (KSA * (n : ℝ) ^ ((1 : ℝ) / 8) * Real.sqrt (Real.log n) +
        24 * Real.log n / bernsteinRate θ B +
        2 * Real.sqrt (lawVar ν) * Real.sqrt (6 * Real.log n))
      ((n : ℝ) ^ (-(2 : ℝ)) + 2 / (n : ℝ) ^ 3 + 2 / (n : ℝ) ^ 3 +
        2 * n * Real.exp (-Real.sqrt (6 * Real.log n) ^ 2 / 2)) k₁ n := by
    unfold mainBound
    have hr' := rPrime_pos hvlo hvhi
    have hvhi0 := hvhi.le
    refine add_nonneg (add_nonneg (by positivity) (add_nonneg ?_ (by positivity))) ?_
    · exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hE0)
        (add_nonneg (by positivity) (div_nonneg hvhi0 (by positivity)))
    · exact add_nonneg (mul_nonneg (div_nonneg (by linarith [cTail_pos]) hr'.le) (Real.exp_pos _).le)
        (mul_nonneg (div_nonneg (by linarith) hθτ.le) (Real.exp_pos _).le)
  have hk0 : 0 ≤ kEndpoint vlo vhi / eps := by
    unfold kEndpoint
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hepspos.le
  rw [← ENNReal.ofReal_add hk0 hmb0]
  exact ENNReal.ofReal_le_ofReal hnum

/-! ## The reduction -/

theorem dEtaL_comm (γ : ℝ) (μ ρ : ProbabilityMeasure ℝ) : dEtaL γ μ ρ = dEtaL γ ρ μ := by
  unfold dEtaL
  refine lintegral_congr fun x => ?_
  rw [abs_sub_comm]

set_option maxHeartbeats 1000000 in
/-- **WP5 reduction**: (SA) over every class together with the Brownian side gives (U). -/
theorem universality_of_SA_lifetime
    (hSA : ∀ vlo vhi κ₃ B θ D c₀ : ℝ, 0 < vlo → vlo ≤ vhi → 0 < θ → 0 < c₀ →
      StrongApproxClass vlo vhi κ₃ B θ D c₀)
    {𝒯 : Measure ℝ} {θτ Eτ : ℝ} (hL : LifetimeSide 𝒯 θτ Eτ) : GEPUniversality := by
  refine ⟨17 / 32, by norm_num, fun vlo vhi κ₃ hvlo hvv => ?_⟩
  have hvhi : 0 < vhi := hvlo.trans_le hvv
  have hθτ := hL.θpos
  refine ⟨saGamma vlo vhi θτ, saGamma_pos hvlo hvhi hθτ, fun B θ D c₀ hθ hc₀ => ?_⟩
  obtain ⟨KSA, n₀, hKSA, hn₀, hSAc⟩ := hSA vlo vhi κ₃ B θ D c₀ hvlo hvv hθ hc₀
  set cB := bernsteinRate θ B with hcBdef
  set L := saL vlo vhi θτ with hLdef
  set e0 : ℝ := max (max (max (max (epsZero vhi (univBeta vlo κ₃)) (Real.exp 1))
    (max (Real.sqrt ((n₀ : ℝ) * vhi / L)) (2 * vhi / L)))
    (max (max ((4 * saA vlo vhi θτ) ^ 4) (2 * vhi))
      (max ((4 * saKchi KSA cB vhi) ^ 2) ((1215 / cB) ^ 2))))
    (2 * saGamma vlo vhi θτ * vhi / min (θ / 4) (θ ^ 2 / (16 * B))) with he0
  refine ⟨2 * saK vlo vhi θτ Eτ KSA cB, e0, fun eps heps ν ν' hν hsν hν' hsν' => ?_⟩
  have hε₁ : epsZero vhi (univBeta vlo κ₃) ≤ eps := by
    refine le_trans ?_ heps; rw [he0]
    exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hε₂ : Real.exp 1 ≤ eps := by
    refine le_trans ?_ heps; rw [he0]
    exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hε₃ : (n₀ : ℝ) * vhi / L ≤ eps ^ 2 := by
    have h1 : Real.sqrt ((n₀ : ℝ) * vhi / L) ≤ eps := by
      refine le_trans ?_ heps; rw [he0]
      exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
    have hL0 := saL_pos hvlo hvhi hθτ
    have h0 : 0 ≤ (n₀ : ℝ) * vhi / L := by positivity
    calc (n₀ : ℝ) * vhi / L = Real.sqrt ((n₀ : ℝ) * vhi / L) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ eps ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have hε₄ : 2 * vhi / L ≤ eps := by
    refine le_trans ?_ heps; rw [he0]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hε₅ : (4 * saA vlo vhi θτ) ^ 4 ≤ eps := by
    refine le_trans ?_ heps; rw [he0]
    exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _)))
  have hε₆ : 2 * vhi ≤ eps := by
    refine le_trans ?_ heps; rw [he0]
    exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _)))
  have hε₇ : (4 * saKchi KSA cB vhi) ^ 2 ≤ eps := by
    refine le_trans ?_ heps; rw [he0]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _)))
  have hε₈ : (1215 / cB) ^ 2 ≤ eps := by
    refine le_trans ?_ heps; rw [he0]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _)))
  have hε₉ : 2 * saGamma vlo vhi θτ * vhi / min (θ / 4) (θ ^ 2 / (16 * B)) ≤ eps := by
    refine le_trans ?_ heps; rw [he0]
    exact le_max_right _ _
  have hb1 := single_law_bound hν hvlo hθ hL hKSA hn₀ (fun n hn => hSAc ν hν hsν n hn)
    hε₁ hε₂ hε₃ hε₄ hε₅ hε₆ hε₇ hε₈ hε₉
  have hb2 := single_law_bound hν' hvlo hθ hL hKSA hn₀ (fun n hn => hSAc ν' hν' hsν' n hn)
    hε₁ hε₂ hε₃ hε₄ hε₅ hε₆ hε₇ hε₈ hε₉
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans hε₁
  have hK0 : 0 ≤ saK vlo vhi θτ Eτ KSA cB * eps ^ (-(17 / 32 : ℝ)) := by
    have hnn : 0 ≤ saK vlo vhi θτ Eτ KSA cB := by
      unfold saK
      have hE0 : 0 ≤ Eτ := by
        have := hL.tail_le 0
        have := measureReal_nonneg (μ := 𝒯) (s := {t | (0 : ℝ) ≤ t})
        simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at *
        linarith
      have hkE : 0 ≤ kEndpoint vlo vhi := by
        unfold kEndpoint; exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hB := hν.B_pos
      have hcB : 0 < cB := bernsteinRate_pos hθ hB
      have hKχ : 0 ≤ saKchi KSA cB vhi := by
        unfold saKchi
        exact add_nonneg (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hKSA)
          (div_nonneg (by norm_num) hcB.le)) (by positivity)
      have hr' := rPrime_pos hvlo hvhi
      have hL0 := saL_pos hvlo hvhi hθτ
      have hvhi0 := hvhi.le
      have hcT := cTail_pos
      have h3 : 0 ≤ Real.exp (saGamma vlo vhi θτ) * Eτ * (12 * saKchi KSA cB vhi / θτ + vhi) :=
        mul_nonneg (mul_nonneg (Real.exp_pos _).le hE0)
          (add_nonneg (div_nonneg (by positivity) hθτ.le) hvhi0)
      have h5 : 0 ≤ 2 * cTail / rPrime vlo vhi + 2 * Eτ / θτ :=
        add_nonneg (div_nonneg (by linarith) hr'.le) (div_nonneg (by linarith) hθτ.le)
      have h2 : 0 ≤ 2 * vhi * Real.exp (saGamma vlo vhi θτ) := by positivity
      have h4 : 0 ≤ 7 * (vhi / saL vlo vhi θτ) ^ 2 * (saL vlo vhi θτ + 1) *
          Real.exp (saGamma vlo vhi θτ) := by positivity
      linarith
    exact mul_nonneg hnn (Real.rpow_nonneg (by linarith) _)
  calc dEtaL (saGamma vlo vhi θτ) (rawLaw eps ν) (rawLaw eps ν')
      ≤ dEtaL (saGamma vlo vhi θτ) (rawLaw eps ν) ⟨𝒯, hL.prob⟩ +
          dEtaL (saGamma vlo vhi θτ) ⟨𝒯, hL.prob⟩ (rawLaw eps ν') := dEtaL_triangle _ _ _ _
    _ = dEtaL (saGamma vlo vhi θτ) (rawLaw eps ν) ⟨𝒯, hL.prob⟩ +
          dEtaL (saGamma vlo vhi θτ) (rawLaw eps ν') ⟨𝒯, hL.prob⟩ := by rw [dEtaL_comm _ ⟨𝒯, hL.prob⟩]
    _ ≤ ENNReal.ofReal (saK vlo vhi θτ Eτ KSA cB * eps ^ (-(17 / 32 : ℝ))) +
          ENNReal.ofReal (saK vlo vhi θτ Eτ KSA cB * eps ^ (-(17 / 32 : ℝ))) := add_le_add hb1 hb2
    _ = ENNReal.ofReal (2 * saK vlo vhi θτ Eτ KSA cB * eps ^ (-(17 / 32 : ℝ))) := by
        rw [← ENNReal.ofReal_add hK0 hK0]; congr 1; ring

end

end PGM
