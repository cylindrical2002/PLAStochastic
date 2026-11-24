import PLAStochastic.Index.KRE.CurvedLayer
import PLAStochastic.Index.KRE.TwoRegimeRecursion
import PLAStochastic.Index.KRE.LatticeWindow
import PLAStochastic.Index.GRE.FixedParameter

/-!
# Bridge: the layer counts of ALG-RE on curved keys (Model K)

Deterministic bridge between the one-layer bounds of `PLAStochastic.Index.KRE.CurvedLayer` and the height
recursion of `PLAStochastic.Index.KRE.TwoRegimeRecursion`.  The reference keys `z` satisfy the conclusions of the
good event of `PLAStochastic.Index.KRE.GoodEvent` (constant `80`), bundled as `KREPath`; the input keys of
ALG-RE are the curved keys `p s = φ (z s / z n)`.  With `Λ = (L / (2δ)) 80` (`kreLam`):

* noise regime, upper (`kre_hup`): if `Δ_ℓ ≤ Dn` and `16 Λ Dn³ eps³ log n ≤ n`, then
  `M_{ℓ+1} ≤ 514 mbar_ℓ + (t + 1)` with `mbar_ℓ = N_ℓ / (Δ_ℓ eps²)`;
* noise regime, lower (`kre_hlo`): if `Δ_ℓ ≤ Dn` and
  `9 · 10⁸ Λ j² Dn³ eps³ log n ≤ n`, then `(aRE / 4) mbar_ℓ - t ≤ M_{ℓ+1}`;
* curvature regime (`kre_hC`): with `c₁ = eps² / (409600 log n)`, `c₂ = √(eps / (16 Λ))`,
  `c₃ = 1 / (8 Λ)`, `640 log n ≤ eps Dn` and `8 Λ log n ≤ n`, every layer with
  `Dn < Δ_ℓ` and `1 ≤ τ♭(Δ_ℓ)` for the halved constants has
  `M_{ℓ+1} ≤ N_ℓ / τ♭(Δ_ℓ) + 1`;
* the height bounds `kreBridge_height_le` and `kreBridge_logb_lt_height`.

Nothing here is probabilistic.
-/

namespace PGM

noncomputable section

/-- The conclusions of the Model K good event for the reference keys `z`, together with the
    analytic data of the change of keys `φ` (derivative `φ' ≥ δ > 0` within `[0, 1]`,
    `φ'` `L`-Lipschitz there). -/
structure KREPath (φ φ' : ℝ → ℝ) (L δ : ℝ) (z : ℕ → ℝ) (n : ℕ) (eps : ℝ) (t j : ℕ) :
    Prop where
  deriv : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ (φ' x) (Set.Icc 0 1) x
  lip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |φ' x - φ' y| ≤ L * |x - y|
  delta_pos : 0 < δ
  le_deriv : ∀ x ∈ Set.Icc (0 : ℝ) 1, δ ≤ φ' x
  strictMono : StrictMono z
  mem_Icc : ∀ s < n, z s / z n ∈ Set.Icc (0 : ℝ) 1
  span : ∀ a b : ℕ, a ≤ b → b < n → z b - z a ≤ 80 * ((b - a : ℝ) + Real.log n)
  tube : ∀ a b : ℕ, a ≤ b → b < n →
    |z b - z a - (b - a)| ≤ 80 * (Real.sqrt ((b - a) * Real.log n) + Real.log n)
  half_le : (n : ℝ) / 2 ≤ z n
  bracket : ∀ θ : ℝ, θ = eps / 2 ∨ θ = 2 * eps →
    ∀ d K : ℕ, 1 ≤ d → 1 ≤ K → d ≤ 2 * n → K ≤ 2 * n →
      aLow * K / (d * θ ^ 2) - t ≤ (finSegCount θ (fun k => z (k * d)) K : ℝ) ∧
        (finSegCount θ (fun k => z (k * d)) K : ℝ) ≤ 128 * K / (d * θ ^ 2) + t + 1
  window : ∀ d a : ℕ, 1 ≤ d → d ≤ 2 * n → a ≤ 2 * n →
    ¬ windowFeasible (2 * eps) (fun k => z (k * d)) a (a + (j * kreL (2 * eps) d + 1))

/-- `Λ = (L / (2δ)) · 80`. -/
def kreLam (L δ : ℝ) : ℝ := L / (2 * δ) * 80

/-- Layer-side noise entry `c₁ = eps² / (409600 log n)`. -/
def kreC₁ (n : ℕ) (eps : ℝ) : ℝ := eps ^ 2 / (409600 * Real.log n)

/-- Layer-side curvature entry `c₂ = √(eps / (16 Λ))`. -/
def kreC₂ (eps L δ : ℝ) : ℝ := Real.sqrt (eps / (16 * kreLam L δ))

/-- Layer-side span entry `c₃ = 1 / (8 Λ)`. -/
def kreC₃ (L δ : ℝ) : ℝ := 1 / (8 * kreLam L δ)

/-! ## Elementary facts -/

theorem floor_facts {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ ⌊x⌋₊ ∧ x / 2 ≤ (⌊x⌋₊ : ℝ) ∧ (⌊x⌋₊ : ℝ) ≤ x := by
  have h1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have h1' : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
  have h2 := Nat.lt_floor_add_one x
  have h3 := Nat.floor_le (by linarith : (0 : ℝ) ≤ x)
  exact ⟨h1, by linarith, h3⟩

/-- `(K / τ : ℕ) ≤ 2 K / x` when `x / 2 ≤ τ`, `0 < x`. -/
theorem natDiv_le_of_half_le {K τ : ℕ} {x : ℝ} (hx : 0 < x) (hτ : x / 2 ≤ (τ : ℝ)) :
    ((K / τ : ℕ) : ℝ) ≤ K / (x / 2) :=
  Nat.cast_div_le.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg K) (by linarith) hτ)

/-! ## The three cost bounds -/

/-- **Noise-regime upper cost.**  With `τ ≤ Δ eps²`, `1 ≤ Δ ≤ Dn`, `1 ≤ eps`,
    `1 ≤ log n` and `16 Λ Dn³ eps³ log n ≤ n` (`Λ = 80 M`):
    `eps / 2 + Ψbar τ (eps / 2) ≤ eps`. -/
theorem psi_up_le {M eps Δ Dn τ ℓn N : ℝ} (hM : 0 ≤ M) (heps : 1 ≤ eps) (hΔ : 1 ≤ Δ)
    (hΔD : Δ ≤ Dn) (hτ0 : 0 ≤ τ) (hτ : τ ≤ Δ * eps ^ 2) (hℓ : 1 ≤ ℓn) (hN : 0 < N)
    (hN1 : 16 * (M * 80) * Dn ^ 3 * eps ^ 3 * ℓn ≤ N) :
    eps / 2 + (τ + 2 * (eps / 2)) * M * (80 * (τ * Δ + ℓn)) / (N / 2) ≤ eps := by
  have hΛ : 0 ≤ M * 80 := by linarith
  have he2 : 1 ≤ eps ^ 2 := one_le_pow₀ heps
  have he2' : eps ≤ eps ^ 2 := by
    have := mul_le_mul_of_nonneg_left heps (by linarith : (0 : ℝ) ≤ eps)
    nlinarith
  have hw : 1 ≤ Δ * eps ^ 2 := one_le_mul_of_one_le_of_one_le hΔ he2
  have hu0 : 0 ≤ τ + 2 * (eps / 2) := by linarith
  have hu : τ + 2 * (eps / 2) ≤ 2 * (Δ * eps ^ 2) := by
    have : eps ^ 2 ≤ Δ * eps ^ 2 := le_mul_of_one_le_left (by linarith) hΔ
    linarith
  have hv0 : 0 ≤ τ * Δ + ℓn := by
    have := mul_nonneg hτ0 (by linarith : (0 : ℝ) ≤ Δ)
    linarith
  have hA : 1 ≤ Δ * eps ^ 2 * Δ := one_le_mul_of_one_le_of_one_le hw hΔ
  have hv : τ * Δ + ℓn ≤ 2 * (Δ * eps ^ 2 * Δ * ℓn) := by
    have h1 : τ * Δ ≤ Δ * eps ^ 2 * Δ := mul_le_mul_of_nonneg_right hτ (by linarith)
    have h2 : Δ * eps ^ 2 * Δ ≤ Δ * eps ^ 2 * Δ * ℓn :=
      le_mul_of_one_le_right (by linarith) hℓ
    have h3 : ℓn ≤ Δ * eps ^ 2 * Δ * ℓn := le_mul_of_one_le_left (by linarith) hA
    linarith
  have hprod : M * 80 * (τ + 2 * (eps / 2)) * (τ * Δ + ℓn) ≤
      M * 80 * (2 * (Δ * eps ^ 2)) * (2 * (Δ * eps ^ 2 * Δ * ℓn)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hu hΛ) hv hv0 (mul_nonneg hΛ (by linarith))
  have hrhs : M * 80 * (2 * (Δ * eps ^ 2)) * (2 * (Δ * eps ^ 2 * Δ * ℓn)) =
      eps / 4 * (16 * (M * 80) * eps ^ 3 * ℓn * Δ ^ 3) := by ring
  have hD3 : Δ ^ 3 ≤ Dn ^ 3 := pow_le_pow_left₀ (by linarith) hΔD 3
  have hc0 : 0 ≤ 16 * (M * 80) * eps ^ 3 * ℓn := by
    have : 0 ≤ eps ^ 3 := by positivity
    have : 0 ≤ ℓn := by linarith
    positivity
  have h16 := mul_le_mul_of_nonneg_left hD3 hc0
  have h16' : 16 * (M * 80) * eps ^ 3 * ℓn * Dn ^ 3 ≤ N := by linarith
  have hfin := mul_le_mul_of_nonneg_left (h16.trans h16') (by linarith : (0 : ℝ) ≤ eps / 4)
  have e : (τ + 2 * (eps / 2)) * M * (80 * (τ * Δ + ℓn)) =
      M * 80 * (τ + 2 * (eps / 2)) * (τ * Δ + ℓn) := by ring
  have hkey : (τ + 2 * (eps / 2)) * M * (80 * (τ * Δ + ℓn)) / (N / 2) ≤ eps / 2 := by
    rw [div_le_iff₀ (by linarith), e]
    linarith
  linarith

/-- **Noise-regime lower cost.**  With `τ ≤ 21061 J Δ eps²`, `1 ≤ J`, `1 ≤ Δ ≤ Dn`,
    `1 ≤ eps`, `1 ≤ log n` and `9 · 10⁸ Λ J² Dn³ eps³ log n ≤ n` (`Λ = 80 M`):
    `eps + Ψbar τ eps ≤ 2 eps`. -/
theorem psi_lo_le {M eps Δ Dn τ J ℓn N : ℝ} (hM : 0 ≤ M) (heps : 1 ≤ eps) (hΔ : 1 ≤ Δ)
    (hΔD : Δ ≤ Dn) (hJ : 1 ≤ J) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 21061 * J * Δ * eps ^ 2)
    (hℓ : 1 ≤ ℓn) (hN : 0 < N)
    (hN2 : 9 * 10 ^ 8 * (M * 80) * J ^ 2 * Dn ^ 3 * eps ^ 3 * ℓn ≤ N) :
    eps + (τ + 2 * eps) * M * (80 * (τ * Δ + ℓn)) / (N / 2) ≤ 2 * eps := by
  have hΛ : 0 ≤ M * 80 := by linarith
  have he2 : 1 ≤ eps ^ 2 := one_le_pow₀ heps
  have he2' : eps ≤ eps ^ 2 := by
    have := mul_le_mul_of_nonneg_left heps (by linarith : (0 : ℝ) ≤ eps)
    nlinarith
  have hw1 : 1 ≤ Δ * eps ^ 2 := one_le_mul_of_one_le_of_one_le hΔ he2
  have hw : 1 ≤ J * Δ * eps ^ 2 := by
    have := one_le_mul_of_one_le_of_one_le hJ hw1
    linarith [mul_assoc J Δ (eps ^ 2)]
  have hu0 : 0 ≤ τ + 2 * eps := by linarith
  have hu : τ + 2 * eps ≤ 21063 * (J * Δ * eps ^ 2) := by
    have : eps ^ 2 ≤ J * Δ * eps ^ 2 := by
      have h := le_mul_of_one_le_left (by linarith : (0 : ℝ) ≤ eps ^ 2)
        (one_le_mul_of_one_le_of_one_le hJ hΔ)
      linarith
    linarith
  have hv0 : 0 ≤ τ * Δ + ℓn := by
    have := mul_nonneg hτ0 (by linarith : (0 : ℝ) ≤ Δ)
    linarith
  have hA : 1 ≤ J * Δ * eps ^ 2 * Δ := one_le_mul_of_one_le_of_one_le hw hΔ
  have hv : τ * Δ + ℓn ≤ 21062 * (J * Δ * eps ^ 2 * Δ * ℓn) := by
    have h1 : τ * Δ ≤ 21061 * (J * Δ * eps ^ 2 * Δ) := by
      have := mul_le_mul_of_nonneg_right hτ (by linarith : (0 : ℝ) ≤ Δ)
      linarith
    have h2 : J * Δ * eps ^ 2 * Δ ≤ J * Δ * eps ^ 2 * Δ * ℓn :=
      le_mul_of_one_le_right (by linarith) hℓ
    have h3 : ℓn ≤ J * Δ * eps ^ 2 * Δ * ℓn := le_mul_of_one_le_left (by linarith) hA
    linarith
  have hprod : M * 80 * (τ + 2 * eps) * (τ * Δ + ℓn) ≤
      M * 80 * (21063 * (J * Δ * eps ^ 2)) * (21062 * (J * Δ * eps ^ 2 * Δ * ℓn)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hu hΛ) hv hv0 (mul_nonneg hΛ (by linarith))
  have hrhs : M * 80 * (21063 * (J * Δ * eps ^ 2)) * (21062 * (J * Δ * eps ^ 2 * Δ * ℓn)) =
      eps * (443628906 * ((M * 80) * J ^ 2 * eps ^ 3 * ℓn * Δ ^ 3)) := by ring
  have hD3 : Δ ^ 3 ≤ Dn ^ 3 := pow_le_pow_left₀ (by linarith) hΔD 3
  have hc0 : 0 ≤ (M * 80) * J ^ 2 * eps ^ 3 * ℓn := by
    have : 0 ≤ eps ^ 3 := by positivity
    have : 0 ≤ ℓn := by linarith
    positivity
  have h16 := mul_le_mul_of_nonneg_left hD3 hc0
  have hX0 : 0 ≤ (M * 80) * J ^ 2 * eps ^ 3 * ℓn * Dn ^ 3 := by
    have := pow_nonneg (by linarith : (0 : ℝ) ≤ Dn) 3
    positivity
  have h16' : 443628906 * ((M * 80) * J ^ 2 * eps ^ 3 * ℓn * Dn ^ 3) ≤ N / 2 := by linarith
  have h17 : 443628906 * ((M * 80) * J ^ 2 * eps ^ 3 * ℓn * Δ ^ 3) ≤ N / 2 := by linarith
  have hfin := mul_le_mul_of_nonneg_left h17 (by linarith : (0 : ℝ) ≤ eps)
  have e : (τ + 2 * eps) * M * (80 * (τ * Δ + ℓn)) =
      M * 80 * (τ + 2 * eps) * (τ * Δ + ℓn) := by ring
  have hkey : (τ + 2 * eps) * M * (80 * (τ * Δ + ℓn)) / (N / 2) ≤ eps := by
    rw [div_le_iff₀ (by linarith), e]
    linarith
  linarith

/-- **Curvature-regime cost.**  With `409600 τ log n ≤ eps² Δ`, `16 Λ τ² Δ ≤ eps n`,
    `8 Λ τ Δ ≤ n`, `640 log n ≤ eps Dn`, `Dn < Δ` and `8 Λ log n ≤ n` (`Λ = 80 M`), the
    tube width `x = 80 (√(τ Δ log n) + log n)` satisfies
    `x / Δ + Ψbar τ (x / Δ) ≤ eps`. -/
theorem psi_curv_le {M eps Δ Dn τ ℓn N : ℝ} (hM : 0 ≤ M) (heps : 1 ≤ eps) (hΔ : 1 ≤ Δ)
    (hΔD : Dn < Δ) (hτ0 : 0 ≤ τ) (hℓ : 1 ≤ ℓn) (hN : 0 < N)
    (h1 : 409600 * τ * ℓn ≤ eps ^ 2 * Δ) (h2 : 16 * (M * 80) * τ ^ 2 * Δ ≤ eps * N)
    (h3 : 8 * (M * 80) * τ * Δ ≤ N) (hC1 : 640 * ℓn ≤ eps * Dn)
    (hC2 : 8 * (M * 80) * ℓn ≤ N) :
    80 * (Real.sqrt (τ * Δ * ℓn) + ℓn) / Δ +
      (τ + 2 * (80 * (Real.sqrt (τ * Δ * ℓn) + ℓn) / Δ)) * M *
        (80 * (τ * Δ + ℓn)) / (N / 2) ≤ eps := by
  have hΛ : 0 ≤ M * 80 := by linarith
  have hΔ0 : 0 < Δ := by linarith
  have hℓ0 : 0 ≤ ℓn := by linarith
  set X := 80 * (Real.sqrt (τ * Δ * ℓn) + ℓn) with hX
  -- the tube width is at most `eps Δ / 4`
  have hsq : Real.sqrt (τ * Δ * ℓn) ≤ eps * Δ / 640 := by
    rw [Real.sqrt_le_left (by positivity)]
    have := mul_le_mul_of_nonneg_right h1 hΔ0.le
    have e : (eps * Δ / 640) ^ 2 = eps ^ 2 * Δ * Δ / 409600 := by ring
    rw [e, le_div_iff₀ (by norm_num)]
    linarith
  have hlog : ℓn ≤ eps * Δ / 640 := by
    have := mul_le_mul_of_nonneg_left hΔD.le (by linarith : (0 : ℝ) ≤ eps)
    linarith
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hXle : X ≤ eps * Δ / 4 := by rw [hX]; linarith
  set y := X / Δ with hy
  have hy0 : 0 ≤ y := div_nonneg hX0 hΔ0.le
  have hy4 : y ≤ eps / 4 := by
    rw [hy, div_le_iff₀ hΔ0]
    linarith
  -- the cost term
  have hΛτ : 0 ≤ M * 80 * τ := mul_nonneg hΛ hτ0
  have hΛτΔ : 0 ≤ M * 80 * τ * Δ := mul_nonneg hΛτ hΔ0.le
  have t1 : M * 80 * τ * ℓn ≤ M * 80 * τ * (eps * Δ / 640) :=
    mul_le_mul_of_nonneg_left hlog hΛτ
  have t2 : 2 * y * (M * 80 * τ * Δ) ≤ eps / 2 * (N / 8) :=
    mul_le_mul (by linarith) (by linarith) hΛτΔ (by linarith)
  have t3 : 2 * y * (M * 80 * ℓn) ≤ eps / 2 * (N / 8) :=
    mul_le_mul (by linarith) (by linarith) (mul_nonneg hΛ hℓ0) (by linarith)
  have t4 : eps / 640 * (M * 80 * τ * Δ) ≤ eps / 640 * (N / 8) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have e : (τ + 2 * y) * M * (80 * (τ * Δ + ℓn)) =
      M * 80 * τ ^ 2 * Δ + M * 80 * τ * ℓn + 2 * y * (M * 80 * τ * Δ) +
        2 * y * (M * 80 * ℓn) := by ring
  have e2 : M * 80 * τ * (eps * Δ / 640) = eps / 640 * (M * 80 * τ * Δ) := by ring
  have hkey : (τ + 2 * y) * M * (80 * (τ * Δ + ℓn)) / (N / 2) ≤ 3 * eps / 4 := by
    rw [div_le_iff₀ (by linarith), e]
    nlinarith
  linarith

section Layer

variable {φ φ' : ℝ → ℝ} {L δ : ℝ} {z : ℕ → ℝ} {n : ℕ} {eps : ℝ} {t j : ℕ}

/-- Every layer of ALG-RE on the curved keys is a `CurvedLattice`. -/
theorem KREPath.curvedLattice (H : KREPath φ φ' L δ z n eps t j) (heps : 1 ≤ eps) (hn : 1 ≤ n)
    (ℓ : ℕ) :
    CurvedLattice φ φ' z (z n) L δ 80 n (reDelta eps (fun s => φ (z s / z n)) n ℓ)
      (reSize eps (fun s => φ (z s / z n)) n ℓ) where
  strictMono := H.strictMono
  deriv := H.deriv
  lip := H.lip
  delta_pos := H.delta_pos
  le_deriv := H.le_deriv
  mem_Icc := H.mem_Icc
  one_le_spacing := one_le_reDelta heps hn ℓ
  size := (re_cover heps hn ℓ).1
  Kst_nonneg := by norm_num
  span := H.span
  half_le := H.half_le

theorem KREPath.lam_nonneg (H : KREPath φ φ' L δ z n eps t j) : 0 ≤ kreLam L δ := by
  have h := H.lip 1 ⟨zero_le_one, le_rfl⟩ 0 ⟨le_rfl, zero_le_one⟩
  norm_num at h
  have hL : 0 ≤ L := (abs_nonneg _).trans h
  unfold kreLam
  have := H.delta_pos
  positivity

/-- Basic size facts of a layer: `1 ≤ Δ_ℓ ≤ 2n`, `1 ≤ N_ℓ ≤ 2n`. -/
theorem layer_bounds {p : ℕ → ℝ} (heps : 1 ≤ eps) (hn : 1 ≤ n) (ℓ : ℕ) :
    1 ≤ reDelta eps p n ℓ ∧ reDelta eps p n ℓ ≤ 2 * n ∧ 1 ≤ reSize eps p n ℓ ∧
      reSize eps p n ℓ ≤ 2 * n := by
  have h1 := one_le_reDelta (p := p) heps hn ℓ
  have h2 := one_le_reSize (p := p) heps hn ℓ
  have h3 := reSize_mul_reDelta_lt (p := p) heps hn ℓ
  have h4 : reSize eps p n ℓ ≤ reSize eps p n ℓ * reDelta eps p n ℓ :=
    Nat.le_mul_of_pos_right _ (by omega)
  have h5 : reDelta eps p n ℓ ≤ reSize eps p n ℓ * reDelta eps p n ℓ :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- **Noise regime, upper bracket** (`hup` of `kreHeight_le`, `A = eps²`, `B = 514`,
    additive term `t + 1`). -/
theorem kre_hup (H : KREPath φ φ' L δ z n eps t j) (heps : 1 ≤ eps) (hn3 : 3 ≤ n) {Dn : ℝ}
    (hN1 : 16 * kreLam L δ * Dn ^ 3 * eps ^ 3 * Real.log n ≤ n) :
    ∀ ℓ, (reDelta eps (fun s => φ (z s / z n)) n ℓ : ℝ) ≤ Dn →
      (reSegs eps (fun s => φ (z s / z n)) n ℓ : ℝ) ≤
        514 * reMbar eps (fun s => φ (z s / z n)) n (eps ^ 2) ℓ + ((t : ℝ) + 1) := by
  intro ℓ hD
  have hn : 1 ≤ n := by omega
  have HC := H.curvedLattice heps hn ℓ
  obtain ⟨hΔ1, hΔ2, hK1, hK2⟩ := layer_bounds (p := fun s => φ (z s / z n)) heps hn ℓ
  set Δ := reDelta eps (fun s => φ (z s / z n)) n ℓ with hΔ
  set K := reSize eps (fun s => φ (z s / z n)) n ℓ with hK
  have hΔr : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ1
  have he2 : (1 : ℝ) ≤ eps ^ 2 := one_le_pow₀ heps
  have hw : (1 : ℝ) ≤ Δ * eps ^ 2 := one_le_mul_of_one_le_of_one_le hΔr he2
  obtain ⟨hτ1, hτhalf, hτle⟩ := floor_facts hw
  set τ₀ := ⌊(Δ : ℝ) * eps ^ 2⌋₊ with hτ₀
  have hlog : 1 ≤ Real.log n := one_le_log_of_three_le hn3
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hΨ := psi_up_le (M := L / (2 * δ)) (N := (n : ℝ)) (ℓn := Real.log n)
    (by have := H.lam_nonneg; unfold kreLam at this; linarith) heps hΔr hD
    (Nat.cast_nonneg τ₀) hτle hlog hnpos hN1
  have h1 := HC.finSegCount_curved_le (by linarith) hτ1 hΨ
  have h2 := (H.bracket (eps / 2) (Or.inl rfl) Δ K hΔ1 hK1 hΔ2 hK2).2
  have h1r : (reSegs eps (fun s => φ (z s / z n)) n ℓ : ℝ) ≤
      (finSegCount (eps / 2) (fun k => z (k * Δ)) K : ℝ) + ((K / τ₀ : ℕ) : ℝ) := by
    exact_mod_cast h1
  have h3 := natDiv_le_of_half_le (K := K) (by linarith) hτhalf
  have hm : reMbar eps (fun s => φ (z s / z n)) n (eps ^ 2) ℓ = (K : ℝ) / (Δ * eps ^ 2) := rfl
  have hΔ0 : (Δ : ℝ) ≠ 0 := by positivity
  have he0 : eps ≠ 0 := by positivity
  have e1 : 128 * (K : ℝ) / (Δ * (eps / 2) ^ 2) = 512 * ((K : ℝ) / (Δ * eps ^ 2)) := by
    field_simp; ring
  have e2 : (K : ℝ) / (Δ * eps ^ 2 / 2) = 2 * ((K : ℝ) / (Δ * eps ^ 2)) := by
    field_simp
  rw [hm]
  rw [e1] at h2
  rw [e2] at h3
  linarith

/-- `j kreL (2 eps) Δ + 1 ≤ 21061 j Δ eps²`. -/
theorem tau_one_le {eps : ℝ} (heps : 1 ≤ eps) {j Δ : ℕ} (hj : 1 ≤ j) (hΔ : 1 ≤ Δ) :
    ((j * kreL (2 * eps) Δ + 1 : ℕ) : ℝ) ≤ 21061 * j * Δ * eps ^ 2 := by
  have hk := kreL_le (2 * eps) Δ
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hΔr : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have he2 : (1 : ℝ) ≤ eps ^ 2 := one_le_pow₀ heps
  have hw : (1 : ℝ) ≤ Δ * eps ^ 2 := one_le_mul_of_one_le_of_one_le hΔr he2
  have h1 : (j : ℝ) * kreL (2 * eps) Δ ≤ j * (2 * (2592 * Δ * (2 * eps) ^ 2 + 162)) :=
    mul_le_mul_of_nonneg_left hk (by linarith)
  have h2 : (j : ℝ) ≤ j * (Δ * eps ^ 2) := le_mul_of_one_le_right (by linarith) hw
  have e : (j : ℝ) * (2 * (2592 * Δ * (2 * eps) ^ 2 + 162)) =
      20736 * (j * (Δ * eps ^ 2)) + 324 * j := by ring
  have e2 : (21061 : ℝ) * j * Δ * eps ^ 2 = 21061 * (j * (Δ * eps ^ 2)) := by ring
  push_cast
  rw [e2]
  linarith

/-- **Noise regime, lower bracket** (`hlo` of `logb_lt_kreHeight`, `A = eps²`,
    `a = aRE / 4`). -/
theorem kre_hlo (H : KREPath φ φ' L δ z n eps t j) (heps : 1 ≤ eps) (hn3 : 3 ≤ n)
    (hj : 1 ≤ j) {Dn : ℝ}
    (hN2 : 9 * 10 ^ 8 * kreLam L δ * (j : ℝ) ^ 2 * Dn ^ 3 * eps ^ 3 * Real.log n ≤ n) :
    ∀ ℓ, (reDelta eps (fun s => φ (z s / z n)) n ℓ : ℝ) ≤ Dn →
      aRE / 4 * reMbar eps (fun s => φ (z s / z n)) n (eps ^ 2) ℓ - t ≤
        (reSegs eps (fun s => φ (z s / z n)) n ℓ : ℝ) := by
  intro ℓ hD
  have hn : 1 ≤ n := by omega
  have HC := H.curvedLattice heps hn ℓ
  obtain ⟨hΔ1, hΔ2, hK1, hK2⟩ := layer_bounds (p := fun s => φ (z s / z n)) heps hn ℓ
  set Δ := reDelta eps (fun s => φ (z s / z n)) n ℓ with hΔ
  set K := reSize eps (fun s => φ (z s / z n)) n ℓ with hK
  have hΔr : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ1
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hlog : 1 ≤ Real.log n := one_le_log_of_three_le hn3
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set τ₁ := j * kreL (2 * eps) Δ + 1 with hτ₁
  have hτ := tau_one_le heps hj hΔ1
  rw [← hτ₁] at hτ
  have hΨ := psi_lo_le (M := L / (2 * δ)) (N := (n : ℝ)) (ℓn := Real.log n)
    (by have := H.lam_nonneg; unfold kreLam at this; linarith) heps hΔr hD hjr
    (Nat.cast_nonneg τ₁) hτ hlog hnpos hN2
  have hV : ∀ a, a + τ₁ ≤ K → ¬ windowFeasible (2 * eps) (fun k => z (k * Δ)) a (a + τ₁) :=
    fun a ha => H.window Δ a hΔ1 hΔ2 (by omega)
  have h1 := HC.finSegCount_le_curved hΨ hV
  have h2 := (H.bracket (2 * eps) (Or.inr rfl) Δ K hΔ1 hK1 hΔ2 hK2).1
  have h1r : (finSegCount (2 * eps) (fun k => z (k * Δ)) K : ℝ) ≤
      (reSegs eps (fun s => φ (z s / z n)) n ℓ : ℝ) := by
    exact_mod_cast h1
  have hm : reMbar eps (fun s => φ (z s / z n)) n (eps ^ 2) ℓ = (K : ℝ) / (Δ * eps ^ 2) := rfl
  have hΔ0 : (Δ : ℝ) ≠ 0 := by positivity
  have he0 : eps ≠ 0 := by positivity
  have e1 : aLow * (K : ℝ) / (Δ * (2 * eps) ^ 2) = aLow / 4 * ((K : ℝ) / (Δ * eps ^ 2)) := by
    field_simp; ring
  have hm0 : 0 ≤ (K : ℝ) / (Δ * eps ^ 2) := by positivity
  have h3 : aRE / 4 * ((K : ℝ) / (Δ * eps ^ 2)) ≤ aLow / 4 * ((K : ℝ) / (Δ * eps ^ 2)) :=
    mul_le_mul_of_nonneg_right (by linarith [aRE_le_aLow]) hm0
  rw [hm]
  rw [e1] at h2
  linarith

/-- Halving all three constants halves `τ♭`. -/
theorem kreTau_half (n : ℕ) (c₁ c₂ c₃ Δ : ℝ) :
    kreTau n (c₁ / 2) (c₂ / 2) (c₃ / 2) Δ = kreTau n c₁ c₂ c₃ Δ / 2 := by
  unfold kreTau
  rw [show c₁ / 2 * Δ = c₁ * Δ / 2 by ring,
    show c₂ / 2 * Real.sqrt (n / Δ) = c₂ * Real.sqrt (n / Δ) / 2 by ring,
    show c₃ / 2 * (n / Δ) = c₃ * (n / Δ) / 2 by ring,
    min_div_div_right (by norm_num), min_div_div_right (by norm_num)]

/-- The three entries of `τ♭` for the layer-side constants, in product form. -/
theorem kreTau_entries {n : ℕ} {eps L δ Δ τ : ℝ} (hΛ : 0 < kreLam L δ) (heps : 0 < eps)
    (hΔ : 0 < Δ) (hℓ : 0 < Real.log n) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ kreTau n (kreC₁ n eps) (kreC₂ eps L δ) (kreC₃ L δ) Δ) :
    409600 * τ * Real.log n ≤ eps ^ 2 * Δ ∧ 16 * kreLam L δ * τ ^ 2 * Δ ≤ eps * n ∧
      8 * kreLam L δ * τ * Δ ≤ n := by
  unfold kreTau at hτ
  have ha := hτ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hb := hτ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hc := hτ.trans (min_le_right _ _)
  unfold kreC₁ at ha
  unfold kreC₂ at hb
  unfold kreC₃ at hc
  set Λ := kreLam L δ with hΛdef
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨?_, ?_, ?_⟩
  · calc 409600 * τ * Real.log n
        ≤ 409600 * (eps ^ 2 / (409600 * Real.log n) * Δ) * Real.log n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha (by norm_num)) hℓ.le
      _ = eps ^ 2 * Δ := by field_simp
  · have h0 : (0 : ℝ) ≤ eps / (16 * Λ) := by positivity
    have h0' : (0 : ℝ) ≤ n / Δ := by positivity
    have hsq := pow_le_pow_left₀ hτ0 hb 2
    rw [mul_pow, Real.sq_sqrt h0, Real.sq_sqrt h0'] at hsq
    calc 16 * Λ * τ ^ 2 * Δ ≤ 16 * Λ * (eps / (16 * Λ) * (n / Δ)) * Δ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity)) hΔ.le
      _ = eps * n := by field_simp
  · calc 8 * Λ * τ * Δ ≤ 8 * Λ * (1 / (8 * Λ) * (n / Δ)) * Δ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity)) hΔ.le
      _ = n := by field_simp

/-- **Curvature regime** (`hC` of `kreHeight_le`, with the halved constants
    `c₁ / 2`, `c₂ / 2`, `c₃ / 2`). -/
theorem kre_hC (H : KREPath φ φ' L δ z n eps t j) (heps : 1 ≤ eps) (hn3 : 3 ≤ n) (hL : 0 < L)
    {Dn : ℝ} (hC1 : 640 * Real.log n ≤ eps * Dn) (hC2 : 8 * kreLam L δ * Real.log n ≤ n) :
    ∀ ℓ, Dn < (reDelta eps (fun s => φ (z s / z n)) n ℓ : ℝ) →
      1 ≤ kreTau n (kreC₁ n eps / 2) (kreC₂ eps L δ / 2) (kreC₃ L δ / 2)
        (reDelta eps (fun s => φ (z s / z n)) n ℓ) →
      (reSegs eps (fun s => φ (z s / z n)) n ℓ : ℝ) ≤
        reSize eps (fun s => φ (z s / z n)) n ℓ /
          kreTau n (kreC₁ n eps / 2) (kreC₂ eps L δ / 2) (kreC₃ L δ / 2)
            (reDelta eps (fun s => φ (z s / z n)) n ℓ) + 1 := by
  intro ℓ hD hτ
  have hn : 1 ≤ n := by omega
  have HC := H.curvedLattice heps hn ℓ
  obtain ⟨hΔ1, hΔ2, hK1, hK2⟩ := layer_bounds (p := fun s => φ (z s / z n)) heps hn ℓ
  set Δ := reDelta eps (fun s => φ (z s / z n)) n ℓ with hΔ
  set K := reSize eps (fun s => φ (z s / z n)) n ℓ with hK
  have hΔr : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ1
  have hlog : 1 ≤ Real.log n := one_le_log_of_three_le hn3
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [kreTau_half] at hτ ⊢
  set x := kreTau n (kreC₁ n eps) (kreC₂ eps L δ) (kreC₃ L δ) Δ with hx
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨hτ1, hτhalf, hτle⟩ := floor_facts hx1
  set τb := ⌊x⌋₊ with hτb
  have hδ := H.delta_pos
  have hΛ : 0 < kreLam L δ := by unfold kreLam; positivity
  obtain ⟨e1, e2, e3⟩ := kreTau_entries hΛ (by linarith) (by linarith) (by linarith)
    (Nat.cast_nonneg τb) hτle
  have hxeps := psi_curv_le (M := L / (2 * δ)) (N := (n : ℝ)) (ℓn := Real.log n)
    (by positivity) heps hΔr hD (Nat.cast_nonneg τb) hlog hnpos e1 e2 e3 hC1 hC2
  have h1 := HC.finSegCount_curved_le_div H.tube hτ1 le_rfl hxeps
  have h1r : (reSegs eps (fun s => φ (z s / z n)) n ℓ : ℝ) ≤ ((K / τb : ℕ) : ℝ) + 1 := by
    exact_mod_cast h1
  have h3 := natDiv_le_of_half_le (K := K) (by linarith) hτhalf
  linarith

/-! ## The height of ALG-RE on the curved keys -/

/-- **Upper bound.**  `kreHeight_le` with `A = eps²`, `B = 514`, `a = aRE / 4`,
    additive term `t + 1` and the recursion constants `c₁ / 2`, `c₂ / 2`, `c₃ / 2`. -/
theorem kreBridge_height_le (H : KREPath φ φ' L δ z n eps t j) (heps : 1 ≤ eps)
    (hn3 : 3 ≤ n) (hL : 0 < L) {Dn : ℝ}
    (hN1 : 16 * kreLam L δ * Dn ^ 3 * eps ^ 3 * Real.log n ≤ n)
    (hC1 : 640 * Real.log n ≤ eps * Dn) (hC2 : 8 * kreLam L δ * Real.log n ≤ n)
    (hc₁D : 1 ≤ kreC₁ n eps / 2 * Dn)
    (hside : 64 * (kreC₂ eps L δ / 2) ^ 2 * n ≤ (kreC₁ n eps / 2) ^ 5 * Dn ^ 6)
    (hq : 1 < eps ^ 2 / (4 * 514)) (hqn : eps ^ 2 / (4 * 514) ≤ n) :
    (reHeight eps (fun s => φ (z s / z n)) n : ℝ) ≤
      Real.logb 2 (Real.log n / Real.log (eps ^ 2 / (4 * 514))) +
        Real.logb 2 (2 * (514 * (4 * ((t : ℝ) + 1) / (aRE / 4)) + ((t : ℝ) + 1))) +
        Real.logb 2 (Real.log n) +
        Real.logb 2 (max (3 * max 1 (16 / (kreC₂ eps L δ / 2) ^ 2)) (4 / (kreC₃ L δ / 2)) + 1) +
        8 := by
  have hδ := H.delta_pos
  have hlog : 1 ≤ Real.log n := one_le_log_of_three_le hn3
  have hΛ : 0 < kreLam L δ := by unfold kreLam; positivity
  have hc₁ : 0 < kreC₁ n eps / 2 := by
    unfold kreC₁
    have : 0 < eps ^ 2 := by positivity
    have : 0 < 409600 * Real.log n := by linarith
    positivity
  have hc₂ : 0 < kreC₂ eps L δ / 2 := by
    unfold kreC₂
    have : 0 < eps / (16 * kreLam L δ) := div_pos (by linarith) (by linarith)
    have := Real.sqrt_pos.2 this
    linarith
  have hc₃ : 0 < kreC₃ L δ / 2 := by
    unfold kreC₃
    have : 0 < 1 / (8 * kreLam L δ) := div_pos one_pos (by linarith)
    linarith
  have ha : 0 < aRE / 4 := by linarith [aRE_pos]
  have ha1 : aRE / 4 ≤ 1 := by linarith [aRE_le_one]
  have ht : (1 : ℝ) ≤ (t : ℝ) + 1 := by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  exact kreHeight_le heps hn3 ha ha1 (by norm_num) ht hq hqn hc₁ hc₂ hc₃ hc₁D hside
    (kre_hup H heps hn3 hN1) (kre_hC H heps hn3 hL hC1 hC2)

/-- **Lower bound.**  `logb_lt_kreHeight` with `A = eps²` and `a = aRE / 4`. -/
theorem kreBridge_logb_lt_height (H : KREPath φ φ' L δ z n eps t j) (heps : 1 ≤ eps)
    (hn3 : 3 ≤ n) (ht : 1 ≤ t) (hj : 1 ≤ j) {Dn : ℝ}
    (hN2 : 9 * 10 ^ 8 * kreLam L δ * (j : ℝ) ^ 2 * Dn ^ 3 * eps ^ 3 * Real.log n ≤ n)
    (hDn : Real.sqrt (Real.sqrt n) ≤ Dn) (hsqrt : 4 * (t : ℝ) / (aRE / 4) ≤ Real.sqrt n) :
    Real.logb 2 (Real.log n / (2 * Real.log (2 / (aRE / 4) * eps ^ 2))) <
      reHeight eps (fun s => φ (z s / z n)) n := by
  have ha : 0 < aRE / 4 := by linarith [aRE_pos]
  have ha1 : aRE / 4 ≤ 1 := by linarith [aRE_le_one]
  have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
  exact logb_lt_kreHeight heps (by omega) ha ha1 htr (one_le_pow₀ heps) hDn
    (kre_hlo H heps hn3 hj hN2) hsqrt

end Layer

end

end PGM
