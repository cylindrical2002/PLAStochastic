import PLAStochastic.Index.GRE.PreciseHeightDefs

/-!
# Uniform layer bounds of `thm:uniform`: noise bracket, band dichotomy, curvature upper count

Deterministic per-layer bounds of Section 3 of `thm:uniform`
(`research/2026-09-24-re-curvature-uniform/tex/main.tex`) for the Rényi keys
`renyiKeys f n ω` of a density `f ∈ 𝔉_δ`, off the bad event `kreBad` of `PLAStochastic.Index.KRE.GoodEvent`.
The curvature size enters only through `D = effDelta n δ ∈ (0, 1]`: the quantile derivative
`1 / f ∘ Q` is `D L / f₋³`-Lipschitz, so `KREPath` holds with that constant (`krePath_unif`)
and `Λ = kreLam (D L / f₋³) (1 / f₊) = κ D` with `κ = 40 f₊ L / f₋³` (`kreLam_unif`).

* `lem:noise` (`unif_noise`): `kre_hup`, `kre_hlo` with `Dn = Δ_ℓ` and `re_compress`.
* `lem:band` (`unif_band`): `kre_hC`; all three entries of `τ♭` exceed `2 (n^{1/4} + 1)`.
* `lem:curv`(b) (`unif_curvUp`): `kre_hC`, `M ≤ N_ℓ / τ♭ + 1`, entry by entry.

The numerical side conditions on `n` and `ε` are bundled in `UnifCond`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Topology

/-! ## Constants and the path data -/

/-- `κ = 40 f₊ L / f₋³`. -/
def unifKappa (c : DensityClassParams) : ℝ := 40 * c.fmax * c.L / c.fmin ^ 3

theorem unifKappa_pos (c : DensityClassParams) : 0 < unifKappa c := by
  unfold unifKappa
  have := c.fmin_pos
  have := c.L_pos
  have : 0 < c.fmax := lt_of_lt_of_le one_pos c.one_le_fmax
  positivity

/-- `Λ = κ D` for the Lipschitz constant `D L / f₋³` and `φ' ≥ 1 / f₊`. -/
theorem kreLam_unif (c : DensityClassParams) (D : ℝ) :
    kreLam (D * c.L / c.fmin ^ 3) (1 / c.fmax) = D * unifKappa c := by
  unfold kreLam unifKappa
  have := c.fmin_pos.ne'
  have : c.fmax ≠ 0 := (lt_of_lt_of_le one_pos c.one_le_fmax).ne'
  field_simp
  ring

theorem effDelta_pos {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) : 0 < effDelta n δ := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  exact lt_of_lt_of_le (by positivity) (le_max_right _ _)

theorem effDelta_le_one {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : δ ≤ 1) : effDelta n δ ≤ 1 := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ h1
  exact max_le hδ ((div_le_one (by linarith)).2 this)

/-- Off the bad event the reference walk and the quantile of `f ∈ 𝔉_δ` form a `KREPath`
with Lipschitz constant `effDelta n δ · L / f₋³`. -/
theorem krePath_unif {c : DensityClassParams} {δ : ℝ} {f : ℝ → ℝ} (hf : c.Mem δ f) {n : ℕ}
    (hn : 160000 ≤ n) {eps : ℝ} {t j : ℕ} {ω : ℕ → ℝ} (hω : ω ∉ kreBad expCoord n eps t j) :
    KREPath (quantK f 0 1) (fun u => 1 / f (quantK f 0 1 u)) (effDelta n δ * c.L / c.fmin ^ 3)
      (1 / c.fmax) (fun s => expPartial s ω) n eps t j where
  deriv := kre_quantK_deriv hf.2.2.1
  lip := fun _ hx _ hy => (abs_inv_f_quantK_sub_le hf.2.2.1 hx hy).trans
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) c.L_pos.le) (pow_nonneg c.fmin_pos.le 3))
      (abs_nonneg _))
  delta_pos := kre_quantK_delta_pos hf.2.2.1
  le_deriv := kre_quantK_le_deriv hf.2.2.1
  strictMono := refWalk_strictMono hω
  mem_Icc := refWalk_div_mem_Icc hω
  span := refWalk_span hω
  tube := refWalk_tube hω
  half_le := half_le_refWalk hω hn
  bracket := fun _ hθ => refWalk_bracket hω hθ
  window := refWalk_not_windowFeasible hω

/-! ## Side conditions -/

/-- The numerical side conditions on `n` and `ε` of the layer bounds; `q = n^{1/4}`. -/
structure UnifCond (c : DensityClassParams) (n : ℕ) (eps : ℝ) : Prop where
  n_ge : 160000 ≤ n
  eps_ge : 46 ≤ eps
  noise1 : 16 * unifKappa c ≤ Real.log n ^ 3
  noise2 : 9 * 10 ^ 8 * unifKappa c * CjK ^ 2 ≤ Real.log n
  noise3 : 64 / (cRE * aRE) + 32 / aRE ≤ Real.log n
  lam : 8 * unifKappa c * Real.log n ≤ n
  band0 : 2 * 640 ^ 3 * Real.log n ^ 7 ≤ n
  band1 : 3276800 ^ 3 * Real.log n ^ 7 ≤ (n : ℝ) ^ (1 / 4 : ℝ)
  band2 : 1024 ^ 3 * unifKappa c ^ 3 * Real.log n ^ 4 ≤ (n : ℝ) ^ (1 / 4 : ℝ)
  band3 : 64 ^ 3 * unifKappa c ^ 3 * Real.log n ^ 4 ≤ (n : ℝ) ^ (1 / 4 : ℝ)
  low : 2 + 80 * Real.log n ≤ n

namespace UnifCond

variable {c : DensityClassParams} {n : ℕ} {eps : ℝ}

theorem three_le (hc : UnifCond c n eps) : 3 ≤ n := le_trans (by norm_num) hc.n_ge

theorem one_le (hc : UnifCond c n eps) : 1 ≤ n := le_trans (by norm_num) hc.n_ge

theorem one_le_eps (hc : UnifCond c n eps) : 1 ≤ eps := le_trans (by norm_num) hc.eps_ge

theorem one_le_log (hc : UnifCond c n eps) : 1 ≤ Real.log n :=
  one_le_log_of_three_le hc.three_le

theorem one_le_q (hc : UnifCond c n eps) : 1 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast hc.one_le
  exact Real.one_le_rpow this (by norm_num)

end UnifCond

theorem rpow_quarter_pow_four (n : ℕ) : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

/-! ## `lem:noise` -/

section Layer

variable {c : DensityClassParams} {n : ℕ} {eps : ℝ} {ω : ℕ → ℝ} {δ : ℝ} {f : ℝ → ℝ}

/-- **Noise layers** (`lem:noise`). -/
theorem unif_noise (hc : UnifCond c n eps)
    (hω : ω ∉ kreBad expCoord n eps (tRE n) (jK n)) (hf : c.Mem δ f) (ℓ : ℕ)
    (hN1 : effDelta n δ * eps ^ 3 * (reDelta eps (renyiKeys f n ω) n ℓ : ℝ) ^ 3 ≤
      n / Real.log n ^ 4)
    (hN2 : eps ^ 2 * (reDelta eps (renyiKeys f n ω) n ℓ : ℝ) ^ 2 ≤ n / Real.log n ^ 2) :
    1 / 2056 * eps ^ 2 * (reDelta eps (renyiKeys f n ω) n ℓ : ℝ) ^ 2 ≤
        reDelta eps (renyiKeys f n ω) n (ℓ + 1) ∧
      (reDelta eps (renyiKeys f n ω) n (ℓ + 1) : ℝ) ≤
        8 / aRE * eps ^ 2 * (reDelta eps (renyiKeys f n ω) n ℓ : ℝ) ^ 2 ∧
      2 ≤ reSize eps (renyiKeys f n ω) n (ℓ + 1) := by
  have H := krePath_unif hf hc.n_ge hω
  have heps := hc.one_le_eps
  have hn3 := hc.three_le
  have hn1 := hc.one_le
  have hY := hc.one_le_log
  have hc1 := hc.noise1
  have hc2 := hc.noise2
  have hc3 := hc.noise3
  have hjle : (jK n : ℝ) ≤ CjK * Real.log n := jK_le hY
  set Y := Real.log n with hYdef
  set D := effDelta n δ with hDdef
  set κ := unifKappa c with hκdef
  have hκ : 0 < κ := unifKappa_pos c
  have hD0 : 0 < D := effDelta_pos hn1 δ
  set p := renyiKeys f n ω with hp
  set Δ := reDelta eps p n ℓ with hΔdef
  have hΔ1 : (1 : ℝ) ≤ Δ := by exact_mod_cast one_le_reDelta (p := p) heps hn1 ℓ
  have hΔ0 : (0 : ℝ) < Δ := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  have hY0 : 0 < Y := by linarith
  have hY4 : 0 < Y ^ 4 := by positivity
  have he0 : 0 < eps := by linarith
  -- the cube condition in the form `D ε³ Δ³ Y⁴ ≤ n`
  have hcube : D * eps ^ 3 * Δ ^ 3 * Y ^ 4 ≤ n := by
    have := (le_div_iff₀ hY4).1 hN1
    linarith
  have hX0 : 0 ≤ D * eps ^ 3 * Δ ^ 3 := by positivity
  -- condition of `kre_hup`
  have hup1 : 16 * kreLam (D * c.L / c.fmin ^ 3) (1 / c.fmax) * (Δ : ℝ) ^ 3 * eps ^ 3 * Y ≤
      n := by
    rw [kreLam_unif]
    have h1 : 16 * κ * (D * eps ^ 3 * Δ ^ 3) * Y ≤ Y ^ 3 * (D * eps ^ 3 * Δ ^ 3) * Y :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc1 hX0) hY0.le
    have e : Y ^ 3 * (D * eps ^ 3 * Δ ^ 3) * Y = D * eps ^ 3 * Δ ^ 3 * Y ^ 4 := by ring
    calc 16 * (D * κ) * (Δ : ℝ) ^ 3 * eps ^ 3 * Y = 16 * κ * (D * eps ^ 3 * Δ ^ 3) * Y := by
          ring
      _ ≤ _ := h1
      _ = _ := e
      _ ≤ n := hcube
  have hup : (reSegs eps p n ℓ : ℝ) ≤ 514 * reMbar eps p n (eps ^ 2) ℓ + ((tRE n : ℝ) + 1) :=
    kre_hup H heps hn3 hup1 ℓ le_rfl
  -- condition of `kre_hlo`
  have hj : 1 ≤ jK n := one_le_jK (by omega)
  have hlo1 : 9 * 10 ^ 8 * kreLam (D * c.L / c.fmin ^ 3) (1 / c.fmax) * (jK n : ℝ) ^ 2 *
      (Δ : ℝ) ^ 3 * eps ^ 3 * Y ≤ n := by
    rw [kreLam_unif]
    have hj0 : (0 : ℝ) ≤ jK n := Nat.cast_nonneg _
    have hj2 : (jK n : ℝ) ^ 2 ≤ (CjK * Y) ^ 2 := pow_le_pow_left₀ hj0 hjle 2
    have hA : 0 ≤ 9 * 10 ^ 8 * κ * (D * eps ^ 3 * Δ ^ 3) * Y := by positivity
    have h1 : 9 * 10 ^ 8 * κ * (D * eps ^ 3 * Δ ^ 3) * Y * (jK n : ℝ) ^ 2 ≤
        9 * 10 ^ 8 * κ * (D * eps ^ 3 * Δ ^ 3) * Y * (CjK * Y) ^ 2 :=
      mul_le_mul_of_nonneg_left hj2 hA
    have h2 : 9 * 10 ^ 8 * κ * CjK ^ 2 * (D * eps ^ 3 * Δ ^ 3 * Y ^ 3) ≤
        Y * (D * eps ^ 3 * Δ ^ 3 * Y ^ 3) :=
      mul_le_mul_of_nonneg_right hc2 (by positivity)
    calc 9 * 10 ^ 8 * (D * κ) * (jK n : ℝ) ^ 2 * (Δ : ℝ) ^ 3 * eps ^ 3 * Y
        = 9 * 10 ^ 8 * κ * (D * eps ^ 3 * Δ ^ 3) * Y * (jK n : ℝ) ^ 2 := by ring
      _ ≤ 9 * 10 ^ 8 * κ * (D * eps ^ 3 * Δ ^ 3) * Y * (CjK * Y) ^ 2 := h1
      _ = 9 * 10 ^ 8 * κ * CjK ^ 2 * (D * eps ^ 3 * Δ ^ 3 * Y ^ 3) := by ring
      _ ≤ Y * (D * eps ^ 3 * Δ ^ 3 * Y ^ 3) := h2
      _ = D * eps ^ 3 * Δ ^ 3 * Y ^ 4 := by ring
      _ ≤ n := hcube
  have hlo : aRE / 4 * reMbar eps p n (eps ^ 2) ℓ - (tRE n : ℝ) ≤ reSegs eps p n ℓ :=
    kre_hlo H heps hn3 hj hlo1 ℓ le_rfl
  -- the mean count is at least `Y²`
  have hmbar : Y ^ 2 ≤ reMbar eps p n (eps ^ 2) ℓ := by
    have hcov := (re_cover (p := p) heps hn1 ℓ).2
    have hK : (n : ℝ) ≤ (reSize eps p n ℓ : ℝ) * Δ := by exact_mod_cast hcov
    have hY2 : 0 < Y ^ 2 := by positivity
    have h1 : eps ^ 2 * Δ ^ 2 * Y ^ 2 ≤ n := by
      have := (le_div_iff₀ hY2).1 hN2
      linarith
    unfold reMbar
    rw [le_div_iff₀ (by positivity)]
    have h2 : Y ^ 2 * (Δ * eps ^ 2) * Δ ≤ (reSize eps p n ℓ : ℝ) * Δ := by
      have e : Y ^ 2 * (Δ * eps ^ 2) * Δ = eps ^ 2 * Δ ^ 2 * Y ^ 2 := by ring
      rw [e]
      exact h1.trans hK
    exact le_of_mul_le_mul_right h2 hΔ0
  -- the concentration threshold
  have htle : (tRE n : ℝ) ≤ 4 * Y / cRE + 1 := by
    have hcRE := cRE_pos
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 4 * Y / cRE by positivity)
    unfold tRE
    rw [← hYdef]
    linarith
  have haRE := aRE_pos
  have hcRE := cRE_pos
  have hτ : 4 * ((tRE n : ℝ) + 1) / (aRE / 4) ≤ reMbar eps p n (eps ^ 2) ℓ := by
    refine le_trans ?_ hmbar
    have h1 : 4 * ((tRE n : ℝ) + 1) / (aRE / 4) ≤ 4 * (4 * Y / cRE + 2) / (aRE / 4) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    have e : 4 * (4 * Y / cRE + 2) / (aRE / 4) = 64 / (cRE * aRE) * Y + 32 / aRE := by
      field_simp; ring
    have h32 : 0 ≤ 32 / aRE := by positivity
    have h2 : 64 / (cRE * aRE) * Y + 32 / aRE ≤ (64 / (cRE * aRE) + 32 / aRE) * Y := by
      have : 32 / aRE ≤ 32 / aRE * Y := le_mul_of_one_le_right h32 hY
      linarith
    have h3 : (64 / (cRE * aRE) + 32 / aRE) * Y ≤ Y * Y :=
      mul_le_mul_of_nonneg_right hc3 hY0.le
    rw [e] at h1
    have : Y * Y = Y ^ 2 := by ring
    linarith
  have hA : 4 * (514 : ℝ) ≤ eps ^ 2 :=
    calc 4 * (514 : ℝ) ≤ 46 ^ 2 := by norm_num
      _ ≤ eps ^ 2 := pow_le_pow_left₀ (by norm_num) hc.eps_ge 2
  have hlo' : aRE / 4 * reMbar eps p n (eps ^ 2) ℓ - ((tRE n : ℝ) + 1) ≤ reSegs eps p n ℓ := by
    linarith
  have ht1 : (1 : ℝ) ≤ (tRE n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ tRE n := Nat.cast_nonneg _
    linarith
  obtain ⟨h1, h2, -⟩ := re_compress heps hn1 (a := aRE / 4) (B := 514) (t := (tRE n : ℝ) + 1)
    (by linarith) (by linarith [aRE_le_one]) (by norm_num) ht1 hA hlo' hup hτ
  have h3 := (re_compress_upper heps hn1 (a := aRE / 4) (t := (tRE n : ℝ) + 1)
    (by linarith) ht1 (by linarith) hlo' hτ).2.2
  refine ⟨?_, ?_, h3⟩
  · have e : eps ^ 2 / (4 * 514) * (Δ : ℝ) ^ 2 = 1 / 2056 * eps ^ 2 * (Δ : ℝ) ^ 2 := by ring
    rw [← e]
    exact h1
  · have e : 2 / (aRE / 4) * eps ^ 2 * (Δ : ℝ) ^ 2 = 8 / aRE * eps ^ 2 * (Δ : ℝ) ^ 2 := by
      field_simp; ring
    rw [← e]
    exact h2

end Layer

/-! ## `lem:band` and `lem:curv`(b) -/

/-- The three entries of `τ♭` for the layer-side constants at curvature size `D`. -/
theorem kreTau_unif (c : DensityClassParams) (n : ℕ) (eps D Δ : ℝ) :
    kreTau n (kreC₁ n eps / 2) (kreC₂ eps (D * c.L / c.fmin ^ 3) (1 / c.fmax) / 2)
        (kreC₃ (D * c.L / c.fmin ^ 3) (1 / c.fmax) / 2) Δ =
      min (min (eps ^ 2 / (409600 * Real.log n) / 2 * Δ)
          (Real.sqrt (eps / (16 * (D * unifKappa c))) / 2 * Real.sqrt (n / Δ)))
        (1 / (8 * (D * unifKappa c)) / 2 * (n / Δ)) := by
  unfold kreTau kreC₁ kreC₂ kreC₃
  rw [kreLam_unif]

/-- `640 log n < R` from `n ≤ R³ log⁴ n`. -/
theorem lt_mul_of_cube {c : DensityClassParams} {n : ℕ} {eps : ℝ} (hc : UnifCond c n eps)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : (n : ℝ) ≤ R ^ 3 * Real.log n ^ 4) :
    640 * Real.log n < R := by
  have hY := hc.one_le_log
  have h0 := hc.band0
  by_contra h
  have h' : R ≤ 640 * Real.log n := not_lt.1 h
  have h3 : R ^ 3 ≤ (640 * Real.log n) ^ 3 := pow_le_pow_left₀ hR0 h' 3
  have h4 : R ^ 3 * Real.log n ^ 4 ≤ (640 * Real.log n) ^ 3 * Real.log n ^ 4 :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  have e : (640 * Real.log n) ^ 3 * Real.log n ^ 4 = 640 ^ 3 * Real.log n ^ 7 := by ring
  have h7 : 0 < 640 ^ 3 * Real.log n ^ 7 := by positivity
  linarith

/-- The side conditions of `kre_hC` at curvature size `D ≤ 1` with `Dn = 640 log n / ε`. -/
theorem kre_hC_conds {c : DensityClassParams} {n : ℕ} {eps : ℝ} (hc : UnifCond c n eps)
    {D : ℝ} (hD0 : 0 < D) (hD1 : D ≤ 1) :
    0 < D * c.L / c.fmin ^ 3 ∧ 640 * Real.log n ≤ eps * (640 * Real.log n / eps) ∧
      8 * kreLam (D * c.L / c.fmin ^ 3) (1 / c.fmax) * Real.log n ≤ n := by
  have he0 : 0 < eps := by linarith [hc.one_le_eps]
  have hκ := unifKappa_pos c
  have hY := hc.one_le_log
  refine ⟨by have := c.L_pos; have := c.fmin_pos; positivity, by rw [mul_div_cancel₀ _ he0.ne'],
    ?_⟩
  rw [kreLam_unif]
  have h1 : D * unifKappa c ≤ unifKappa c := mul_le_of_le_one_left hκ.le hD1
  have h2 : 8 * (D * unifKappa c) * Real.log n ≤ 8 * unifKappa c * Real.log n := by
    have : (0 : ℝ) ≤ Real.log n := by linarith
    nlinarith
  linarith [hc.lam]

/-- `√(a + b) ≤ √a + √b`. -/
theorem sqrt_add_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity), add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
  have := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  nlinarith

section Layer2

variable {c : DensityClassParams} {n : ℕ} {eps : ℝ} {ω : ℕ → ℝ} {δ : ℝ} {f : ℝ → ℝ}

/-- **Band layers** (`lem:band`): one segment, or promotion step at least `n^{1/4}`. -/
theorem unif_band (hc : UnifCond c n eps)
    (hω : ω ∉ kreBad expCoord n eps (tRE n) (jK n)) (hf : c.Mem δ f) (ℓ : ℕ)
    (hB : (n : ℝ) / Real.log n ^ 4 <
        effDelta n δ * eps ^ 3 * (reDelta eps (renyiKeys f n ω) n ℓ : ℝ) ^ 3 ∨
      (n : ℝ) / Real.log n ^ 2 < eps ^ 2 * (reDelta eps (renyiKeys f n ω) n ℓ : ℝ) ^ 2)
    (hB2 : effDelta n δ * eps ^ 3 * (reDelta eps (renyiKeys f n ω) n ℓ : ℝ) ^ 3 <
      n * Real.log n ^ 4) :
    reSegs eps (renyiKeys f n ω) n ℓ = 1 ∨
      (n : ℝ) ^ (1 / 4 : ℝ) ≤ reStep eps (renyiKeys f n ω) n ℓ := by
  have H := krePath_unif hf hc.n_ge hω
  have heps := hc.one_le_eps
  have he0 : 0 < eps := by linarith
  have hn3 := hc.three_le
  have hn1 := hc.one_le
  have hY := hc.one_le_log
  have hb1 := hc.band1
  have hb2 := hc.band2
  have hb3 := hc.band3
  have hq1 : 1 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := hc.one_le_q
  have hq4 := rpow_quarter_pow_four n
  have hD0 : 0 < effDelta n δ := effDelta_pos hn1 δ
  have hD1 : effDelta n δ ≤ 1 := effDelta_le_one hn1 hf.2.1
  obtain ⟨hL, hC1, hC2⟩ := kre_hC_conds hc hD0 hD1
  set Y := Real.log n with hYdef
  set D := effDelta n δ with hDdef
  set κ := unifKappa c with hκdef
  have hκ : 0 < κ := unifKappa_pos c
  set p := renyiKeys f n ω with hp
  set Δ := reDelta eps p n ℓ with hΔdef
  have hΔ1 : (1 : ℝ) ≤ Δ := by exact_mod_cast one_le_reDelta (p := p) heps hn1 ℓ
  have hΔ0 : (0 : ℝ) < Δ := by linarith
  set q := (n : ℝ) ^ (1 / 4 : ℝ) with hqdef
  have hq0 : 0 < q := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  have hY0 : 0 < Y := by linarith
  -- `n < (ε Δ)³ Y⁴`
  have hR1 : 1 ≤ eps * Δ := one_le_mul_of_one_le_of_one_le heps hΔ1
  have hR : (n : ℝ) < (eps * Δ) ^ 3 * Y ^ 4 := by
    rcases hB with hA | hA
    · have h1 := (div_lt_iff₀ (by positivity : (0 : ℝ) < Y ^ 4)).1 hA
      have h2 : D * eps ^ 3 * (Δ : ℝ) ^ 3 ≤ (eps * Δ) ^ 3 := by
        have e : (eps * Δ) ^ 3 = 1 * (eps ^ 3 * (Δ : ℝ) ^ 3) := by ring
        rw [e, mul_assoc]
        exact mul_le_mul_of_nonneg_right hD1 (by positivity)
      have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ Y ^ 4)
      linarith
    · have h1 := (div_lt_iff₀ (by positivity : (0 : ℝ) < Y ^ 2)).1 hA
      have h2 : eps ^ 2 * (Δ : ℝ) ^ 2 * Y ^ 2 ≤ (eps * Δ) ^ 3 * Y ^ 4 := by
        have e : eps ^ 2 * (Δ : ℝ) ^ 2 = (eps * Δ) ^ 2 := by ring
        rw [e]
        have h3 : (eps * Δ) ^ 2 ≤ (eps * Δ) ^ 3 := pow_le_pow_right₀ hR1 (by norm_num)
        have h4 : Y ^ 2 ≤ Y ^ 4 := pow_le_pow_right₀ hY (by norm_num)
        exact mul_le_mul h3 h4 (by positivity) (by positivity)
      linarith
  -- `P = ε D Δ` has `P³ < q⁴ Y⁴`
  set P := eps * D * Δ with hPdef
  have hP0 : 0 ≤ P := by positivity
  have hP3 : P ^ 3 < q ^ 4 * Y ^ 4 := by
    have h1 : P ^ 3 ≤ D * eps ^ 3 * (Δ : ℝ) ^ 3 := by
      have e : P ^ 3 = D ^ 3 * (eps ^ 3 * (Δ : ℝ) ^ 3) := by rw [hPdef]; ring
      have hD3 : D ^ 3 ≤ D := by
        have e2 : D ^ 3 = D * D ^ 2 := by ring
        rw [e2]
        exact mul_le_of_le_one_right hD0.le (pow_le_one₀ hD0.le hD1)
      rw [e, mul_assoc]
      exact mul_le_mul_of_nonneg_right hD3 (by positivity)
    rw [hq4]
    linarith
  have hDΔ : D * Δ ≤ P := by
    have hP' : D * Δ * eps = P := by rw [hPdef]; ring
    rw [← hP']
    exact le_mul_of_one_le_right (by positivity) heps
  -- the three entries of `τ♭` are at least `4 q`
  have hE1 : 4 * q ≤ eps ^ 2 / (409600 * Y) / 2 * Δ := by
    have hED : 3276800 * Y * q ≤ eps * Δ := by
      by_contra h
      have h' := (not_le.1 h).le
      have h3 : (eps * Δ) ^ 3 ≤ (3276800 * Y * q) ^ 3 := pow_le_pow_left₀ (by linarith) h' 3
      have h4 := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ Y ^ 4)
      have e : (3276800 * Y * q) ^ 3 * Y ^ 4 = (3276800 ^ 3 * Y ^ 7) * q ^ 3 := by ring
      have h5 : (3276800 ^ 3 * Y ^ 7) * q ^ 3 ≤ q * q ^ 3 :=
        mul_le_mul_of_nonneg_right hb1 (by positivity)
      have e2 : q * q ^ 3 = n := by rw [← hq4]; ring
      linarith
    have e : eps ^ 2 / (409600 * Y) / 2 * Δ = eps * (eps * Δ) / (819200 * Y) := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have h1 : eps * Δ ≤ eps * (eps * Δ) := le_mul_of_one_le_left (by linarith) heps
    have h2 : 4 * q * (819200 * Y) = 3276800 * Y * q := by ring
    linarith
  have hE2 : 4 * q ≤ Real.sqrt (eps / (16 * (D * κ))) / 2 * Real.sqrt (n / Δ) := by
    have e : Real.sqrt (eps / (16 * (D * κ))) / 2 * Real.sqrt (n / Δ) =
        Real.sqrt (eps / (16 * (D * κ)) * (n / Δ)) / 2 := by
      rw [Real.sqrt_mul (by positivity)]; ring
    rw [e, le_div_iff₀ (by norm_num), Real.le_sqrt (by positivity) (by positivity)]
    -- `1024 κ P ≤ q²`
    have hKP : 1024 * κ * P ≤ q ^ 2 := by
      have h1 : (1024 * κ * P) ^ 3 ≤ (q ^ 2) ^ 3 := by
        have e1 : (1024 * κ * P) ^ 3 = 1024 ^ 3 * κ ^ 3 * P ^ 3 := by ring
        have h2 : 1024 ^ 3 * κ ^ 3 * P ^ 3 ≤ 1024 ^ 3 * κ ^ 3 * (q ^ 4 * Y ^ 4) :=
          mul_le_mul_of_nonneg_left hP3.le (by positivity)
        have h3 : 1024 ^ 3 * κ ^ 3 * Y ^ 4 ≤ q ^ 2 := by
          have : q ≤ q ^ 2 := by nlinarith
          linarith
        have h4 : 1024 ^ 3 * κ ^ 3 * (q ^ 4 * Y ^ 4) = (1024 ^ 3 * κ ^ 3 * Y ^ 4) * q ^ 4 := by
          ring
        have h5 := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ q ^ 4)
        have e2 : (q ^ 2) ^ 3 = q ^ 2 * q ^ 4 := by ring
        linarith
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h1
    rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
    have e2 : (4 * q * 2) ^ 2 * (16 * (D * κ) * Δ) = 1024 * κ * (D * Δ) * q ^ 2 := by ring
    rw [e2]
    have h1 : 1024 * κ * (D * Δ) * q ^ 2 ≤ 1024 * κ * P * q ^ 2 := by
      have : 0 ≤ 1024 * κ := by positivity
      have := mul_le_mul_of_nonneg_left hDΔ this
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : 1024 * κ * P * q ^ 2 ≤ q ^ 2 * q ^ 2 :=
      mul_le_mul_of_nonneg_right hKP (by positivity)
    have e3 : q ^ 2 * q ^ 2 = n := by rw [← hq4]; ring
    have h3 : (n : ℝ) ≤ eps * n := le_mul_of_one_le_left hnr.le heps
    linarith
  have hE3 : 4 * q ≤ 1 / (8 * (D * κ)) / 2 * (n / Δ) := by
    have e : 1 / (8 * (D * κ)) / 2 * (n / Δ) = n / (16 * κ * (D * Δ)) := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have hKP : 64 * κ * P ≤ q ^ 3 := by
      have h1 : (64 * κ * P) ^ 3 ≤ (q ^ 3) ^ 3 := by
        have e1 : (64 * κ * P) ^ 3 = 64 ^ 3 * κ ^ 3 * P ^ 3 := by ring
        have h2 : 64 ^ 3 * κ ^ 3 * P ^ 3 ≤ 64 ^ 3 * κ ^ 3 * (q ^ 4 * Y ^ 4) :=
          mul_le_mul_of_nonneg_left hP3.le (by positivity)
        have h3 : 64 ^ 3 * κ ^ 3 * Y ^ 4 ≤ q ^ 5 := by
          have : q ≤ q ^ 5 := by
            calc q = q ^ 1 := (pow_one q).symm
              _ ≤ q ^ 5 := pow_le_pow_right₀ hq1 (by norm_num)
          linarith
        have h4 : 64 ^ 3 * κ ^ 3 * (q ^ 4 * Y ^ 4) = (64 ^ 3 * κ ^ 3 * Y ^ 4) * q ^ 4 := by ring
        have h5 := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ q ^ 4)
        have e2 : (q ^ 3) ^ 3 = q ^ 5 * q ^ 4 := by ring
        linarith
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h1
    have h1 : 4 * q * (16 * κ * (D * Δ)) ≤ q * (64 * κ * P) := by
      have e : 4 * q * (16 * κ * (D * Δ)) = q * (64 * κ) * (D * Δ) := by ring
      have e' : q * (64 * κ * P) = q * (64 * κ) * P := by ring
      rw [e, e']
      exact mul_le_mul_of_nonneg_left hDΔ (by positivity)
    have h2 : q * (64 * κ * P) ≤ q * q ^ 3 := mul_le_mul_of_nonneg_left hKP hq0.le
    have e3 : q * q ^ 3 = n := by rw [← hq4]; ring
    linarith
  set τb := kreTau n (kreC₁ n eps / 2) (kreC₂ eps (D * c.L / c.fmin ^ 3) (1 / c.fmax) / 2)
    (kreC₃ (D * c.L / c.fmin ^ 3) (1 / c.fmax) / 2) Δ with hτbdef
  have hτb : 4 * q ≤ τb := by
    rw [hτbdef, kreTau_unif]
    exact le_min (le_min hE1 hE2) hE3
  -- `kre_hC`
  have hDn : 640 * Y / eps < Δ := by
    rw [div_lt_iff₀ he0, mul_comm (Δ : ℝ)]
    exact lt_mul_of_cube hc (by positivity) hR.le
  have hM : (reSegs eps p n ℓ : ℝ) ≤ reSize eps p n ℓ / τb + 1 :=
    kre_hC H heps hn3 hL hC1 hC2 ℓ hDn (show 1 ≤ τb by linarith)
  -- the dichotomy
  have hM1 : 1 ≤ reSegs eps p n ℓ := one_le_reSegs heps hn1 ℓ
  by_cases hK : (reSize eps p n ℓ : ℝ) < τb
  · left
    have h1 : (reSize eps p n ℓ : ℝ) / τb < 1 := (div_lt_one (by linarith)).2 hK
    have h2 : (reSegs eps p n ℓ : ℝ) < 2 := by linarith
    have h3 : reSegs eps p n ℓ < 2 := by exact_mod_cast h2
    omega
  · right
    have hK' : τb ≤ (reSize eps p n ℓ : ℝ) := not_lt.1 hK
    set K := reSize eps p n ℓ with hKdef
    set M := reSegs eps p n ℓ with hMdef
    have hτ0 : 0 < τb := by linarith
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
    -- `M τ♭ ≤ 2 K`
    have h1 : (M : ℝ) * τb ≤ 2 * K := by
      have h2 : 1 ≤ (K : ℝ) / τb := (le_div_iff₀ hτ0).2 (by linarith)
      have h3 : (M : ℝ) ≤ 2 * ((K : ℝ) / τb) := by linarith
      calc (M : ℝ) * τb ≤ 2 * ((K : ℝ) / τb) * τb := mul_le_mul_of_nonneg_right h3 hτ0.le
        _ = 2 * K := by field_simp
    have hd : K < (K / M) * M + M := Nat.lt_div_mul_add (by omega)
    have hdr : (K : ℝ) < ((K / M : ℕ) : ℝ) * M + M := by exact_mod_cast hd
    have hstep : reStep eps p n ℓ = K / M := rfl
    rw [hstep]
    by_contra hlt
    have hlt' : ((K / M : ℕ) : ℝ) < q := not_le.1 hlt
    have h4 : ((K / M : ℕ) : ℝ) * M < q * M := mul_lt_mul_of_pos_right hlt' hM0
    have h5 : (M : ℝ) * (4 * q) ≤ (M : ℝ) * τb := mul_le_mul_of_nonneg_left hτb hM0.le
    have h7 : (1 : ℝ) * M ≤ q * M := mul_le_mul_of_nonneg_right hq1 hM0.le
    linarith

/-- **Curvature layers, upper count** (`lem:curv`(b)). -/
theorem unif_curvUp (hc : UnifCond c n eps)
    (hω : ω ∉ kreBad expCoord n eps (tRE n) (jK n)) (hf : c.Mem δ f) (ℓ : ℕ)
    (h2 : 2 ≤ reSize eps (renyiKeys f n ω) n ℓ)
    (hC : (n : ℝ) * Real.log n ^ 4 ≤
      effDelta n δ * eps ^ 3 * (reDelta eps (renyiKeys f n ω) n ℓ : ℝ) ^ 3) :
    (reSegs eps (renyiKeys f n ω) n ℓ : ℝ) ≤
      (1638400 + 16 * Real.sqrt (unifKappa c)) *
          Real.sqrt (effDelta n δ * ((n : ℝ) / reDelta eps (renyiKeys f n ω) n ℓ) / eps) +
        (32 * unifKappa c + 1) := by
  have H := krePath_unif hf hc.n_ge hω
  have heps := hc.one_le_eps
  have he0 : 0 < eps := by linarith
  have hn3 := hc.three_le
  have hn1 := hc.one_le
  have hY := hc.one_le_log
  have hD0 : 0 < effDelta n δ := effDelta_pos hn1 δ
  have hD1 : effDelta n δ ≤ 1 := effDelta_le_one hn1 hf.2.1
  obtain ⟨hL, hC1, hC2⟩ := kre_hC_conds hc hD0 hD1
  set Y := Real.log n with hYdef
  set D := effDelta n δ with hDdef
  set κ := unifKappa c with hκdef
  have hκ : 0 < κ := unifKappa_pos c
  set p := renyiKeys f n ω with hp
  set Δ := reDelta eps p n ℓ with hΔdef
  have hΔ1 : (1 : ℝ) ≤ Δ := by exact_mod_cast one_le_reDelta (p := p) heps hn1 ℓ
  have hΔ0 : (0 : ℝ) < Δ := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  have hY0 : 0 < Y := by linarith
  have hΔn : (Δ : ℝ) < n := by exact_mod_cast reDelta_lt heps hn1 h2
  set s := (n : ℝ) / Δ with hsdef
  have hsΔ : s * Δ = n := by rw [hsdef]; field_simp
  have hs0 : 0 < s := by positivity
  -- `N_ℓ ≤ 2 s`
  set K := reSize eps p n ℓ with hKdef
  have hK2 : (K : ℝ) ≤ 2 * s := by
    have hc1 := (re_cover (p := p) heps hn1 ℓ).1
    have hK1 : 1 ≤ K := one_le_reSize heps hn1 ℓ
    have h1 : ((K - 1 : ℕ) : ℝ) * Δ < n := by exact_mod_cast hc1
    rw [Nat.cast_sub hK1, Nat.cast_one] at h1
    have h3 : ((K : ℝ) - 1) * Δ < s * Δ := by rw [hsΔ]; exact h1
    have h4 : (K : ℝ) - 1 < s := lt_of_mul_lt_mul_right h3 hΔ0.le
    have h5 : (1 : ℝ) ≤ s := by rw [hsdef, le_div_iff₀ hΔ0]; linarith
    linarith
  -- `640 log n < ε Δ`
  have hDe : D * eps ^ 3 * (Δ : ℝ) ^ 3 ≤ (eps * Δ) ^ 3 := by
    have e : (eps * Δ) ^ 3 = 1 * (eps ^ 3 * (Δ : ℝ) ^ 3) := by ring
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_right hD1 (by positivity)
  have hR : (n : ℝ) ≤ (eps * Δ) ^ 3 * Y ^ 4 := by
    have h1 : (n : ℝ) ≤ n * Y ^ 4 := le_mul_of_one_le_right hnr.le (one_le_pow₀ hY)
    have h3 : (eps * Δ) ^ 3 ≤ (eps * Δ) ^ 3 * Y ^ 4 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ hY)
    linarith
  have hDn : 640 * Y / eps < Δ := by
    rw [div_lt_iff₀ he0, mul_comm (Δ : ℝ)]
    exact lt_mul_of_cube hc (by positivity) hR
  set e₁ := eps ^ 2 / (409600 * Y) / 2 * Δ with he₁
  set e₂ := Real.sqrt (eps / (16 * (D * κ))) / 2 * Real.sqrt (n / Δ) with he₂
  set e₃ := 1 / (8 * (D * κ)) / 2 * (n / Δ) with he₃
  have he₁0 : 0 < e₁ := by positivity
  have he₂0 : 0 < e₂ := by
    have h1 : 0 < eps / (16 * (D * κ)) := by positivity
    have h2 := Real.sqrt_pos.2 h1
    have h3 := Real.sqrt_pos.2 (show (0 : ℝ) < n / Δ by positivity)
    positivity
  have he₃0 : 0 < e₃ := by positivity
  set τb := kreTau n (kreC₁ n eps / 2) (kreC₂ eps (D * c.L / c.fmin ^ 3) (1 / c.fmax) / 2)
    (kreC₃ (D * c.L / c.fmin ^ 3) (1 / c.fmax) / 2) Δ with hτbdef
  have hτe : τb = min (min e₁ e₂) e₃ := by rw [hτbdef, kreTau_unif]
  have hτ0 : 0 < τb := by rw [hτe]; exact lt_min (lt_min he₁0 he₂0) he₃0
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  -- `M ≤ K / τ♭ + 1`
  have hM : (reSegs eps p n ℓ : ℝ) ≤ K / τb + 1 := by
    by_cases h1 : 1 ≤ τb
    · exact kre_hC H heps hn3 hL hC1 hC2 ℓ hDn h1
    · have h1' : τb ≤ 1 := (not_le.1 h1).le
      have h3 : (reSegs eps p n ℓ : ℝ) ≤ K := by exact_mod_cast reSegs_le_reSize heps ℓ
      have h4 : (K : ℝ) ≤ K / τb := le_div_self hK0 hτ0 h1'
      linarith
  -- `K / τ♭ ≤ K / e₁ + K / e₂ + K / e₃`
  have hsum : (K : ℝ) / τb ≤ K / e₁ + K / e₂ + K / e₃ := by
    have h1 : 0 ≤ (K : ℝ) / e₁ := by positivity
    have h2 : 0 ≤ (K : ℝ) / e₂ := by positivity
    have h3 : 0 ≤ (K : ℝ) / e₃ := by positivity
    rw [hτe]
    rcases min_choice (min e₁ e₂) e₃ with h | h <;> rw [h]
    · rcases min_choice e₁ e₂ with h' | h' <;> rw [h'] <;> linarith
    · linarith
  -- the three terms
  set r := Real.sqrt (D * s / eps) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hx : s * Y ≤ r * (eps ^ 2 * Δ) := by
    have h1 : (n : ℝ) * Y ^ 2 ≤ D * eps ^ 3 * (Δ : ℝ) ^ 3 := by
      have : (n : ℝ) * Y ^ 2 ≤ n * Y ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY (by norm_num)) hnr.le
      linarith
    have h2 : s * Y ^ 2 ≤ D * eps ^ 3 * Δ ^ 2 := by
      have h3 : s * Y ^ 2 * Δ ≤ D * eps ^ 3 * Δ ^ 2 * Δ := by
        calc s * Y ^ 2 * Δ = n * Y ^ 2 := by rw [← hsΔ]; ring
          _ ≤ D * eps ^ 3 * Δ ^ 3 := h1
          _ = D * eps ^ 3 * Δ ^ 2 * Δ := by ring
      exact le_of_mul_le_mul_right h3 hΔ0
    have h3 : (s * Y) ^ 2 ≤ D * s / eps * (eps ^ 2 * Δ) ^ 2 := by
      have e : D * s / eps * (eps ^ 2 * Δ) ^ 2 = s * (D * eps ^ 3 * Δ ^ 2) := by
        field_simp
      rw [e]
      have e2 : (s * Y) ^ 2 = s * (s * Y ^ 2) := by ring
      rw [e2]
      exact mul_le_mul_of_nonneg_left h2 hs0.le
    have h4 : r * (eps ^ 2 * Δ) = Real.sqrt (D * s / eps * (eps ^ 2 * Δ) ^ 2) := by
      rw [hr, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [h4]
    exact (Real.le_sqrt (by positivity) (by positivity)).2 h3
  have hT1 : (K : ℝ) / e₁ ≤ 1638400 * r := by
    rw [div_le_iff₀ he₁0]
    have e : 1638400 * r * e₁ = 2 * (r * (eps ^ 2 * Δ)) / Y := by
      rw [he₁]; field_simp; ring
    rw [e, le_div_iff₀ hY0]
    have h1 : (K : ℝ) * Y ≤ 2 * s * Y := mul_le_mul_of_nonneg_right hK2 hY0.le
    linarith
  have hT2 : (K : ℝ) / e₂ ≤ 16 * Real.sqrt κ * r := by
    rw [div_le_iff₀ he₂0]
    have h1 : Real.sqrt κ * Real.sqrt (D * s / eps) * Real.sqrt (eps / (16 * (D * κ))) *
        Real.sqrt (n / Δ) = s / 4 := by
      rw [← Real.sqrt_mul hκ.le, ← Real.sqrt_mul (by positivity),
        ← Real.sqrt_mul (by positivity), ← hsdef]
      have e : κ * (D * s / eps) * (eps / (16 * (D * κ))) * s = (s / 4) ^ 2 := by
        field_simp; ring
      rw [e, Real.sqrt_sq (by positivity)]
    have e : 16 * Real.sqrt κ * r * e₂ = 2 * s := by
      calc 16 * Real.sqrt κ * r * e₂
          = 8 * (Real.sqrt κ * Real.sqrt (D * s / eps) * Real.sqrt (eps / (16 * (D * κ))) *
            Real.sqrt (n / Δ)) := by rw [hr, he₂]; ring
        _ = 2 * s := by rw [h1]; ring
    rw [e]
    exact hK2
  have hT3 : (K : ℝ) / e₃ ≤ 32 * κ := by
    rw [div_le_iff₀ he₃0]
    have e : 32 * κ * e₃ = 2 * s / D := by rw [he₃, hsdef]; field_simp; ring
    rw [e, le_div_iff₀ hD0]
    have : (K : ℝ) * D ≤ K := mul_le_of_le_one_right hK0 hD1
    linarith
  have hsk : 0 ≤ Real.sqrt κ := Real.sqrt_nonneg _
  have hfin : (1638400 + 16 * Real.sqrt κ) * r + (32 * κ + 1) =
      1638400 * r + 16 * Real.sqrt κ * r + 32 * κ + 1 := by ring
  rw [hfin]
  linarith

end Layer2

end

end PGM
