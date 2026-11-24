import PLAStochastic.Index.KRE.Uniform.LayerBoundsUpper
import PLAStochastic.Index.KRE.Uniform.LandauChaining

/-!
# Uniform layer bounds of `thm:uniform`: the curvature lower count

`lem:curv`(a) of `research/2026-09-24-re-curvature-uniform/tex/main.tex` (the Landau-type
estimate `lem:landau` of the precision-ceiling note, with the constants tracked in `δ`), for
the Rényi keys `x_j = Q (z (j Δ) / z n)` of `f ∈ 𝔉_δ`, `δ > 0`, off `kreBad`.

With `G = (z n / Δ) F`, `G' = (z n / Δ) f` and `Λ = (z n / Δ) δ L`, the keys satisfy
`G (x_j) = z (j Δ) / Δ` exactly, so on a greedy window of `τ` keys `G (x_j)` is within
`θ = ε + 160 √(τ log n / Δ)` of a line (tube bound).  `landau_chain` with the mesh
`h = 320 Δ / (f₋ n)` and the class condition `|f b - f a| ≥ δ V` give
`s δ V / 2 ≤ 4 M √(2 ε Λ) + 4 M^{3/4} (25600 Λ² log n K / Δ)^{1/4} + M Λ h`
(`sum_rpow_quarter_le`), and one of the three terms is at least `s δ V / 6`
(`curvLow_cases`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Topology

/-- `c₁ = V / √(3456 L)`. -/
def unifC1 (c : DensityClassParams) : ℝ := c.V / Real.sqrt (3456 * c.L)

/-- `c₂ = (V⁴ / (152882380800 L²))^{1/3}`. -/
def unifC2 (c : DensityClassParams) : ℝ := (c.V ^ 4 / (152882380800 * c.L ^ 2)) ^ (1 / 3 : ℝ)

/-- `c₃ = f₋ V / (5760 L)`. -/
def unifC3 (c : DensityClassParams) : ℝ := c.fmin * c.V / (5760 * c.L)

/-- `K_L = 307200 L / f₋² + 164 / (f₋ a) + 164 / (f₋ (1 - b))`. -/
def unifKL (c : DensityClassParams) : ℝ :=
  307200 * c.L / c.fmin ^ 2 + 164 / (c.fmin * c.a) + 164 / (c.fmin * (1 - c.b))

theorem unifC1_pos (c : DensityClassParams) : 0 < unifC1 c := by
  unfold unifC1
  have := c.V_pos
  have := Real.sqrt_pos.2 (show (0 : ℝ) < 3456 * c.L by linarith [c.L_pos])
  positivity

theorem unifC2_pos (c : DensityClassParams) : 0 < unifC2 c := by
  unfold unifC2
  have := c.V_pos
  have := c.L_pos
  exact Real.rpow_pos_of_pos (by positivity) _

theorem unifC3_pos (c : DensityClassParams) : 0 < unifC3 c := by
  unfold unifC3
  have := c.V_pos
  have := c.L_pos
  have := c.fmin_pos
  positivity

theorem unifKL_pos (c : DensityClassParams) : 0 < unifKL c := by
  unfold unifKL
  have := c.L_pos
  have := c.fmin_pos
  have := c.a_pos
  have : 0 < 1 - c.b := by linarith [c.b_lt_one]
  positivity

/-! ## Elementary inequalities -/

theorem rpow_quarter_pow_four' {y : ℝ} (hy : 0 ≤ y) : (y ^ (1 / 4 : ℝ)) ^ 4 = y := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
  norm_num

/-- `√(160 √x Λ) = (25600 Λ² x)^{1/4}`. -/
theorem sqrt_mul_sqrt_eq_rpow {Λ x : ℝ} (hΛ : 0 ≤ Λ) (hx : 0 ≤ x) :
    Real.sqrt (160 * Real.sqrt x * Λ) = (25600 * Λ ^ 2 * x) ^ (1 / 4 : ℝ) := by
  have h1 : 160 * Real.sqrt x * Λ = Real.sqrt (25600 * Λ ^ 2 * x) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hΛ,
      show (25600 : ℝ) = 160 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    ring
  rw [h1, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  norm_num

/-- One window: `4 √((θ + Λ h²) Λ) ≤ 4 √(2 ε Λ) + 4 (25600 Λ² x)^{1/4}` for
`θ = ε + 160 √x` and `Λ h² ≤ 1 ≤ ε`. -/
theorem window_term_le {eps Λ h x : ℝ} (heps : 1 ≤ eps) (hΛ : 0 ≤ Λ) (hh : Λ * h ^ 2 ≤ 1)
    (hx : 0 ≤ x) :
    4 * Real.sqrt ((eps + 160 * Real.sqrt x + Λ * h ^ 2) * Λ) ≤
      4 * Real.sqrt (2 * eps * Λ) + 4 * (25600 * Λ ^ 2 * x) ^ (1 / 4 : ℝ) := by
  have h1 : (eps + 160 * Real.sqrt x + Λ * h ^ 2) * Λ ≤ 2 * eps * Λ + 160 * Real.sqrt x * Λ := by
    have : eps + 160 * Real.sqrt x + Λ * h ^ 2 ≤ 2 * eps + 160 * Real.sqrt x := by linarith
    nlinarith
  have h2 := Real.sqrt_le_sqrt h1
  have h3 := sqrt_add_le_add (by positivity : (0 : ℝ) ≤ 2 * eps * Λ)
    (by positivity : (0 : ℝ) ≤ 160 * Real.sqrt x * Λ)
  rw [sqrt_mul_sqrt_eq_rpow hΛ hx] at h3
  linarith

/-- The tube bound on a window of `τ` keys: `80 (√(t Δ Y) + Y) / Δ ≤ 160 √(τ Y / Δ)` for
`0 ≤ t ≤ τ`, `1 ≤ τ`, `0 ≤ Y ≤ Δ`. -/
theorem tube_div_le {Y Δ t τ : ℝ} (hY : 0 ≤ Y) (hYΔ : Y ≤ Δ) (ht : 0 ≤ t) (htτ : t ≤ τ)
    (hτ : 1 ≤ τ) :
    80 * (Real.sqrt (t * Δ * Y) + Y) / Δ ≤ 160 * Real.sqrt (τ * Y / Δ) := by
  have hΔ0 : 0 < Δ ∨ Δ = 0 := by
    rcases (le_trans hY hYΔ).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  rcases hΔ0 with hΔ | hΔ
  · have e : Δ * Real.sqrt (τ * Y / Δ) = Real.sqrt (τ * Δ * Y) := by
      rw [show τ * Δ * Y = Δ ^ 2 * (τ * Y / Δ) by field_simp, Real.sqrt_mul (by positivity),
        Real.sqrt_sq hΔ.le]
    have h1 : Real.sqrt (t * Δ * Y) ≤ Real.sqrt (τ * Δ * Y) := by
      apply Real.sqrt_le_sqrt
      have := mul_le_mul_of_nonneg_right htτ (mul_nonneg hΔ.le hY)
      linarith [mul_assoc t Δ Y, mul_assoc τ Δ Y]
    have h2 : Y ≤ Real.sqrt (τ * Δ * Y) := by
      rw [Real.le_sqrt hY (by positivity)]
      have : Y ≤ τ * Δ := by nlinarith
      nlinarith
    rw [div_le_iff₀ hΔ]
    nlinarith
  · subst hΔ
    have : Y = 0 := le_antisymm hYΔ hY
    subst this
    simp

/-- **The three cases of the chaining inequality** `s δ V / 2 ≤ R₁ + R₂ + R₃`. -/
theorem curvLow_cases (c : DensityClassParams) {s δ eps Λ Λh Y Δ K M : ℝ} {n : ℝ}
    (hs : 0 < s) (hδ : 0 < δ) (heps : 1 ≤ eps) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ 3 * s * δ * c.L)
    (hY : 0 < Y) (hΔ : 0 < Δ) (hK0 : 0 ≤ K) (hK : K ≤ 2 * s) (hM : 0 ≤ M) (hsn : s * Δ = n)
    (hΛh : Λh ≤ 960 * δ * c.L / c.fmin)
    (hchain : s * δ * c.V / 2 ≤ 4 * M * Real.sqrt (2 * eps * Λ) +
      4 * M ^ (3 / 4 : ℝ) * (25600 * Λ ^ 2 * Y / Δ * K) ^ (1 / 4 : ℝ) + M * Λh) :
    min (min (unifC1 c * Real.sqrt (δ * s / eps))
        (unifC2 c * δ ^ (2 / 3 : ℝ) * (n / Y) ^ (1 / 3 : ℝ))) (unifC3 c * s) ≤ M := by
  have hV := c.V_pos
  have hL := c.L_pos
  have hfm := c.fmin_pos
  have he0 : 0 < eps := by linarith
  set B := s * δ * c.V / 6 with hB
  have hB0 : 0 < B := by positivity
  by_cases h1 : B ≤ 4 * M * Real.sqrt (2 * eps * Λ)
  · -- the curvature-over-tolerance case
    refine (min_le_left _ _).trans ((min_le_left _ _).trans ?_)
    have hsq : B ^ 2 ≤ 16 * M ^ 2 * (2 * eps * Λ) := by
      have := pow_le_pow_left₀ hB0.le h1 2
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)] at this
      linarith
    have hsq' : B ^ 2 ≤ M ^ 2 * (96 * eps * s * δ * c.L) := by
      have : 16 * M ^ 2 * (2 * eps * Λ) ≤ 16 * M ^ 2 * (2 * eps * (3 * s * δ * c.L)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      nlinarith
    apply le_of_pow_le_pow_left₀ two_ne_zero hM
    have e : (unifC1 c * Real.sqrt (δ * s / eps)) ^ 2 =
        c.V ^ 2 * δ * s / (3456 * c.L * eps) := by
      unfold unifC1
      rw [mul_pow, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have e1 : c.V ^ 2 * δ * s * (s * δ / 36) = B ^ 2 := by rw [hB]; ring
    have e2 : M ^ 2 * (3456 * c.L * eps) * (s * δ / 36) = M ^ 2 * (96 * eps * s * δ * c.L) := by
      ring
    have key : c.V ^ 2 * δ * s * (s * δ / 36) ≤ M ^ 2 * (3456 * c.L * eps) * (s * δ / 36) := by
      rw [e1, e2]
      exact hsq'
    exact le_of_mul_le_mul_right key (by positivity)
  by_cases h2 : B ≤ 4 * M ^ (3 / 4 : ℝ) * (25600 * Λ ^ 2 * Y / Δ * K) ^ (1 / 4 : ℝ)
  · -- the noise-over-window case
    refine (min_le_left _ _).trans ((min_le_right _ _).trans ?_)
    have hT0 : 0 ≤ 25600 * Λ ^ 2 * Y / Δ * K := by positivity
    have h4 : B ^ 4 ≤ 256 * M ^ 3 * (25600 * Λ ^ 2 * Y / Δ * K) := by
      have := pow_le_pow_left₀ hB0.le h2 4
      rw [mul_pow, mul_pow, rpow_quarter_pow_four' hT0] at this
      have e : (M ^ (3 / 4 : ℝ)) ^ 4 = M ^ 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hM]
        norm_num
      rw [e] at this
      linarith
    have hΛ2 : Λ ^ 2 ≤ (3 * s * δ * c.L) ^ 2 := pow_le_pow_left₀ hΛ0 hΛ 2
    have h5 : 25600 * Λ ^ 2 * Y / Δ * K ≤ 25600 * (3 * s * δ * c.L) ^ 2 * Y / Δ * (2 * s) := by
      have : 25600 * Λ ^ 2 * Y / Δ ≤ 25600 * (3 * s * δ * c.L) ^ 2 * Y / Δ := by
        apply div_le_div_of_nonneg_right _ hΔ.le
        nlinarith
      exact mul_le_mul this hK hK0 (by positivity)
    have h6 : B ^ 4 ≤ 256 * M ^ 3 * (25600 * (3 * s * δ * c.L) ^ 2 * Y / Δ * (2 * s)) :=
      h4.trans (mul_le_mul_of_nonneg_left h5 (by positivity))
    apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hM
    have e : (unifC2 c * δ ^ (2 / 3 : ℝ) * (n / Y) ^ (1 / 3 : ℝ)) ^ 3 =
        c.V ^ 4 / (152882380800 * c.L ^ 2) * δ ^ 2 * (s * Δ / Y) := by
      have hn0 : 0 ≤ n / Y := by rw [← hsn]; positivity
      unfold unifC2
      rw [mul_pow, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (δ ^ (2 / 3 : ℝ)),
        ← Real.rpow_natCast ((n / Y) ^ (1 / 3 : ℝ)), ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul hδ.le, ← Real.rpow_mul hn0, hsn]
      norm_num
    rw [e]
    have e2 : c.V ^ 4 / (152882380800 * c.L ^ 2) * δ ^ 2 * (s * Δ / Y) =
        c.V ^ 4 * δ ^ 2 * s * Δ / (152882380800 * c.L ^ 2 * Y) := by
      field_simp
    rw [e2, div_le_iff₀ (by positivity)]
    have e3 : c.V ^ 4 * δ ^ 2 * s * Δ * (s ^ 3 * δ ^ 2 / (1296 * Δ)) = B ^ 4 := by
      rw [hB]; field_simp; ring
    have e4 : M ^ 3 * (152882380800 * c.L ^ 2 * Y) * (s ^ 3 * δ ^ 2 / (1296 * Δ)) =
        256 * M ^ 3 * (25600 * (3 * s * δ * c.L) ^ 2 * Y / Δ * (2 * s)) := by
      field_simp; ring
    have key : c.V ^ 4 * δ ^ 2 * s * Δ * (s ^ 3 * δ ^ 2 / (1296 * Δ)) ≤
        M ^ 3 * (152882380800 * c.L ^ 2 * Y) * (s ^ 3 * δ ^ 2 / (1296 * Δ)) := by
      rw [e3, e4]
      exact h6
    exact le_of_mul_le_mul_right key (by positivity)
  · -- the mesh case
    refine (min_le_right _ _).trans ?_
    have h3 : B ≤ M * Λh := by
      have := not_le.1 h1
      have := not_le.1 h2
      have e : s * δ * c.V / 2 = 3 * B := by rw [hB]; ring
      linarith
    have h4 : B ≤ M * (960 * δ * c.L / c.fmin) := h3.trans (mul_le_mul_of_nonneg_left hΛh hM)
    have e : unifC3 c * s = c.fmin * c.V * s / (5760 * c.L) := by unfold unifC3; ring
    rw [e, div_le_iff₀ (by positivity)]
    have e1 : c.fmin * c.V * s * (δ / (6 * c.fmin)) = B := by rw [hB]; field_simp
    have e2 : M * (5760 * c.L) * (δ / (6 * c.fmin)) = M * (960 * δ * c.L / c.fmin) := by
      field_simp; ring
    have key : c.fmin * c.V * s * (δ / (6 * c.fmin)) ≤
        M * (5760 * c.L) * (δ / (6 * c.fmin)) := by
      rw [e1, e2]
      exact h4
    exact le_of_mul_le_mul_right key (by positivity)

/-! ## The curvature lower count -/

section Layer

variable {c : DensityClassParams} {n : ℕ} {eps : ℝ} {ω : ℕ → ℝ} {δ : ℝ} {f : ℝ → ℝ}

/-- Off `kreBad`: `z n ≤ 3 n`, `z 0 ≤ 2 + 80 log n` and `z n - z m ≤ 2 (n - m) + 80 log n`. -/
theorem refWalk_bounds (hc : UnifCond c n eps)
    (hω : ω ∉ kreBad expCoord n eps (tRE n) (jK n)) :
    expPartial n ω ≤ 3 * n ∧ expPartial 0 ω ≤ 2 + 80 * Real.log n ∧
      ∀ m, m ≤ n → expPartial n ω - expPartial m ω ≤ 2 * ((n : ℝ) - m) + 80 * Real.log n := by
  have hgood := (notMem_kreBad hω).1
  have hn1 := hc.one_le
  have hsum : ∀ t, expPartial t ω = expSum expCoord 0 (t + 1) ω := fun t => by
    unfold expPartial expSum
    rw [Finset.range_eq_Ico]
  refine ⟨?_, ?_, ?_⟩
  · have h := expSum_le_of_mem_expGood hgood hn1 (a := 0) (b := n + 1) (by omega) (by omega)
    rw [hsum]
    simp only [Nat.sub_zero, Nat.cast_add, Nat.cast_one] at h
    linarith [hc.low]
  · have h := expSum_le_of_mem_expGood hgood hn1 (a := 0) (b := 1) (by omega) (by omega)
    rw [hsum]
    simp only [Nat.sub_zero, Nat.cast_one, mul_one] at h
    exact h
  · intro m hm
    have h := expSum_le_of_mem_expGood hgood hn1 (a := m + 1) (b := n + 1) (by omega) (by omega)
    have e : refWalk expCoord ω n - refWalk expCoord ω m = expSum expCoord (m + 1) (n + 1) ω :=
      refWalk_sub expCoord ω hm
    have e2 : ((n + 1 - (m + 1) : ℕ) : ℝ) = (n : ℝ) - m := by
      rw [show n + 1 - (m + 1) = n - m by omega, Nat.cast_sub hm]
    rw [e2] at h
    have e3 : expPartial n ω - expPartial m ω = refWalk expCoord ω n - refWalk expCoord ω m := rfl
    rw [e3, e]
    exact h

/-- **Curvature layers, lower count** (`lem:curv`(a)). -/
theorem unif_curvLow (hc : UnifCond c n eps)
    (hω : ω ∉ kreBad expCoord n eps (tRE n) (jK n)) (hf : c.Mem δ f) (hδ : 0 < δ) (ℓ : ℕ)
    (h2 : 2 ≤ reSize eps (renyiKeys f n ω) n ℓ)
    (hΔY : Real.log n ^ 2 ≤ (reDelta eps (renyiKeys f n ω) n ℓ : ℝ))
    (hKL : unifKL c ≤ (n : ℝ) / reDelta eps (renyiKeys f n ω) n ℓ) :
    min (min (unifC1 c * Real.sqrt (δ * ((n : ℝ) / reDelta eps (renyiKeys f n ω) n ℓ) / eps))
        (unifC2 c * δ ^ (2 / 3 : ℝ) * ((n : ℝ) / Real.log n) ^ (1 / 3 : ℝ)))
      (unifC3 c * ((n : ℝ) / reDelta eps (renyiKeys f n ω) n ℓ)) ≤
      reSegs eps (renyiKeys f n ω) n ℓ := by
  have H := krePath_unif hf hc.n_ge hω
  have hf' := hf.2.2.1
  have hδ1 := hf.2.1
  have hVδ := hf.2.2.2
  have heps := hc.one_le_eps
  have heps0 : (0 : ℝ) ≤ eps := by linarith
  have hn1 := hc.one_le
  have hY := hc.one_le_log
  obtain ⟨hZ3, hz0, htail⟩ := refWalk_bounds hc hω
  have hZ2 : (n : ℝ) / 2 ≤ expPartial n ω := H.half_le
  have hV := c.V_pos
  have hL := c.L_pos
  have hfm := c.fmin_pos
  have ha0 := c.a_pos
  have hb1 : 0 < 1 - c.b := by linarith [c.b_lt_one]
  have hKL' : 307200 * c.L / c.fmin ^ 2 + 164 / (c.fmin * c.a) + 164 / (c.fmin * (1 - c.b)) ≤
      (n : ℝ) / reDelta eps (renyiKeys f n ω) n ℓ := hKL
  have hk1 : 0 ≤ 307200 * c.L / c.fmin ^ 2 := by positivity
  have hk2 : 0 ≤ 164 / (c.fmin * c.a) := by positivity
  have hk3 : 0 ≤ 164 / (c.fmin * (1 - c.b)) := by positivity
  set Y := Real.log n with hYdef
  set p := renyiKeys f n ω with hp
  set Δ := reDelta eps p n ℓ with hΔdef
  set K := reSize eps p n ℓ with hKdef
  set M := reSegs eps p n ℓ with hMdef
  set Z := expPartial n ω with hZdef
  have hΔ1 : (1 : ℝ) ≤ Δ := by exact_mod_cast one_le_reDelta (p := p) heps hn1 ℓ
  have hΔ0 : (0 : ℝ) < Δ := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  have hY0 : 0 < Y := by linarith
  have hYΔ : Y ≤ Δ := le_trans (le_self_pow₀ hY (by norm_num)) hΔY
  have hZ0 : 0 < Z := by linarith
  have hΔn : (Δ : ℝ) < n := by exact_mod_cast reDelta_lt heps hn1 h2
  set s := (n : ℝ) / Δ with hsdef
  have hsΔ : s * Δ = n := by rw [hsdef]; field_simp
  have hs0 : 0 < s := by positivity
  have hK1 : 1 ≤ K := one_le_reSize heps hn1 ℓ
  have hcov : (n : ℝ) ≤ K * Δ := by exact_mod_cast (re_cover (p := p) heps hn1 ℓ).2
  have hK2 : (K : ℝ) ≤ 2 * s := by
    have hc1 := (re_cover (p := p) heps hn1 ℓ).1
    have h1 : ((K - 1 : ℕ) : ℝ) * Δ < n := by exact_mod_cast hc1
    rw [Nat.cast_sub hK1, Nat.cast_one] at h1
    have h3 : ((K : ℝ) - 1) * Δ < s * Δ := by rw [hsΔ]; exact h1
    have h4 : (K : ℝ) - 1 < s := lt_of_mul_lt_mul_right h3 hΔ0.le
    have h5 : (1 : ℝ) ≤ s := by rw [hsdef, le_div_iff₀ hΔ0]; linarith
    linarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  -- the keys
  have hlt : ∀ j < K, j * Δ < n := fun j hj => mul_reDelta_lt heps hn1 hj
  set x : ℕ → ℝ := fun j => p (j * Δ) with hxdef
  have hxeq : ∀ j, x j = quantK f 0 1 (expPartial (j * Δ) ω / Z) := fun j => rfl
  have hu : ∀ j < K, expPartial (j * Δ) ω / Z ∈ Set.Icc (0 : ℝ) 1 :=
    fun j hj => H.mem_Icc _ (hlt j hj)
  set Λ := Z / Δ * (δ * c.L) with hΛdef
  set h := 320 * Δ / (c.fmin * n) with hhdef
  have hΛ0 : 0 ≤ Λ := by positivity
  have hh : 0 ≤ h := by positivity
  have hderiv : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun y => Z / Δ * cdfK f 0 y) (Z / Δ * f y) (Set.Icc 0 1) y :=
    fun y hy => (hasDerivWithinAt_cdfK hf' hy).const_mul _
  have hlip : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (0 : ℝ) 1,
      |Z / Δ * f y - Z / Δ * f w| ≤ Λ * |y - w| := by
    intro y hy w hw
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity), hΛdef, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hf'.lip y hy w hw) (by positivity)
  have hzlt : ∀ j, j + 1 < K → expPartial (j * Δ) ω < expPartial ((j + 1) * Δ) ω := by
    intro j hj
    have hΔ1' : 1 ≤ Δ := one_le_reDelta (p := p) heps hn1 ℓ
    apply H.strictMono
    show j * Δ < (j + 1) * Δ
    rw [Nat.succ_mul]
    omega
  have hmono : ∀ j, j + 1 < K → x j < x (j + 1) := by
    intro j hj
    rw [hxeq, hxeq]
    exact quantK_strictMonoOn hf' (hu j (by omega)) (hu (j + 1) hj)
      (div_lt_div_of_pos_right (hzlt j hj) hZ0)
  have hmem : ∀ j < K, x j ∈ Set.Icc (0 : ℝ) 1 := fun j _ => quantK_mem hf' _
  have hmesh : ∀ j, j + 1 < K → x (j + 1) - x j ≤ h := by
    intro j hj
    rw [hxeq, hxeq]
    have huv : expPartial (j * Δ) ω / Z ≤ expPartial ((j + 1) * Δ) ω / Z :=
      div_le_div_of_nonneg_right (hzlt j hj).le hZ0.le
    have h1 := quantK_sub_le hf' (hu j (by omega)) (hu (j + 1) hj) huv
    have hspan : expPartial ((j + 1) * Δ) ω - expPartial (j * Δ) ω ≤
        80 * ((((j + 1) * Δ : ℕ) : ℝ) - ((j * Δ : ℕ) : ℝ) + Y) :=
      H.span (j * Δ) ((j + 1) * Δ) (Nat.mul_le_mul_right _ (Nat.le_succ j)) (hlt (j + 1) hj)
    have e : (((j + 1) * Δ : ℕ) : ℝ) - ((j * Δ : ℕ) : ℝ) = Δ := by push_cast; ring
    rw [e] at hspan
    have h3 : expPartial ((j + 1) * Δ) ω - expPartial (j * Δ) ω ≤ 160 * Δ := by linarith
    refine h1.trans ?_
    rw [div_sub_div_same, div_div, hhdef, div_le_div_iff₀ (by positivity) (by positivity)]
    have a1 := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ c.fmin * n)
    have a2 : 160 * Δ * (c.fmin * n) ≤ 320 * Δ * (Z * c.fmin) := by
      have := mul_le_mul_of_nonneg_left (show (n : ℝ) ≤ 2 * Z by linarith)
        (by positivity : (0 : ℝ) ≤ 160 * Δ * c.fmin)
      linarith
    linarith
  -- the greedy cuts
  have hP : WindowPartition (windowFeasible eps (fun j => p (j * Δ))) K M
      (finCut eps (fun j => p (j * Δ)) K) := finCut_windowPartition heps0 _ K
  set cc := finCut eps (fun j => p (j * Δ)) K with hccdef
  set θ : ℕ → ℝ := fun i => eps + 160 * Real.sqrt (((cc (i + 1) : ℝ) - cc i) * Y / Δ)
    with hθdef
  have hθ : ∀ i < M, 0 ≤ θ i := fun i _ => by positivity
  have hfit : ∀ i < M, ∃ α β : ℝ, ∀ j, cc i ≤ j → j < cc (i + 1) →
      |Z / Δ * cdfK f 0 (x j) - (α * x j + β)| ≤ θ i := by
    intro i hi
    obtain ⟨α₀, β₀, hαβ⟩ := hP.window i hi
    have hlt_i := hP.lt_succ i hi
    have hle_K : cc (i + 1) ≤ K := hP.le_finish (by omega)
    refine ⟨α₀, β₀ + cc i + (expPartial (cc i * Δ) ω - ((cc i * Δ : ℕ) : ℝ)) / Δ, ?_⟩
    intro j hj1 hj2
    have hjK : j < K := by omega
    have h1 := hαβ (j - cc i) (by omega)
    have e1 : shiftSeq (fun j => p (j * Δ)) (cc i) (j - cc i) = x j := by
      simp only [shiftSeq]
      rw [Nat.add_sub_cancel' hj1]
    rw [e1, Nat.cast_sub hj1] at h1
    have hG : Z / Δ * cdfK f 0 (x j) = expPartial (j * Δ) ω / Δ := by
      rw [hxeq, cdfK_quantK hf' (hu j hjK)]
      field_simp
    rw [hG]
    have htube : |expPartial (j * Δ) ω - expPartial (cc i * Δ) ω -
        (((j * Δ : ℕ) : ℝ) - ((cc i * Δ : ℕ) : ℝ))| ≤
        80 * (Real.sqrt ((((j * Δ : ℕ) : ℝ) - ((cc i * Δ : ℕ) : ℝ)) * Y) + Y) :=
      H.tube _ _ (Nat.mul_le_mul_right _ hj1) (hlt j hjK)
    have e3 : ((j * Δ : ℕ) : ℝ) - ((cc i * Δ : ℕ) : ℝ) = ((j : ℝ) - cc i) * Δ := by
      push_cast; ring
    rw [e3] at htube
    have hjc : (cc i : ℝ) ≤ j := by exact_mod_cast hj1
    have hjc2 : (j : ℝ) + 1 ≤ cc (i + 1) := by exact_mod_cast hj2
    have hcc : (cc i : ℝ) + 1 ≤ cc (i + 1) := by exact_mod_cast hlt_i
    have htd := tube_div_le hY0.le hYΔ (t := (j : ℝ) - cc i) (τ := (cc (i + 1) : ℝ) - cc i)
      (by linarith) (by linarith) (by linarith)
    have key : expPartial (j * Δ) ω / Δ - (α₀ * x j +
        (β₀ + cc i + (expPartial (cc i * Δ) ω - ((cc i * Δ : ℕ) : ℝ)) / Δ)) =
        (expPartial (j * Δ) ω - expPartial (cc i * Δ) ω - ((j : ℝ) - cc i) * Δ) / Δ +
          (((j : ℝ) - cc i) - (α₀ * x j + β₀)) := by
      push_cast
      field_simp
      ring
    rw [key]
    have ht2 : |(expPartial (j * Δ) ω - expPartial (cc i * Δ) ω - ((j : ℝ) - cc i) * Δ) / Δ| ≤
        80 * (Real.sqrt (((j : ℝ) - cc i) * Δ * Y) + Y) / Δ := by
      rw [abs_div, abs_of_pos hΔ0]
      exact div_le_div_of_nonneg_right htube hΔ0.le
    have h1' : |((j : ℝ) - cc i) - (α₀ * x j + β₀)| ≤ eps := h1
    have habs := abs_add_le
      ((expPartial (j * Δ) ω - expPartial (cc i * Δ) ω - ((j : ℝ) - cc i) * Δ) / Δ)
      (((j : ℝ) - cc i) - (α₀ * x j + β₀))
    have hθi : θ i = eps + 160 * Real.sqrt (((cc (i + 1) : ℝ) - cc i) * Y / Δ) := rfl
    rw [hθi]
    linarith
  -- the range of the keys contains `[a, b]`
  have ha : x 0 ≤ c.a := by
    have hu0 := hu 0 (by omega)
    rw [Nat.zero_mul] at hu0
    have h1 := quantK_sub_le hf' ⟨le_refl (0 : ℝ), zero_le_one⟩ hu0 hu0.1
    rw [quantK_zero hf', sub_zero, sub_zero] at h1
    have hx0 : x 0 = quantK f 0 1 (expPartial 0 ω / Z) := by rw [hxeq, Nat.zero_mul]
    rw [hx0]
    refine h1.trans ?_
    have hA := (div_le_div_iff₀ (by positivity) hΔ0).1 (show 164 / (c.fmin * c.a) ≤ n / Δ by
      linarith)
    rw [div_div, div_le_iff₀ (by positivity)]
    have : expPartial 0 ω ≤ 82 * Δ := by linarith
    have a1 := mul_le_mul_of_nonneg_right (show (n : ℝ) ≤ 2 * Z by linarith)
      (by positivity : (0 : ℝ) ≤ c.fmin * c.a)
    linarith
  have hb : c.b ≤ x (K - 1) := by
    have hK' : K - 1 < K := by omega
    have huK := hu (K - 1) hK'
    have h1 := quantK_sub_le hf' huK ⟨zero_le_one, le_refl (1 : ℝ)⟩ huK.2
    rw [quantK_one hf'] at h1
    have hm : (K - 1) * Δ ≤ n := (hlt _ hK').le
    have ht := htail ((K - 1) * Δ) hm
    have em : (((K - 1) * Δ : ℕ) : ℝ) = ((K : ℝ) - 1) * Δ := by
      rw [Nat.cast_mul, Nat.cast_sub hK1, Nat.cast_one]
    rw [em] at ht
    have hB := (div_le_div_iff₀ (by positivity) hΔ0).1
      (show 164 / (c.fmin * (1 - c.b)) ≤ n / Δ by linarith)
    have h2' : (1 - expPartial ((K - 1) * Δ) ω / Z) / c.fmin ≤ 1 - c.b := by
      rw [one_sub_div hZ0.ne', div_div, div_le_iff₀ (by positivity)]
      have : Z - expPartial ((K - 1) * Δ) ω ≤ 82 * Δ := by linarith
      have a1 := mul_le_mul_of_nonneg_right (show (n : ℝ) ≤ 2 * Z by linarith)
        (by positivity : (0 : ℝ) ≤ c.fmin * (1 - c.b))
      linarith
    rw [hxeq]
    linarith
  -- Landau chaining
  have hland := landau_chain (G := fun y => Z / Δ * cdfK f 0 y) (G' := fun y => Z / Δ * f y)
    (Λ := Λ) (h := h) (x := x) (K := K) (M := M) (c := cc) (θ := θ) (a := c.a) (b := c.b)
    hderiv hlip hh hmono hmem hmesh hP.start hP.finish hP.lt_succ hfit hθ ha c.a_lt_b.le hb
  -- the left side
  have hleft : s * δ * c.V / 2 ≤ |Z / Δ * f c.b - Z / Δ * f c.a| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    have h1 : Z / Δ * (δ * c.V) ≤ Z / Δ * |f c.b - f c.a| :=
      mul_le_mul_of_nonneg_left hVδ (by positivity)
    have h2 : s / 2 ≤ Z / Δ := by
      have e : s / 2 = ((n : ℝ) / 2) / Δ := by rw [hsdef]; ring
      rw [e]
      exact div_le_div_of_nonneg_right hZ2 hΔ0.le
    have h3 : s / 2 * (δ * c.V) ≤ Z / Δ * (δ * c.V) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have e : s * δ * c.V / 2 = s / 2 * (δ * c.V) := by ring
    linarith
  -- the bounds on `Λ`, `Λ h`, `Λ h²`
  have hΛ3 : Λ ≤ 3 * s * δ * c.L := by
    have h1 : Z / Δ ≤ 3 * s := by
      have e : 3 * s = (3 * (n : ℝ)) / Δ := by rw [hsdef]; ring
      rw [e]
      exact div_le_div_of_nonneg_right hZ3 hΔ0.le
    have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ δ * c.L)
    rw [hΛdef]
    linarith
  have hΛh : Λ * h ≤ 960 * δ * c.L / c.fmin := by
    have e : Λ * h = 320 * Z * δ * c.L / (c.fmin * n) := by
      rw [hΛdef, hhdef]; field_simp
    rw [e, div_le_div_iff₀ (by positivity) hfm]
    have := mul_le_mul_of_nonneg_left hZ3 (by positivity : (0 : ℝ) ≤ 320 * δ * c.L * c.fmin)
    linarith
  have hΛhh : Λ * h ^ 2 ≤ 1 := by
    have e : Λ * h ^ 2 = Λ * h * h := by ring
    rw [e]
    have h1 : Λ * h * h ≤ 960 * δ * c.L / c.fmin * h := mul_le_mul_of_nonneg_right hΛh hh
    have h2 : 960 * δ * c.L / c.fmin * h ≤ 1 := by
      rw [hhdef]
      have e2 : 960 * δ * c.L / c.fmin * (320 * Δ / (c.fmin * n)) =
          δ * (307200 * c.L / c.fmin ^ 2) * Δ / n := by field_simp; ring
      rw [e2, div_le_one hnr]
      have hA : 307200 * c.L / c.fmin ^ 2 * Δ ≤ n := by
        have := (le_div_iff₀ hΔ0).1 (show 307200 * c.L / c.fmin ^ 2 ≤ n / Δ by linarith)
        linarith
      have hA0 : 0 ≤ 307200 * c.L / c.fmin ^ 2 * Δ := by positivity
      have h3 := mul_le_of_le_one_left hA0 hδ1
      have e3 : δ * (307200 * c.L / c.fmin ^ 2) * Δ = δ * (307200 * c.L / c.fmin ^ 2 * Δ) := by
        ring
      linarith
    linarith
  -- the right side
  set A := 25600 * Λ ^ 2 * Y / Δ with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hsumτ : ∑ i ∈ range M, ((cc (i + 1) : ℝ) - cc i) = K := by
    rw [Finset.sum_range_sub (fun i => (cc i : ℝ)), hP.finish, hP.start, Nat.cast_zero, sub_zero]
  have hτ0 : ∀ i < M, 0 ≤ A * ((cc (i + 1) : ℝ) - cc i) := by
    intro i hi
    have : (cc i : ℝ) ≤ cc (i + 1) := by exact_mod_cast (hP.lt_succ i hi).le
    have : 0 ≤ (cc (i + 1) : ℝ) - cc i := by linarith
    positivity
  have hterm : ∀ i ∈ range M, 4 * Real.sqrt ((θ i + Λ * h ^ 2) * Λ) ≤
      4 * Real.sqrt (2 * eps * Λ) + 4 * (A * ((cc (i + 1) : ℝ) - cc i)) ^ (1 / 4 : ℝ) := by
    intro i hi
    have hi' := mem_range.1 hi
    have : (cc i : ℝ) ≤ cc (i + 1) := by exact_mod_cast (hP.lt_succ i hi').le
    have hx0 : 0 ≤ ((cc (i + 1) : ℝ) - cc i) * Y / Δ := by
      have : 0 ≤ (cc (i + 1) : ℝ) - cc i := by linarith
      positivity
    have h1 := window_term_le heps hΛ0 hΛhh hx0
    have e : 25600 * Λ ^ 2 * (((cc (i + 1) : ℝ) - cc i) * Y / Δ) =
        A * ((cc (i + 1) : ℝ) - cc i) := by rw [hAdef]; ring
    rw [e] at h1
    exact h1
  have hsum1 := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_const, card_range, nsmul_eq_mul] at hsum1
  have e5 : ∑ i ∈ range M, 4 * (A * ((cc (i + 1) : ℝ) - cc i)) ^ (1 / 4 : ℝ) =
      4 * ∑ i ∈ range M, (A * ((cc (i + 1) : ℝ) - cc i)) ^ (1 / 4 : ℝ) :=
    (Finset.mul_sum _ _ _).symm
  rw [e5] at hsum1
  have hhold := sum_rpow_quarter_le M (fun i => A * ((cc (i + 1) : ℝ) - cc i)) hτ0
  rw [← Finset.mul_sum, hsumτ] at hhold
  have hchain : s * δ * c.V / 2 ≤ 4 * M * Real.sqrt (2 * eps * Λ) +
      4 * M ^ (3 / 4 : ℝ) * (25600 * Λ ^ 2 * Y / Δ * K) ^ (1 / 4 : ℝ) + M * (Λ * h) := by
    have e : 4 * (M : ℝ) ^ (3 / 4 : ℝ) * (25600 * Λ ^ 2 * Y / Δ * K) ^ (1 / 4 : ℝ) =
        4 * ((M : ℝ) ^ (3 / 4 : ℝ) * (A * K) ^ (1 / 4 : ℝ)) := by rw [hAdef]; ring
    rw [e]
    have h4 := mul_le_mul_of_nonneg_left hhold (by norm_num : (0 : ℝ) ≤ 4)
    have e2 : (M : ℝ) * Λ * h = M * (Λ * h) := by ring
    linarith
  exact curvLow_cases c hs0 hδ heps hΛ0 hΛ3 hY0 hΔ0 hK0 hK2 hM0 hsΔ hΛh hchain

end Layer

end

end PGM
