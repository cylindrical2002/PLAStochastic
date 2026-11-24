import PLAStochastic.Index.GEP.OrbitClosure.CharFunDensity
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# WP2: the density of partial sums (`lem:charfn`, `lem:sumdensity`)

Source: `research/2026-09-25-kep-proof/tex/main.tex`, `lem:charfn` (L214–244) and
`lem:sumdensity` (L246–270).  All densities are in the measure form `LocBd`.

* `one_sub_norm_charFun_sq_ge` (`lem:charfn`): a law with `LocBd M` and variance `σ²` has
  `1 - |ψ(t)|² ≥ c₀ min(1, t²σ²)/(Mσ)²`, `c₀ = 1.8·10⁻⁴`.  The proof differs from the TeX
  (which symmetrises to `Y = X - X'` and splits `|t|σ ≥ 1` / `|t|σ < 1`): it works with `X`
  itself and one parameter choice for all `t > 0`.  With `s = min(1, tσ)`,
  `η = s²/(1250 (Mσ)²)` and any phase `θ`, the set `{|x - m| < 2σ, 1 - cos(tx - θ) < η}` lies
  in at most `t(2σ + δ)/π + 1` intervals of length `2δ`, `δ = πs/(50 Mσ t)`
  (`1 - cos u ≥ 2 dist(u, 2πℤ)²/π²`; `exists_int_near`, `measure_near_le`), hence has mass
  `≤ 1/4` (`covering_arith`, using `Mσ ≥ 3/16` from Chebyshev and `LocBd`); Chebyshev gives
  `P(|X - m| ≥ 2σ) ≤ 1/4`, so `∫ (1 - cos(tx - θ)) dμ ≥ η/2` (`integral_one_sub_cos_ge`).
  Taking `θ = arg ψ(t)` gives `|ψ(t)| ≤ 1 - s²/(2500 (Mσ)²)`, and
  `1 - |ψ|² ≥ 1 - |ψ|`, `1/2500 ≥ c₀`.  The mean hypothesis is not used.
* `norm_charFun_le_taylor`: for `|t| ≤ 1/(βσ)`, `|ψ(t)| ≤ 1 - t²σ²/3`
  (`|e^{iu} - 1 - iu + u²/2| ≤ |u|³/6` for the centred variable, `E|X - m|³ ≤ βσ³`, `β ≥ 1`;
  the remainder bound is `norm_cexp_sub_taylor_two_le`, proved by two applications of
  `image_norm_le_of_norm_deriv_right_le_deriv_boundary` from `‖e^{is} - 1‖ ≤ |s|`).
* `locBd_convPow_of_moments` (`lem:sumdensity`): for `n ≥ 2`,
  `LocBd ((√n σ)⁻¹ + M exp(-c₀ (n-2) / (2 β² (Mσ)²))) (convPow μ n)`.  Proof: `ψ^n` is the
  characteristic function (`charFun_convPow`), integrable since `|ψ|^n ≤ |ψ|²`
  (`integral_norm_charFun_sq_le`); pointwise
  `|ψ(t)|^n ≤ e^{-nσ²t²/3} + e^{-c₀(n-2)/(2β²(Mσ)²)} |ψ(t)|²`
  (Taylor bound for `|t| ≤ t₀ = 1/(βσ)`, `lem:charfn` beyond); integrate
  (`integral_gaussian`, `∫|ψ|² ≤ 2πM`) and apply `locBd_of_integrable_charFun`.
* `locBd_convPow` (normalised form used by the one-layer bound): on `MomClass b β vmin`,
  `LocBd (L₀/√n + D e^{-c₂ (n-2)/D²}) (convPow ρ n)` with `L₀, c₂` depending only on
  `(b, β, vmin)`.  The leading term does not depend on `D`: this is the "forgetting" of the
  input density bound that closes the orbit induction.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal Real

/-- `‖e^{is} - 1 - is‖ ≤ s²/2` for `s ≥ 0`. -/
private theorem norm_cexp_sub_one_sub_le_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    ‖cexp (s * I) - 1 - s * I‖ ≤ s ^ 2 / 2 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cexp (x * I) - 1 - x * I)
      (cexp (x * I) * I - I) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) * I) I x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).mul_const I
    have h2 : HasDerivAt (fun x : ℝ => cexp (x * I)) (cexp (x * I) * I) x := h1.cexp
    exact (h2.sub_const 1).sub h1
  have hB : ∀ x : ℝ, HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
    intro x
    simpa using ((hasDerivAt_pow 2 x).div_const 2)
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := s)
    (f := fun x : ℝ => cexp (x * I) - 1 - x * I) (f' := fun x => cexp (x * I) * I - I)
    (B := fun x : ℝ => x ^ 2 / 2) (B' := fun x => x) ?_ ?_ ?_ hB ?_ ⟨hs, le_rfl⟩
  · exact fun x _ => (hd x).continuousAt.continuousWithinAt
  · exact fun x _ => (hd x).hasDerivWithinAt
  · simp
  · intro x hx
    have hx0 : 0 ≤ x := hx.1
    have : cexp (x * I) * I - I = I * (cexp (I * x) - 1) := by ring_nf
    rw [this, norm_mul, Complex.norm_I, one_mul]
    calc ‖cexp (I * x) - 1‖ ≤ ‖x‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      _ = x := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]

/-- `‖e^{iu} - 1 - iu + u²/2‖ ≤ u³/6` for `u ≥ 0`. -/
private theorem norm_cexp_sub_taylor_two_le_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
    ‖cexp (u * I) - 1 - u * I + ((u ^ 2 / 2 : ℝ) : ℂ)‖ ≤ u ^ 3 / 6 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cexp (x * I) - 1 - x * I + ((x ^ 2 / 2 : ℝ) : ℂ))
      (cexp (x * I) * I - I + x) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) * I) I x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).mul_const I
    have h3r : HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
      simpa using ((hasDerivAt_pow 2 x).div_const 2)
    have h3 : HasDerivAt (fun x : ℝ => ((x ^ 2 / 2 : ℝ) : ℂ)) (x : ℂ) x := h3r.ofReal_comp
    have h2 : HasDerivAt (fun x : ℝ => cexp (x * I)) (cexp (x * I) * I) x := h1.cexp
    exact ((h2.sub_const 1).sub h1).add h3
  have hB : ∀ x : ℝ, HasDerivAt (fun x : ℝ => x ^ 3 / 6) (x ^ 2 / 2) x := by
    intro x
    have h := (hasDerivAt_pow 3 x).div_const 6
    have e : ((3 : ℕ) : ℝ) * x ^ (3 - 1) / 6 = x ^ 2 / 2 := by
      rw [show (3 : ℕ) - 1 = 2 from rfl]; push_cast; ring
    rwa [e] at h
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := u)
    (f := fun x : ℝ => cexp (x * I) - 1 - x * I + ((x ^ 2 / 2 : ℝ) : ℂ))
    (f' := fun x => cexp (x * I) * I - I + x)
    (B := fun x : ℝ => x ^ 3 / 6) (B' := fun x => x ^ 2 / 2) ?_ ?_ ?_ hB ?_ ⟨hu, le_rfl⟩
  · exact fun x _ => (hd x).continuousAt.continuousWithinAt
  · exact fun x _ => (hd x).hasDerivWithinAt
  · simp
  · intro x hx
    have : cexp (x * I) * I - I + x = I * (cexp (x * I) - 1 - x * I) := by
      linear_combination (x : ℂ) * I_sq
    rw [this, norm_mul, Complex.norm_I, one_mul]
    exact norm_cexp_sub_one_sub_le_of_nonneg hx.1

/-- **Second-order Taylor bound for `e^{iu}`**: `‖e^{iu} - 1 - iu + u²/2‖ ≤ |u|³/6`. -/
theorem norm_cexp_sub_taylor_two_le (u : ℝ) :
    ‖cexp (u * I) - 1 - u * I + ((u ^ 2 / 2 : ℝ) : ℂ)‖ ≤ |u| ^ 3 / 6 := by
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]; exact norm_cexp_sub_taylor_two_le_of_nonneg hu
  · have h := norm_cexp_sub_taylor_two_le_of_nonneg (neg_nonneg.2 hu)
    rw [abs_of_nonpos hu]
    have hc : cexp (((-u : ℝ) : ℂ) * I) - 1 - ((-u : ℝ) : ℂ) * I + (((-u) ^ 2 / 2 : ℝ) : ℂ) =
        (starRingEnd ℂ) (cexp (u * I) - 1 - u * I + ((u ^ 2 / 2 : ℝ) : ℂ)) := by
      simp only [map_add, map_sub, map_mul, map_one, Complex.conj_ofReal,
        Complex.conj_I, ← Complex.exp_conj]
      push_cast
      ring_nf
    rw [hc, Complex.norm_conj] at h
    exact h

/-- **Taylor bound near the origin.**  For `|t| ≤ 1/(βσ)`, `|ψ(t)| ≤ 1 - t²σ²/3`. -/
theorem norm_charFun_le_taylor {μ : Measure ℝ} [IsProbabilityMeasure μ] {m σ β : ℝ}
    (h3 : MemLp id 3 μ) (hm : ∫ x, x ∂μ = m) (hvar : ∫ x, (x - m) ^ 2 ∂μ = σ ^ 2)
    (hσ : 0 < σ) (hβ : 1 ≤ β) (hκ : ∫ x, |x - m| ^ 3 ∂μ ≤ β * σ ^ 3) {t : ℝ}
    (ht : |t| ≤ 1 / (β * σ)) :
    ‖charFun μ t‖ ≤ 1 - t ^ 2 * σ ^ 2 / 3 := by
  -- integrability
  have hint1 : Integrable (fun x : ℝ => x) μ := h3.integrable (by norm_num)
  have hint2 : Integrable (fun x : ℝ => (x - m) ^ 2) μ :=
    Integrable.of_integral_ne_zero (by rw [hvar]; positivity)
  have hint3 : Integrable (fun x : ℝ => |x - m| ^ 3) μ := by
    have h3' : MemLp (fun x : ℝ => x - m) ((3 : ℕ) : ℝ≥0∞) μ := by
      have := h3.sub (memLp_const m)
      exact_mod_cast this
    simpa [Real.norm_eq_abs] using h3'.integrable_norm_pow (by norm_num)
  -- the centred exponential
  set w : ℝ → ℂ := fun x => cexp (((t * (x - m) : ℝ) : ℂ) * I) with hw
  have hψ : charFun μ t = cexp (((t * m : ℝ) : ℂ) * I) * ∫ x, w x ∂μ := by
    rw [charFun_apply_real, ← integral_const_mul]
    congr 1; funext x
    rw [hw, ← Complex.exp_add]; congr 1; push_cast; ring
  have hnormψ : ‖charFun μ t‖ = ‖∫ x, w x ∂μ‖ := by
    rw [hψ, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hw_int : Integrable w μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (ae_of_all _ fun x => ?_)
    · exact Continuous.aestronglyMeasurable (by rw [hw]; fun_prop)
    · rw [hw, Complex.norm_exp_ofReal_mul_I]
  -- the polynomial part
  set P : ℝ → ℂ := fun x =>
    (((1 - (t * (x - m)) ^ 2 / 2 : ℝ)) : ℂ) + ((t * (x - m) : ℝ) : ℂ) * I with hP
  have hre_int : Integrable (fun x : ℝ => 1 - (t * (x - m)) ^ 2 / 2) μ := by
    have : (fun x : ℝ => 1 - (t * (x - m)) ^ 2 / 2) =
        fun x => 1 - t ^ 2 / 2 * (x - m) ^ 2 := by funext x; ring
    rw [this]
    exact (integrable_const 1).sub (hint2.const_mul _)
  have him_int : Integrable (fun x : ℝ => t * (x - m)) μ :=
    (hint1.sub (integrable_const m)).const_mul t
  have hP_int : Integrable P μ := by
    rw [hP]
    exact hre_int.ofReal.add (him_int.ofReal.mul_const I)
  have hre : ∫ x, (1 - (t * (x - m)) ^ 2 / 2) ∂μ = 1 - t ^ 2 * σ ^ 2 / 2 := by
    have : (fun x : ℝ => 1 - (t * (x - m)) ^ 2 / 2) =
        fun x => 1 - t ^ 2 / 2 * (x - m) ^ 2 := by funext x; ring
    rw [this, integral_sub (integrable_const 1) (hint2.const_mul _), integral_const,
      integral_const_mul, hvar]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    ring
  have him : ∫ x, t * (x - m) ∂μ = 0 := by
    rw [integral_const_mul, integral_sub hint1 (integrable_const m), hm, integral_const]
    simp
  have hintP : ∫ x, P x ∂μ = ((1 - t ^ 2 * σ ^ 2 / 2 : ℝ) : ℂ) := by
    have hA : Integrable (fun x : ℝ => (((1 - (t * (x - m)) ^ 2 / 2 : ℝ)) : ℂ)) μ :=
      hre_int.ofReal
    have hB : Integrable (fun x : ℝ => ((t * (x - m) : ℝ) : ℂ) * I) μ :=
      him_int.ofReal.mul_const I
    simp only [hP]
    rw [integral_add hA hB, integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal, hre, him]
    simp
  -- the remainder
  have hr : ∀ x, ‖w x - P x‖ ≤ |t| ^ 3 / 6 * |x - m| ^ 3 := by
    intro x
    have h := norm_cexp_sub_taylor_two_le (t * (x - m))
    have e : w x - P x = cexp (((t * (x - m) : ℝ) : ℂ) * I) - 1 - ((t * (x - m) : ℝ) : ℂ) * I +
        (((t * (x - m)) ^ 2 / 2 : ℝ) : ℂ) := by
      rw [hw, hP]; push_cast; ring
    rw [e]
    calc _ ≤ |t * (x - m)| ^ 3 / 6 := h
      _ = |t| ^ 3 / 6 * |x - m| ^ 3 := by rw [abs_mul, mul_pow]; ring
  have hsplit : ∫ x, w x ∂μ = ∫ x, P x ∂μ + ∫ x, (w x - P x) ∂μ := by
    have h' : Integrable (fun x => w x - P x) μ := hw_int.sub hP_int
    calc ∫ x, w x ∂μ = ∫ x, (P x + (w x - P x)) ∂μ := by congr 1; funext x; ring
      _ = ∫ x, P x ∂μ + ∫ x, (w x - P x) ∂μ := integral_add hP_int h'
  -- arithmetic
  have hβσ : 0 < β * σ := by positivity
  have h1 : |t| * (β * σ) ≤ 1 := by
    rw [le_div_iff₀ hβσ] at ht; exact ht
  have h2 : |t| * σ ≤ 1 := by
    have : |t| * σ ≤ |t| * (β * σ) := by
      nlinarith [mul_nonneg (mul_nonneg (abs_nonneg t) hσ.le) (sub_nonneg.2 hβ)]
    linarith
  have hts : t ^ 2 * σ ^ 2 = (|t| * σ) ^ 2 := by rw [mul_pow, sq_abs]
  have hts1 : t ^ 2 * σ ^ 2 ≤ 1 := by
    rw [hts]; have := abs_nonneg t; nlinarith [mul_nonneg (abs_nonneg t) hσ.le]
  have hrem : ∫ x, ‖w x - P x‖ ∂μ ≤ t ^ 2 * σ ^ 2 / 6 := by
    calc ∫ x, ‖w x - P x‖ ∂μ ≤ ∫ x, |t| ^ 3 / 6 * |x - m| ^ 3 ∂μ :=
          integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) (hint3.const_mul _)
            (ae_of_all _ hr)
      _ = |t| ^ 3 / 6 * ∫ x, |x - m| ^ 3 ∂μ := integral_const_mul _ _
      _ ≤ |t| ^ 3 / 6 * (β * σ ^ 3) := by gcongr
      _ = (|t| * σ) ^ 2 * (|t| * (β * σ)) / 6 := by ring
      _ ≤ (|t| * σ) ^ 2 * 1 / 6 := by gcongr
      _ = t ^ 2 * σ ^ 2 / 6 := by rw [hts]; ring
  rw [hnormψ, hsplit, hintP]
  calc ‖((1 - t ^ 2 * σ ^ 2 / 2 : ℝ) : ℂ) + ∫ x, (w x - P x) ∂μ‖
      ≤ ‖((1 - t ^ 2 * σ ^ 2 / 2 : ℝ) : ℂ)‖ + ‖∫ x, (w x - P x) ∂μ‖ := norm_add_le _ _
    _ ≤ (1 - t ^ 2 * σ ^ 2 / 2) + ∫ x, ‖w x - P x‖ ∂μ := by
        gcongr
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        · exact norm_integral_le_integral_norm _
    _ ≤ 1 - t ^ 2 * σ ^ 2 / 3 := by linarith

/-- A local bound of a probability measure is positive. -/
private theorem LocBd.pos_of_prob {M : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hM : LocBd M μ) : 0 < M := by
  by_contra hneg
  have h1 := hM univ MeasurableSet.univ
  rw [measure_univ, ENNReal.ofReal_of_nonpos (not_lt.1 hneg), zero_mul] at h1
  exact one_ne_zero (le_zero_iff.1 h1)

/-- If `1 - cos(t x - θ) < η` then `x` is within `π √(η/2)/t` of a point `(θ + 2πk)/t`. -/
private theorem exists_int_near {t θ η x : ℝ} (ht : 0 < t) (h : 1 - Real.cos (t * x - θ) < η) :
    ∃ k : ℤ, |x - (θ + 2 * π * k) / t| < π * Real.sqrt (η / 2) / t := by
  set u := t * x - θ with hu
  set k : ℤ := round (u / (2 * π)) with hk
  refine ⟨k, ?_⟩
  set w := u - k * (2 * π) with hw
  have hpi : 0 < 2 * π := by positivity
  have hwpi : |w| ≤ π := by
    have h1 := abs_sub_round (u / (2 * π))
    have e : w = (u / (2 * π) - round (u / (2 * π))) * (2 * π) := by
      rw [hw, hk]; field_simp
    rw [e, abs_mul, abs_of_pos hpi]
    calc |u / (2 * π) - round (u / (2 * π))| * (2 * π) ≤ 1 / 2 * (2 * π) := by gcongr
      _ = π := by ring
  have hcos : Real.cos u = Real.cos w := by rw [hw, Real.cos_sub_int_mul_two_pi]
  have hq := Real.cos_le_one_sub_mul_cos_sq hwpi
  have h2 : 2 / π ^ 2 * w ^ 2 < η := by rw [hcos] at h; linarith
  have hπ2 : 0 < π ^ 2 := by positivity
  have h2' : 2 * w ^ 2 < η * π ^ 2 := by
    calc 2 * w ^ 2 = (2 / π ^ 2 * w ^ 2) * π ^ 2 := by field_simp
      _ < η * π ^ 2 := by gcongr
  have hη : 0 ≤ η := by
    have : 0 ≤ 2 / π ^ 2 * w ^ 2 := by positivity
    linarith
  have h3 : w ^ 2 < (π * Real.sqrt (η / 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    linarith
  have h4 : |w| < π * Real.sqrt (η / 2) := abs_lt_of_sq_lt_sq h3 (by positivity)
  have h5 : x - (θ + 2 * π * k) / t = w / t := by
    rw [hw, hu]; field_simp; ring
  rw [h5, abs_div, abs_of_pos ht]
  exact div_lt_div_of_pos_right h4 ht

/-- **Covering of the sublevel set.**  The part of `{1 - cos(t x - θ) < η}` in `|x - m| < R`
lies in at most `t(R + δ)/π + 1` intervals of length `2δ`. -/
private theorem measure_near_le {μ : Measure ℝ} {M t θ η δ m R : ℝ} (hM : LocBd M μ)
    (hM0 : 0 < M) (ht : 0 < t) (hδ : 0 < δ) (hR : 0 < R)
    (hnear : ∀ x, 1 - Real.cos (t * x - θ) < η → ∃ k : ℤ, |x - (θ + 2 * π * k) / t| < δ) :
    μ {x | |x - m| < R ∧ 1 - Real.cos (t * x - θ) < η} ≤
      ENNReal.ofReal ((t * (R + δ) / π + 1) * (M * (2 * δ))) := by
  have hpi : 0 < 2 * π := by positivity
  set lo := (t * (m - R - δ) - θ) / (2 * π) with hlo
  set hi := (t * (m + R + δ) - θ) / (2 * π) with hhi
  set F := Finset.Icc ⌈lo⌉ ⌊hi⌋ with hF
  set c : ℤ → ℝ := fun k => (θ + 2 * π * k) / t with hc
  have hsub : {x | |x - m| < R ∧ 1 - Real.cos (t * x - θ) < η} ⊆
      ⋃ k ∈ F, Ioo (c k - δ) (c k + δ) := by
    rintro x ⟨hxR, hxη⟩
    obtain ⟨k, hk⟩ := hnear x hxη
    rw [abs_lt] at hk hxR
    simp only [mem_iUnion, mem_Ioo, exists_prop]
    refine ⟨k, ?_, by rw [hc]; constructor <;> linarith [hk.1, hk.2]⟩
    have hc1 : m - R - δ < (θ + 2 * π * k) / t := by linarith [hk.2]
    have hc2 : (θ + 2 * π * k) / t < m + R + δ := by linarith [hk.1]
    rw [lt_div_iff₀ ht] at hc1
    rw [div_lt_iff₀ ht] at hc2
    rw [hF, Finset.mem_Icc]
    constructor
    · rw [Int.ceil_le, hlo, div_le_iff₀ hpi]; linarith
    · rw [Int.le_floor, hhi, le_div_iff₀ hpi]; linarith
  have hcard : (F.card : ℝ) ≤ t * (R + δ) / π + 1 := by
    have e1 : (F.card : ℝ) = ((F.card : ℤ) : ℝ) := (Int.cast_natCast _).symm
    rw [e1, hF, Int.card_Icc, Int.toNat_eq_max]
    push_cast
    have hfl := Int.floor_le hi
    have hce := Int.le_ceil lo
    have ehl : hi - lo = t * (R + δ) / π := by
      rw [hhi, hlo]; field_simp; ring
    have hpos : 0 ≤ t * (R + δ) / π := by positivity
    refine max_le ?_ (by linarith)
    linarith
  calc μ {x | |x - m| < R ∧ 1 - Real.cos (t * x - θ) < η}
      ≤ μ (⋃ k ∈ F, Ioo (c k - δ) (c k + δ)) := measure_mono hsub
    _ ≤ ∑ k ∈ F, μ (Ioo (c k - δ) (c k + δ)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ F, ENNReal.ofReal (M * (2 * δ)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        calc μ (Ioo (c k - δ) (c k + δ)) ≤ ENNReal.ofReal M * volume (Ioo (c k - δ) (c k + δ)) :=
              hM _ measurableSet_Ioo
          _ = ENNReal.ofReal (M * (2 * δ)) := by
              rw [Real.volume_Ioo, ← ENNReal.ofReal_mul hM0.le]; congr 1; ring
    _ = ENNReal.ofReal (F.card * (M * (2 * δ))) := by
        rw [Finset.sum_const, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _ : (0 : ℝ) ≤ F.card), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((t * (R + δ) / π + 1) * (M * (2 * δ))) := by
        gcongr

/-- Chebyshev: `P(|X - m| ≥ r) ≤ σ²/r²`. -/
private theorem measureReal_le_abs_sub_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {m σ r : ℝ}
    (hint : Integrable (fun x => (x - m) ^ 2) μ) (hvar : ∫ x, (x - m) ^ 2 ∂μ = σ ^ 2)
    (hr : 0 < r) : μ.real {x | r ≤ |x - m|} ≤ σ ^ 2 / r ^ 2 := by
  have h := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (ae_of_all _ fun x => sq_nonneg (x - m)) hint (r ^ 2)
  rw [hvar] at h
  have hset : {x : ℝ | r ≤ |x - m|} = {x | r ^ 2 ≤ (x - m) ^ 2} := by
    ext x
    change r ≤ |x - m| ↔ r ^ 2 ≤ (x - m) ^ 2
    rw [← sq_abs (x - m), sq_le_sq₀ hr.le (abs_nonneg _)]
  rw [hset, le_div_iff₀ (by positivity)]
  linarith

/-- `M σ ≥ 3/16` for a law with `LocBd M` and variance `σ²`. -/
private theorem three_div_sixteen_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {M m σ : ℝ}
    (hM : LocBd M μ) (hint : Integrable (fun x => (x - m) ^ 2) μ)
    (hvar : ∫ x, (x - m) ^ 2 ∂μ = σ ^ 2) (hσ : 0 < σ) : 3 / 16 ≤ M * σ := by
  have hM0 := hM.pos_of_prob
  have hcheb := measureReal_le_abs_sub_le hint hvar (by positivity : (0 : ℝ) < 2 * σ)
  have e : σ ^ 2 / (2 * σ) ^ 2 = 1 / 4 := by field_simp; ring
  rw [e] at hcheb
  have hcover : (univ : Set ℝ) ⊆ Ioo (m - 2 * σ) (m + 2 * σ) ∪ {x | 2 * σ ≤ |x - m|} := by
    intro x _
    by_cases h : 2 * σ ≤ |x - m|
    · exact Or.inr h
    · left
      rw [not_le, abs_lt] at h
      constructor <;> linarith [h.1, h.2]
  have h1 : (1 : ℝ) ≤ μ.real (Ioo (m - 2 * σ) (m + 2 * σ)) + μ.real {x | 2 * σ ≤ |x - m|} := by
    calc (1 : ℝ) = μ.real univ := probReal_univ.symm
      _ ≤ μ.real (Ioo (m - 2 * σ) (m + 2 * σ) ∪ {x | 2 * σ ≤ |x - m|}) := measureReal_mono hcover
      _ ≤ _ := measureReal_union_le _ _
  have h2 : μ.real (Ioo (m - 2 * σ) (m + 2 * σ)) ≤ M * (4 * σ) := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    calc μ (Ioo (m - 2 * σ) (m + 2 * σ))
        ≤ ENNReal.ofReal M * volume (Ioo (m - 2 * σ) (m + 2 * σ)) := hM _ measurableSet_Ioo
      _ = ENNReal.ofReal (M * (4 * σ)) := by
          rw [Real.volume_Ioo, ← ENNReal.ofReal_mul hM0.le]; congr 1; ring
  linarith

/-- The arithmetic of the covering bound: the sublevel set has mass at most `1/4`. -/
private theorem covering_arith {M σ t s : ℝ} (hM0 : 0 < M) (hσ : 0 < σ) (ht : 0 < t)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hst : s ≤ t * σ) (hMσ : 3 / 16 ≤ M * σ) :
    (t * (2 * σ + π * s / (50 * M * σ * t)) / π + 1) * (M * (2 * (π * s / (50 * M * σ * t))))
      ≤ 1 / 4 := by
  have e : (t * (2 * σ + π * s / (50 * M * σ * t)) / π + 1) *
      (M * (2 * (π * s / (50 * M * σ * t)))) =
      2 * s / 25 + π * s * (s / (σ * t)) * (1 / (M * σ)) / 1250 + π * (s / (σ * t)) / 25 := by
    field_simp; ring
  rw [e]
  have hp : s / (σ * t) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hq : 1 / (M * σ) ≤ 16 / 3 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hp0 : 0 ≤ s / (σ * t) := by positivity
  have hq0 : 0 ≤ 1 / (M * σ) := by positivity
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have h1 : π * s * (s / (σ * t)) * (1 / (M * σ)) ≤ π * 1 * 1 * (16 / 3) := by gcongr
  have h2 : π * (s / (σ * t)) ≤ π * 1 := by gcongr
  linarith

/-- **Phase bound.**  For `t > 0` and every phase `θ`,
`∫ (1 - cos(t x - θ)) dμ ≥ min(1, tσ)² / (2500 (Mσ)²)`. -/
private theorem integral_one_sub_cos_ge {μ : Measure ℝ} [IsProbabilityMeasure μ] {M m σ t : ℝ}
    (hM : LocBd M μ) (hint : Integrable (fun x => (x - m) ^ 2) μ)
    (hvar : ∫ x, (x - m) ^ 2 ∂μ = σ ^ 2) (hσ : 0 < σ) (ht : 0 < t) (θ : ℝ) :
    min 1 (t * σ) ^ 2 / (2500 * (M * σ) ^ 2) ≤ ∫ x, (1 - Real.cos (t * x - θ)) ∂μ := by
  have hM0 := hM.pos_of_prob
  have hMσ := three_div_sixteen_le hM hint hvar hσ
  set s := min 1 (t * σ) with hs
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hst : s ≤ t * σ := min_le_right _ _
  set η := s ^ 2 / (1250 * (M * σ) ^ 2) with hη
  set δ := π * s / (50 * M * σ * t) with hδ
  have hδ0 : 0 < δ := by positivity
  have hsqrt : π * Real.sqrt (η / 2) / t = δ := by
    have e : η / 2 = (s / (50 * (M * σ))) ^ 2 := by rw [hη]; field_simp; ring
    rw [e, Real.sqrt_sq (by positivity), hδ]; field_simp
  have hnear : ∀ x, 1 - Real.cos (t * x - θ) < η →
      ∃ k : ℤ, |x - (θ + 2 * π * k) / t| < δ := by
    intro x hx
    obtain ⟨k, hk⟩ := exists_int_near ht hx
    exact ⟨k, hsqrt ▸ hk⟩
  have hS := measure_near_le (m := m) (R := 2 * σ) hM hM0 ht hδ0 (by positivity) hnear
  have harith := covering_arith hM0 hσ ht hs0 hs1 hst hMσ
  rw [← hδ] at harith
  have hSreal : μ.real {x | |x - m| < 2 * σ ∧ 1 - Real.cos (t * x - θ) < η} ≤ 1 / 4 :=
    ENNReal.toReal_le_of_le_ofReal (by norm_num) (hS.trans (ENNReal.ofReal_le_ofReal harith))
  have hcheb := measureReal_le_abs_sub_le hint hvar (by positivity : (0 : ℝ) < 2 * σ)
  have e4 : σ ^ 2 / (2 * σ) ^ 2 = 1 / 4 := by field_simp; ring
  rw [e4] at hcheb
  set g : ℝ → ℝ := fun x => 1 - Real.cos (t * x - θ) with hg
  have hcover : (univ : Set ℝ) ⊆ {x | η ≤ g x} ∪
      ({x | 2 * σ ≤ |x - m|} ∪ {x | |x - m| < 2 * σ ∧ 1 - Real.cos (t * x - θ) < η}) := by
    intro x _
    by_cases h1 : η ≤ g x
    · exact Or.inl h1
    · right
      by_cases h2 : 2 * σ ≤ |x - m|
      · exact Or.inl h2
      · exact Or.inr ⟨not_le.1 h2, not_le.1 h1⟩
  have h1 : (1 : ℝ) ≤ μ.real {x | η ≤ g x} + (μ.real {x | 2 * σ ≤ |x - m|} +
      μ.real {x | |x - m| < 2 * σ ∧ 1 - Real.cos (t * x - θ) < η}) := by
    calc (1 : ℝ) = μ.real univ := probReal_univ.symm
      _ ≤ _ := measureReal_mono hcover
      _ ≤ _ := measureReal_union_le _ _
      _ ≤ _ := by gcongr; exact measureReal_union_le _ _
  have hA : 1 / 2 ≤ μ.real {x | η ≤ g x} := by linarith
  have hg_int : Integrable g μ := by
    refine Integrable.mono' (integrable_const (2 : ℝ)) ?_ (ae_of_all _ fun x => ?_)
    · exact Continuous.aestronglyMeasurable (by rw [hg]; fun_prop)
    · rw [hg, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [Real.cos_le_one (t * x - θ), Real.neg_one_le_cos (t * x - θ)]
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun x => sub_nonneg.2 (Real.cos_le_one (t * x - θ))) hg_int η
  have hη0 : 0 ≤ η := by positivity
  calc s ^ 2 / (2500 * (M * σ) ^ 2) = η * (1 / 2) := by rw [hη]; field_simp; ring
    _ ≤ η * μ.real {x | η ≤ g x} := by gcongr
    _ ≤ ∫ x, g x ∂μ := hmarkov

/-- For `t > 0`: `‖ψ(t)‖ ≤ 1 - min(1, tσ)²/(2500 (Mσ)²)`. -/
private theorem norm_charFun_le_of_pos {μ : Measure ℝ} [IsProbabilityMeasure μ] {M m σ t : ℝ}
    (hM : LocBd M μ) (hint : Integrable (fun x => (x - m) ^ 2) μ)
    (hvar : ∫ x, (x - m) ^ 2 ∂μ = σ ^ 2) (hσ : 0 < σ) (ht : 0 < t) :
    ‖charFun μ t‖ ≤ 1 - min 1 (t * σ) ^ 2 / (2500 * (M * σ) ^ 2) := by
  set z := charFun μ t with hz
  set θ := Complex.arg z with hθ
  have h := integral_one_sub_cos_ge hM hint hvar hσ ht θ
  have hcos_int : Integrable (fun x : ℝ => Real.cos (t * x - θ)) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (ae_of_all _ fun x => ?_)
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  have hint_c : Integrable (fun x : ℝ => cexp (((t * x - θ : ℝ) : ℂ) * I)) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (ae_of_all _ fun x => ?_)
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · rw [Complex.norm_exp_ofReal_mul_I]
  have hz1 : cexp (-(θ : ℂ) * I) * z = (‖z‖ : ℂ) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
    rw [mul_left_comm, ← Complex.exp_add, ← hθ]
    simp
  have hz2 : cexp (-(θ : ℂ) * I) * z = ∫ x, cexp (((t * x - θ : ℝ) : ℂ) * I) ∂μ := by
    rw [hz, charFun_apply_real, ← integral_const_mul]
    congr 1; funext x
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hre : ∫ x, Real.cos (t * x - θ) ∂μ = ‖z‖ := by
    have h1 : ∫ x, Real.cos (t * x - θ) ∂μ =
        ∫ x, RCLike.re (cexp (((t * x - θ : ℝ) : ℂ) * I)) ∂μ := by
      congr 1; funext x; rw [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re]
    rw [h1, integral_re hint_c, ← hz2, hz1, RCLike.re_to_complex, Complex.ofReal_re]
  rw [integral_sub (integrable_const 1) hcos_int, integral_const, hre] at h
  simp only [probReal_univ, smul_eq_mul, one_mul] at h
  linarith

/-- The constant `c₀ = 1.8·10⁻⁴` of `lem:charfn`. -/
def c0CharFn : ℝ := 9 / 50000

theorem c0CharFn_pos : 0 < c0CharFn := by unfold c0CharFn; norm_num

/-- **`lem:charfn`.**  `1 - |ψ(t)|² ≥ c₀ min(1, t²σ²)/(Mσ)²` for a law with `LocBd M`, mean
`m` and variance `σ² > 0`. -/
theorem one_sub_norm_charFun_sq_ge {μ : Measure ℝ} [IsProbabilityMeasure μ] {M m σ : ℝ}
    (hM : LocBd M μ) (h2 : MemLp id 2 μ) (hm : ∫ x, x ∂μ = m)
    (hvar : ∫ x, (x - m) ^ 2 ∂μ = σ ^ 2) (hσ : 0 < σ) (t : ℝ) :
    c0CharFn * min 1 (t ^ 2 * σ ^ 2) / (M * σ) ^ 2 ≤ 1 - ‖charFun μ t‖ ^ 2 := by
  -- The mean hypothesis `hm` is not needed: the bound holds around any centre `m`.
  have _hmean := hm
  have hint : Integrable (fun x => (x - m) ^ 2) μ := (h2.sub (memLp_const m)).integrable_sq
  have key : ∀ τ : ℝ, 0 < τ →
      c0CharFn * min 1 (τ ^ 2 * σ ^ 2) / (M * σ) ^ 2 ≤ 1 - ‖charFun μ τ‖ ^ 2 := by
    intro τ hτ
    have h := norm_charFun_le_of_pos hM hint hvar hσ hτ
    have hn0 := norm_nonneg (charFun μ τ)
    have hn1 := norm_charFun_le_one (μ := μ) τ
    have hτσ : 0 < τ * σ := mul_pos hτ hσ
    have hsq : min 1 (τ * σ) ^ 2 = min 1 (τ ^ 2 * σ ^ 2) := by
      rcases le_total (τ * σ) 1 with h1 | h1
      · rw [min_eq_right h1, min_eq_right (by nlinarith)]; ring
      · rw [min_eq_left h1, min_eq_left (by nlinarith)]; ring
    rw [← hsq]
    have hc0 : c0CharFn ≤ 1 / 2500 := by unfold c0CharFn; norm_num
    have hA : c0CharFn * min 1 (τ * σ) ^ 2 / (M * σ) ^ 2 ≤
        min 1 (τ * σ) ^ 2 / (2500 * (M * σ) ^ 2) := by
      have e : min 1 (τ * σ) ^ 2 / (2500 * (M * σ) ^ 2) =
          1 / 2500 * min 1 (τ * σ) ^ 2 / (M * σ) ^ 2 := by field_simp
      rw [e]
      gcongr
    have hsq' : ‖charFun μ τ‖ ^ 2 ≤ ‖charFun μ τ‖ := by nlinarith
    linarith
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h := key (-t) (neg_pos.2 ht)
    rwa [charFun_neg, Complex.norm_conj, neg_sq] at h
  · have h1 := norm_charFun_le_one (μ := μ) (0 : ℝ)
    have h0 := norm_nonneg (charFun μ 0)
    have e : min 1 ((0 : ℝ) ^ 2 * σ ^ 2) = 0 := by simp
    rw [e, mul_zero, zero_div]
    nlinarith
  · exact key t ht

/-- Monotonicity of `LocBd` in the constant. -/
private theorem LocBd.mono_const {D D' : ℝ} {μ : Measure ℝ} (h : LocBd D μ) (hDD : D ≤ D') :
    LocBd D' μ :=
  fun A hA => (h A hA).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hDD) _)

/-- **`lem:sumdensity`**, unnormalised form: for `n ≥ 2`, `S_n` has local bound
`(√n σ)⁻¹ + M exp(-c₀ (n - 2) / (2 β² (Mσ)²))`. -/
theorem locBd_convPow_of_moments {μ : Measure ℝ} [IsProbabilityMeasure μ] {M m σ β : ℝ}
    (hM : LocBd M μ) (hM0 : 0 < M) (h3 : MemLp id 3 μ) (hm : ∫ x, x ∂μ = m)
    (hvar : ∫ x, (x - m) ^ 2 ∂μ = σ ^ 2) (hσ : 0 < σ) (hβ : 1 ≤ β)
    (hκ : ∫ x, |x - m| ^ 3 ∂μ ≤ β * σ ^ 3) {n : ℕ} (hn : 2 ≤ n) :
    LocBd ((Real.sqrt n * σ)⁻¹ +
      M * Real.exp (-(c0CharFn * ((n : ℝ) - 2)) / (2 * β ^ 2 * (M * σ) ^ 2)))
      (convPow μ n) := by
  have h2 : MemLp id 2 μ := h3.mono_exponent (by norm_num)
  obtain ⟨hint2, hL2⟩ := integral_norm_charFun_sq_le hM
  have hβ0 : 0 < β := by linarith
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set q : ℝ := c0CharFn / (β ^ 2 * (M * σ) ^ 2) with hq
  have hq0 : 0 < q := by have := c0CharFn_pos; positivity
  set E₂ : ℝ := Real.exp (-(c0CharFn * ((n : ℝ) - 2)) / (2 * β ^ 2 * (M * σ) ^ 2)) with hE₂
  have hE₂0 : 0 ≤ E₂ := (Real.exp_pos _).le
  have hE₂' : E₂ = Real.exp (-(q / 2)) ^ (n - 2) := by
    rw [hE₂, ← Real.exp_nat_mul]
    congr 1
    rw [Nat.cast_sub hn, hq]
    push_cast
    field_simp
  set b : ℝ := n * σ ^ 2 / 3 with hb
  have hb0 : 0 < b := by positivity
  have hpt : ∀ t, ‖charFun μ t‖ ^ n ≤ Real.exp (-b * t ^ 2) + E₂ * ‖charFun μ t‖ ^ 2 := by
    intro t
    have hn0 := norm_nonneg (charFun μ t)
    have hn1 := norm_charFun_le_one (μ := μ) t
    by_cases ht : |t| ≤ 1 / (β * σ)
    · have hT := norm_charFun_le_taylor h3 hm hvar hσ hβ hκ ht
      have h1 : ‖charFun μ t‖ ≤ Real.exp (-(t ^ 2 * σ ^ 2 / 3)) :=
        hT.trans (by linarith [Real.add_one_le_exp (-(t ^ 2 * σ ^ 2 / 3))])
      have h1' : ‖charFun μ t‖ ^ n ≤ Real.exp (-b * t ^ 2) := by
        calc ‖charFun μ t‖ ^ n ≤ Real.exp (-(t ^ 2 * σ ^ 2 / 3)) ^ n := pow_le_pow_left₀ hn0 h1 n
          _ = Real.exp (-b * t ^ 2) := by rw [← Real.exp_nat_mul, hb]; congr 1; ring
      have : 0 ≤ E₂ * ‖charFun μ t‖ ^ 2 := by positivity
      linarith
    · push Not at ht
      have hC := one_sub_norm_charFun_sq_ge hM h2 hm hvar hσ t
      have hmin : 1 / β ^ 2 ≤ min 1 (t ^ 2 * σ ^ 2) := by
        refine le_min ?_ ?_
        · rw [div_le_one (by positivity)]; nlinarith
        · have h1 : 1 < |t| * (β * σ) := by rwa [div_lt_iff₀ (by positivity)] at ht
          rw [div_le_iff₀ (by positivity)]
          have e : t ^ 2 * σ ^ 2 * β ^ 2 = (|t| * (β * σ)) ^ 2 := by
            rw [mul_pow, mul_pow, sq_abs]; ring
          rw [e]; nlinarith
      have hqle : q ≤ c0CharFn * min 1 (t ^ 2 * σ ^ 2) / (M * σ) ^ 2 := by
        have e : q = c0CharFn * (1 / β ^ 2) / (M * σ) ^ 2 := by rw [hq]; field_simp
        rw [e]
        have := c0CharFn_pos
        gcongr
      have hsq : ‖charFun μ t‖ ^ 2 ≤ Real.exp (-(q / 2)) ^ 2 := by
        have e : Real.exp (-(q / 2)) ^ 2 = Real.exp (-q) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        rw [e]
        linarith [Real.add_one_le_exp (-q)]
      have hnorm : ‖charFun μ t‖ ≤ Real.exp (-(q / 2)) :=
        (sq_le_sq₀ hn0 (Real.exp_pos _).le).1 hsq
      have e : ‖charFun μ t‖ ^ n = ‖charFun μ t‖ ^ (n - 2) * ‖charFun μ t‖ ^ 2 := by
        rw [← pow_add, Nat.sub_add_cancel hn]
      rw [e, hE₂']
      have h1 : ‖charFun μ t‖ ^ (n - 2) ≤ Real.exp (-(q / 2)) ^ (n - 2) :=
        pow_le_pow_left₀ hn0 hnorm _
      have h2 : 0 ≤ Real.exp (-b * t ^ 2) := (Real.exp_pos _).le
      have h3 : ‖charFun μ t‖ ^ (n - 2) * ‖charFun μ t‖ ^ 2 ≤
          Real.exp (-(q / 2)) ^ (n - 2) * ‖charFun μ t‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      linarith
  have hfun : charFun (convPow μ n) = fun t => charFun μ t ^ n := funext (charFun_convPow μ n)
  have hint_n : Integrable (charFun (convPow μ n)) := by
    rw [hfun]
    refine Integrable.mono' hint2 ?_ (ae_of_all _ fun t => ?_)
    · exact (stronglyMeasurable_charFun (μ := μ)).aestronglyMeasurable.pow n
    · rw [norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) (norm_charFun_le_one t) hn
  have hloc := locBd_of_integrable_charFun hint_n
  refine hloc.mono_const ?_
  have hint_pow : Integrable (fun t => ‖charFun μ t‖ ^ n) := by
    have := hint_n.norm
    rw [hfun] at this
    simpa [norm_pow] using this
  have hI : ∫ t, ‖charFun (convPow μ n) t‖ ≤ Real.sqrt (π / b) + E₂ * (2 * π * M) := by
    rw [hfun]
    simp only [norm_pow]
    calc ∫ t, ‖charFun μ t‖ ^ n ≤ ∫ t, (Real.exp (-b * t ^ 2) + E₂ * ‖charFun μ t‖ ^ 2) :=
          integral_mono hint_pow ((integrable_exp_neg_mul_sq hb0).add (hint2.const_mul E₂)) hpt
      _ = Real.sqrt (π / b) + E₂ * ∫ t, ‖charFun μ t‖ ^ 2 := by
          rw [integral_add (integrable_exp_neg_mul_sq hb0) (hint2.const_mul E₂),
            integral_gaussian, integral_const_mul]
      _ ≤ Real.sqrt (π / b) + E₂ * (2 * π * M) := by gcongr
  have hsqrt : Real.sqrt (π / b) ≤ 2 * π * (Real.sqrt n * σ)⁻¹ := by
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
    have hsn2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by linarith)
    have hpos : 0 ≤ 2 * π * (Real.sqrt n * σ)⁻¹ := by positivity
    rw [← Real.sqrt_sq hpos]
    refine Real.sqrt_le_sqrt ?_
    have e1 : (2 * π * (Real.sqrt n * σ)⁻¹) ^ 2 = 4 * π ^ 2 / (Real.sqrt n ^ 2 * σ ^ 2) := by
      ring
    rw [hsn2] at e1
    have e2 : π / b = 3 * π / (n * σ ^ 2) := by rw [hb]; field_simp
    rw [e1, e2, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [Real.pi_gt_three]
  have h2pi : 0 < (2 * π)⁻¹ := by positivity
  calc (2 * π)⁻¹ * ∫ t, ‖charFun (convPow μ n) t‖
      ≤ (2 * π)⁻¹ * (Real.sqrt (π / b) + E₂ * (2 * π * M)) := by gcongr
    _ ≤ (2 * π)⁻¹ * (2 * π * (Real.sqrt n * σ)⁻¹ + E₂ * (2 * π * M)) := by gcongr
    _ = (Real.sqrt n * σ)⁻¹ + M * E₂ := by field_simp

/-- **`lem:sumdensity`**, normalised form on the moment class.  `L₀` and `c₂` depend only on
`(b, β, vmin)`; the input density bound `D` enters only through the second term. -/
theorem locBd_convPow {b β vmin : ℝ} (hvmin : 0 < vmin) (hvb : vmin ≤ b) (hβ : 1 ≤ β) :
    ∃ L₀ c₂ : ℝ, 0 < L₀ ∧ 0 < c₂ ∧ ∀ (ρ : ProbabilityMeasure ℝ) (D : ℝ), 0 < D →
      MomClass b β vmin ρ → LocBd D (ρ : Measure ℝ) → ∀ n : ℕ, 2 ≤ n →
        LocBd (L₀ / Real.sqrt n + D * Real.exp (-c₂ * ((n : ℝ) - 2) / D ^ 2))
          (convPow (ρ : Measure ℝ) n) := by
  have hb0 : 0 < b := lt_of_lt_of_le hvmin hvb
  have hβ0 : 0 < β := by linarith
  refine ⟨(Real.sqrt vmin)⁻¹, c0CharFn / (2 * β ^ 2 * b), by positivity,
    by have := c0CharFn_pos; positivity, ?_⟩
  intro ρ D hD hmom hloc n hn
  have hvar_pos : 0 < lawVar ρ := lt_of_lt_of_le hvmin hmom.var_ge
  set σ := Real.sqrt (lawVar ρ) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hvar_pos
  have hσ2 : σ ^ 2 = lawVar ρ := Real.sq_sqrt hvar_pos.le
  have hm : ∫ x, x ∂(ρ : Measure ℝ) = 1 := hmom.mean
  have hvar : ∫ x, (x - 1) ^ 2 ∂(ρ : Measure ℝ) = σ ^ 2 := by
    rw [hσ2, lawVar, hmom.mean]
  have h := locBd_convPow_of_moments hloc hD hmom.memLp3 hm hvar hσ hβ hmom.third_le hn
  refine h.mono_const ?_
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hσv : Real.sqrt vmin ≤ σ := Real.sqrt_le_sqrt hmom.var_ge
  have hsv : 0 < Real.sqrt vmin := Real.sqrt_pos.2 hvmin
  gcongr ?_ + D * Real.exp ?_
  · rw [div_eq_mul_inv, mul_inv, mul_comm]
    gcongr
  · have hn0 : 0 ≤ c0CharFn * ((n : ℝ) - 2) := by
      have := c0CharFn_pos; nlinarith
    have e1 : -(c0CharFn * ((n : ℝ) - 2)) / (2 * β ^ 2 * (D * σ) ^ 2) =
        -((c0CharFn * ((n : ℝ) - 2)) / (2 * β ^ 2 * D ^ 2 * σ ^ 2)) := by ring
    have e2 : -(c0CharFn / (2 * β ^ 2 * b)) * ((n : ℝ) - 2) / D ^ 2 =
        -((c0CharFn * ((n : ℝ) - 2)) / (2 * β ^ 2 * D ^ 2 * b)) := by
      field_simp
    rw [e1, e2, neg_le_neg_iff]
    have hσb : σ ^ 2 ≤ b := by rw [hσ2]; exact hmom.var_le
    exact div_le_div_of_nonneg_left hn0 (by positivity) (by gcongr)

end

end PGM
