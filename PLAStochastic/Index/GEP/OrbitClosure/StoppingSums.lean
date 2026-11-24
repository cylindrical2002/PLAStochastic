import PLAStochastic.Index.GEP.OrbitClosure.Defs

/-!
# WP2: the summation over stopping times (`density-tail.md` §5)

Pure real analysis.  `E = eps²` is the time scale, `a ≥ 0` the position, and
`qdev t a = min((a - t)²/t, |a - t|)`.

* `qdev_add_ge` (`density-tail.md` (5.1)): `t/E + Q_t(a) ≥ a/(2E)` for `E ≥ 1`, `t > 0`, `a ≥ 0`.
* `sum_sqrt_exp_qdev_le` (`density-tail.md` (5.3)):
  `sup_{a ≥ 0} ∑_{t ≥ 1} t^{-1/2} e^{-b Q_t(a)} < ∞`.  Instead of the three ranges of the
  source, the proof uses `Q_t(a) ≥ (√t - √a)²` (`sq_sqrt_sub_le_qdev`) and telescopes: each
  term is at most `(16 + 4/b)` times the increment of the bounded function `y ↦ y/(1+|y|)`
  between `y = √(t-1) - √a` and `y = √t - √a` (`term_le_increment`), so every partial sum is
  at most `2(16 + 4/b)`.
* `sum_kernel_le` (`density-tail.md` (5.2)–(5.3) and the last display of §5):
  `∑_t t^{-3/2} e^{-γ(E/t + t/E + Q_t(a))} ≤ (K/E) e^{-(γ/4) a/E}`, with `K` depending on `γ`
  only (split `γ(E/t + t/E + Q) ≥ γE/t + γa/(4E) + (γ/2)Q`, then `t⁻¹ e^{-γE/t} ≤ 1/(γE)`
  and (5.3) with `b = γ/2`; `K = K_{γ/2}/γ`).
* `sum_aux_le`: the part of the sum carried by the input density bound `D`,
  `∑_t t⁻¹ D e^{-c₂(⌊t/2⌋ - 2)/D²} e^{-γ(E/t + t/E + Q_t(a))} ≤ E⁻¹ e^{-(γ/4) a/E}` once
  `eps ≥ e₄(γ, c₂, D)`.  Instead of splitting at `t = eps^{3/2}`, the proof uses
  `γE/t + ct/4 ≥ √(γc) eps` (AM–GM, `c = c₂/D²`), so every term is at most
  `D e^{5c/2} e^{-√(γc) eps} e^{-(γ/4)a/E} (e^{-c/4})^t` (`aux_term_le`), and the geometric sum
  times `e^{-√(γc) eps}` is below `eps⁻²` for `eps ≥ max(1, 6A/(γc)^{3/2})`, where
  `A = D e^{5c/2}/(1 - e^{-c/4})` (`mul_exp_neg_le_inv_sq`, from `e^x ≥ x³/6`).
  This replaces the "natural scale" step of `prop:transfer`
  (`research/2026-09-25-kep-proof/tex/main.tex` L318–325).
-/

namespace PGM

noncomputable section

open Set Filter
open scoped ENNReal

private theorem qdev_nonneg {t a : ℝ} (ht : 0 ≤ t) : 0 ≤ qdev t a :=
  le_min (div_nonneg (sq_nonneg _) ht) (abs_nonneg _)

/-- (5.1): `t/E + Q_t(a) ≥ a/(2E)`. -/
theorem qdev_add_ge {E t a : ℝ} (hE : 1 ≤ E) (ht : 0 < t) (ha : 0 ≤ a) :
    a / (2 * E) ≤ t / E + qdev t a := by
  have hE0 : 0 < E := by linarith
  rcases le_or_gt a (2 * t) with h | h
  · have h1 : a / (2 * E) ≤ t / E := by
      rw [div_le_div_iff₀ (by positivity) hE0]; nlinarith
    linarith [qdev_nonneg (a := a) ht.le]
  · have hq : a - t ≤ qdev t a := by
      refine le_min ?_ (le_abs_self _)
      rw [le_div_iff₀ ht]; nlinarith
    have h1 : a / (2 * E) ≤ a / 2 :=
      div_le_div_of_nonneg_left ha (by norm_num) (by linarith)
    have h2 : 0 ≤ t / E := div_nonneg ht.le hE0.le
    linarith

/-- `Q_t(a) ≥ (√t - √a)²`. -/
private theorem sq_sqrt_sub_le_qdev {t a : ℝ} (ht : 0 < t) (ha : 0 ≤ a) :
    (Real.sqrt t - Real.sqrt a) ^ 2 ≤ qdev t a := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hr : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hts : t = Real.sqrt t ^ 2 := (Real.sq_sqrt ht.le).symm
  have har : a = Real.sqrt a ^ 2 := (Real.sq_sqrt ha).symm
  set s := Real.sqrt t
  set r := Real.sqrt a
  refine le_min ?_ ?_
  · rw [le_div_iff₀ ht]
    have h1 : (a - t) ^ 2 = (s - r) ^ 2 * (r + s) ^ 2 := by rw [hts, har]; ring
    rw [h1]
    have h2 : t ≤ (r + s) ^ 2 := by rw [hts]; nlinarith
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  · have h1 : |a - t| = |s - r| * (r + s) := by
      rw [hts, har, show r ^ 2 - s ^ 2 = (r - s) * (r + s) by ring, abs_mul,
        abs_of_nonneg (by linarith : 0 ≤ r + s), abs_sub_comm]
    rw [h1, ← sq_abs, sq]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_le]; constructor <;> linarith

/-- The bounded increasing function `y ↦ y/(1+|y|)` has increments at least
`(y₂ - y₁)/((1+|y₁|)(1+|y₂|))`. -/
private theorem div_one_add_abs_sub_ge {y₁ y₂ : ℝ} (h : y₁ ≤ y₂) :
    (y₂ - y₁) / ((1 + |y₁|) * (1 + |y₂|)) ≤ y₂ / (1 + |y₂|) - y₁ / (1 + |y₁|) := by
  have h1 : 0 < 1 + |y₁| := by positivity
  have h2 : 0 < 1 + |y₂| := by positivity
  have key : y₂ - y₁ ≤ y₂ * (1 + |y₁|) - y₁ * (1 + |y₂|) := by
    rcases le_total 0 y₁ with h₁ | h₁ <;> rcases le_total 0 y₂ with h₂ | h₂
    · rw [abs_of_nonneg h₁, abs_of_nonneg h₂]; nlinarith
    · rw [abs_of_nonneg h₁, abs_of_nonpos h₂]; nlinarith
    · rw [abs_of_nonpos h₁, abs_of_nonneg h₂]; nlinarith
    · rw [abs_of_nonpos h₁, abs_of_nonpos h₂]; nlinarith
  have heq : y₂ / (1 + |y₂|) - y₁ / (1 + |y₁|) =
      (y₂ * (1 + |y₁|) - y₁ * (1 + |y₂|)) / ((1 + |y₁|) * (1 + |y₂|)) := by
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right key (by positivity)

private theorem abs_div_one_add_abs_le (y : ℝ) : |y / (1 + |y|)| ≤ 1 := by
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + |y|), div_le_one (by positivity)]
  linarith

/-- The pointwise bound behind (5.3): for `t ≥ 1`, the term is dominated by an increment of the
bounded function `y ↦ y/(1+|y|)` along `y = √t - √a`. -/
private theorem term_le_increment {b t a : ℝ} (hb : 0 < b) (ht : 1 ≤ t) (ha : 0 ≤ a) :
    (Real.sqrt t)⁻¹ * Real.exp (-b * qdev t a) ≤
      (16 + 4 / b) * ((Real.sqrt t - Real.sqrt a) / (1 + |Real.sqrt t - Real.sqrt a|) -
        (Real.sqrt (t - 1) - Real.sqrt a) / (1 + |Real.sqrt (t - 1) - Real.sqrt a|)) := by
  set y₂ := Real.sqrt t - Real.sqrt a with hy₂
  set y₁ := Real.sqrt (t - 1) - Real.sqrt a with hy₁
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 (by linarith)
  have hs1 : 0 ≤ Real.sqrt (t - 1) := Real.sqrt_nonneg _
  have hsq_t : Real.sqrt t ^ 2 = t := Real.sq_sqrt (by linarith)
  have hsq_t1 : Real.sqrt (t - 1) ^ 2 = t - 1 := Real.sq_sqrt (by linarith)
  -- `√(t-1) ≤ √t ≤ √(t-1) + 1`
  have hle : Real.sqrt (t - 1) ≤ Real.sqrt t := Real.sqrt_le_sqrt (by linarith)
  have hle1 : Real.sqrt t ≤ Real.sqrt (t - 1) + 1 := by nlinarith
  -- `√t - √(t-1) ≥ 1/(2√t)`
  have hdiff : 1 / (2 * Real.sqrt t) ≤ y₂ - y₁ := by
    rw [hy₂, hy₁, div_le_iff₀ (by positivity)]
    nlinarith
  have hy12 : y₁ ≤ y₂ := by rw [hy₂, hy₁]; linarith
  have habs1 : |y₁| ≤ |y₂| + 1 := by
    have : |y₁| ≤ |y₂| + |y₁ - y₂| := by
      calc |y₁| = |y₂ + (y₁ - y₂)| := by ring_nf
        _ ≤ |y₂| + |y₁ - y₂| := abs_add_le _ _
    have h2 : |y₁ - y₂| ≤ 1 := by
      rw [abs_le]; constructor <;> (rw [hy₂, hy₁]; linarith)
    linarith
  have hprod : (1 + |y₁|) * (1 + |y₂|) ≤ (2 + |y₂|) ^ 2 := by
    have := abs_nonneg y₂; nlinarith [abs_nonneg y₁]
  -- the Gaussian factor
  have hgauss : 2 * Real.exp (-b * y₂ ^ 2) * (2 + |y₂|) ^ 2 ≤ 16 + 4 / b := by
    have hsq : (2 + |y₂|) ^ 2 ≤ 8 + 2 * y₂ ^ 2 := by
      have := sq_abs y₂; nlinarith [sq_nonneg (|y₂| - 2)]
    have he1 : Real.exp (-b * y₂ ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg y₂]
    have he2 : y₂ ^ 2 * Real.exp (-b * y₂ ^ 2) ≤ 1 / b := by
      rw [le_div_iff₀ hb]
      have h3 : b * y₂ ^ 2 + 1 ≤ Real.exp (b * y₂ ^ 2) := Real.add_one_le_exp _
      have h4 : Real.exp (b * y₂ ^ 2) * Real.exp (-b * y₂ ^ 2) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      have h5 : 0 < Real.exp (-b * y₂ ^ 2) := Real.exp_pos _
      nlinarith
    have hpos : 0 < Real.exp (-b * y₂ ^ 2) := Real.exp_pos _
    calc 2 * Real.exp (-b * y₂ ^ 2) * (2 + |y₂|) ^ 2
        ≤ 2 * Real.exp (-b * y₂ ^ 2) * (8 + 2 * y₂ ^ 2) := by gcongr
      _ = 16 * Real.exp (-b * y₂ ^ 2) + 4 * (y₂ ^ 2 * Real.exp (-b * y₂ ^ 2)) := by ring
      _ ≤ 16 * 1 + 4 * (1 / b) := by gcongr
      _ = 16 + 4 / b := by ring
  have hq : Real.exp (-b * qdev t a) ≤ Real.exp (-b * y₂ ^ 2) := by
    rw [Real.exp_le_exp]
    have := sq_sqrt_sub_le_qdev (t := t) (a := a) (by linarith) ha
    nlinarith
  have hinc := div_one_add_abs_sub_ge hy12
  have hK : 0 ≤ 16 + 4 / b := by positivity
  calc (Real.sqrt t)⁻¹ * Real.exp (-b * qdev t a)
      ≤ (Real.sqrt t)⁻¹ * Real.exp (-b * y₂ ^ 2) := by gcongr
    _ = (2 * Real.exp (-b * y₂ ^ 2) * (2 + |y₂|) ^ 2) *
          (1 / (2 * Real.sqrt t) / (2 + |y₂|) ^ 2) := by
        field_simp
    _ ≤ (16 + 4 / b) * ((y₂ - y₁) / ((1 + |y₁|) * (1 + |y₂|))) := by
        apply mul_le_mul hgauss _ (by positivity) hK
        calc 1 / (2 * Real.sqrt t) / (2 + |y₂|) ^ 2
            ≤ (y₂ - y₁) / (2 + |y₂|) ^ 2 := by gcongr
          _ ≤ (y₂ - y₁) / ((1 + |y₁|) * (1 + |y₂|)) := by
            apply div_le_div_of_nonneg_left (by linarith) (by positivity) hprod
    _ ≤ (16 + 4 / b) * (y₂ / (1 + |y₂|) - y₁ / (1 + |y₁|)) := by gcongr

/-- (5.3): a uniform bound for `∑_t t^{-1/2} e^{-b Q_t(a)}`. -/
theorem sum_sqrt_exp_qdev_le {b : ℝ} (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ a : ℝ, 0 ≤ a →
      ∑' t : ℕ, ENNReal.ofReal ((Real.sqrt t)⁻¹ * Real.exp (-b * qdev t a)) ≤
        ENNReal.ofReal K := by
  refine ⟨2 * (16 + 4 / b), by positivity, fun a ha => ?_⟩
  set G : ℕ → ℝ := fun i =>
    (Real.sqrt ((i : ℝ) - 1) - Real.sqrt a) / (1 + |Real.sqrt ((i : ℝ) - 1) - Real.sqrt a|)
    with hG
  have hterm : ∀ i : ℕ, (Real.sqrt i)⁻¹ * Real.exp (-b * qdev i a) ≤
      (16 + 4 / b) * (G (i + 1) - G i) := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [hG, Real.sqrt_eq_zero_of_nonpos (show (-1 : ℝ) ≤ 0 by norm_num)]
    · have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
      have := term_le_increment hb hi1 ha
      simpa [hG] using this
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∑ i ∈ Finset.range n, (Real.sqrt i)⁻¹ * Real.exp (-b * qdev i a)
      ≤ ∑ i ∈ Finset.range n, (16 + 4 / b) * (G (i + 1) - G i) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (16 + 4 / b) * (G n - G 0) := by rw [← Finset.mul_sum, Finset.sum_range_sub]
    _ ≤ (16 + 4 / b) * 2 := by
        gcongr
        have h1 := abs_div_one_add_abs_le (Real.sqrt ((n : ℝ) - 1) - Real.sqrt a)
        have h2 := abs_div_one_add_abs_le (Real.sqrt ((0 : ℕ) - 1 : ℝ) - Real.sqrt a)
        rw [abs_le] at h1 h2
        simp only [hG]
        linarith [h1.2, h2.1]
    _ = 2 * (16 + 4 / b) := by ring

/-- **The main summation kernel.**  `K` depends on `γ` only. -/
theorem sum_kernel_le {γ : ℝ} (hγ : 0 < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ E : ℝ, 1 ≤ E → ∀ a : ℝ, 0 ≤ a →
      ∑' t : ℕ, ENNReal.ofReal (((t : ℝ) * Real.sqrt t)⁻¹ *
          Real.exp (-γ * (E / t + t / E + qdev t a))) ≤
        ENNReal.ofReal (K / E * Real.exp (-(γ / 4) * a / E)) := by
  obtain ⟨K₁, hK₁, hsum⟩ := sum_sqrt_exp_qdev_le (b := γ / 2) (by positivity)
  refine ⟨K₁ / γ, by positivity, fun E hE a ha => ?_⟩
  have hE0 : 0 < E := by linarith
  set c : ℝ := 1 / (γ * E) * Real.exp (-(γ / 4) * a / E) with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ t : ℕ, ((t : ℝ) * Real.sqrt t)⁻¹ * Real.exp (-γ * (E / t + t / E + qdev t a)) ≤
      c * ((Real.sqrt t)⁻¹ * Real.exp (-(γ / 2) * qdev t a)) := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
    have hq := qdev_add_ge hE ht0 ha
    have hq0 := qdev_nonneg (a := a) ht0.le
    have hexp : Real.exp (-γ * (E / t + t / E + qdev t a)) ≤
        Real.exp (-(γ * E / t)) *
          (Real.exp (-(γ / 4) * a / E) * Real.exp (-(γ / 2) * qdev t a)) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have h4 : a / (4 * E) ≤ (t / E + qdev t a) / 2 := by
        have : a / (4 * E) = a / (2 * E) / 2 := by ring
        rw [this]; linarith
      have ht' : 0 ≤ t / E := div_nonneg ht0.le hE0.le
      have key : 0 ≤ γ * (t / E + qdev t a / 2 - a / (4 * E)) := mul_nonneg hγ.le (by linarith)
      have e1 : -(γ / 4) * a / E = -(γ * (a / (4 * E))) := by ring
      have e2 : γ * E / t = γ * (E / t) := by ring
      rw [e1, e2]
      nlinarith
    have hx : (t : ℝ)⁻¹ * Real.exp (-(γ * E / t)) ≤ 1 / (γ * E) := by
      set x := γ * E / t with hx
      have hx0 : 0 < x := by positivity
      have h1 : (t : ℝ)⁻¹ = x / (γ * E) := by rw [hx]; field_simp
      rw [h1, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      have h2 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
      have h3 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-x)]
    calc ((t : ℝ) * Real.sqrt t)⁻¹ * Real.exp (-γ * (E / t + t / E + qdev t a))
        ≤ ((t : ℝ) * Real.sqrt t)⁻¹ * (Real.exp (-(γ * E / t)) *
            (Real.exp (-(γ / 4) * a / E) * Real.exp (-(γ / 2) * qdev t a))) := by gcongr
      _ = ((t : ℝ)⁻¹ * Real.exp (-(γ * E / t))) * Real.exp (-(γ / 4) * a / E) *
            ((Real.sqrt t)⁻¹ * Real.exp (-(γ / 2) * qdev t a)) := by rw [mul_inv]; ring
      _ ≤ 1 / (γ * E) * Real.exp (-(γ / 4) * a / E) *
            ((Real.sqrt t)⁻¹ * Real.exp (-(γ / 2) * qdev t a)) := by gcongr
  calc ∑' t : ℕ, ENNReal.ofReal (((t : ℝ) * Real.sqrt t)⁻¹ *
          Real.exp (-γ * (E / t + t / E + qdev t a)))
      ≤ ∑' t : ℕ, ENNReal.ofReal c *
          ENNReal.ofReal ((Real.sqrt t)⁻¹ * Real.exp (-(γ / 2) * qdev t a)) := by
        refine ENNReal.tsum_le_tsum fun t => ?_
        rw [← ENNReal.ofReal_mul hc0]
        exact ENNReal.ofReal_le_ofReal (hpt t)
    _ = ENNReal.ofReal c *
          ∑' t : ℕ, ENNReal.ofReal ((Real.sqrt t)⁻¹ * Real.exp (-(γ / 2) * qdev t a)) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal K₁ := by gcongr; exact hsum a ha
    _ = ENNReal.ofReal (K₁ / γ / E * Real.exp (-(γ / 4) * a / E)) := by
        rw [← ENNReal.ofReal_mul hc0]; congr 1; rw [hc]; field_simp

/-- Pointwise bound for the auxiliary sum: with `c = c₂/D²` and `κ = √γ √c`, the `t`-th term is
at most `D e^{5c/2} e^{-κ eps} e^{-(γ/4)a/eps²} · (e^{-c/4})^t`. -/
private theorem aux_term_le {γ c₂ D eps a : ℝ} (hγ : 0 < γ) (hc₂ : 0 < c₂) (hD : 0 < D)
    (heps1 : 1 ≤ eps) (ha : 0 ≤ a) (t : ℕ) :
    (t : ℝ)⁻¹ * (D * Real.exp (-c₂ * (((t / 2 : ℕ) : ℝ) - 2) / D ^ 2)) *
        Real.exp (-γ * (eps ^ 2 / t + t / eps ^ 2 + qdev t a)) ≤
      D * Real.exp (5 * (c₂ / D ^ 2) / 2) *
        Real.exp (-(Real.sqrt γ * Real.sqrt (c₂ / D ^ 2) * eps)) *
        Real.exp (-(γ / 4) * a / eps ^ 2) * Real.exp (-(c₂ / D ^ 2 / 4)) ^ t := by
  set c : ℝ := c₂ / D ^ 2 with hc
  have hc0 : 0 < c := by positivity
  set κ : ℝ := Real.sqrt γ * Real.sqrt c with hκ
  have heps0 : 0 < eps := by linarith
  have hE1 : 1 ≤ eps ^ 2 := by nlinarith
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp only [Nat.cast_zero, inv_zero, zero_mul, pow_zero, mul_one]; positivity
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hfl : (t : ℝ) - 1 ≤ 2 * ((t / 2 : ℕ) : ℝ) := by
    have h := Nat.div_add_mod t 2
    have h2 := Nat.mod_lt t (by norm_num : 2 > 0)
    have e : (t : ℝ) = 2 * ((t / 2 : ℕ) : ℝ) + ((t % 2 : ℕ) : ℝ) := by exact_mod_cast h.symm
    have e2 : ((t % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp h2
    linarith
  have h1 : Real.exp (-c₂ * (((t / 2 : ℕ) : ℝ) - 2) / D ^ 2) ≤
      Real.exp (5 * c / 2) * Real.exp (-(c * t / 2)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have e : -c₂ * (((t / 2 : ℕ) : ℝ) - 2) / D ^ 2 = -(c * (((t / 2 : ℕ) : ℝ) - 2)) := by
      rw [hc]; ring
    rw [e]
    have : c * (t - 1) ≤ c * (2 * ((t / 2 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hfl hc0.le
    linarith
  have hamgm : κ * eps ≤ γ * eps ^ 2 / t + c * t / 4 := by
    have hsg := Real.sq_sqrt hγ.le
    have hsc := Real.sq_sqrt hc0.le
    rw [div_add_div _ _ ht0.ne' (by norm_num : (4 : ℝ) ≠ 0), le_div_iff₀ (by positivity), hκ]
    have key : Real.sqrt γ * Real.sqrt c * eps * (t * 4) ≤
        Real.sqrt γ ^ 2 * eps ^ 2 * 4 + t * (Real.sqrt c ^ 2 * t) := by
      nlinarith [sq_nonneg (2 * Real.sqrt γ * eps - Real.sqrt c * t)]
    rw [hsg, hsc] at key
    linarith
  have hq := qdev_add_ge hE1 ht0 ha
  have hq0 := qdev_nonneg (a := a) ht0.le
  have h2 : Real.exp (-γ * (eps ^ 2 / t + t / eps ^ 2 + qdev t a)) ≤
      Real.exp (-(γ * eps ^ 2 / t)) * Real.exp (-(γ / 4) * a / eps ^ 2) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h4 : a / (4 * eps ^ 2) ≤ t / eps ^ 2 + qdev t a := by
      have : a / (4 * eps ^ 2) ≤ a / (2 * eps ^ 2) :=
        div_le_div_of_nonneg_left ha (by positivity) (by nlinarith)
      linarith
    have key : γ * (a / (4 * eps ^ 2)) ≤ γ * (t / eps ^ 2 + qdev t a) :=
      mul_le_mul_of_nonneg_left h4 hγ.le
    have e1 : -(γ / 4) * a / eps ^ 2 = -(γ * (a / (4 * eps ^ 2))) := by ring
    have e2 : -γ * (eps ^ 2 / t + t / eps ^ 2 + qdev t a) =
        -(γ * eps ^ 2 / t) - γ * (t / eps ^ 2 + qdev t a) := by ring
    rw [e1, e2]
    linarith
  have h3 : Real.exp (-(γ * eps ^ 2 / t)) * Real.exp (-(c * t / 2)) ≤
      Real.exp (-(κ * eps)) * Real.exp (-(c / 4)) ^ t := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have e : (t : ℝ) * -(c / 4) = -(c * t / 4) := by ring
    rw [e]
    have : 0 ≤ c * t / 4 := by positivity
    linarith
  have hinv : (t : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1
  calc (t : ℝ)⁻¹ * (D * Real.exp (-c₂ * (((t / 2 : ℕ) : ℝ) - 2) / D ^ 2)) *
        Real.exp (-γ * (eps ^ 2 / t + t / eps ^ 2 + qdev t a))
      ≤ 1 * (D * (Real.exp (5 * c / 2) * Real.exp (-(c * t / 2)))) *
        (Real.exp (-(γ * eps ^ 2 / t)) * Real.exp (-(γ / 4) * a / eps ^ 2)) := by
        gcongr
    _ = D * Real.exp (5 * c / 2) * Real.exp (-(γ / 4) * a / eps ^ 2) *
        (Real.exp (-(γ * eps ^ 2 / t)) * Real.exp (-(c * t / 2))) := by ring
    _ ≤ D * Real.exp (5 * c / 2) * Real.exp (-(γ / 4) * a / eps ^ 2) *
        (Real.exp (-(κ * eps)) * Real.exp (-(c / 4)) ^ t) := by gcongr
    _ = D * Real.exp (5 * c / 2) * Real.exp (-(κ * eps)) *
        Real.exp (-(γ / 4) * a / eps ^ 2) * Real.exp (-(c / 4)) ^ t := by ring

/-- `A e^{-κ eps} ≤ eps⁻²` once `eps ≥ 6A/κ³` (and `eps > 0`). -/
private theorem mul_exp_neg_le_inv_sq {A κ eps : ℝ} (hκ : 0 < κ) (heps0 : 0 < eps)
    (hepsA : 6 * A / κ ^ 3 ≤ eps) :
    A * Real.exp (-(κ * eps)) ≤ 1 / eps ^ 2 := by
  have h3 : (κ * eps) ^ 3 / 6 ≤ Real.exp (κ * eps) := by
    have := Real.pow_div_factorial_le_exp (κ * eps) (by positivity) 3
    simpa [Nat.factorial] using this
  have h6A : 6 * A ≤ κ ^ 3 * eps := by
    rw [div_le_iff₀ (by positivity)] at hepsA; linarith
  have h4 : A * eps ^ 2 ≤ (κ * eps) ^ 3 / 6 := by
    have h4' : 6 * A * eps ^ 2 ≤ κ ^ 3 * eps * eps ^ 2 :=
      mul_le_mul_of_nonneg_right h6A (sq_nonneg _)
    calc A * eps ^ 2 = 6 * A * eps ^ 2 / 6 := by ring
      _ ≤ κ ^ 3 * eps * eps ^ 2 / 6 := by gcongr
      _ = (κ * eps) ^ 3 / 6 := by ring
  have h5 : Real.exp (κ * eps) * Real.exp (-(κ * eps)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [le_div_iff₀ (by positivity)]
  calc A * Real.exp (-(κ * eps)) * eps ^ 2 = (A * eps ^ 2) * Real.exp (-(κ * eps)) := by ring
    _ ≤ Real.exp (κ * eps) * Real.exp (-(κ * eps)) := by
        gcongr; exact h4.trans h3
    _ = 1 := h5

/-- **The part carried by the input density bound**: negligible for `eps ≥ e₄(γ, c₂, D)`. -/
theorem sum_aux_le {γ c₂ D : ℝ} (hγ : 0 < γ) (hc₂ : 0 < c₂) (hD : 0 < D) :
    ∃ e₄ : ℝ, ∀ eps, e₄ ≤ eps → ∀ a : ℝ, 0 ≤ a →
      ∑' t : ℕ, ENNReal.ofReal ((t : ℝ)⁻¹ *
          (D * Real.exp (-c₂ * (((t / 2 : ℕ) : ℝ) - 2) / D ^ 2)) *
          Real.exp (-γ * (eps ^ 2 / t + t / eps ^ 2 + qdev t a))) ≤
        ENNReal.ofReal (1 / eps ^ 2 * Real.exp (-(γ / 4) * a / eps ^ 2)) := by
  set c : ℝ := c₂ / D ^ 2 with hc
  have hc0 : 0 < c := by positivity
  set κ : ℝ := Real.sqrt γ * Real.sqrt c with hκ
  have hκ0 : 0 < κ := by positivity
  set r : ℝ := Real.exp (-(c / 4)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  have hr1' : 0 < 1 - r := by linarith
  set A : ℝ := D * Real.exp (5 * c / 2) * (1 - r)⁻¹ with hA
  refine ⟨max 1 (6 * A / κ ^ 3), fun eps heps a ha => ?_⟩
  have heps1 : 1 ≤ eps := le_trans (le_max_left _ _) heps
  have hepsA : 6 * A / κ ^ 3 ≤ eps := le_trans (le_max_right _ _) heps
  have heps0 : 0 < eps := by linarith
  set B : ℝ := D * Real.exp (5 * c / 2) * Real.exp (-(κ * eps)) *
    Real.exp (-(γ / 4) * a / eps ^ 2) with hB
  have hsumm : Summable fun t : ℕ => B * r ^ t :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left B
  have hfin := mul_exp_neg_le_inv_sq hκ0 heps0 hepsA
  calc ∑' t : ℕ, ENNReal.ofReal ((t : ℝ)⁻¹ *
          (D * Real.exp (-c₂ * (((t / 2 : ℕ) : ℝ) - 2) / D ^ 2)) *
          Real.exp (-γ * (eps ^ 2 / t + t / eps ^ 2 + qdev t a)))
      ≤ ∑' t : ℕ, ENNReal.ofReal (B * r ^ t) :=
        ENNReal.tsum_le_tsum fun t =>
          ENNReal.ofReal_le_ofReal (aux_term_le hγ hc₂ hD heps1 ha t)
    _ = ENNReal.ofReal (∑' t : ℕ, B * r ^ t) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun t => by positivity) hsumm).symm
    _ ≤ ENNReal.ofReal (1 / eps ^ 2 * Real.exp (-(γ / 4) * a / eps ^ 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, hB]
        have e : D * Real.exp (5 * c / 2) * Real.exp (-(κ * eps)) *
            Real.exp (-(γ / 4) * a / eps ^ 2) * (1 - r)⁻¹ =
            (A * Real.exp (-(κ * eps))) * Real.exp (-(γ / 4) * a / eps ^ 2) := by
          rw [hA]; ring
        rw [e]
        gcongr

end

end PGM
