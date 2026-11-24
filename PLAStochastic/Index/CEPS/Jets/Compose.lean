import PLAStochastic.Index.CEPS.Jets.Calculus
import PLAStochastic.ForMathlib.Analysis.Asymptotics.InverseExpansion

/-!
# X8: expansion of an integral of a holomorphic function along an expanding family

`hasInverseExpansion_re_integral_comp`: let `G y` be holomorphic on the disc `B(z₀ y, 2ρ)` with
`‖G y z - G y (z₀ y)‖ ≤ A y` there, and let a family `Z ε y` admit the expansion
`Z ε y = z₀ y + ∑_{p=1}^{P} ε^{-p} d p y + O(ε^{-(P+1)} w y)` with `‖d p y‖ ≤ K_d w y`,
`0 ≤ w ≤ 1` and `A w` integrable. Then `ε ↦ Re (a ∫ G y (Z ε y) dy + b)` has an expansion of
order `P` in `ε⁻¹`, whose `n`-th coefficient is the real part of the `n`-th Taylor coefficient at
`h = 0` of the holomorphic function `h ↦ a ∫ G y (z₀ y + ∑_{p=1}^{n} h^p d p y) dy + b`.

The proof uses the Lipschitz bound `‖G y z - G y z'‖ ≤ (2 A y/ρ) ‖z - z'‖` on `B(z₀ y, ρ)`, the
holomorphy of the parametric integrals `Φ_n h = ∫ G y (z₀ y + ∑_{p ≤ n} h^p d p y)` on a small
disc, the Taylor remainder bound of `Φ_P` on that disc, and the identification of the
derivatives of `Φ_P` and `Φ_n` at `0` up to order `n` (they differ by `O(‖h‖^{n+1})`).
-/

noncomputable section

open MeasureTheory Metric

namespace PGM

/-- Lipschitz bound on `B(c, ρ)` from a bound on `B(c, 2ρ)`. -/
private theorem norm_sub_le_of_ball_two {g : ℂ → ℂ} {c : ℂ} {ρ M : ℝ} (hρ : 0 < ρ)
    (hg : DifferentiableOn ℂ g (ball c (2 * ρ))) (hM : ∀ z ∈ ball c (2 * ρ), ‖g z - g c‖ ≤ M)
    {z z' : ℂ} (hz : ‖z - c‖ < ρ) (hz' : ‖z' - c‖ < ρ) :
    ‖g z - g z'‖ ≤ 2 * M / ρ * ‖z - z'‖ := by
  have h := norm_sub_le_of_ball_half (f := fun x => g x - g c) (c := c) (r := 2 * ρ) (M := M)
    (by positivity) (hg.sub_const _) hM (z := z) (w := z')
    (by rw [mem_ball, dist_eq_norm]; linarith) (by rw [mem_ball, dist_eq_norm]; linarith)
  calc ‖g z - g z'‖ = ‖(g z - g c) - (g z' - g c)‖ := by congr 1; ring
    _ ≤ 4 * M / (2 * ρ) * ‖z - z'‖ := h
    _ = 2 * M / ρ * ‖z - z'‖ := by field_simp; ring

/-- A sum `∑_{p ∈ s} h^p d p y` over at most `P` indices `p ≥ m` with `‖d p y‖ ≤ K_d w y`. -/
private theorem norm_sum_pow_mul_le {d : ℕ → ℝ → ℂ} {w : ℝ → ℝ} {K_d : ℝ} {P : ℕ}
    (hw0 : ∀ y, 0 ≤ w y) (hdb : ∀ p ∈ Finset.Icc 1 P, ∀ y, ‖d p y‖ ≤ K_d * w y)
    {s : Finset ℕ} {m : ℕ} {h : ℂ} (y : ℝ) (hs : s ⊆ Finset.Icc 1 P) (hcard : s.card ≤ P)
    (hm : ∀ p ∈ s, m ≤ p) (hh : ‖h‖ ≤ 1) :
    ‖∑ p ∈ s, h ^ p * d p y‖ ≤ P * (‖h‖ ^ m * (|K_d| * w y)) := by
  calc ‖∑ p ∈ s, h ^ p * d p y‖ ≤ ∑ p ∈ s, ‖h ^ p * d p y‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ s, ‖h‖ ^ m * (|K_d| * w y) := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [norm_mul, norm_pow]
        exact mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) hh (hm p hp))
          ((hdb p (hs hp) y).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (hw0 y)))
          (norm_nonneg _) (by positivity)
    _ = s.card * (‖h‖ ^ m * (|K_d| * w y)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ P * (‖h‖ ^ m * (|K_d| * w y)) := by
        have : 0 ≤ ‖h‖ ^ m * (|K_d| * w y) := mul_nonneg (by positivity)
          (mul_nonneg (abs_nonneg _) (hw0 y))
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) this

/-- Integrability from continuity and an integrable distance to an integrable function. -/
private theorem integrable_of_norm_sub_le {F₁ F₂ : ℝ → ℂ} {B : ℝ → ℝ} (h1 : Continuous F₁)
    (h2 : Integrable F₂) (hB : Integrable B) (hb : ∀ y, ‖F₁ y - F₂ y‖ ≤ B y) :
    Integrable F₁ := by
  refine (h2.norm.add hB).mono' h1.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  calc ‖F₁ y‖ = ‖F₂ y + (F₁ y - F₂ y)‖ := by rw [add_sub_cancel]
    _ ≤ ‖F₂ y‖ + ‖F₁ y - F₂ y‖ := norm_add_le _ _
    _ ≤ ‖F₂ y‖ + B y := by gcongr; exact hb y

/-- Distance of two integrals from a pointwise bound `c B`. -/
private theorem norm_integral_sub_le_mul {F₁ F₂ : ℝ → ℂ} {B : ℝ → ℝ} (c : ℝ)
    (h1 : Integrable F₁) (h2 : Integrable F₂) (hB : Integrable B)
    (hb : ∀ y, ‖F₁ y - F₂ y‖ ≤ c * B y) :
    ‖(∫ y, F₁ y) - ∫ y, F₂ y‖ ≤ c * ∫ y, B y := by
  rw [← integral_sub h1 h2, ← integral_const_mul]
  exact norm_integral_le_of_norm_le (hB.const_mul c) (ae_of_all _ hb)

/-- Expansion of `Re (a ∫ G y (Z ε y) dy + b)` in powers of `ε⁻¹` when `Z ε` has an expansion of
order `P` in `ε⁻¹` around `z₀`, with jets `d p` dominated by a weight `w ≤ 1` and `G y`
holomorphic on `B(z₀ y, 2ρ)` with oscillation `A y` there (`A w` integrable). The `n`-th
coefficient is the real part of the `n`-th Taylor coefficient at `0` of
`h ↦ a ∫ G y (z₀ y + ∑_{p=1}^{n} h^p d p y) dy + b`. -/
theorem hasInverseExpansion_re_integral_comp
    {G : ℝ → ℂ → ℂ} {z₀ : ℝ → ℂ} {d : ℕ → ℝ → ℂ} {Z : ℝ → ℝ → ℂ} {A w : ℝ → ℝ}
    {ρ K_d K_R ε₀ : ℝ} {P : ℕ} (a b : ℂ) (hρ : 0 < ρ)
    (hG : ∀ y, DifferentiableOn ℂ (G y) (Metric.ball (z₀ y) (2 * ρ)))
    (hGc : ContinuousOn (fun p : ℝ × ℂ => G p.1 p.2) {p | ‖p.2 - z₀ p.1‖ < 2 * ρ})
    (hz₀ : Continuous z₀)
    (hA : ∀ y, ∀ z ∈ Metric.ball (z₀ y) (2 * ρ), ‖G y z - G y (z₀ y)‖ ≤ A y)
    (hAw : MeasureTheory.Integrable fun y => A y * w y)
    (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∀ y, w y ≤ 1)
    (hG0 : MeasureTheory.Integrable fun y => G y (z₀ y))
    (hd : ∀ p ∈ Finset.Icc 1 P, Continuous (d p))
    (hdb : ∀ p ∈ Finset.Icc 1 P, ∀ y, ‖d p y‖ ≤ K_d * w y)
    (hZ : ∀ ε, ε₀ ≤ ε → Continuous (Z ε))
    (hZb : ∀ ε, ε₀ ≤ ε → ∀ y, ‖Z ε y - z₀ y -
      ∑ p ∈ Finset.Icc 1 P, ((ε⁻¹ : ℝ) : ℂ) ^ p * d p y‖ ≤ K_R * (ε⁻¹) ^ (P + 1) * w y) :
    HasInverseExpansionAtOrder (fun ε => (a * (∫ y, G y (Z ε y)) + b).re)
      (fun n => (iteratedDeriv n (fun h : ℂ =>
        a * (∫ y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 n, h ^ p * d p y)) + b) 0 /
          (n.factorial : ℂ)).re) P := by
  classical
  -- the oscillation is nonnegative, and `G y` is `(2 A y / ρ)`-Lipschitz on `B(z₀ y, ρ)`
  have hA0 : ∀ y, 0 ≤ A y := fun y => by
    simpa using hA y (z₀ y) (mem_ball_self (by positivity))
  have hlip : ∀ y, ∀ z z' : ℂ, ‖z - z₀ y‖ < ρ → ‖z' - z₀ y‖ < ρ →
      ‖G y z - G y z'‖ ≤ 2 * A y / ρ * ‖z - z'‖ := fun y z z' hz hz' =>
    norm_sub_le_of_ball_two hρ (hG y) (hA y) hz hz'
  -- the radius `h₁` of the disc on which the jets stay in `B(z₀ y, ρ / 2)`
  set L : ℝ := P * |K_d| + 1 with hL
  have hL0 : 0 < L := by positivity
  set h₁ : ℝ := min 1 (ρ / (2 * L)) with hh₁
  have hh₁0 : 0 < h₁ := lt_min one_pos (by positivity)
  have hh₁1 : h₁ ≤ 1 := min_le_left _ _
  have hh₁L : h₁ * L ≤ ρ / 2 := by
    calc h₁ * L ≤ ρ / (2 * L) * L := mul_le_mul_of_nonneg_right (min_le_right _ _) hL0.le
      _ = ρ / 2 := by field_simp
  have hS1 : ∀ n ≤ P, ∀ h : ℂ, ‖h‖ ≤ 1 → ∀ y,
      ‖∑ p ∈ Finset.Icc 1 n, h ^ p * d p y‖ ≤ ‖h‖ * L * w y := by
    intro n hn h hh y
    have hsub : Finset.Icc 1 n ⊆ Finset.Icc 1 P := Finset.Icc_subset_Icc_right hn
    have := norm_sum_pow_mul_le (m := 1) hw0 hdb y hsub (by simp [Nat.card_Icc]; omega)
      (fun p hp => (Finset.mem_Icc.mp hp).1) hh
    calc _ ≤ _ := this
      _ = ‖h‖ * (P * |K_d|) * w y := by ring
      _ ≤ ‖h‖ * L * w y := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)) (hw0 y)
  have hball : ∀ n ≤ P, ∀ h ∈ ball (0 : ℂ) h₁, ∀ y,
      ‖∑ p ∈ Finset.Icc 1 n, h ^ p * d p y‖ < ρ / 2 := by
    intro n hn h hh y
    have hh' : ‖h‖ < h₁ := by rwa [mem_ball, dist_zero_right] at hh
    calc ‖∑ p ∈ Finset.Icc 1 n, h ^ p * d p y‖ ≤ ‖h‖ * L * w y := hS1 n hn h (by linarith) y
      _ ≤ ‖h‖ * L * 1 := mul_le_mul_of_nonneg_left (hw1 y) (by positivity)
      _ < h₁ * L := by rw [mul_one]; exact mul_lt_mul_of_pos_right hh' hL0
      _ ≤ ρ / 2 := hh₁L
  -- continuity and holomorphy of the integrands
  have hcontG : ∀ F : ℝ → ℂ, Continuous F → (∀ y, ‖F y - z₀ y‖ < 2 * ρ) →
      Continuous fun y => G y (F y) := fun F hF hFb =>
    hGc.comp_continuous (continuous_id.prodMk hF) hFb
  have hcontΨ : ∀ n ≤ P, ∀ h ∈ ball (0 : ℂ) h₁,
      Continuous fun y => G y (z₀ y + ∑ p ∈ Finset.Icc 1 n, h ^ p * d p y) := by
    intro n hn h hh
    refine hcontG _ (hz₀.add (continuous_finsetSum _ fun p hp => continuous_const.mul
      (hd p (Finset.Icc_subset_Icc_right hn hp)))) fun y => ?_
    rw [add_sub_cancel_left]
    linarith [hball n hn h hh y]
  have hdiffΨ : ∀ n ≤ P, ∀ y, DifferentiableOn ℂ
      (fun h : ℂ => G y (z₀ y + ∑ p ∈ Finset.Icc 1 n, h ^ p * d p y)) (ball 0 h₁) := by
    intro n hn y
    have hpoly : DifferentiableOn ℂ
        (fun h : ℂ => z₀ y + ∑ p ∈ Finset.Icc 1 n, h ^ p * d p y) (ball 0 h₁) := by
      apply Differentiable.differentiableOn
      fun_prop
    refine (hG y).comp hpoly fun h hh => ?_
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    linarith [hball n hn h hh y]
  -- the value at `h = 0` and the oscillation bound on the disc
  have hΨ0 : ∀ n y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 n, (0 : ℂ) ^ p * d p y) = G y (z₀ y) := by
    intro n y
    rw [Finset.sum_eq_zero fun p hp => by
      rw [zero_pow (by have := (Finset.mem_Icc.mp hp).1; omega), zero_mul], add_zero]
  have hB : Integrable fun y => 2 * L / ρ * (A y * w y) := hAw.const_mul _
  have hbound : ∀ n ≤ P, ∀ y, ∀ h ∈ ball (0 : ℂ) h₁,
      ‖G y (z₀ y + ∑ p ∈ Finset.Icc 1 n, h ^ p * d p y) -
        G y (z₀ y + ∑ p ∈ Finset.Icc 1 n, (0 : ℂ) ^ p * d p y)‖ ≤ 2 * L / ρ * (A y * w y) := by
    intro n hn y h hh
    have hh' : ‖h‖ < h₁ := by rwa [mem_ball, dist_zero_right] at hh
    rw [hΨ0]
    have hS := hball n hn h hh y
    calc _ ≤ 2 * A y / ρ * ‖z₀ y + ∑ p ∈ Finset.Icc 1 n, h ^ p * d p y - z₀ y‖ :=
          hlip y _ _ (by rw [add_sub_cancel_left]; linarith) (by simpa using hρ)
      _ = 2 * A y / ρ * ‖∑ p ∈ Finset.Icc 1 n, h ^ p * d p y‖ := by rw [add_sub_cancel_left]
      _ ≤ 2 * A y / ρ * (‖h‖ * L * w y) :=
          mul_le_mul_of_nonneg_left (hS1 n hn h (by linarith) y) (by have := hA0 y; positivity)
      _ ≤ 2 * A y / ρ * (1 * L * w y) := by
          have := hA0 y; have := hw0 y
          gcongr; linarith
      _ = 2 * L / ρ * (A y * w y) := by ring
  have hint0 : ∀ n, Integrable fun y => G y (z₀ y + ∑ p ∈ Finset.Icc 1 n, (0 : ℂ) ^ p * d p y) :=
    fun n => by simpa only [hΨ0] using hG0
  have hmeasΨ : ∀ n ≤ P, ∀ h ∈ ball (0 : ℂ) h₁, AEStronglyMeasurable
      (fun y => G y (z₀ y + ∑ p ∈ Finset.Icc 1 n, h ^ p * d p y)) volume :=
    fun n hn h hh => (hcontΨ n hn h hh).aestronglyMeasurable
  have hintΨ : ∀ n ≤ P, ∀ h ∈ ball (0 : ℂ) h₁,
      Integrable fun y => G y (z₀ y + ∑ p ∈ Finset.Icc 1 n, h ^ p * d p y) := fun n hn h hh =>
    integrable_of_ball_bound (Ψ := fun y h => G y (z₀ y + ∑ p ∈ Finset.Icc 1 n, h ^ p * d p y))
      (hmeasΨ n hn) (hint0 n) hB (fun y h hh => hbound n hn y h hh) hh
  have hΦd : ∀ n ≤ P, DifferentiableOn ℂ
      (fun h : ℂ => a * (∫ y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 n, h ^ p * d p y)) + b)
      (ball 0 h₁) := fun n hn =>
    ((differentiableOn_integral_of_ball
      (Ψ := fun y h => G y (z₀ y + ∑ p ∈ Finset.Icc 1 n, h ^ p * d p y)) hh₁0
      (fun y => hdiffΨ n hn y) (hmeasΨ n hn) (hint0 n) hB
      (fun y h hh => hbound n hn y h hh)).const_mul a).add_const b
  -- Taylor coefficients of the order-`P` function agree with those of order `k ≤ P`
  have hcoef : ∀ k ≤ P,
      iteratedDeriv k
        (fun h : ℂ => a * (∫ y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y)) + b) 0 =
      iteratedDeriv k
        (fun h : ℂ => a * (∫ y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 k, h ^ p * d p y)) + b) 0 := by
    intro k hk
    refine iteratedDeriv_eq_of_norm_sub_le_pow (K := ‖a‖ * (2 * (P * |K_d|) / ρ *
      ∫ y, A y * w y)) hh₁0 (hΦd P le_rfl) (hΦd k hk) (fun h hh => ?_) le_rfl
    have hh' : ‖h‖ < h₁ := by rwa [mem_ball, dist_zero_right] at hh
    have hsplit : ∀ y, ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y =
        ∑ p ∈ Finset.Icc 1 k, h ^ p * d p y + ∑ p ∈ Finset.Ioc k P, h ^ p * d p y := by
      intro y
      have e : ∀ n, Finset.Icc 1 n = Finset.Ioc 0 n := fun n => by
        ext p; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
      rw [e, e, Finset.sum_Ioc_consecutive _ (Nat.zero_le k) hk]
    have hpt : ∀ y, ‖G y (z₀ y + ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y) -
        G y (z₀ y + ∑ p ∈ Finset.Icc 1 k, h ^ p * d p y)‖ ≤
          2 * (P * |K_d|) / ρ * ‖h‖ ^ (k + 1) * (A y * w y) := by
      intro y
      have hP := hball P le_rfl h hh y
      have hk' := hball k hk h hh y
      have hIoc := norm_sum_pow_mul_le (s := Finset.Ioc k P) (m := k + 1) hw0 hdb y
        (fun p hp => by
          simp only [Finset.mem_Ioc] at hp; simp only [Finset.mem_Icc]; omega)
        (by simp [Nat.card_Ioc]) (fun p hp => by simp only [Finset.mem_Ioc] at hp; omega)
        (h := h) (by linarith)
      calc _ ≤ 2 * A y / ρ * ‖(z₀ y + ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y) -
            (z₀ y + ∑ p ∈ Finset.Icc 1 k, h ^ p * d p y)‖ :=
            hlip y _ _ (by rw [add_sub_cancel_left]; linarith)
              (by rw [add_sub_cancel_left]; linarith)
        _ = 2 * A y / ρ * ‖∑ p ∈ Finset.Ioc k P, h ^ p * d p y‖ := by
            rw [hsplit y]; congr 2; ring
        _ ≤ 2 * A y / ρ * (P * (‖h‖ ^ (k + 1) * (|K_d| * w y))) :=
            mul_le_mul_of_nonneg_left hIoc (by have := hA0 y; positivity)
        _ = 2 * (P * |K_d|) / ρ * ‖h‖ ^ (k + 1) * (A y * w y) := by ring
    have hI := norm_integral_sub_le_mul _ (hintΨ P le_rfl h hh) (hintΨ k hk h hh) hAw hpt
    calc _ = ‖a * ((∫ y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y)) -
          ∫ y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 k, h ^ p * d p y))‖ := by congr 1; ring
      _ = ‖a‖ * ‖(∫ y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y)) -
          ∫ y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 k, h ^ p * d p y)‖ := norm_mul _ _
      _ ≤ ‖a‖ * (2 * (P * |K_d|) / ρ * ‖h‖ ^ (k + 1) * ∫ y, A y * w y) := by gcongr
      _ = _ := by ring
  -- the Taylor remainder of the order-`P` function on `‖h‖ ≤ h₁ / 4`
  have htaylor : ∀ h : ℂ, ‖h‖ ≤ h₁ / 4 →
      ‖(a * (∫ y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y)) + b) -
        ∑ k ∈ Finset.range (P + 1), iteratedDeriv k
          (fun h : ℂ => a * (∫ y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y)) + b) 0 /
            (k.factorial : ℂ) * h ^ k‖ ≤
        2 * (‖a‖ * ∫ y, 2 * L / ρ * (A y * w y)) * (2 * ‖h‖ / h₁) ^ (P + 1) := by
    intro h hh
    refine norm_sub_taylor_le_of_ball hh₁0 (hΦd P le_rfl) (fun h' hh' => ?_) P hh
    have := norm_integral_sub_le_of_ball
      (Ψ := fun y h => G y (z₀ y + ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y))
      (hmeasΨ P le_rfl) (hint0 P) hB (fun y h hh => hbound P le_rfl y h hh) hh'
    calc _ = ‖a * ((∫ y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 P, h' ^ p * d p y)) -
          ∫ y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 P, (0 : ℂ) ^ p * d p y))‖ := by congr 1; ring
      _ ≤ ‖a‖ * ∫ y, 2 * L / ρ * (A y * w y) := by rw [norm_mul]; gcongr
  -- the threshold
  set t₁ : ℝ := min (h₁ / 4) (ρ / (2 * (|K_R| + 1))) with ht₁
  have ht₁0 : 0 < t₁ := lt_min (by positivity) (by positivity)
  have ht₁h : t₁ ≤ h₁ / 4 := min_le_left _ _
  have ht₁R : |K_R| * t₁ ≤ ρ / 2 := by
    calc |K_R| * t₁ ≤ (|K_R| + 1) * (ρ / (2 * (|K_R| + 1))) :=
          mul_le_mul (by linarith) (min_le_right _ _) ht₁0.le (by positivity)
      _ = ρ / 2 := by field_simp
  refine ⟨‖a‖ * (2 * |K_R| / ρ * ∫ y, A y * w y) +
    2 * (‖a‖ * ∫ y, 2 * L / ρ * (A y * w y)) * (2 / h₁) ^ (P + 1), max ε₀ t₁⁻¹,
    fun ε hε => ?_⟩
  have hε₀ : ε₀ ≤ ε := (le_max_left _ _).trans hε
  have hεt : t₁⁻¹ ≤ ε := (le_max_right _ _).trans hε
  have hε0 : 0 < ε := (inv_pos.mpr ht₁0).trans_le hεt
  have ht0 : 0 < ε⁻¹ := inv_pos.mpr hε0
  have ht : ε⁻¹ ≤ t₁ := inv_le_of_inv_le₀ ht₁0 hεt
  have ht1 : ε⁻¹ ≤ 1 := by linarith
  set h : ℂ := ((ε⁻¹ : ℝ) : ℂ) with hhdef
  have hnorm : ‖h‖ = ε⁻¹ := by rw [hhdef, Complex.norm_real, Real.norm_of_nonneg ht0.le]
  have hh : h ∈ ball (0 : ℂ) h₁ := by rw [mem_ball, dist_zero_right, hnorm]; linarith
  -- the family is close to the order-`P` jet and stays in `B(z₀ y, ρ)`
  have hpow : ε⁻¹ ^ (P + 1) ≤ ε⁻¹ := pow_le_of_le_one ht0.le ht1 (Nat.succ_ne_zero P)
  have hR' : ∀ y, ‖Z ε y - (z₀ y + ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y)‖ ≤
      |K_R| * ε⁻¹ ^ (P + 1) * w y := by
    intro y
    have hR := hZb ε hε₀ y
    rw [← hhdef] at hR
    rw [← sub_sub]
    exact hR.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) (hw0 y))
  have hZin : ∀ y, ‖Z ε y - z₀ y‖ < ρ := by
    intro y
    have hS := hball P le_rfl h hh y
    have hsmall : |K_R| * ε⁻¹ ^ (P + 1) * w y ≤ ρ / 2 := by
      calc |K_R| * ε⁻¹ ^ (P + 1) * w y ≤ |K_R| * ε⁻¹ * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)) (hw1 y) (hw0 y)
              (by positivity)
        _ ≤ |K_R| * t₁ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
        _ ≤ ρ / 2 := ht₁R
    calc ‖Z ε y - z₀ y‖ = ‖(Z ε y - (z₀ y + ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y)) +
          ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y‖ := by congr 1; ring
      _ ≤ ‖Z ε y - (z₀ y + ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y)‖ +
          ‖∑ p ∈ Finset.Icc 1 P, h ^ p * d p y‖ := norm_add_le _ _
      _ < ρ := by linarith [hR' y]
  have hZpt : ∀ y, ‖G y (Z ε y) - G y (z₀ y + ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y)‖ ≤
      2 * |K_R| / ρ * ε⁻¹ ^ (P + 1) * (A y * w y) := by
    intro y
    have hS := hball P le_rfl h hh y
    calc _ ≤ 2 * A y / ρ * ‖Z ε y - (z₀ y + ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y)‖ :=
          hlip y _ _ (hZin y) (by rw [add_sub_cancel_left]; linarith)
      _ ≤ 2 * A y / ρ * (|K_R| * ε⁻¹ ^ (P + 1) * w y) :=
          mul_le_mul_of_nonneg_left (hR' y) (by have := hA0 y; positivity)
      _ = 2 * |K_R| / ρ * ε⁻¹ ^ (P + 1) * (A y * w y) := by ring
  have hZint : Integrable fun y => G y (Z ε y) :=
    integrable_of_norm_sub_le (hcontG _ (hZ ε hε₀) fun y => by linarith [hZin y])
      (hintΨ P le_rfl h hh) (hAw.const_mul (2 * |K_R| / ρ * ε⁻¹ ^ (P + 1))) hZpt
  have hfar := norm_integral_sub_le_mul _ hZint (hintΨ P le_rfl h hh) hAw hZpt
  have hT := htaylor h (by rw [hnorm]; linarith)
  -- assemble
  simp only [inversePolynomial]
  have hpoly : ∑ j ∈ Finset.range (P + 1), (iteratedDeriv j (fun h : ℂ =>
        a * (∫ y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 j, h ^ p * d p y)) + b) 0 /
          (j.factorial : ℂ)).re * ε⁻¹ ^ j =
      (∑ k ∈ Finset.range (P + 1), iteratedDeriv k
          (fun h : ℂ => a * (∫ y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y)) + b) 0 /
            (k.factorial : ℂ) * h ^ k).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hcoef j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), hhdef, ← Complex.ofReal_pow,
      Complex.re_mul_ofReal]
  rw [hpoly, ← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_sub_le_norm_sub_add_norm_sub _
    (a * (∫ y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y)) + b) _).trans ?_
  have h1 : ‖(a * (∫ y, G y (Z ε y)) + b) -
      (a * (∫ y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y)) + b)‖ ≤
        ‖a‖ * (2 * |K_R| / ρ * ε⁻¹ ^ (P + 1) * ∫ y, A y * w y) := by
    calc _ = ‖a * ((∫ y, G y (Z ε y)) -
          ∫ y, G y (z₀ y + ∑ p ∈ Finset.Icc 1 P, h ^ p * d p y))‖ := by congr 1; ring
      _ ≤ _ := by rw [norm_mul]; gcongr
  rw [hnorm] at hT
  calc _ ≤ ‖a‖ * (2 * |K_R| / ρ * ε⁻¹ ^ (P + 1) * ∫ y, A y * w y) +
        2 * (‖a‖ * ∫ y, 2 * L / ρ * (A y * w y)) * (2 * ε⁻¹ / h₁) ^ (P + 1) :=
        add_le_add h1 hT
    _ = _ := by ring
