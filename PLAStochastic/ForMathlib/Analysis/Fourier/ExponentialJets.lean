import PLAStochastic.ForMathlib.Analysis.Fourier.WeightedRemainder
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Exponential envelopes of finite jets from an envelope and bounded derivatives -/

noncomputable section

open Set
open Filter Topology
open scoped ContDiff

namespace PGM

theorem abs_deriv_le_secant_add_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {B t δ : ℝ} (hδ : 0 < δ)
    (hb : ∀ x ∈ Icc t (t + δ), |iteratedDeriv 2 f x| ≤ B) :
    |deriv f t| ≤ (|f (t + δ)| + |f t|) / δ + B * δ := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd' : Differentiable ℝ (deriv f) :=
    (hf.deriv' (n := 1)).differentiable (by norm_num)
  obtain ⟨y, hy, he⟩ := exists_deriv_eq_slope f (by linarith : t < t + δ)
    hf.continuous.continuousOn hd.differentiableOn
  have hlip : |deriv f y - deriv f t| ≤ B * (y - t) := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := deriv f) (f' := deriv (deriv f))
      (C := B) (fun x _ => (hd' x).hasDerivAt.hasDerivWithinAt)
      (fun x hx => ?_) y ⟨hy.1.le, hy.2.le⟩
    · simpa only [Real.norm_eq_abs] using h
    · simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Real.norm_eq_abs] using hb x ⟨hx.1, hx.2.le⟩
  have hsec : |deriv f y| ≤ (|f (t + δ)| + |f t|) / δ := by
    rw [he, add_sub_cancel_left, abs_div, abs_of_pos hδ]
    exact div_le_div_of_nonneg_right (abs_sub _ _) hδ.le
  have hB : 0 ≤ B := (abs_nonneg (iteratedDeriv 2 f t)).trans (hb t ⟨le_rfl, by linarith⟩)
  calc
    _ = |deriv f y - (deriv f y - deriv f t)| := by congr 1; ring
    _ ≤ |deriv f y| + |deriv f y - deriv f t| := abs_sub _ _
    _ ≤ (|f (t + δ)| + |f t|) / δ + B * (y - t) := add_le_add hsec hlip
    _ ≤ _ := by gcongr; linarith [hy.2]

/-- The symmetric envelope costs half its rate when one derivative is extracted. -/
theorem abs_deriv_le_exponential_envelope {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {A B θ : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B) (hθ : 0 < θ)
    (ha : ∀ x, |f x| ≤ A * Real.exp (-θ * |x|))
    (hb : ∀ x, |iteratedDeriv 2 f x| ≤ B) (x : ℝ) :
    |deriv f x| ≤ (A * Real.exp θ + A + B) * Real.exp (-(θ / 2) * |x|) := by
  let δ := Real.exp (-(θ / 2) * |x|)
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg x])
  have hs := abs_deriv_le_secant_add_bound (t := x) hf hδ (fun y _ => hb y)
  have hxδ : |x| - 1 ≤ |x + δ| := by
    have := abs_sub_abs_le_abs_sub x (x + δ)
    rw [show x - (x + δ) = -δ by ring, abs_neg, abs_of_pos hδ] at this
    linarith
  have hy : |f (x + δ)| ≤ A * Real.exp θ * Real.exp (-θ * |x|) := by
    calc
      _ ≤ A * Real.exp (-θ * |x + δ|) := ha _
      _ ≤ A * Real.exp (θ + -θ * |x|) := by gcongr; nlinarith
      _ = _ := by rw [Real.exp_add]; ring
  have hfirst : (|f (x + δ)| + |f x|) / δ ≤
      (A * Real.exp θ + A) * Real.exp (-(θ / 2) * |x|) := by
    calc
      _ ≤ ((A * Real.exp θ + A) * Real.exp (-θ * |x|)) / δ := by
        apply div_le_div_of_nonneg_right _ hδ.le
        nlinarith [ha x]
      _ = _ := by
        dsimp [δ]
        rw [mul_div_assoc, ← Real.exp_sub]
        congr 2
        ring
  calc
    _ ≤ _ := hs
    _ ≤ (A * Real.exp θ + A) * Real.exp (-(θ / 2) * |x|) + B * δ := add_le_add hfirst le_rfl
    _ = _ := by dsimp [δ]; ring

/-- Every finite jet of an eventually smooth family has a common positive exponential envelope. -/
theorem eventually_finite_exponential_jets {F : ℝ → ℝ → ℝ} {m : ℕ} {A B θ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ)
    (hf : ∀ᶠ eps in atTop, ContDiff ℝ (m + 1) (F eps))
    (hb : ∀ᶠ eps in atTop, ∀ j ≤ m + 1, ∀ x, |iteratedDeriv j (F eps) x| ≤ B)
    (ha : ∀ᶠ eps in atTop, ∀ x, |F eps x| ≤ A * Real.exp (-θ * |x|)) :
    ∃ D ρ : ℝ, 0 ≤ D ∧ 0 < ρ ∧
      ∀ᶠ eps in atTop, ∀ j ≤ m, ∀ x, |iteratedDeriv j (F eps) x| ≤ D * Real.exp (-ρ * |x|) := by
  have haux : ∀ n : ℕ,
      (∀ᶠ eps in atTop, ContDiff ℝ (n + 1) (F eps)) →
      (∀ᶠ eps in atTop, ∀ j ≤ n + 1, ∀ x, |iteratedDeriv j (F eps) x| ≤ B) →
      ∃ D ρ : ℝ, 0 ≤ D ∧ 0 < ρ ∧
        ∀ᶠ eps in atTop, ∀ j ≤ n, ∀ x, |iteratedDeriv j (F eps) x| ≤ D * Real.exp (-ρ * |x|) := by
    intro n
    induction n with
    | zero =>
      intro _ _
      refine ⟨A, θ, hA, hθ, ?_⟩
      filter_upwards [ha] with eps he j hj x
      have : j = 0 := by omega
      simpa only [this, iteratedDeriv_zero] using he x
    | succ n ih =>
      intro hf' hb'
      obtain ⟨D, ρ, hD, hρ, hd⟩ := ih
        (hf'.mono fun _ he => he.of_le (by exact_mod_cast (show n + 1 ≤ n + 1 + 1 by omega)))
        (hb'.mono fun _ he j hj => he j (by omega))
      let D' := D * Real.exp ρ + D + B
      refine ⟨D + D', ρ / 2, by dsimp [D']; positivity, by positivity, ?_⟩
      filter_upwards [hf', hb', hd] with eps heps hbe hde j hj x
      rcases (show j ≤ n + 1 by omega).lt_or_eq with hj' | rfl
      · have hex : Real.exp (-ρ * |x|) ≤ Real.exp (-(ρ / 2) * |x|) :=
          Real.exp_le_exp.mpr (by nlinarith [abs_nonneg x])
        exact (hde j (by omega) x).trans
          (mul_le_mul (by dsimp [D']; nlinarith [Real.exp_pos ρ]) hex (Real.exp_pos _).le (by dsimp [D']; positivity))
      · have hcd : ContDiff ℝ 2 (iteratedDeriv n (F eps)) := by
          rw [iteratedDeriv_eq_iterate]
          apply ContDiff.iterate_deriv' 2 n
          exact heps.of_le (by exact_mod_cast (show 2 + n ≤ n + 1 + 1 by omega))
        have hsecond : ∀ y, |iteratedDeriv 2 (iteratedDeriv n (F eps)) y| ≤ B := by
          intro y
          have hcomp : iteratedDeriv 2 (iteratedDeriv n (F eps)) = iteratedDeriv (n + 2) (F eps) := by
            simp only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, Nat.add_comm 2 n]
          rw [hcomp]
          exact hbe (n + 2) (by omega) y
        rw [iteratedDeriv_succ]
        have hdnew := abs_deriv_le_exponential_envelope hcd hD hB hρ (hde n le_rfl) hsecond x
        exact hdnew.trans (mul_le_mul_of_nonneg_right (by dsimp [D']; linarith : D' ≤ D + D') (Real.exp_pos _).le)
  exact haux m hf hb

end PGM
