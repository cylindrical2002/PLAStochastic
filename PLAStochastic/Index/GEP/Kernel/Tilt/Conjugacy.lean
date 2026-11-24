import PLAStochastic.Index.GEP.SurvivalBound.KilledRow.Defs
import Mathlib.Probability.Moments.Tilted

/-!
# Exact exponential tilting of the killed chain

Every interval projection is retained. The identity is pointwise for the
original integral operators and does not replace killed powers by free powers.
It supplies the change of law used for slopes outside the critical window.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

theorem kernel_kStep_const_smul (J : Set ℝ) (μ : Measure ℝ) (β a c : ℝ)
    (f : ℝ → ℂ) :
    kStep J μ β a (fun y => c • f y) = fun x => c • kStep J μ β a f x := by
  funext x
  by_cases hx : x ∈ J
  · simp only [kStep, indicator_of_mem hx]
    exact integral_smul c _
  · simp only [kStep, indicator_of_notMem hx, smul_zero]

/-- The one-step identity includes the exact cumulant normalizer. -/
theorem kernel_kStep_tilt (J : Set ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (β : ℝ) {a lam : ℝ} (ha : a ≠ 0)
    (hM : Integrable (fun t : ℝ => Real.exp (lam * t)) μ)
    (f : ℝ → ℂ) (x : ℝ) :
    kStep J (μ.tilted (fun t => lam * t)) β a
        (fun y => Real.exp (lam * y / a) • f y) x =
      Real.exp (lam * (x + β) / a - cgf id μ lam) • kStep J μ β a f x := by
  by_cases hx : x ∈ J
  · simp only [kStep, indicator_of_mem hx]
    have ht := integral_tilted_mul_eq_cgf (X := id) (μ := μ)
      (fun t => Real.exp (lam * (x + β - a * t) / a) • f (x + β - a * t)) hM
    simp only [id_eq] at ht
    rw [ht]
    simp only [smul_smul, ← Real.exp_add]
    have he (t : ℝ) :
        lam * t - cgf id μ lam + lam * (x + β - a * t) / a =
          lam * (x + β) / a - cgf id μ lam := by
      field_simp
      ring
    simp_rw [he]
    exact integral_smul _ _
  · simp only [kStep, indicator_of_notMem hx, smul_zero]

/-- Conjugacy for every actual killed iterate, with no hypotheses on the
terminal function beyond those implicit in the Bochner integral definition. -/
theorem kernel_killed_tilt_conjugacy (J : Set ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (β : ℝ) {a lam : ℝ} (ha : a ≠ 0)
    (hM : Integrable (fun t : ℝ => Real.exp (lam * t)) μ)
    (f : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    ((kStep J (μ.tilted (fun t => lam * t)) β a)^[n]
        (fun y => Real.exp (lam * y / a) • f y)) x =
      Real.exp ((n : ℝ) * (lam * β / a - cgf id μ lam) + lam * x / a) •
        ((kStep J μ β a)^[n] f) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have he : (kStep J (μ.tilted (fun t => lam * t)) β a)^[n]
        (fun y => Real.exp (lam * y / a) • f y) =
          fun y => Real.exp ((n : ℝ) * (lam * β / a - cgf id μ lam)) •
            (Real.exp (lam * y / a) • ((kStep J μ β a)^[n] f) y) := by
      funext y
      rw [ih, Real.exp_add, mul_smul]
    rw [he, kernel_kStep_const_smul]
    dsimp only
    rw [kernel_kStep_tilt J μ β ha hM, smul_smul, ← Real.exp_add]
    congr 2
    push_cast
    ring

/-- The original killed chain expressed under its tilted law. The factor
retains the slope and the starting point exactly. -/
theorem kernel_killed_eq_tilt (J : Set ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (β : ℝ) {a lam : ℝ} (ha : a ≠ 0)
    (hM : Integrable (fun t : ℝ => Real.exp (lam * t)) μ)
    (f : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    ((kStep J μ β a)^[n] f) x =
      Real.exp ((n : ℝ) * cgf id μ lam - lam * (x + n * β) / a) •
        ((kStep J (μ.tilted (fun t => lam * t)) β a)^[n]
          (fun y => Real.exp (lam * y / a) • f y)) x := by
  rw [kernel_killed_tilt_conjugacy J μ β ha hM, smul_smul, ← Real.exp_add]
  have he : (n : ℝ) * cgf id μ lam - lam * (x + n * β) / a +
      ((n : ℝ) * (lam * β / a - cgf id μ lam) + lam * x / a) = 0 := by ring
  rw [he, Real.exp_zero, one_smul]

/-- One deterministic inserted gap, with the same projection as a real step. -/
def kernelMarkedStep (J : Set ℝ) (β a t : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  J.indicator (fun x => f (x + β - a * t))

theorem kernel_markedStep_const_smul (J : Set ℝ) (β a t c : ℝ) (f : ℝ → ℂ) :
    kernelMarkedStep J β a t (fun y => c • f y) =
      fun x => c • kernelMarkedStep J β a t f x := by
  funext x
  by_cases hx : x ∈ J <;> simp [kernelMarkedStep, hx]

theorem kernel_killed_const_smul (J : Set ℝ) (μ : Measure ℝ) (β a c : ℝ)
    (f : ℝ → ℂ) (n : ℕ) :
    (kStep J μ β a)^[n] (fun y => c • f y) =
      fun x => c • ((kStep J μ β a)^[n] f) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, kernel_kStep_const_smul]
    simp only [Function.iterate_succ_apply']

theorem kernel_markedStep_tilt (J : Set ℝ) (β t lam : ℝ) {a : ℝ} (ha : a ≠ 0)
    (f : ℝ → ℂ) (x : ℝ) :
    kernelMarkedStep J β a t (fun y => Real.exp (lam * y / a) • f y) x =
      Real.exp (lam * β / a - lam * t + lam * x / a) •
        kernelMarkedStep J β a t f x := by
  by_cases hx : x ∈ J
  · simp only [kernelMarkedStep, indicator_of_mem hx]
    congr 2
    field_simp
    ring
  · simp [kernelMarkedStep, hx]

/-- An actual chain with one inserted gap has exactly one fewer random
normalizing factor. This is the marked factor needed in the flux formula. -/
theorem kernel_killed_marked_tilt_conjugacy (J : Set ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (β t : ℝ) {a lam : ℝ} (ha : a ≠ 0)
    (hM : Integrable (fun y : ℝ => Real.exp (lam * y)) μ)
    (f : ℝ → ℂ) (l r : ℕ) (x : ℝ) :
    ((kStep J (μ.tilted (fun y => lam * y)) β a)^[l]
      (kernelMarkedStep J β a t
        ((kStep J (μ.tilted (fun y => lam * y)) β a)^[r]
          (fun y => Real.exp (lam * y / a) • f y)))) x =
      Real.exp (((l : ℝ) + r) * (lam * β / a - cgf id μ lam) +
        lam * β / a - lam * t + lam * x / a) •
        ((kStep J μ β a)^[l] (kernelMarkedStep J β a t ((kStep J μ β a)^[r] f))) x := by
  let C := lam * β / a - cgf id μ lam
  have hi : (kStep J (μ.tilted (fun y => lam * y)) β a)^[r]
      (fun y => Real.exp (lam * y / a) • f y) =
        fun y => Real.exp ((r : ℝ) * C) •
          (Real.exp (lam * y / a) • ((kStep J μ β a)^[r] f) y) := by
    funext y
    rw [kernel_killed_tilt_conjugacy J μ β ha hM, Real.exp_add, mul_smul]
  have hm : kernelMarkedStep J β a t
      (fun y => Real.exp (lam * y / a) • ((kStep J μ β a)^[r] f) y) =
        fun y => Real.exp (lam * β / a - lam * t) •
          (Real.exp (lam * y / a) •
            kernelMarkedStep J β a t ((kStep J μ β a)^[r] f) y) := by
    funext y
    rw [kernel_markedStep_tilt J β t lam ha, Real.exp_add, mul_smul]
  rw [hi, kernel_markedStep_const_smul, hm, kernel_killed_const_smul]
  dsimp only
  rw [kernel_killed_const_smul]
  dsimp only
  rw [kernel_killed_tilt_conjugacy J μ β ha hM, smul_smul, smul_smul,
    ← Real.exp_add, ← Real.exp_add]
  congr 2
  dsimp [C]
  ring

theorem kernel_killed_marked_eq_tilt (J : Set ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (β t : ℝ) {a lam : ℝ} (ha : a ≠ 0)
    (hM : Integrable (fun y : ℝ => Real.exp (lam * y)) μ)
    (f : ℝ → ℂ) (l r : ℕ) (x : ℝ) :
    ((kStep J μ β a)^[l] (kernelMarkedStep J β a t ((kStep J μ β a)^[r] f))) x =
      Real.exp (((l : ℝ) + r) * cgf id μ lam -
        lam * (x + (l + r + 1) * β) / a + lam * t) •
        ((kStep J (μ.tilted (fun y => lam * y)) β a)^[l]
          (kernelMarkedStep J β a t
            ((kStep J (μ.tilted (fun y => lam * y)) β a)^[r]
              (fun y => Real.exp (lam * y / a) • f y)))) x := by
  rw [kernel_killed_marked_tilt_conjugacy J μ β t ha hM, smul_smul, ← Real.exp_add]
  have he : ((l : ℝ) + r) * cgf id μ lam -
      lam * (x + (l + r + 1) * β) / a + lam * t +
        (((l : ℝ) + r) * (lam * β / a - cgf id μ lam) +
          lam * β / a - lam * t + lam * x / a) = 0 := by ring
  rw [he, Real.exp_zero, one_smul]

end
end PGM
