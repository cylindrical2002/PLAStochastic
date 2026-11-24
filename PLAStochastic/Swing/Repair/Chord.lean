import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The deterministic chord argument for the Swing repair

This module formalizes the half-budget argument in `paper/repair_section.tex`.
All arithmetic is over the exact real numbers. The target of the error bound is
the piecewise-linear interpolation of observed samples.
-/

namespace SwingRepair

noncomputable section

/-- The affine line through the true anchor with the given slope. -/
def line (t₀ y₀ m t : ℝ) : ℝ := y₀ + m * (t - t₀)

/-- Linear interpolation, written in barycentric coordinates. -/
def blend (a b θ : ℝ) : ℝ := (1 - θ) * a + θ * b

/-- The true-endpoint chord on a time interval. -/
def chord (t₀ t₁ y₀ y₁ t : ℝ) : ℝ :=
  blend y₀ y₁ ((t - t₀) / (t₁ - t₀))

@[simp] theorem blend_zero (a b : ℝ) : blend a b 0 = a := by
  simp [blend]

@[simp] theorem blend_one (a b : ℝ) : blend a b 1 = b := by
  simp [blend]

@[simp] theorem chord_left (t₀ t₁ y₀ y₁ : ℝ) :
    chord t₀ t₁ y₀ y₁ t₀ = y₀ := by
  simp [chord]

@[simp] theorem chord_right {t₀ t₁ : ℝ} (h : t₀ < t₁) (y₀ y₁ : ℝ) :
    chord t₀ t₁ y₀ y₁ t₁ = y₁ := by
  simp [chord, ne_of_gt (sub_pos.mpr h)]

theorem continuous_chord (t₀ t₁ y₀ y₁ : ℝ) :
    Continuous (chord t₀ t₁ y₀ y₁) := by
  unfold chord blend
  fun_prop

/-- Endpoint error bounds propagate throughout an affine interpolation. -/
theorem blend_error {a b c d θ ε : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (ha : |a - c| ≤ ε) (hb : |b - d| ≤ ε) :
    |blend a b θ - blend c d θ| ≤ ε := by
  have heq : blend a b θ - blend c d θ =
      (1 - θ) * (a - c) + θ * (b - d) := by
    unfold blend
    ring
  rw [heq]
  calc
    |(1 - θ) * (a - c) + θ * (b - d)|
      ≤ |(1 - θ) * (a - c)| + |θ * (b - d)| := abs_add_le _ _
    _ = (1 - θ) * |a - c| + θ * |b - d| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - θ),
        abs_of_nonneg hθ₀]
    _ ≤ (1 - θ) * ε + θ * ε :=
      add_le_add (mul_le_mul_of_nonneg_left ha (by linarith))
        (mul_le_mul_of_nonneg_left hb hθ₀)
    _ = ε := by ring

/-- The chord correction is the endpoint residual multiplied by a number in [0,1]. -/
theorem chord_sub_line {t₀ t₁ : ℝ} (h : t₀ < t₁) (y₀ y₁ m t : ℝ) :
    chord t₀ t₁ y₀ y₁ t - line t₀ y₀ m t =
      ((t - t₀) / (t₁ - t₀)) * (y₁ - line t₀ y₀ m t₁) := by
  unfold chord blend line
  field_simp [ne_of_gt (sub_pos.mpr h)]
  ring

/-- Replacing a feasible anchored line by the true-endpoint chord costs at most δ. -/
theorem chord_line_error {t₀ t₁ y₀ y₁ m t δ : ℝ}
    (h : t₀ < t₁) (ht₀ : t₀ ≤ t) (ht₁ : t ≤ t₁)
    (hend : |y₁ - line t₀ y₀ m t₁| ≤ δ) :
    |chord t₀ t₁ y₀ y₁ t - line t₀ y₀ m t| ≤ δ := by
  have hd : 0 < t₁ - t₀ := sub_pos.mpr h
  have hθ₀ : 0 ≤ (t - t₀) / (t₁ - t₀) :=
    div_nonneg (sub_nonneg.mpr ht₀) hd.le
  have hθ₁ : (t - t₀) / (t₁ - t₀) ≤ 1 := by
    apply (div_le_one hd).mpr
    linarith
  rw [chord_sub_line h, abs_mul, abs_of_nonneg hθ₀]
  calc
    (t - t₀) / (t₁ - t₀) * |y₁ - line t₀ y₀ m t₁|
      ≤ 1 * |y₁ - line t₀ y₀ m t₁| :=
        mul_le_mul_of_nonneg_right hθ₁ (abs_nonneg _)
    _ ≤ δ := by simpa using hend

/-- The paper's half-budget lemma, for any sample inside an accepted prefix. -/
theorem chord_sample_error {t₀ t₁ y₀ y₁ m t y ε : ℝ}
    (h : t₀ < t₁) (ht₀ : t₀ ≤ t) (ht₁ : t ≤ t₁)
    (hend : |y₁ - line t₀ y₀ m t₁| ≤ ε / 2)
    (hsample : |y - line t₀ y₀ m t| ≤ ε / 2) :
    |y - chord t₀ t₁ y₀ y₁ t| ≤ ε := by
  have hc := chord_line_error h ht₀ ht₁ hend
  calc
    |y - chord t₀ t₁ y₀ y₁ t|
      = |(y - line t₀ y₀ m t) +
          (line t₀ y₀ m t - chord t₀ t₁ y₀ y₁ t)| := by congr 1; ring
    _ ≤ |y - line t₀ y₀ m t| +
          |line t₀ y₀ m t - chord t₀ t₁ y₀ y₁ t| := abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := by
      rw [abs_sub_comm (line t₀ y₀ m t)]
      exact add_le_add hsample hc
    _ = ε := by ring

/-- Every chord is affine in its time argument. -/
theorem chord_blend (t₀ t₁ y₀ y₁ u v θ : ℝ) :
    chord t₀ t₁ y₀ y₁ (blend u v θ) =
      blend (chord t₀ t₁ y₀ y₁ u) (chord t₀ t₁ y₀ y₁ v) θ := by
  unfold chord blend
  ring

/-- A uniform endpoint bound controls the whole original sampling interval. -/
theorem chord_edge_error {t₀ t₁ y₀ y₁ u v yu yv θ ε : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hu : |yu - chord t₀ t₁ y₀ y₁ u| ≤ ε)
    (hv : |yv - chord t₀ t₁ y₀ y₁ v| ≤ ε) :
    |blend yu yv θ - chord t₀ t₁ y₀ y₁ (blend u v θ)| ≤ ε := by
  rw [chord_blend]
  exact blend_error hθ₀ hθ₁ hu hv

/-- Half-budget feasibility implies the full error bound on an entire grid edge. -/
theorem repair_edge_error {t₀ t₁ y₀ y₁ m u v yu yv θ ε : ℝ}
    (h : t₀ < t₁) (hu₀ : t₀ ≤ u) (hu₁ : u ≤ t₁)
    (hv₀ : t₀ ≤ v) (hv₁ : v ≤ t₁)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hend : |y₁ - line t₀ y₀ m t₁| ≤ ε / 2)
    (hu : |yu - line t₀ y₀ m u| ≤ ε / 2)
    (hv : |yv - line t₀ y₀ m v| ≤ ε / 2) :
    |blend yu yv θ - chord t₀ t₁ y₀ y₁ (blend u v θ)| ≤ ε := by
  exact chord_edge_error hθ₀ hθ₁
    (chord_sample_error h hu₀ hu₁ hend hu)
    (chord_sample_error h hv₀ hv₁ hend hv)

end

end SwingRepair
