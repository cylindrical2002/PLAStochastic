import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.WedgeSeries.SumCDFSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
Analytic Dirichlet sine kernel on a bounded interval. No probabilistic identification
is assumed here: its equality to the actual killed Brownian measure is a separate theorem.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace BrownianAffine

/-- Positive sine frequency; index zero is the first Dirichlet mode. -/
def heatFrequency (r : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) * (Real.pi / r)

def heatScale (r : ℝ) : ℝ := (Real.pi / r) ^ 2 / 2

/-- Explicit candidate for every mixed spatial derivative of a single mode. -/
def heatSpatialMode (r : ℝ) (a b n : ℕ) (t x z : ℝ) : ℝ :=
  (2 / r * heatFrequency r n ^ (a + b)) *
    (Real.sin (heatFrequency r n * x + (a : ℝ) * Real.pi / 2) *
      Real.sin (heatFrequency r n * z + (b : ℝ) * Real.pi / 2)) *
    Real.exp (-(heatFrequency r n ^ 2) * t / 2)

/-- The corresponding analytic series. -/
def heatSpatialSeries (r : ℝ) (a b : ℕ) (t x z : ℝ) : ℝ :=
  ∑' n, heatSpatialMode r a b n t x z

def dirichletHeatKernel (r t x z : ℝ) : ℝ := heatSpatialSeries r 0 0 t x z

def heatSpatialBound (r δ : ℝ) (a b n : ℕ) : ℝ :=
  (2 / r * (Real.pi / r) ^ (a + b)) *
    (((n : ℝ) + 1) ^ (a + b) * Real.exp (-((n : ℝ) + 1) * (heatScale r * δ)))

theorem heatFrequency_pos {r : ℝ} (hr : 0 < r) (n : ℕ) : 0 < heatFrequency r n := by
  unfold heatFrequency
  positivity

theorem heatScale_pos {r : ℝ} (hr : 0 < r) : 0 < heatScale r := by
  unfold heatScale
  positivity

theorem heatSpatialMode_bound {r δ t : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ) (ht : δ ≤ t)
    (a b n : ℕ) (x z : ℝ) :
    ‖heatSpatialMode r a b n t x z‖ ≤ heatSpatialBound r δ a b n := by
  have hf := (heatFrequency_pos hr n).le
  have hc : 0 ≤ 2 / r * heatFrequency r n ^ (a + b) := by positivity
  have hs : |Real.sin (heatFrequency r n * x + (a : ℝ) * Real.pi / 2) *
      Real.sin (heatFrequency r n * z + (b : ℝ) * Real.pi / 2)| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have hexp : Real.exp (-(heatFrequency r n ^ 2) * t / 2) ≤
      Real.exp (-((n : ℝ) + 1) * (heatScale r * δ)) := by
    apply Real.exp_le_exp.mpr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hm : 0 ≤ ((n : ℝ) + 1) ^ 2 - ((n : ℝ) + 1) := by nlinarith
    have hp := mul_nonneg hm (mul_nonneg (heatScale_pos hr).le hδ)
    have ht' := mul_le_mul_of_nonneg_left ht (sq_nonneg (heatFrequency r n))
    unfold heatFrequency heatScale at *
    nlinarith
  calc
    _ = (2 / r * heatFrequency r n ^ (a + b)) *
        |Real.sin (heatFrequency r n * x + (a : ℝ) * Real.pi / 2) *
          Real.sin (heatFrequency r n * z + (b : ℝ) * Real.pi / 2)| *
        Real.exp (-(heatFrequency r n ^ 2) * t / 2) := by
      rw [heatSpatialMode, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hc,
        abs_of_pos (Real.exp_pos _)]
    _ ≤ (2 / r * heatFrequency r n ^ (a + b)) *
        Real.exp (-(heatFrequency r n ^ 2) * t / 2) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs hc) (Real.exp_nonneg _)
    _ ≤ (2 / r * heatFrequency r n ^ (a + b)) *
        Real.exp (-((n : ℝ) + 1) * (heatScale r * δ)) :=
      mul_le_mul_of_nonneg_left hexp hc
    _ = _ := by simp only [heatSpatialBound, heatFrequency, mul_pow]; ring

theorem summable_heatSpatialBound {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (a b : ℕ) :
    Summable (heatSpatialBound r δ a b) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul (a + b) (mul_pos (heatScale_pos hr) hδ)
  have hs := (summable_nat_add_iff 1).mpr h
  convert! hs.mul_left (2 / r * (Real.pi / r) ^ (a + b)) using 1
  funext n
  simp only [heatSpatialBound, Nat.cast_add, Nat.cast_one, neg_mul, mul_comm]
  congr 3
  ring

theorem summable_heatSpatialMode {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (a b : ℕ) (x z : ℝ) : Summable (fun n => heatSpatialMode r a b n t x z) :=
  (summable_heatSpatialBound hr ht a b).of_norm_bounded
    (fun n => heatSpatialMode_bound hr ht.le le_rfl a b n x z)

/-- Uniform convergence of every spatial derivative series over all positions, for time at least δ. -/
theorem tendstoUniformlyOn_heatSpatialSeries {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (a b : ℕ) :
    TendstoUniformlyOn
      (fun N (p : ℝ × ℝ × ℝ) => ∑ n ∈ Finset.range N,
        heatSpatialMode r a b n p.1 p.2.1 p.2.2)
      (fun p => heatSpatialSeries r a b p.1 p.2.1 p.2.2)
      atTop {p | δ ≤ p.1} := by
  exact tendstoUniformlyOn_tsum_nat (summable_heatSpatialBound hr hδ a b)
    (fun n p hp => heatSpatialMode_bound hr hδ.le hp a b n p.2.1 p.2.2)

theorem hasDerivAt_heatSpatialMode_left (r : ℝ) (a b n : ℕ) (t x z : ℝ) :
    HasDerivAt (fun y => heatSpatialMode r a b n t y z)
      (heatSpatialMode r (a + 1) b n t x z) x := by
  have hd := (((hasDerivAt_id x).const_mul (heatFrequency r n)).add_const
    ((a : ℝ) * Real.pi / 2)).sin
  convert! ((hd.mul_const (Real.sin (heatFrequency r n * z + (b : ℝ) * Real.pi / 2))).const_mul
    (2 / r * heatFrequency r n ^ (a + b))).mul_const
    (Real.exp (-(heatFrequency r n ^ 2) * t / 2)) using 1
  unfold heatSpatialMode
  rw [show a + 1 + b = a + b + 1 by omega, pow_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show heatFrequency r n * x + ((a : ℝ) + 1) * Real.pi / 2 =
    (heatFrequency r n * x + (a : ℝ) * Real.pi / 2) + Real.pi / 2 by ring,
    Real.sin_add_pi_div_two]
  simp only [id_eq]
  ring

theorem heatSpatialMode_swap (r : ℝ) (a b n : ℕ) (t x z : ℝ) :
    heatSpatialMode r a b n t x z = heatSpatialMode r b a n t z x := by
  unfold heatSpatialMode
  rw [Nat.add_comm a b, mul_comm (Real.sin _) (Real.sin _)]

theorem hasDerivAt_heatSpatialMode_right (r : ℝ) (a b n : ℕ) (t x z : ℝ) :
    HasDerivAt (fun y => heatSpatialMode r a b n t x y)
      (heatSpatialMode r a (b + 1) n t x z) z := by
  simpa only [heatSpatialMode_swap r a b, heatSpatialMode_swap r a (b + 1)] using
    hasDerivAt_heatSpatialMode_left r b a n t z x

/-- Every spatial derivative is justified by a summable majorant, on the entire real line. -/
theorem hasDerivAt_heatSpatialSeries_left {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (a b : ℕ) (x z : ℝ) :
    HasDerivAt (fun y => heatSpatialSeries r a b t y z)
      (heatSpatialSeries r (a + 1) b t x z) x := by
  exact hasDerivAt_tsum (summable_heatSpatialBound hr ht (a + 1) b)
    (fun n y => hasDerivAt_heatSpatialMode_left r a b n t y z)
    (fun n y => heatSpatialMode_bound hr ht.le le_rfl (a + 1) b n y z)
    (summable_heatSpatialMode hr ht a b x z) x

theorem hasDerivAt_heatSpatialSeries_right {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (a b : ℕ) (x z : ℝ) :
    HasDerivAt (fun y => heatSpatialSeries r a b t x y)
      (heatSpatialSeries r a (b + 1) t x z) z := by
  exact hasDerivAt_tsum (summable_heatSpatialBound hr ht a (b + 1))
    (fun n y => hasDerivAt_heatSpatialMode_right r a b n t x y)
    (fun n y => heatSpatialMode_bound hr ht.le le_rfl a (b + 1) n x y)
    (summable_heatSpatialMode hr ht a b x z) z

theorem dirichletHeatKernel_series (r t x z : ℝ) :
    dirichletHeatKernel r t x z = ∑' n : ℕ,
      2 / r * (Real.sin (heatFrequency r n * x) * Real.sin (heatFrequency r n * z)) *
        Real.exp (-(heatFrequency r n ^ 2) * t / 2) := by
  simp only [dirichletHeatKernel, heatSpatialSeries, heatSpatialMode, Nat.cast_zero,
    zero_mul, zero_div, add_zero, pow_zero, mul_one]

theorem dirichletHeatKernel_symm (r t x z : ℝ) :
    dirichletHeatKernel r t x z = dirichletHeatKernel r t z x := by
  apply tsum_congr
  intro n
  exact heatSpatialMode_swap r 0 0 n t x z

theorem dirichletHeatKernel_zero_left (r t z : ℝ) : dirichletHeatKernel r t 0 z = 0 := by
  simp [dirichletHeatKernel, heatSpatialSeries, heatSpatialMode]

theorem dirichletHeatKernel_zero_right (r t x : ℝ) : dirichletHeatKernel r t x 0 = 0 := by
  rw [dirichletHeatKernel_symm]
  exact dirichletHeatKernel_zero_left r t x

theorem dirichletHeatKernel_at_width_left {r : ℝ} (hr : r ≠ 0) (t z : ℝ) :
    dirichletHeatKernel r t r z = 0 := by
  rw [dirichletHeatKernel_series]
  have hs (n : ℕ) : Real.sin (heatFrequency r n * r) = 0 := by
    have hfreq : heatFrequency r n * r = ((n + 1 : ℕ) : ℝ) * Real.pi := by
      unfold heatFrequency
      push_cast
      field_simp
    rw [hfreq]
    exact Real.sin_nat_mul_pi (n + 1)
  simp only [hs, zero_mul, mul_zero, tsum_zero]

theorem dirichletHeatKernel_at_width_right {r : ℝ} (hr : r ≠ 0) (t x : ℝ) :
    dirichletHeatKernel r t x r = 0 := by
  rw [dirichletHeatKernel_symm]
  exact dirichletHeatKernel_at_width_left hr t x

end BrownianAffine
