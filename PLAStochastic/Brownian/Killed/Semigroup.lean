import PLAStochastic.Brownian.Killed.HeatIdentification
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Spatially differentiated Dirichlet semigroup identities, proved by summable bounds
and sine orthogonality rather than assumed differentiability of an integral. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem norm_heatSpatialSeries_le {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (a b : ℕ) (x z : ℝ) :
    ‖heatSpatialSeries r a b t x z‖ ≤ ∑' n, heatSpatialBound r t a b n := by
  have hs := summable_heatSpatialMode hr ht a b x z
  have hb := summable_heatSpatialBound hr ht a b
  calc
    _ ≤ ∑' n, ‖heatSpatialMode r a b n t x z‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ _ := hs.norm.tsum_le_tsum (fun n => heatSpatialMode_bound hr ht.le le_rfl a b n x z) hb

theorem integral_heatSpatialSeries_mul {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (a b : ℕ) (x : ℝ) {g : ℝ → ℝ} (hg : Continuous g) {M : ℝ}
    (hb : ∀ z, ‖g z‖ ≤ M) :
    (∫ z in Icc (0 : ℝ) r, heatSpatialSeries r a b t x z * g z) =
      ∑' n, ∫ z in Icc (0 : ℝ) r, heatSpatialMode r a b n t x z * g z := by
  let F : ℕ → ℝ → ℝ := fun n z => heatSpatialMode r a b n t x z * g z
  have hi (n : ℕ) : IntegrableOn (F n) (Icc 0 r) := by
    apply Continuous.integrableOn_Icc
    exact (by dsimp only [F, heatSpatialMode]; fun_prop)
  have hbn (n : ℕ) : 0 ≤ heatSpatialBound r t a b n :=
    (norm_nonneg _).trans (heatSpatialMode_bound hr ht.le le_rfl a b n x 0)
  have hbound (n : ℕ) (z : ℝ) : ‖F n z‖ ≤ heatSpatialBound r t a b n * M := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul (heatSpatialMode_bound hr ht.le le_rfl a b n x z) (hb z)
      (norm_nonneg _) (hbn n)
  have hnorm (n : ℕ) : (∫ z in Icc (0 : ℝ) r, ‖F n z‖) ≤
      r * (heatSpatialBound r t a b n * M) := by
    calc
      _ ≤ ∫ _z in Icc (0 : ℝ) r, heatSpatialBound r t a b n * M :=
        integral_mono_ae (hi n).norm (integrable_const _) (Eventually.of_forall (hbound n))
      _ = _ := by
        rw [integral_const]
        simp only [measureReal_restrict_apply_univ, smul_eq_mul,
          Real.volume_real_Icc_of_le hr.le, sub_zero]
  have hs : Summable (fun n => ∫ z in Icc (0 : ℝ) r, ‖F n z‖) :=
    (((summable_heatSpatialBound hr ht a b).mul_right M).mul_left r).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hnorm
  have heq (z : ℝ) : heatSpatialSeries r a b t x z * g z = ∑' n, F n z := by
    unfold heatSpatialSeries
    exact (tsum_mul_right).symm
  simp only [heq]
  exact (integral_tsum_of_summable_integral_norm hi hs).symm

theorem integral_heatSpatialSeries_sine {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (a : ℕ) (x : ℝ) (m : ℕ) :
    (∫ z in Icc (0 : ℝ) r, heatSpatialSeries r a 0 t x z *
      Real.sin (heatFrequency r m * z)) =
      heatFrequency r m ^ a * Real.sin (heatFrequency r m * x + (a : ℝ) * Real.pi / 2) *
        Real.exp (-(heatFrequency r m ^ 2) * t / 2) := by
  rw [integral_heatSpatialSeries_mul hr ht a 0 x (by fun_prop)
    (fun z => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (heatFrequency r m * z))]
  have hint (n : ℕ) : (∫ z in Icc (0 : ℝ) r, heatSpatialMode r a 0 n t x z *
      Real.sin (heatFrequency r m * z)) =
      (2 / r * heatFrequency r n ^ a *
        Real.sin (heatFrequency r n * x + (a : ℝ) * Real.pi / 2) *
          Real.exp (-(heatFrequency r n ^ 2) * t / 2)) *
            (if n = m then r / 2 else 0) := by
    have hf (z : ℝ) : heatSpatialMode r a 0 n t x z * Real.sin (heatFrequency r m * z) =
        (2 / r * heatFrequency r n ^ a *
          Real.sin (heatFrequency r n * x + (a : ℝ) * Real.pi / 2) *
            Real.exp (-(heatFrequency r n ^ 2) * t / 2)) *
              (Real.sin (heatFrequency r n * z) * Real.sin (heatFrequency r m * z)) := by
      dsimp only [heatSpatialMode]
      simp only [add_zero, Nat.cast_zero, zero_mul, zero_div]
      ring
    simp only [hf]
    rw [integral_const_mul, integral_Icc_heatSine_mul_heatSine hr n m]
  simp only [hint]
  rw [tsum_eq_single m (fun n hnm => by rw [if_neg hnm, mul_zero]), if_pos rfl]
  field_simp

theorem heatSpatialSeries_swap (r : ℝ) (a b : ℕ) (t x z : ℝ) :
    heatSpatialSeries r a b t x z = heatSpatialSeries r b a t z x := by
  apply tsum_congr
  intro n
  exact heatSpatialMode_swap r a b n t x z

/-- Every spatial derivative satisfies the differentiated semigroup identity.
The proof exchanges only absolutely integrable, uniformly bounded series. -/
theorem integral_heatSpatialSeries_mul_heatSpatialSeries {r t s : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hs : 0 < s) (a b : ℕ) (x z : ℝ) :
    (∫ y in Icc (0 : ℝ) r, heatSpatialSeries r a 0 t x y *
      heatSpatialSeries r 0 b s y z) = heatSpatialSeries r a b (t + s) x z := by
  have hg : Continuous (fun y => heatSpatialSeries r 0 b s y z) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (hasDerivAt_heatSpatialSeries_left hr hs 0 b y z).continuousAt
  rw [integral_heatSpatialSeries_mul hr ht a 0 x hg
    (fun y => norm_heatSpatialSeries_le hr hs 0 b y z)]
  have hint (n : ℕ) : (∫ y in Icc (0 : ℝ) r, heatSpatialMode r a 0 n t x y *
      heatSpatialSeries r 0 b s y z) = heatSpatialMode r a b n (t + s) x z := by
    have hf (y : ℝ) : heatSpatialMode r a 0 n t x y * heatSpatialSeries r 0 b s y z =
        (2 / r * heatFrequency r n ^ a *
          Real.sin (heatFrequency r n * x + (a : ℝ) * Real.pi / 2) *
            Real.exp (-(heatFrequency r n ^ 2) * t / 2)) *
              (heatSpatialSeries r b 0 s z y * Real.sin (heatFrequency r n * y)) := by
      rw [heatSpatialSeries_swap r 0 b s y z]
      dsimp only [heatSpatialMode]
      simp only [add_zero, Nat.cast_zero, zero_mul, zero_div]
      ring
    simp only [hf]
    rw [integral_const_mul, integral_heatSpatialSeries_sine hr hs b z n]
    unfold heatSpatialMode
    rw [show -(heatFrequency r n ^ 2) * (t + s) / 2 =
      -(heatFrequency r n ^ 2) * t / 2 + -(heatFrequency r n ^ 2) * s / 2 by ring,
      Real.exp_add, pow_add]
    ring
  simp only [hint]
  rfl

theorem integral_dirichletHeatKernel_mul {r t s : ℝ} (hr : 0 < r)
    (ht : 0 < t) (hs : 0 < s) (x z : ℝ) :
    (∫ y in Icc (0 : ℝ) r, dirichletHeatKernel r t x y * dirichletHeatKernel r s y z) =
      dirichletHeatKernel r (t + s) x z :=
  integral_heatSpatialSeries_mul_heatSpatialSeries hr ht hs 0 0 x z

/-- The inward derivative at the left endpoint. -/
def heatBoundaryLeft (r t x : ℝ) : ℝ := heatSpatialSeries r 0 1 t x 0
/-- The inward derivative at the right endpoint. -/
def heatBoundaryRight (r t x : ℝ) : ℝ := -heatSpatialSeries r 0 1 t x r
/-- The inward derivative across the two distinct endpoints. -/
def heatCrossBoundary (r t : ℝ) : ℝ := -heatSpatialSeries r 1 1 t r 0

theorem hasDerivAt_heatKernel_zero {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (dirichletHeatKernel r t x) (heatBoundaryLeft r t x) 0 :=
  hasDerivAt_heatSpatialSeries_right hr ht 0 0 x 0

theorem hasDerivAt_heatKernel_width {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (dirichletHeatKernel r t x) (-heatBoundaryRight r t x) r := by
  change HasDerivAt (fun z => heatSpatialSeries r 0 0 t x z)
    (-(-heatSpatialSeries r 0 1 t x r)) r
  rw [neg_neg]
  exact hasDerivAt_heatSpatialSeries_right hr ht 0 0 x r

theorem hasDerivAt_heatBoundaryLeft {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (heatBoundaryLeft r t) (heatSpatialSeries r 1 1 t x 0) x :=
  hasDerivAt_heatSpatialSeries_left hr ht 0 1 x 0

theorem heatFrequency_mul_width {r : ℝ} (hr : r ≠ 0) (n : ℕ) :
    heatFrequency r n * r = ((n : ℝ) + 1) * Real.pi := by
  unfold heatFrequency
  field_simp

theorem cos_heatFrequency_width {r : ℝ} (hr : r ≠ 0) (n : ℕ) :
    Real.cos (heatFrequency r n * r) = (-1 : ℝ) ^ (n + 1) := by
  rw [heatFrequency_mul_width hr]
  exact_mod_cast Real.cos_nat_mul_pi (n + 1)

theorem heatBoundaryLeft_series (r t x : ℝ) :
    heatBoundaryLeft r t x = ∑' n, (2 / r * heatFrequency r n *
      Real.sin (heatFrequency r n * x)) * Real.exp (-(heatFrequency r n ^ 2) * t / 2) := by
  apply tsum_congr
  intro n
  simp [heatSpatialMode, mul_assoc]

theorem heatBoundaryRight_series {r : ℝ} (hr : r ≠ 0) (t x : ℝ) :
    heatBoundaryRight r t x = ∑' n, (2 / r * heatFrequency r n * (-1 : ℝ) ^ n *
      Real.sin (heatFrequency r n * x)) * Real.exp (-(heatFrequency r n ^ 2) * t / 2) := by
  unfold heatBoundaryRight heatSpatialSeries
  rw [← tsum_neg]
  apply tsum_congr
  intro n
  simp only [heatSpatialMode, zero_add, Nat.cast_zero, Nat.cast_one, zero_mul, zero_div,
    add_zero, one_mul, Real.sin_add_pi_div_two, cos_heatFrequency_width hr, pow_succ]
  ring

theorem heatCrossBoundary_series {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    heatCrossBoundary r t = ∑' n, (2 / r * heatFrequency r n ^ 2 * (-1 : ℝ) ^ n) *
      Real.exp (-(heatFrequency r n ^ 2) * t / 2) := by
  unfold heatCrossBoundary heatSpatialSeries
  rw [← tsum_neg]
  apply tsum_congr
  intro n
  simp only [heatSpatialMode, Nat.cast_one, mul_zero, one_mul,
    zero_add, Real.sin_add_pi_div_two, cos_heatFrequency_width hr, pow_succ,
    Real.sin_pi_div_two]
  ring

theorem heatBoundaryRight_reflection {r : ℝ} (hr : r ≠ 0) (t x : ℝ) :
    heatBoundaryRight r t x = heatBoundaryLeft r t (r - x) := by
  rw [heatBoundaryRight_series hr, heatBoundaryLeft_series]
  apply tsum_congr
  intro n
  rw [mul_sub, Real.sin_sub, heatFrequency_mul_width hr]
  have hsin : Real.sin (((n : ℝ) + 1) * Real.pi) = 0 := by
    exact_mod_cast Real.sin_nat_mul_pi (n + 1)
  have hcos : Real.cos (((n : ℝ) + 1) * Real.pi) = (-1 : ℝ) ^ (n + 1) := by
    exact_mod_cast Real.cos_nat_mul_pi (n + 1)
  rw [hsin, hcos, pow_succ]
  ring

/-- The cross-boundary semigroup identity is proved for every positive split of time. -/
theorem integral_heatBoundaryRight_mul_left {r t s : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hs : 0 < s) :
    (∫ y in Icc (0 : ℝ) r, heatBoundaryRight r t y * heatBoundaryLeft r s y) =
      heatCrossBoundary r (t + s) := by
  have heq (y : ℝ) : heatBoundaryRight r t y * heatBoundaryLeft r s y =
      -(heatSpatialSeries r 1 0 t r y * heatSpatialSeries r 0 1 s y 0) := by
    unfold heatBoundaryRight heatBoundaryLeft
    rw [heatSpatialSeries_swap r 0 1 t y r]
    ring
  simp only [heq, integral_neg]
  rw [integral_heatSpatialSeries_mul_heatSpatialSeries hr ht hs 1 1 r 0]
  rfl

private theorem nonneg_deriv_at_left_endpoint {f : ℝ → ℝ} {d r : ℝ}
    (hr : 0 < r) (hd : HasDerivAt f d 0) (h0 : f 0 = 0)
    (hf : ∀ z ∈ Icc 0 r, 0 ≤ f z) : 0 ≤ d := by
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds] with z hz hzr
  simp only [zero_add, h0, sub_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt hz)) (hf z ⟨le_of_lt hz, hzr.le⟩)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem heatBoundaryLeft_nonneg (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r : ℝ} (hr : 0 < r) {T : ℝ≥0} (hT : 0 < T) {x : ℝ} (hx : x ∈ Icc 0 r) :
    0 ≤ heatBoundaryLeft r T x := by
  apply nonneg_deriv_at_left_endpoint hr (hasDerivAt_heatKernel_zero hr hT x)
    (dirichletHeatKernel_zero_right r T x)
  intro z hz
  exact dirichletHeatKernel_nonneg hB hr hx hT hz

theorem heatBoundaryRight_nonneg (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r : ℝ} (hr : 0 < r) {T : ℝ≥0} (hT : 0 < T) {x : ℝ} (hx : x ∈ Icc 0 r) :
    0 ≤ heatBoundaryRight r T x := by
  rw [heatBoundaryRight_reflection hr.ne']
  exact heatBoundaryLeft_nonneg hB hr hT ⟨sub_nonneg.mpr hx.2, sub_le_self _ hx.1⟩

theorem heatCrossBoundary_nonneg (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r : ℝ} (hr : 0 < r) {T : ℝ≥0} (hT : 0 < T) :
    0 ≤ heatCrossBoundary r T := by
  have hhalf : (0 : ℝ) < (T : ℝ) / 2 := by positivity
  have heq : (T : ℝ) / 2 + (T : ℝ) / 2 = T := by ring
  rw [← heq, ← integral_heatBoundaryRight_mul_left hr hhalf hhalf]
  apply setIntegral_nonneg measurableSet_Icc
  intro y hy
  have hL := heatBoundaryLeft_nonneg hB hr (T := T / 2) (by positivity) hy
  have hR := heatBoundaryRight_nonneg hB hr (T := T / 2) (by positivity) hy
  exact mul_nonneg hR hL

/-- The paper's normalization of the left boundary series (our index zero is its mode one). -/
theorem heatBoundaryLeft_paper_series {r : ℝ} (hr : r ≠ 0) (t x : ℝ) :
    heatBoundaryLeft r t x = (2 * Real.pi / r ^ 2) * ∑' n : ℕ,
      (((n : ℝ) + 1) * Real.sin (heatFrequency r n * x)) *
        Real.exp (-(heatFrequency r n ^ 2) * t / 2) := by
  rw [heatBoundaryLeft_series, ← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold heatFrequency
  field_simp

theorem heatCrossBoundary_paper_series {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    heatCrossBoundary r t = (2 * Real.pi ^ 2 / r ^ 3) * ∑' n : ℕ,
      ((-1 : ℝ) ^ n * ((n : ℝ) + 1) ^ 2) *
        Real.exp (-(heatFrequency r n ^ 2) * t / 2) := by
  rw [heatCrossBoundary_series hr, ← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold heatFrequency
  field_simp

theorem heatCrossBoundary_eq_integral_halves {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    heatCrossBoundary r t = ∫ y in Icc (0 : ℝ) r,
      heatBoundaryRight r (t / 2) y * heatBoundaryLeft r (t / 2) y := by
  rw [integral_heatBoundaryRight_mul_left hr (by positivity) (by positivity)]
  congr 1
  ring

/-- A nonzero spectral moment of the actual inward boundary kernel. -/
theorem integral_heatBoundaryLeft_sine {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (n : ℕ) :
    (∫ y in Icc (0 : ℝ) r, heatBoundaryLeft r t y * Real.sin (heatFrequency r n * y)) =
      heatFrequency r n * Real.exp (-(heatFrequency r n ^ 2) * t / 2) := by
  have heq (y : ℝ) : heatBoundaryLeft r t y = heatSpatialSeries r 1 0 t 0 y :=
    heatSpatialSeries_swap r 0 1 t y 0
  simp only [heq]
  rw [integral_heatSpatialSeries_sine hr ht 1 0 n]
  simp

theorem integral_heatBoundaryLeft_sine_pos {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (n : ℕ) :
    0 < ∫ y in Icc (0 : ℝ) r, heatBoundaryLeft r t y * Real.sin (heatFrequency r n * y) := by
  rw [integral_heatBoundaryLeft_sine hr ht n]
  exact mul_pos (heatFrequency_pos hr n) (Real.exp_pos _)

end BrownianAffine
