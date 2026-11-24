import PLAStochastic.Brownian.Killed.Width.JointContinuity
import PLAStochastic.ForMathlib.Topology.UniformSpace.CompactJointConvergence

/-! # Actual heat kernel boundary quotients with changing interval width -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Every derivative in the second position retains the zero first-position boundary. -/
theorem heatSpatialSeries_zero_left (r t z : ℝ) (b : ℕ) :
    heatSpatialSeries r 0 b t 0 z = 0 := by
  simp [heatSpatialSeries, heatSpatialMode]

theorem heatSpatialSeries_at_width_left {r : ℝ} (hr : r ≠ 0) (t z : ℝ) (b : ℕ) :
    heatSpatialSeries r 0 b t r z = 0 := by
  have hs (n : ℕ) : Real.sin (heatFrequency r n * r) = 0 := by
    have hfreq : heatFrequency r n * r = ((n + 1 : ℕ) : ℝ) * Real.pi := by
      unfold heatFrequency
      push_cast
      field_simp
    rw [hfreq]
    exact Real.sin_nat_mul_pi (n + 1)
  simp only [heatSpatialSeries, heatSpatialMode, Nat.cast_zero, zero_mul, zero_div,
    add_zero, hs, zero_mul, mul_zero, tsum_zero]

/-- The quotient at the moving right endpoint is an actual interior derivative. -/
theorem heatSpatialSeries_right_quotient_mvt {r t x : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hx : x < r) (z : ℝ) (b : ℕ) :
    ∃ c ∈ Ioo x r, heatSpatialSeries r 0 b t x z / (r-x) =
      -heatSpatialSeries r 1 b t c z := by
  obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope
    (fun y => heatSpatialSeries r 0 b t y z) (fun y => heatSpatialSeries r 1 b t y z)
    hx (fun y _ => (hasDerivAt_heatSpatialSeries_left hr ht 0 b y z).continuousAt.continuousWithinAt)
    (fun y _ => hasDerivAt_heatSpatialSeries_left hr ht 0 b y z)
  refine ⟨c, hc, ?_⟩
  rw [heatSpatialSeries_at_width_left hr.ne'] at he
  rw [he]
  ring

/-- The quotient at zero is likewise an actual interior derivative. -/
theorem heatSpatialSeries_left_quotient_mvt {r t x : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hx : 0 < x) (z : ℝ) (b : ℕ) :
    ∃ c ∈ Ioo 0 x, heatSpatialSeries r 0 b t x z / x =
      heatSpatialSeries r 1 b t c z := by
  obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope
    (fun y => heatSpatialSeries r 0 b t y z) (fun y => heatSpatialSeries r 1 b t y z)
    hx (fun y _ => (hasDerivAt_heatSpatialSeries_left hr ht 0 b y z).continuousAt.continuousWithinAt)
    (fun y _ => hasDerivAt_heatSpatialSeries_left hr ht 0 b y z)
  refine ⟨c, hc, ?_⟩
  simpa only [heatSpatialSeries_zero_left, sub_zero] using he.symm

/-- Right boundary differentiation remains valid with simultaneous width/time/position limits. -/
theorem tendsto_heatSpatialSeries_right_quotient {ι : Type*} {l : Filter ι}
    {r t x z : ι → ℝ} {r₀ t₀ z₀ : ℝ}
    (hr : Tendsto r l (𝓝 r₀)) (ht : Tendsto t l (𝓝 t₀))
    (hx : Tendsto x l (𝓝 r₀)) (hz : Tendsto z l (𝓝 z₀))
    (hr₀ : 0 < r₀) (ht₀ : 0 < t₀) (hxr : ∀ᶠ i in l, x i < r i) (b : ℕ) :
    Tendsto (fun i => heatSpatialSeries (r i) 0 b (t i) (x i) (z i) / (r i-x i)) l
      (𝓝 (-heatSpatialSeries r₀ 1 b t₀ r₀ z₀)) := by
  classical
  have hex (i : ι) : ∃ c : ℝ, (0 < r i ∧ 0 < t i ∧ x i < r i) →
      c ∈ Ioo (x i) (r i) ∧ heatSpatialSeries (r i) 0 b (t i) (x i) (z i) / (r i-x i) =
        -heatSpatialSeries (r i) 1 b (t i) c (z i) := by
    by_cases h : 0 < r i ∧ 0 < t i ∧ x i < r i
    · obtain ⟨c, hc, he⟩ := heatSpatialSeries_right_quotient_mvt h.1 h.2.1 h.2.2 (z i) b
      exact ⟨c, fun _ => ⟨hc, he⟩⟩
    · exact ⟨r₀, fun hh => (h hh).elim⟩
  choose c hc using hex
  have hg := (hr.eventually (Ioi_mem_nhds hr₀)).and
    ((ht.eventually (Ioi_mem_nhds ht₀)).and hxr)
  have hct : Tendsto c l (𝓝 r₀) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hx hr
      (hg.mono (fun i hi => (hc i hi).1.1.le)) (hg.mono (fun i hi => (hc i hi).1.2.le))
  exact (tendsto_heatSpatialSeries_joint hr ht hct hz hr₀ ht₀ 1 b).neg.congr'
    (hg.mono (fun i hi => (hc i hi).2.symm))

/-- Left boundary differentiation with simultaneous width/time/position limits. -/
theorem tendsto_heatSpatialSeries_left_quotient {ι : Type*} {l : Filter ι}
    {r t x z : ι → ℝ} {r₀ t₀ z₀ : ℝ}
    (hr : Tendsto r l (𝓝 r₀)) (ht : Tendsto t l (𝓝 t₀))
    (hx : Tendsto x l (𝓝 0)) (hz : Tendsto z l (𝓝 z₀))
    (hr₀ : 0 < r₀) (ht₀ : 0 < t₀) (hxpos : ∀ᶠ i in l, 0 < x i) (b : ℕ) :
    Tendsto (fun i => heatSpatialSeries (r i) 0 b (t i) (x i) (z i) / x i) l
      (𝓝 (heatSpatialSeries r₀ 1 b t₀ 0 z₀)) := by
  classical
  have hex (i : ι) : ∃ c : ℝ, (0 < r i ∧ 0 < t i ∧ 0 < x i) →
      c ∈ Ioo 0 (x i) ∧ heatSpatialSeries (r i) 0 b (t i) (x i) (z i) / x i =
        heatSpatialSeries (r i) 1 b (t i) c (z i) := by
    by_cases h : 0 < r i ∧ 0 < t i ∧ 0 < x i
    · obtain ⟨c, hc, he⟩ := heatSpatialSeries_left_quotient_mvt h.1 h.2.1 h.2.2 (z i) b
      exact ⟨c, fun _ => ⟨hc, he⟩⟩
    · exact ⟨0, fun hh => (h hh).elim⟩
  choose c hc using hex
  have hg := (hr.eventually (Ioi_mem_nhds hr₀)).and
    ((ht.eventually (Ioi_mem_nhds ht₀)).and hxpos)
  have hct : Tendsto c l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hx
      (hg.mono (fun i hi => (hc i hi).1.1.le)) (hg.mono (fun i hi => (hc i hi).1.2.le))
  exact (tendsto_heatSpatialSeries_joint hr ht hct hz hr₀ ht₀ 1 b).congr'
    (hg.mono (fun i hi => (hc i hi).2.symm))

/-- The actual moving-width heat kernel quotient converges to the right boundary flux. -/
theorem tendsto_dirichletHeatKernel_right_quotient {ι : Type*} {l : Filter ι}
    {r t x z : ι → ℝ} {r₀ t₀ z₀ : ℝ}
    (hr : Tendsto r l (𝓝 r₀)) (ht : Tendsto t l (𝓝 t₀))
    (hx : Tendsto x l (𝓝 r₀)) (hz : Tendsto z l (𝓝 z₀))
    (hr₀ : 0 < r₀) (ht₀ : 0 < t₀) (hxr : ∀ᶠ i in l, x i < r i) :
    Tendsto (fun i => dirichletHeatKernel (r i) (t i) (x i) (z i) / (r i-x i)) l
      (𝓝 (heatBoundaryRight r₀ t₀ z₀)) := by
  simpa only [dirichletHeatKernel, heatBoundaryRight, heatSpatialSeries_swap r₀ 1 0]
    using tendsto_heatSpatialSeries_right_quotient hr ht hx hz hr₀ ht₀ hxr 0

/-- The opposite boundary flux quotient converges to the true cross-boundary kernel. -/
theorem tendsto_heatBoundaryRight_left_quotient {ι : Type*} {l : Filter ι}
    {r t x : ι → ℝ} {r₀ t₀ : ℝ}
    (hr : Tendsto r l (𝓝 r₀)) (ht : Tendsto t l (𝓝 t₀))
    (hx : Tendsto x l (𝓝 0)) (hr₀ : 0 < r₀) (ht₀ : 0 < t₀)
    (hxpos : ∀ᶠ i in l, 0 < x i) :
    Tendsto (fun i => heatBoundaryRight (r i) (t i) (x i) / x i) l
      (𝓝 (heatCrossBoundary r₀ t₀)) := by
  simpa only [heatBoundaryRight, heatCrossBoundary, neg_div,
    heatSpatialSeries_swap r₀ 1 1 t₀ 0 r₀]
    using (tendsto_heatSpatialSeries_left_quotient hr ht hx hr hr₀ ht₀ hxpos 1).neg

end BrownianAffine
