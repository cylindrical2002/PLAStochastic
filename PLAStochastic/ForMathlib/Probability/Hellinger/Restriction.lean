import PLAStochastic.ForMathlib.Probability.Hellinger.Density

/-!
# Event bounds from Hellinger distance

Restriction to a measurable event is a contraction on the square-root `L²`
vectors. Consequently, square roots of event probabilities differ by at most
the full Hellinger distance. This is the event bound used for uncensoring a
finite-window endpoint block.
-/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory Set

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Probability mass of an event, expressed relative to the fixed reference measure. -/
def mass (p : HellingerDensity μ) (s : Set α) : ℝ := ∫ x in s, p.density x ∂μ

theorem mass_nonneg (p : HellingerDensity μ) (s : Set α) : 0 ≤ p.mass s :=
  integral_nonneg p.nonneg

def rootOn (p : HellingerDensity μ) (s : Set α) (hs : MeasurableSet s) : Lp ℝ 2 μ :=
  (p.sqrt_memLp.indicator hs).toLp (s.indicator fun x => Real.sqrt (p.density x))

theorem rootOn_ae (p : HellingerDensity μ) (s : Set α) (hs : MeasurableSet s) :
    p.rootOn s hs =ᵐ[μ] s.indicator (fun x => Real.sqrt (p.density x)) :=
  MemLp.coeFn_toLp _

theorem norm_rootOn_sq (p : HellingerDensity μ) (s : Set α) (hs : MeasurableSet s) :
    ‖p.rootOn s hs‖ ^ 2 = p.mass s := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, mass, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [p.rootOn_ae s hs] with x hx
  rw [hx]
  by_cases hxs : x ∈ s
  · simp only [indicator_of_mem hxs, RCLike.inner_apply, conj_trivial]
    exact Real.mul_self_sqrt (p.nonneg x)
  · simp [indicator_of_notMem hxs]

theorem norm_rootOn (p : HellingerDensity μ) (s : Set α) (hs : MeasurableSet s) :
    ‖p.rootOn s hs‖ = Real.sqrt (p.mass s) := by
  rw [← p.norm_rootOn_sq s hs, Real.sqrt_sq (norm_nonneg _)]

theorem dist_rootOn_le (p q : HellingerDensity μ) (s : Set α) (hs : MeasurableSet s) :
    dist (p.rootOn s hs) (q.rootOn s hs) ≤ p.hellinger q := by
  rw [dist_eq_norm, hellinger, dist_eq_norm]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (p.rootOn s hs) (q.rootOn s hs),
    Lp.coeFn_sub p.root q.root, p.rootOn_ae s hs, q.rootOn_ae s hs,
    p.root_ae, q.root_ae] with x hsub hfull hp hq hpr hqr
  simp only [hsub, hfull, Pi.sub_apply, hp, hq, hpr, hqr]
  by_cases hx : x ∈ s
  · simp only [indicator_of_mem hx, le_refl]
  · simp only [indicator_of_notMem hx, sub_self, norm_zero]
    exact norm_nonneg _

/-- Hellinger controls square roots of probabilities of every measurable event. -/
theorem abs_sqrt_mass_sub_le (p q : HellingerDensity μ) (s : Set α)
    (hs : MeasurableSet s) :
    |Real.sqrt (p.mass s) - Real.sqrt (q.mass s)| ≤ p.hellinger q := by
  rw [← norm_rootOn p s hs, ← norm_rootOn q s hs]
  exact (abs_norm_sub_norm_le _ _).trans
    (by simpa only [dist_eq_norm] using dist_rootOn_le p q s hs)

theorem sqrt_mass_le (p q : HellingerDensity μ) (s : Set α)
    (hs : MeasurableSet s) :
    Real.sqrt (p.mass s) ≤ Real.sqrt (q.mass s) + p.hellinger q := by
  have h := (abs_le.mp (abs_sqrt_mass_sub_le p q s hs)).2
  linarith

/-- A small reference event remains small after Hellinger comparison. -/
theorem mass_le_sq_sqrt_add (p q : HellingerDensity μ) (s : Set α)
    (hs : MeasurableSet s) :
    p.mass s ≤ (Real.sqrt (q.mass s) + p.hellinger q) ^ 2 := by
  have h := sqrt_mass_le p q s hs
  have hp := Real.sq_sqrt (p.mass_nonneg s)
  have hnon : 0 ≤ Real.sqrt (p.mass s) := Real.sqrt_nonneg _
  nlinarith [Real.sqrt_nonneg (q.mass s), hellinger_nonneg p q]

end

end ProbabilityTheory.HellingerDensity
