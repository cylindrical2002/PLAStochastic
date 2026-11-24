import PLAStochastic.Index.CEPS.Band.SecondWidth
import PLAStochastic.Index.CEPS.Band.UnitDifferentiability
import PLAStochastic.Index.CEPS.Band.FiniteWidthDecay
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Pointwise classical second width derivatives

Only differentiability of the density and a uniform bound on its first derivative
are added to the killed-band assumptions. Finite bridges are differentiable after
rescaling their intermediate positions. Summable killed-gap width moduli justify
the infinite derivative series. The second survival derivative follows by the
product rule in the Hadamard identity, including at both ends of the width window.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

/-- The derivative bound from a Lipschitz constant on a closed nondegenerate interval
also holds at either endpoint, provided the classical derivative really exists. -/
theorem cepsBand_norm_deriv_le_closed {F : ℝ → ℂ} {C : ℝ≥0} {a b l : ℝ}
    (hab : a < b) (hl : l ∈ Icc a b) (hLip : LipschitzOnWith C F (Icc a b))
    (hd : DifferentiableAt ℝ F l) : ‖deriv F l‖ ≤ C := by
  have hb : ∀ x ∈ Icc a b, x ≠ l → ‖slope F l x‖ ≤ C := by
    intro x hx hxl
    rw [slope_def_module, norm_smul, norm_inv, Real.norm_eq_abs]
    calc
      _ ≤ |x - l|⁻¹ * ((C : ℝ) * |x - l|) := by
        exact mul_le_mul_of_nonneg_left (by
          simpa only [Real.norm_eq_abs] using hLip.norm_sub_le hx hl) (by positivity)
      _ = C := by
        have hne : |x - l| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hxl)
        field_simp
  by_cases hlt : l < b
  · apply le_of_tendsto (hd.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE l)).norm
    filter_upwards [Icc_mem_nhdsGT_of_mem (show l ∈ Ico a b from ⟨hl.1, hlt⟩),
      self_mem_nhdsWithin (s := Ioi l) (a := l)] with x hx hxl
    exact hb x hx (ne_of_gt hxl)
  · have hlb : l = b := le_antisymm hl.2 (not_lt.mp hlt)
    apply le_of_tendsto (hd.hasDerivAt.tendsto_slope.mono_left (nhdsLT_le_nhdsNE l)).norm
    filter_upwards [Icc_mem_nhdsLT_of_mem (show l ∈ Ioc a b from ⟨by simpa [hlb] using hab, hl.2⟩),
      self_mem_nhdsWithin (s := Iio l) (a := l)] with x hx hxl
    exact hb x hx (ne_of_lt hxl)

/-- The actual bridge is pointwise differentiable in the open width window.
The proof uses a summable bound on the actual finite derivatives. -/
theorem cepsBand_bridgeSeries_differentiableAt_interior {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    (hd : Differentiable ℝ f) {K : ℝ≥0} (hK : ∀ x, |deriv f x| ≤ K)
    {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 < l) (hlw : l < 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) :
    DifferentiableAt ℝ (cepsBridgeSeries ν f β a q) l := by
  have hLip := cepsBand_density_lipschitz_of_deriv hd hK
  obtain ⟨M, hM, hfinite⟩ := cepsBand_pin_finite_lipschitz hD hθ hvlo hvhi hν hf hLip hw β ha hq
  let g := fun n : ℕ => fun t : ℝ => Complex.exp (-q * ((n : ℂ) + 1)) *
    (krDens (Icc 0 t) ν f β a (n + 1) 0 t : ℂ)
  have ha0 : a ≠ 0 := abs_pos.mp (by linarith : 0 < |a|)
  have hdg : ∀ n t, t ∈ Ioo (w / 2) (2 * w) → HasDerivAt (g n) (deriv (g n) t) t := by
    intro n t ht
    have hp := hf.cepsBand_pin_differentiableAt hd hK β ha0 (by linarith [ht.1] : 0 < t) n
    exact ((hp.hasDerivAt.ofReal_comp).const_mul _).differentiableAt.hasDerivAt
  have hg' : ∀ n t, t ∈ Ioo (w / 2) (2 * w) → ‖deriv (g n) t‖ ≤ (M n : ℝ) := by
    intro n t ht
    exact norm_deriv_le_of_lipschitzOn (Icc_mem_nhds ht.1 ht.2) (hfinite n)
  have hsum := (cepsBand_summable_density_norm hD hθ hvlo hvhi hν hf hw
    hl.le hlw.le β ha hq 0 l).of_norm
  exact (hasDerivAt_tsum_of_isPreconnected hM isOpen_Ioo isPreconnected_Ioo hdg hg'
    ⟨hl, hlw⟩ hsum ⟨hl, hlw⟩).differentiableAt

/-- Pointwise bridge differentiability includes the two ends of the closed window. -/
theorem cepsBand_bridgeSeries_differentiableAt {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    (hd : Differentiable ℝ f) {K : ℝ≥0} (hK : ∀ x, |deriv f x| ≤ K)
    {w l : ℝ} (hw : 4 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (64 * w ^ 2)) ≤ q.re) :
    DifferentiableAt ℝ (cepsBridgeSeries ν f β a q) l := by
  have hl0 : 0 < l := by linarith
  have hql : -(krKappa D vlo vhi / (16 * l ^ 2)) ≤ q.re := by
    have hb : krKappa D vlo vhi / (64 * w ^ 2) ≤ krKappa D vlo vhi / (16 * l ^ 2) := by
      apply div_le_div_of_nonneg_left (krKappa_pos hD hvlo hvhi).le (by positivity)
      nlinarith
    linarith
  exact cepsBand_bridgeSeries_differentiableAt_interior hD hθ hvlo hvhi hν hf hd hK
    (w := l) (by linarith : 2 ≤ l) (by linarith) (by linarith) β ha hql

/-- A genuine bridge derivative has the same polynomial bound as its width modulus. -/
theorem cepsBand_bridgeSeries_first_width {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    (hd : Differentiable ℝ f) {K : ℝ≥0} (hK : ∀ x, |deriv f x| ≤ K)
    {w l : ℝ} (hw : 4 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (64 * w ^ 2)) ≤ q.re) :
    HasDerivAt (cepsBridgeSeries ν f β a q) (deriv (cepsBridgeSeries ν f β a q) l) l ∧
      ‖deriv (cepsBridgeSeries ν f β a q) l‖ ≤ cepsBandPinWidthConst D vlo vhi K * w ^ 6 := by
  have hdU := cepsBand_bridgeSeries_differentiableAt hD hθ hvlo hvhi hν hf hd hK hw hl hlw β ha hq
  refine ⟨hdU.hasDerivAt, ?_⟩
  exact cepsBand_norm_deriv_le_closed (by linarith) ⟨hl, hlw⟩
    (cepsBand_bridgeSeries_lipschitz hD hθ hvlo hvhi hν hf
      (cepsBand_density_lipschitz_of_deriv hd hK) hw β ha hq) hdU

/-- Every width in the closed window has a classical second derivative.
Its expression differentiates the true Hadamard factors. -/
theorem cepsBand_bottomSurv_second_width {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    (hd : Differentiable ℝ f) {K : ℝ≥0} (hK : ∀ x, |deriv f x| ≤ K)
    {w l : ℝ} (hw : 4 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (64 * w ^ 2)) ≤ q.re) :
    HasDerivAt (deriv (cepsBottomSurv ν β a q))
      (deriv (cepsBridgeSeries ν f β a q) l * cepsTopSurv ν β a q l +
        cepsBridgeSeries ν f β a q l * deriv (cepsTopSurv ν β a q) l) l ∧
    ‖deriv (deriv (cepsBottomSurv ν β a q)) l‖ ≤
      cepsBandSecondWidthConst D vlo vhi K * w ^ 9 := by
  have hLip := cepsBand_density_lipschitz_of_deriv hd hK
  have hdU := cepsBand_bridgeSeries_differentiableAt hD hθ hvlo hvhi hν hf hd hK hw hl hlw β ha hq
  have ha' : 1 / 2 ≤ |-a| := by simpa only [abs_neg] using ha
  have heq : cepsTopSurv ν β a q = cepsBottomSurv ν (-β) (-a) q :=
    funext (cepsBand_topSurv_eq_reverse ν β a q)
  have hdH : DifferentiableAt ℝ (cepsTopSurv ν β a q) l := by
    rw [heq]
    exact (cepsBand_bottomSurv_first_width hD hθ hvlo hvhi hν hf hLip hw hl hlw (-β) ha' hq).1.differentiableAt
  have hprod := hdU.hasDerivAt.mul hdH.hasDerivAt
  have hl0 : 0 < l := by linarith
  have hql : -(krKappa D vlo vhi / (16 * l ^ 2)) ≤ q.re := by
    have hb : krKappa D vlo vhi / (64 * w ^ 2) ≤ krKappa D vlo vhi / (16 * l ^ 2) := by
      apply div_le_div_of_nonneg_left (krKappa_pos hD hvlo hvhi).le (by positivity)
      nlinarith
    linarith
  have hevent : deriv (cepsBottomSurv ν β a q) =ᶠ[nhds l]
      (fun t => cepsBridgeSeries ν f β a q t * cepsTopSurv ν β a q t) := by
    filter_upwards [Ioo_mem_nhds (show l / 2 < l by linarith) (show l < 2 * l by linarith)] with t ht
    exact (cepsBand_bottomSurv_hasDerivAt_interior hD hθ hvlo hvhi hν hf hLip
      (w := l) (by linarith : 2 ≤ l) ht.1 ht.2 β ha hql).deriv
  have hsecond := hprod.congr_of_eventuallyEq hevent
  refine ⟨hsecond, ?_⟩
  exact cepsBand_norm_deriv_le_closed (by linarith) ⟨hl, hlw⟩
    (cepsBand_bottomSurv_deriv_lipschitz hD hθ hvlo hvhi hν hf hLip hw β ha hq)
    hsecond.differentiableAt

end
end PGM
