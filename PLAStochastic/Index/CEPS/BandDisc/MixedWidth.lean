import PLAStochastic.Index.CEPS.BandDisc.BridgeWidthSeries
import PLAStochastic.Index.CEPS.BandDisc.FirstWidth

/-!
# All discount derivatives of the genuine bridge and second entrance width derivatives

True finite derivative coefficients pay bridge-width holomorphy. The classical
second Hadamard formula then pays entrance holomorphy. Cauchy's estimate on a
killed-scale disc gives explicit class bounds of degrees `2*k+6` and `2*k+9`.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology NNReal

/-- Cauchy's estimate on a disc separated from the boundary of a holomorphy half-plane. -/
theorem cepsBandDisc_halfPlane_cauchy {F : ℂ → ℂ} {b R M : ℝ}
    (hR : 0 < R) (ha : ∀ z : ℂ, b < z.re → AnalyticAt ℂ F z)
    (hb : ∀ z : ℂ, b < z.re → ‖F z‖ ≤ M) {q : ℂ}
    (hq : b + 2 * R ≤ q.re) (k : ℕ) :
    ‖iteratedDeriv k F q‖ ≤ (k.factorial : ℝ) * M / R ^ k := by
  have hball : closedBall q R ⊆ {z : ℂ | b < z.re} := by
    intro z hz
    have hn : ‖z - q‖ ≤ R := mem_closedBall_iff_norm.mp hz
    have hre := Complex.abs_re_le_norm (z - q)
    have hlo := neg_abs_le (z - q).re
    simp only [Complex.sub_re] at hre hlo
    change b < z.re
    linarith
  have hd : DifferentiableOn ℂ F {z : ℂ | b < z.re} := fun z hz =>
    (ha z hz).differentiableAt.differentiableWithinAt
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR
    (hd.diffContOnCl_ball hball) (fun z hz => hb z (hball (sphere_subset_closedBall hz)))

/-- The class constant for a Cauchy upgrade at killed-scale radius `κ/(256*w²)`. -/
def cepsBandDiscCauchyConst (B κ : ℝ) (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * B * (256 / κ) ^ k

lemma cepsBandDisc_cauchy_budget_eq {B κ w : ℝ} (hκ : 0 < κ) (hw : 0 < w)
    (d k : ℕ) :
    (k.factorial : ℝ) * (B * w ^ d) / (κ / (256 * w ^ 2)) ^ k =
      cepsBandDiscCauchyConst B κ k * w ^ (2 * k + d) := by
  unfold cepsBandDiscCauchyConst
  simp only [div_pow, mul_pow, pow_add, pow_mul]
  field_simp

/-- Every genuine bridge-width derivative has every genuine complex discount derivative. -/
theorem cepsBandDisc_bridge_first_width_iteratedDeriv_le {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    (hd : Differentiable ℝ f) {K : ℝ≥0} (hK : ∀ x, |deriv f x| ≤ K)
    {w l : ℝ} (hw : 4 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (128 * w ^ 2)) ≤ q.re) (k : ℕ) :
    ‖iteratedDeriv k (fun z : ℂ => deriv (cepsBridgeSeries ν f β a z) l) q‖ ≤
      cepsBandDiscCauchyConst (cepsBandPinWidthConst D vlo vhi K) (krKappa D vlo vhi) k *
        w ^ (2 * k + 6) := by
  have hκ := krKappa_pos hD hvlo hvhi
  have hw0 : 0 < w := by linarith
  let R := krKappa D vlo vhi / (256 * w ^ 2)
  have hR : 0 < R := by dsimp [R]; positivity
  have hqR : -(krKappa D vlo vhi / (64 * w ^ 2)) + 2 * R ≤ q.re := by
    have he : -(krKappa D vlo vhi / (64 * w ^ 2)) + 2 * R =
        -(krKappa D vlo vhi / (128 * w ^ 2)) := by dsimp [R]; ring
    rwa [he]
  have h := cepsBandDisc_halfPlane_cauchy hR
    (fun z hz => cepsBandDisc_bridge_first_width_analyticAt hD hθ hvlo hvhi hν hf
      hd hK hw hl hlw β ha hz)
    (fun z hz => (cepsBand_bridgeSeries_first_width hD hθ hvlo hvhi hν hf
      hd hK hw hl hlw β ha hz.le).2) hqR k
  exact h.trans_eq (cepsBandDisc_cauchy_budget_eq hκ hw0 6 k)

/-- The genuine second width derivative is holomorphic in the discount.
Only pointwise differentiability and a bound on the density derivative are required. -/
theorem cepsBandDisc_bottomSurv_second_width_analyticAt {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    (hd : Differentiable ℝ f) {K : ℝ≥0} (hK : ∀ x, |deriv f x| ≤ K)
    {w l : ℝ} (hw : 4 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (64 * w ^ 2)) < q.re) :
    AnalyticAt ℂ (fun z : ℂ => deriv (deriv (cepsBottomSurv ν β a z)) l) q := by
  have hκ := krKappa_pos hD hvlo hvhi
  have hw2 : 2 ≤ w := by linarith
  have hq32 : -(krKappa D vlo vhi / (32 * w ^ 2)) ≤ q.re := by
    have hb : krKappa D vlo vhi / (64 * w ^ 2) ≤ krKappa D vlo vhi / (32 * w ^ 2) := by
      apply div_le_div_of_nonneg_left hκ.le (by positivity)
      nlinarith
    linarith
  have ha' : 1 / 2 ≤ |-a| := by simpa only [abs_neg] using ha
  let V := fun z : ℂ => deriv (cepsBridgeSeries ν f β a z) l
  let U := fun z : ℂ => cepsBridgeSeries ν f β a z l
  let T := fun z : ℂ => cepsTopSurv ν β a z l
  let U' := fun z : ℂ => cepsBridgeSeries ν f (-β) (-a) z l
  let B := fun z : ℂ => cepsBottomSurv ν β a z l
  have hV : AnalyticAt ℂ V q := cepsBandDisc_bridge_first_width_analyticAt
    hD hθ hvlo hvhi hν hf hd hK hw hl hlw β ha hq
  have hU : AnalyticAt ℂ U q := cepsBandDisc_bridgeSeries_analyticAt
    hD hθ hvlo hvhi hν hf hw2 hl hlw β ha hq32
  have hT : AnalyticAt ℂ T q := cepsBandDisc_survival_analyticAt
    hD hθ hvlo hvhi hν hw2 hl hlw β ha hq32 l
  have hU' : AnalyticAt ℂ U' q := cepsBandDisc_bridgeSeries_analyticAt
    hD hθ hvlo hvhi hν hf hw2 hl hlw (-β) ha' hq32
  have hB : AnalyticAt ℂ B q := cepsBandDisc_survival_analyticAt
    hD hθ hvlo hvhi hν hw2 hl hlw β ha hq32 0
  have he : (fun z : ℂ => V z * T z + U z * (U' z * B z)) =ᶠ[𝓝 q]
      (fun z : ℂ => deriv (deriv (cepsBottomSurv ν β a z)) l) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hq] with z hz
    have hsecond := (cepsBand_bottomSurv_second_width hD hθ hvlo hvhi hν hf
      hd hK hw hl hlw β ha hz.le).1.deriv
    have htopfun : cepsTopSurv ν β a z = cepsBottomSurv ν (-β) (-a) z :=
      funext (cepsBand_topSurv_eq_reverse ν β a z)
    have htop := (cepsBand_bottomSurv_first_width hD hθ hvlo hvhi hν hf
      (cepsBand_density_lipschitz_of_deriv hd hK) hw hl hlw (-β) ha' hz.le).1.deriv
    rw [← htopfun] at htop
    rw [hsecond, htop, show cepsTopSurv ν (-β) (-a) z l = cepsBottomSurv ν β a z l by
      simpa only [neg_neg] using cepsBand_topSurv_eq_reverse ν (-β) (-a) z l]
  exact ((hV.mul hT).add (hU.mul (hU'.mul hB))).congr he

/-- All complex discount derivatives of the actual second width derivative have a class budget. -/
theorem cepsBandDisc_bottomSurv_second_width_iteratedDeriv_le {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    (hd : Differentiable ℝ f) {K : ℝ≥0} (hK : ∀ x, |deriv f x| ≤ K)
    {w l : ℝ} (hw : 4 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (128 * w ^ 2)) ≤ q.re) (k : ℕ) :
    ‖iteratedDeriv k (fun z : ℂ => deriv (deriv (cepsBottomSurv ν β a z)) l) q‖ ≤
      cepsBandDiscCauchyConst (cepsBandSecondWidthConst D vlo vhi K) (krKappa D vlo vhi) k *
        w ^ (2 * k + 9) := by
  have hκ := krKappa_pos hD hvlo hvhi
  have hw0 : 0 < w := by linarith
  let R := krKappa D vlo vhi / (256 * w ^ 2)
  have hR : 0 < R := by dsimp [R]; positivity
  have hqR : -(krKappa D vlo vhi / (64 * w ^ 2)) + 2 * R ≤ q.re := by
    have he : -(krKappa D vlo vhi / (64 * w ^ 2)) + 2 * R =
        -(krKappa D vlo vhi / (128 * w ^ 2)) := by dsimp [R]; ring
    rwa [he]
  have h := cepsBandDisc_halfPlane_cauchy hR
    (fun z hz => cepsBandDisc_bottomSurv_second_width_analyticAt hD hθ hvlo hvhi hν hf
      hd hK hw hl hlw β ha hz)
    (fun z hz => (cepsBand_bottomSurv_second_width hD hθ hvlo hvhi hν hf
      hd hK hw hl hlw β ha hz.le).2) hqR k
  exact h.trans_eq (cepsBandDisc_cauchy_budget_eq hκ hw0 9 k)

/-- Reflection supplies the same genuine second width derivative budget for the top entrance. -/
theorem cepsBandDisc_topSurv_second_width_iteratedDeriv_le {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    (hd : Differentiable ℝ f) {K : ℝ≥0} (hK : ∀ x, |deriv f x| ≤ K)
    {w l : ℝ} (hw : 4 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (128 * w ^ 2)) ≤ q.re) (k : ℕ) :
    ‖iteratedDeriv k (fun z : ℂ => deriv (deriv (cepsTopSurv ν β a z)) l) q‖ ≤
      cepsBandDiscCauchyConst (cepsBandSecondWidthConst D vlo vhi K) (krKappa D vlo vhi) k *
        w ^ (2 * k + 9) := by
  have he : (fun z : ℂ => deriv (deriv (cepsTopSurv ν β a z)) l) =
      (fun z : ℂ => deriv (deriv (cepsBottomSurv ν (-β) (-a) z)) l) := by
    funext z
    have hfun : cepsTopSurv ν β a z = cepsBottomSurv ν (-β) (-a) z :=
      funext (cepsBand_topSurv_eq_reverse ν β a z)
    rw [hfun]
  rw [he]
  exact cepsBandDisc_bottomSurv_second_width_iteratedDeriv_le hD hθ hvlo hvhi hν hf hd hK
    hw hl hlw (-β) (by simpa only [abs_neg] using ha) hq k

end
end PGM
