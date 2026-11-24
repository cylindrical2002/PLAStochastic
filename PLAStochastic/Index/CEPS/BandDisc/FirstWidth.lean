import PLAStochastic.Index.CEPS.BandDisc.Analytic

/-!
# Mixed discount derivatives of the genuine first width derivative

The already proved width Hadamard derivative is used without repeating its proof.
Local equality with the product of two holomorphic resolvents pays the mixed
complex derivatives; the explicit Leibniz sum gives degree `2*k+6`.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology NNReal

/-- A class constant for the Leibniz convolution of the bridge and entrance budgets. -/
def cepsBandDiscFirstWidthConst (D vlo vhi : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1), (k.choose i : ℝ) *
    cepsBandMomentConst (cepsBandPinDecayConst D vlo vhi) (krKappa D vlo vhi) i *
    cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) (k - i)

/-- All complex discount derivatives of the actual first width derivative have class bounds.
The width derivative is classical at both ends of the closed width window. -/
theorem cepsBandDisc_bottomSurv_first_width_iteratedDeriv_le {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {f : ℝ → ℝ} (hf : CepsGapDensity ν f D) {K : ℝ≥0} (hLip : LipschitzWith K f)
    {w l : ℝ} (hw : 4 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (128 * w ^ 2)) ≤ q.re) (k : ℕ) :
    ‖iteratedDeriv k (fun z : ℂ => deriv (cepsBottomSurv ν β a z) l) q‖ ≤
      cepsBandDiscFirstWidthConst D vlo vhi k * w ^ (2 * k + 6) := by
  have hκ := krKappa_pos hD hvlo hvhi
  have hw0 : 0 < w := by linarith
  have hw2 : 2 ≤ w := by linarith
  have hmargin : -(krKappa D vlo vhi / (64 * w ^ 2)) < q.re := by
    have hm : krKappa D vlo vhi / (128 * w ^ 2) <
        krKappa D vlo vhi / (64 * w ^ 2) := by
      apply div_lt_div_of_pos_left hκ (by positivity)
      nlinarith [sq_pos_of_pos hw0]
    linarith
  have hq32 : -(krKappa D vlo vhi / (32 * w ^ 2)) ≤ q.re := by
    have hm : krKappa D vlo vhi / (64 * w ^ 2) ≤
        krKappa D vlo vhi / (32 * w ^ 2) := by
      apply div_le_div_of_nonneg_left hκ.le (by positivity)
      nlinarith [sq_pos_of_pos hw0]
    linarith
  let U : ℂ → ℂ := fun z => cepsBridgeSeries ν f β a z l
  let H : ℂ → ℂ := fun z => cepsTopSurv ν β a z l
  have he : (fun z : ℂ => deriv (cepsBottomSurv ν β a z) l) =ᶠ[𝓝 q]
      (fun z => U z * H z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmargin]
      with z hz
    exact (cepsBand_bottomSurv_first_width hD hθ hvlo hvhi hν hf hLip hw hl hlw β ha hz.le).1.deriv
  have hU : AnalyticAt ℂ U q :=
    cepsBandDisc_bridgeSeries_analyticAt hD hθ hvlo hvhi hν hf hw2 hl hlw β ha hq32
  have hH : AnalyticAt ℂ H q :=
    cepsBandDisc_survival_analyticAt hD hθ hvlo hvhi hν hw2 hl hlw β ha hq32 l
  rw [he.iteratedDeriv_eq k, iteratedDeriv_fun_mul hU.contDiffAt hH.contDiffAt]
  calc
    _ ≤ ∑ i ∈ range (k + 1), ‖(k.choose i : ℂ) *
        iteratedDeriv i U q * iteratedDeriv (k - i) H q‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range (k + 1), ((k.choose i : ℝ) *
        cepsBandMomentConst (cepsBandPinDecayConst D vlo vhi) (krKappa D vlo vhi) i *
        cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) (k - i)) *
          w ^ (2 * k + 6) := by
      apply sum_le_sum
      intro i hi
      have hik : i ≤ k := by simpa using mem_range.mp hi
      have hUi := cepsBandDisc_bridgeSeries_iteratedDeriv_le hD hθ hvlo hvhi hν hf
        hw2 hl hlw β ha hq32 i
      have hHi := cepsBandDisc_topSurv_iteratedDeriv_le hD hθ hvlo hvhi hν
        hw2 hl hlw β ha hq32 (k - i)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc
        _ ≤ ((k.choose i : ℝ) *
            (cepsBandMomentConst (cepsBandPinDecayConst D vlo vhi) (krKappa D vlo vhi) i *
              w ^ (2 * i + 3))) *
            (cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) (k - i) *
              w ^ (2 * (k - i) + 3)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hUi (Nat.cast_nonneg _)) hHi
            (norm_nonneg _) (by
              unfold cepsBandMomentConst cepsBandPinDecayConst cepsBandDecayConst
              positivity)
        _ = _ := by
          have hepow : w ^ (2 * i + 3) * w ^ (2 * (k - i) + 3) = w ^ (2 * k + 6) := by
            rw [← pow_add]
            congr 1
            omega
          calc _ = ((k.choose i : ℝ) *
              cepsBandMomentConst (cepsBandPinDecayConst D vlo vhi) (krKappa D vlo vhi) i *
              cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) (k - i)) *
                (w ^ (2 * i + 3) * w ^ (2 * (k - i) + 3)) := by ring
            _ = _ := by rw [hepow]
    _ = _ := by rw [← sum_mul]; rfl

/-- Reflection pays the same mixed derivative budget for the top entrance. -/
theorem cepsBandDisc_topSurv_first_width_iteratedDeriv_le {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {f : ℝ → ℝ} (hf : CepsGapDensity ν f D) {K : ℝ≥0} (hLip : LipschitzWith K f)
    {w l : ℝ} (hw : 4 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (128 * w ^ 2)) ≤ q.re) (k : ℕ) :
    ‖iteratedDeriv k (fun z : ℂ => deriv (cepsTopSurv ν β a z) l) q‖ ≤
      cepsBandDiscFirstWidthConst D vlo vhi k * w ^ (2 * k + 6) := by
  have he : (fun z : ℂ => deriv (cepsTopSurv ν β a z) l) =
      (fun z : ℂ => deriv (cepsBottomSurv ν (-β) (-a) z) l) := by
    funext z
    have hwfun : cepsTopSurv ν β a z = cepsBottomSurv ν (-β) (-a) z :=
      funext (cepsBand_topSurv_eq_reverse ν β a z)
    rw [hwfun]
  rw [he]
  exact cepsBandDisc_bottomSurv_first_width_iteratedDeriv_le hD hθ hvlo hvhi hν hf hLip
    hw hl hlw (-β) (by simpa only [abs_neg] using ha) hq k

end
end PGM
