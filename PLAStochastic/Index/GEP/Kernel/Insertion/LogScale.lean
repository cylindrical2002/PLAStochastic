import PLAStochastic.Index.GEP.Kernel.Insertion.WidthScale
import PLAStochastic.Index.GEP.Kernel.FarSlope.LogCutoff
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The actual near insertion on a logarithmically growing spatial interval -/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- An exponential width error beats every fixed polynomial budget. -/
theorem krInsertion_exp_width_eventually {c : ℝ} (hc : 0 < c) (p B : ℕ) :
    ∀ᶠ w : ℝ in atTop, 1 ≤ w ∧ w^p*Real.exp (-c*w) ≤ 1/w^B := by
  have ht : Tendsto (fun w : ℝ => w^(p+B)*Real.exp (-c*w)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p+B : ℕ) c hc
  filter_upwards [eventually_ge_atTop (1 : ℝ),ht.eventually (eventually_lt_nhds zero_lt_one)] with w hw hb
  refine ⟨hw,(le_div_iff₀ (pow_pos (by linarith : 0 < w) B)).2 ?_⟩
  have he : w^p*Real.exp (-c*w)*w^B = w^(p+B)*Real.exp (-c*w) := by rw [pow_add]; ring
  rw [he]
  exact hb.le

set_option maxHeartbeats 1200000 in
/-- The actual normalized near insertion has the original AL scale with a fixed
logarithmic power eight; the error order is arbitrary and homogeneous in M. -/
theorem krInsertion_coefficient_log_scale (D θ vlo vhi K L α b : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    (hα : 0 < α) (hb : 0 < b) (B : ℕ) :
    ∃ C w0 : ℝ, 0 < C ∧ 96 ≤ w0 ∧
    ∀ (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {w : ℝ} (_hw : w0 ≤ w)
      {S : Set ℝ} (_hS : MeasurableSet S) (_hne : S.Nonempty)
      (_hSI : S ⊆ Ioo (1/2 : ℝ) 2)
      (_H : ∀ a ∈ S, KrBand D θ vlo vhi K L ν f w (α*Real.log w) a 1 a)
      (up outerUp : Bool) {ε M : ℝ} (_hε0 : 0 ≤ ε)
      (_hε : ε ≤ krEps D vlo vhi) (_hM : 0 ≤ M)
      {W : ℕ → ℕ → (ℕ × ℕ × ℕ) → ℝ → (ℕ → ℝ) → ℝ}
      (_hW : ∀ l r t, Measurable (fun p : ℝ × (ℕ → ℝ) => W l r t p.1 p.2))
      (_hWB : ∀ a ∈ S, ∀ l r t g, krInsertionOuter w outerUp l r t a g ≠ 0 →
        |W l r t a g| ≤ (M/w^2)*Real.exp (ε*((t.1 : ℝ)+l+r+t.2.1+t.2.2+2)/w^2)),
    KernelApproxLip (b*Real.log w) (M*(C*Real.sqrt w*Real.log w^8)) (M*(C/w^B))
      (fun x => ∫ a in S, ∑' q : ℕ × ℕ,
        krInsertionCoefficient ν f w up outerUp W q.1 q.2 a*
        kernelMarkedFullDens (Icc 0 w) ν f 1 a x q.1 q.2
          (if up then 0 else w) (if up then w else 0)) := by
  obtain ⟨c,C,hc,hC,hwidth⟩ := krInsertion_coefficient_width_scale D θ vlo vhi K L hD hθ hvlo hvhi
  have he := krInsertion_exp_width_eventually hc 9 B
  have ha := kernel_log_cutoff_eventually hα (show (0 : ℝ) < 1 by norm_num)
  have hr := kernel_log_cutoff_eventually hb (show (0 : ℝ) < 1/8 by norm_num)
  have hl : ∀ᶠ w : ℝ in atTop, 1 ≤ Real.log w :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  obtain ⟨w0,hw0⟩ := eventually_atTop.mp (he.and (ha.and (hr.and hl)))
  refine ⟨2*C*(1+α)^7,max 96 w0,by positivity,le_max_left _ _,?_⟩
  intro ν f w hw S hS hne hSI H up outerUp ε M hε0 hε hM W hW hWB
  have hw96 : 96 ≤ w := (le_max_left _ _).trans hw
  obtain ⟨⟨hw1,hexp⟩,hAw,hRw,hlog⟩ := hw0 w ((le_max_right _ _).trans hw)
  have hwpos : 0 < w := by linarith
  have hlog0 : 0 ≤ Real.log w := by linarith
  have hA : 0 ≤ α*Real.log w := mul_nonneg hα.le hlog0
  have hR : 0 ≤ b*Real.log w := mul_nonneg hb.le hlog0
  have hn := hwidth ν hw96 hS hne hSI H (by simpa only [one_mul] using hAw.2.2)
    up outerUp hR (by nlinarith [hRw.2.2]) hε0 hε (div_nonneg hM (sq_nonneg _)) hW hWB
  have hAlog : 1+α*Real.log w ≤ (1+α)*Real.log w := by nlinarith only [hlog]
  have hlg : 1+Real.log w ≤ 2*Real.log w := by linarith
  have hlogw : Real.log w ≤ w := (Real.log_le_sub_one_of_pos hwpos).trans (by linarith)
  have hAw' : 1+α*Real.log w ≤ (1+α)*w :=
    hAlog.trans (mul_le_mul_of_nonneg_left hlogw (by positivity))
  apply hn.mono
  · calc
      _ = C*M*(1+α*Real.log w)^7*Real.sqrt w*(1+Real.log w) := by field_simp
      _ ≤ C*M*((1+α)*Real.log w)^7*Real.sqrt w*(2*Real.log w) := by gcongr
      _ = _ := by ring
  · calc
      _ = C*M*(1+α*Real.log w)^7*w^2*Real.exp (-c*w) := by field_simp
      _ ≤ C*M*((1+α)*w)^7*w^2*Real.exp (-c*w) := by gcongr
      _ = C*M*(1+α)^7*(w^9*Real.exp (-c*w)) := by ring
      _ ≤ C*M*(1+α)^7*(1/w^B) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ M*((2*C*(1+α)^7)/w^B) := by
        have hp : 0 ≤ C*M*(1+α)^7*(1/w^B) := by positivity
        have hh : C*M*(1+α)^7*(1/w^B) ≤
            C*M*(1+α)^7*(1/w^B)+C*M*(1+α)^7*(1/w^B) := le_add_of_nonneg_right hp
        exact hh.trans_eq (by ring)

end
end PGM
