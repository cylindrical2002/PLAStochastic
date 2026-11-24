import PLAStochastic.Index.GEP.Kernel.FarSlope.Annulus

/-!
# Logarithmic cutoffs after the polynomial budgets are fixed

The cutoff coefficient can depend on the requested spatial window and error
order. Polynomial width losses are absorbed without changing the tail power
or the output test weight.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

theorem kernel_log_cutoff_bound {lam q b : ℝ} (hlam : 0 ≤ lam) (hq : 0 < q) (hb : 0 < b)
    (p B : ℕ) :
    ∃ α : ℝ, 0 < α ∧ ∀ w x : ℝ, 1 ≤ w → x ≤ b*Real.log w →
      w^p*Real.exp (lam*x-q*(α*Real.log w)) ≤ 1/w^B := by
  let α := ((p : ℝ)+(B : ℝ)+lam*b+1)/q
  have hα : 0 < α := by dsimp [α]; positivity
  refine ⟨α,hα,fun w x hw hx => ?_⟩
  have hw0 : 0 < w := by linarith
  have hlw := Real.log_nonneg hw
  have he (n : ℕ) : w^n = Real.exp ((n : ℝ)*Real.log w) := by
    rw [Real.exp_nat_mul,Real.exp_log hw0]
  rw [he p,← Real.exp_add]
  calc
    _ ≤ Real.exp (-(B : ℝ)*Real.log w) := by
      apply Real.exp_le_exp.mpr
      have hx' := mul_le_mul_of_nonneg_left hx hlam
      have hqa : q*α = (p : ℝ)+(B : ℝ)+lam*b+1 := by dsimp [α]; field_simp
      have he' : q*(α*Real.log w) = (q*α)*Real.log w := by ring
      rw [he',hqa]
      nlinarith
    _ = 1/w^B := by rw [neg_mul,Real.exp_neg,← he B,one_div]

theorem kernel_log_cutoff_eventually {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) :
    ∀ᶠ w : ℝ in atTop, 1 ≤ w ∧ 1 ≤ α*Real.log w ∧ α*Real.log w ≤ δ*w := by
  have hlim : Tendsto (fun w : ℝ => α*(Real.log w/w)) atTop (𝓝 0) := by
    simpa only [mul_zero, id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul α
  have hsmall : ∀ᶠ w : ℝ in atTop, α*(Real.log w/w) < δ :=
    hlim.eventually (eventually_lt_nhds hδ)
  have hlarge : ∀ᶠ w : ℝ in atTop, 1/α ≤ Real.log w :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1/α))
  filter_upwards [eventually_ge_atTop (1 : ℝ),hsmall,hlarge] with w hw hs hl
  have hw0 : 0 < w := by linarith
  refine ⟨hw,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hl hα.le
    have he : α*(1/α)=1 := by field_simp
    rwa [he] at hh
  · apply (div_le_iff₀ hw0).mp
    simpa only [mul_div_assoc] using hs.le

/-- A polynomial annular loss is below any prescribed inverse width power
throughout the growing spatial interval, with an admissible near cutoff. -/
theorem kernel_log_cutoff_data {lam q b δ : ℝ} (hlam : 0 ≤ lam) (hq : 0 < q)
    (hb : 0 < b) (hδ : 0 < δ) (p B : ℕ) :
    ∃ α w0 : ℝ, 0 < α ∧ 1 ≤ w0 ∧ ∀ w, w0 ≤ w →
      1 ≤ α*Real.log w ∧ α*Real.log w ≤ δ*w ∧
      ∀ x, x ≤ b*Real.log w → w^p*Real.exp (lam*x-q*(α*Real.log w)) ≤ 1/w^B := by
  obtain ⟨α,hα,hbound⟩ := kernel_log_cutoff_bound hlam hq hb p B
  obtain ⟨w0,hw0⟩ := eventually_atTop.mp (kernel_log_cutoff_eventually hα hδ)
  refine ⟨α,max 1 w0,hα,le_max_left _ _,fun w hw => ?_⟩
  have hww := hw0 w ((le_max_right _ _).trans hw)
  exact ⟨hww.2.1,hww.2.2,fun x hx => hbound w x hww.1 hx⟩

/-- The fixed far-slope crossing exponential absorbs every polynomial loss
and the allowed growing spatial interval. -/
theorem kernel_fixed_far_eventually {lam c b : ℝ} (hlam : 0 ≤ lam)
    (hc : 0 < c) (hb : 0 < b) (p B : ℕ) :
    ∀ᶠ w : ℝ in atTop, 1 ≤ w ∧ ∀ x, x ≤ b*Real.log w →
      w^p*Real.exp (lam*x-c*w) ≤ 1/w^B := by
  let α := (p : ℝ)+(B : ℝ)+lam*b+1
  have hα : 0 < α := by dsimp [α]; positivity
  filter_upwards [kernel_log_cutoff_eventually hα hc] with w hw
  refine ⟨hw.1,fun x hx => ?_⟩
  have hw0 : 0 < w := by linarith [hw.1]
  have he (n : ℕ) : w^n = Real.exp ((n : ℝ)*Real.log w) := by
    rw [Real.exp_nat_mul,Real.exp_log hw0]
  rw [he p,← Real.exp_add]
  calc
    _ ≤ Real.exp (-(B : ℝ)*Real.log w) := by
      apply Real.exp_le_exp.mpr
      have hxl := mul_le_mul_of_nonneg_left hx hlam
      have hlw := Real.log_nonneg hw.1
      have hdec := hw.2.2
      dsimp [α] at hdec
      nlinarith
    _ = 1/w^B := by rw [neg_mul,Real.exp_neg,← he B,one_div]

theorem kernel_log_window_eventually {b : ℝ} (hb : 0 < b) :
    ∀ᶠ w : ℝ in atTop, 1 ≤ w ∧ b*Real.log w ≤ w/8 := by
  filter_upwards [kernel_log_cutoff_eventually hb (by norm_num : (0 : ℝ) < 1/8)] with w hw
  exact ⟨hw.1,by linarith [hw.2.2]⟩

end
end PGM
