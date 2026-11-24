import PLAStochastic.Swing.FrozenCarry.Path.SlopeEnvelope
import PLAStochastic.Swing.FrozenCarry.Path.Finiteness

/-! # Exact floor-scale feasibility thresholds for a fixed Gaussian future path -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} {X : ℕ → Ω → ℝ} {w : ℝ} {ω : Ω}

theorem frozenPrefix_floor_feasible_eventually
    (hv : Tendsto (fun n => frozenUpperSlope X w n ω) atTop (𝓝 0))
    (hA : 0 < frozenSlopeMagnitude X w ω) {q : ℝ} (hq : 0 < q)
    (hqa : q < 2/frozenSlopeMagnitude X w ω) :
    ∀ᶠ E : ℝ in atTop, (⌊q*E⌋₊ : WithTop ℕ) ≤ frozenPrefixLength X w E ω := by
  let A := frozenSlopeMagnitude X w ω
  have hAq : A*q < 2 := by simpa only [mul_comm] using (lt_div_iff₀ hA).mp hqa
  let ε := (2/q-A)/2
  have hε : 0 < ε := by
    have hh := (lt_div_iff₀ hq).mpr hAq
    dsimp [ε]
    linarith
  have hlim : (A+ε)*q < 2 := by
    have he : ε*q = (2-A*q)/2 := by dsimp [ε]; field_simp
    nlinarith
  obtain ⟨C, _, hC⟩ := sublinear_succ_envelope hv hε
  have hh : Tendsto (fun E : ℝ => C/E+(A+ε)*((⌊q*E⌋₊ : ℝ)/E)) atTop
      (𝓝 ((A+ε)*q)) := by
    simpa only [zero_add, id_eq] using!
      (tendsto_const_nhds.div_atTop tendsto_id (f := fun _ : ℝ => C)).add
        ((tendsto_nat_floor_mul_div_atTop hq.le).const_mul (A+ε))
  filter_upwards [hh.eventually (Iio_mem_nhds hlim), eventually_gt_atTop (0 : ℝ)] with E he hE
  apply frozenPrefix_feasible_of_envelope (frozenSlopeMagnitude_bddAbove hv)
    (show 0 ≤ frozenSlopeMagnitude X w ω+ε by linarith) (fun j => (le_abs_self _).trans (hC j))
  have hdiv : C/E+(A+ε)*((⌊q*E⌋₊ : ℝ)/E) = (C+(A+ε)*(⌊q*E⌋₊ : ℝ))/E := by ring
  rw [hdiv] at he
  exact ((div_lt_iff₀ hE).mp he).le

theorem frozenPrefix_floor_infeasible_eventually
    (hv : Tendsto (fun n => frozenUpperSlope X w n ω) atTop (𝓝 0))
    (hA : 0 < frozenSlopeMagnitude X w ω) {q : ℝ}
    (hqa : 2/frozenSlopeMagnitude X w ω < q) :
    ∀ᶠ E : ℝ in atTop, ¬ (⌊q*E⌋₊ : WithTop ℕ) ≤ frozenPrefixLength X w E ω := by
  have hq : 0 < q := (div_pos (by norm_num) hA).trans hqa
  have hqb : 2/q < frozenSlopeMagnitude X w ω := by
    apply (div_lt_iff₀ hq).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hA).mp hqa
  obtain ⟨u, ⟨j, rfl⟩, hj⟩ := exists_lt_of_lt_csSup
    (show (Set.range (fun n => -frozenUpperSlope X w n ω)).Nonempty from Set.range_nonempty _) hqb
  have hj' : frozenUpperSlope X w j ω < -(2/q) := by linarith
  have hn : Tendsto (fun E : ℝ => ⌊q*E⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (Tendsto.const_mul_atTop hq tendsto_id)
  have hpred : Tendsto (fun E : ℝ => ⌊q*E⌋₊-1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hn.eventually (eventually_ge_atTop (b+1))] with E hE
    omega
  have hratio : Tendsto (fun E : ℝ => E/(⌊q*E⌋₊ : ℝ)) atTop (𝓝 q⁻¹) := by
    simpa only [inv_div] using! (tendsto_nat_floor_mul_div_atTop hq.le).inv₀ hq.ne'
  have hl : Tendsto (fun E : ℝ => frozenUpperSlope X w (⌊q*E⌋₊-1) ω - 2*E/(⌊q*E⌋₊ : ℝ))
      atTop (𝓝 (-(2/q))) := by
    simpa only [Function.comp_def, zero_sub, div_eq_mul_inv, mul_assoc] using!
      (hv.comp hpred).sub (hratio.const_mul 2)
  filter_upwards [hl.eventually (Ioi_mem_nhds hj'), hn.eventually (eventually_ge_atTop (j+1))] with E hE hN
  intro hf
  obtain ⟨m, hm⟩ := (le_frozenPrefixLength_iff_slopes (X := X) (w := w) (E := E) (ω := ω) ⌊q*E⌋₊).mp hf
  have he : ((⌊q*E⌋₊-1 : ℕ) : ℝ)+1 = (⌊q*E⌋₊ : ℝ) := by
    have hh : ⌊q*E⌋₊-1+1 = ⌊q*E⌋₊ := by omega
    exact_mod_cast hh
  have hlo := (hm (⌊q*E⌋₊-1) (by omega)).1
  rw [he] at hlo
  exact (not_le_of_gt hE) (hlo.trans (hm j (by omega)).2)

end SwingRepair
