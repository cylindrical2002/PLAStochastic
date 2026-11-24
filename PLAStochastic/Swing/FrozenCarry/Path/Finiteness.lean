import PLAStochastic.Swing.FrozenCarry.Path.Prefix

/-! # Finiteness of the actual frozen prefix from a negative slope and sublinear growth -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} {X : ℕ → Ω → ℝ} {w E : ℝ} {ω : Ω}

/-- The frozen inequalities expressed using their actual positive denominators. -/
theorem le_frozenPrefixLength_iff_slopes (n : ℕ) :
    (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω ↔
      ∃ m : ℝ, ∀ k < n,
        frozenUpperSlope X w k ω-2*E/((k : ℝ)+1) ≤ m ∧ m ≤ frozenUpperSlope X w k ω := by
  rw [le_frozenPrefixLength_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, fun k hk => ?_⟩
    have hh := hm (k+1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    simp only [Nat.add_sub_cancel_right, Nat.cast_add, Nat.cast_one] at hh
    have hk0 : (0 : ℝ) < (k : ℝ)+1 := by positivity
    dsimp only [frozenUpperSlope]
    rw [← sub_div]
    exact ⟨(div_le_iff₀ hk0).mpr hh.1, (le_div_iff₀ hk0).mpr hh.2⟩
  · rintro ⟨m, hm⟩
    refine ⟨m, fun j hj => ?_⟩
    have hj' := Finset.mem_Icc.mp hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hh := hm k (by omega)
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right, Nat.cast_add, Nat.cast_one]
    have hk0 : (0 : ℝ) < (k : ℝ)+1 := by positivity
    dsimp only [frozenUpperSlope] at hh
    rw [← sub_div] at hh
    exact ⟨(div_le_iff₀ hk0).mp hh.1, (le_div_iff₀ hk0).mp hh.2⟩

/-- A single negative upper slope eventually conflicts with the lower slope approaching zero.
This proves finiteness for every real E on each such path, simultaneously. -/
theorem frozenPrefixLength_finite_of_sublinear
    (hv : Tendsto (fun n => frozenUpperSlope X w n ω) atTop (𝓝 0))
    (hneg : ∃ j : ℕ, frozenUpperSlope X w j ω < 0) (E : ℝ) :
    frozenPrefixLength X w E ω ≠ ⊤ := by
  obtain ⟨j, hj⟩ := hneg
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using! (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hc : Tendsto (fun n : ℕ => 2*E/((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  have hl : Tendsto (fun n => frozenUpperSlope X w n ω-2*E/((n : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [sub_zero] using hv.sub hc
  have he := hl.eventually (Ioi_mem_nhds hj)
  obtain ⟨k, hk, hkj⟩ := (he.and (eventually_ge_atTop j)).exists
  have hbad : ¬ (k+1 : ℕ) ≤ frozenPrefixLength X w E ω := by
    intro h
    obtain ⟨m, hm⟩ := (le_frozenPrefixLength_iff_slopes (X := X) (w := w) (E := E) (ω := ω) (k+1)).mp h
    exact (not_le_of_gt hk) ((hm k (by omega)).1.trans (hm j (by omega)).2)
  intro ht
  exact hbad (by rw [ht]; exact le_top)

end SwingRepair
