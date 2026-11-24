import PLAStochastic.Swing.StationaryScale.FavorableGeometry

/-! # The sufficient path event forces a favorable completion

`eq:stationarypathgood` asks that the incoming margin and the whole accepted
fresh walk stay within `ρE`.  On that event the actual completion is one of the
two favorable rejections, with the constrained-SSE slope equal to the accepted
cone endpoint on the side of the carry.  The implication is pathwise.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The sufficient path event of `eq:stationarypathgood`, with `ρ = 1/40`. -/
def nativeRestartPathGood (X : ℕ → Ω → ℝ) (E : ℝ) : Set (ℝ × Ω) :=
  {p | nativeRestartLength X E p.1 p.2 ≠ ⊤ ∧
    |E-abs p.1| ≤ E/40 ∧
    ∀ j : ℕ, ((j : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E p.1 p.2 →
      |cumulativeSamples X j p.2| ≤ E/40}

omit mΩ in
theorem nativeRestartPathGood_subset_favorable (X : ℕ → Ω → ℝ) {E : ℝ} (hE : 0 < E) :
    nativeRestartPathGood X E ⊆ nativeRestartFavorableSet X E := by
  rintro ⟨x, ω⟩ ⟨hfin, hmargin, hwalk⟩
  have hNpos : 0 < nativeRestartLengthNat X E x ω :=
    nativeRestartLengthNat_pos_of_finite X hE.le x ω hfin
  have hcast : ((nativeRestartLengthNat X E x ω : ℕ) : WithTop ℕ) =
      nativeRestartLength X E x ω := nativeRestartLengthNat_cast_of_finite X E x ω hfin
  obtain ⟨k, hk⟩ : ∃ k, nativeRestartLengthNat X E x ω = k+1 :=
    ⟨nativeRestartLengthNat X E x ω-1, by omega⟩
  set D : ℕ → ℝ := fun i => nativeCarriedSamples X (fun _ => x) i ω with hDdef
  have hk1 : (1 : ℕ) ≤ k+1 := by omega
  have hW : ∀ j : ℕ, j ≤ k+1 → |cumulativeSamples X j ω| ≤ E/40 := by
    intro j hj
    refine hwalk j ?_
    rw [← hcast, hk]
    exact_mod_cast hj
  have hDval : ∀ i : ℕ, 1 ≤ i → D i = x+cumulativeSamples X (i-1) ω := by
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j+1 := ⟨i-1, by omega⟩
    simp [hDdef]
  have hmarg := abs_le.mp hmargin
  have hxlo : (1-(1/40 : ℝ))*E ≤ |x| := by linarith [hmarg.2]
  have hxhi : |x| ≤ (1+(1/40 : ℝ))*E := by linarith [hmarg.1]
  have hxne : x ≠ 0 := by
    intro h
    rw [h, abs_zero] at hxlo
    linarith
  have hlen : nativeRestartLength X E x ω = ((k+1 : ℕ) : WithTop ℕ) := by
    rw [← hcast, hk]
  -- the prefix and the rejected sample, as an existence statement
  have hfeas : ∃ m, feasibleSlope (Finset.Icc 1 (k+1)) (fun i => (i : ℝ)) D 0 0 E m := by
    have h := (nativeRestartLengthNat_spec X E x ω hfin).1
    rw [hk] at h
    simpa only [nativePrefixFeasible, Nat.cast_zero, Nat.zero_add] using h
  have hrej : ¬ ∃ m, feasibleSlope (Finset.Icc 1 (k+1+1)) (fun i => (i : ℝ)) D 0 0 E m := by
    have h := (nativeRestartLengthNat_spec X E x ω hfin).2
    rw [hk] at h
    simpa only [nativePrefixFeasible, Nat.cast_zero, Nat.zero_add] using h
  have hslope : nativeRestartSlopeAt X E x (k+1) ω =
      nativeSelectedSlope (Finset.Icc 1 (k+1)) (Finset.nonempty_Icc.mpr hk1)
        (fun i => (i : ℝ)) D 0 0 E := by
    simp only [nativeRestartSlopeAt, dif_pos (by omega : 0 < k+1)]
    rfl
  have hstep : D (k+1+1) = x+cumulativeSamples X k ω+X k ω := by
    rw [hDval (k+1+1) (by omega)]
    simp only [Nat.add_sub_cancel, cumulativeSamples_succ]
    ring
  have hres : nativeRestartResidualAt X E x k ω =
      x+cumulativeSamples X k ω-nativeRestartSlopeAt X E x (k+1) ω*((k+1 : ℕ) : ℝ) := rfl
  rcases lt_or_gt_of_ne hxne with hxneg | hxpos
  · -- negative carry: the reflected upper branch
    have hxv : |x| = -x := abs_of_neg hxneg
    have hlo : ∀ i ∈ Finset.Icc 1 (k+1+1), D i ≤ -((1-(1/20 : ℝ))*E) := by
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hwi := hW (i-1) (by omega)
      rw [hDval i hi'.1]
      rw [hxv] at hxlo hxhi
      linarith [(abs_le.mp hwi).1, (abs_le.mp hwi).2]
    have hhi : ∀ i ∈ Finset.Icc 1 (k+1+1), -((1+(1/20 : ℝ))*E) ≤ D i := by
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hwi := hW (i-1) (by omega)
      rw [hDval i hi'.1]
      rw [hxv] at hxlo hxhi
      linarith [(abs_le.mp hwi).1, (abs_le.mp hwi).2]
    obtain ⟨hsel, hneg, hge, hthr⟩ :=
      favorable_upper_geometry_core hk1 D hE hlo hhi hfeas hrej
    refine Set.mem_iUnion.mpr ⟨(true, k), ?_⟩
    show (x,ω) ∈ nativeRestartFavorableUpperEvent X E k
    refine ⟨hlen, ?_, ?_, ?_, ?_⟩
    · rw [hslope]
      exact hsel
    · rw [hslope, hsel]
      exact hge
    · rw [hslope, hsel]
      exact hneg.le
    · rw [nativeRestartUpperGapAt, hres, hslope] at *
      have hthr' := hthr
      rw [hstep] at hthr'
      push_cast at hthr' ⊢
      nlinarith [hthr']
  · -- positive carry: the lower branch
    have hxv : |x| = x := abs_of_pos hxpos
    have hlo : ∀ i ∈ Finset.Icc 1 (k+1+1), (1-(1/20 : ℝ))*E ≤ D i := by
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hwi := hW (i-1) (by omega)
      rw [hDval i hi'.1]
      rw [hxv] at hxlo hxhi
      linarith [(abs_le.mp hwi).1, (abs_le.mp hwi).2]
    have hhi : ∀ i ∈ Finset.Icc 1 (k+1+1), D i ≤ (1+(1/20 : ℝ))*E := by
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hwi := hW (i-1) (by omega)
      rw [hDval i hi'.1]
      rw [hxv] at hxlo hxhi
      linarith [(abs_le.mp hwi).1, (abs_le.mp hwi).2]
    obtain ⟨hsel, hpos, hle, hthr⟩ :=
      favorable_lower_geometry_core hk1 D hE hlo hhi hfeas hrej
    refine Set.mem_iUnion.mpr ⟨(false, k), ?_⟩
    show (x,ω) ∈ nativeRestartFavorableLowerEvent X E k
    refine ⟨hlen, ?_, ?_, ?_, ?_⟩
    · rw [hslope]
      exact hsel
    · rw [hslope, hsel]
      exact hpos.le
    · rw [hslope, hsel]
      exact hle
    · rw [nativeRestartLowerGapAt, hres, hslope] at *
      have hthr' := hthr
      rw [hstep] at hthr'
      push_cast at hthr' ⊢
      nlinarith [hthr']

end SwingRepair
