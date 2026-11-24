import PLAStochastic.Swing.Restart.Chain.RecordingClock

/-! Every actual native recording clock is finite. A single Gaussian block
obstruction works simultaneously for every real carried state at each start. -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Set Filter
open scoped ENNReal NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- Uniformity of the three-point obstruction gives one full-measure set for
all real states, including states selected from an observed rejection. -/
theorem nativeRestartLength_ae_all_states_finite
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) :
    ∀ᵐ ω ∂μ, ∀ x : ℝ, nativeRestartLength X E x ω ≠ ⊤ := by
  have hz : μ {ω | ∃ x : ℝ, nativeRestartLength X E x ω = ⊤} = 0 := by
    apply le_antisymm _ bot_le
    apply ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one gaussianBlockPass_lt_one)
    intro b
    apply le_trans _ (nativeGaussianBlocksPassed_probability_le hX hi hG hE 0 ⌈8*E^2⌉₊ b (Nat.le_ceil _))
    apply measure_mono
    rintro ω ⟨x, hx⟩ j hj
    obtain ⟨m, hm⟩ := (le_nativePrefixLength_iff (nativeCarriedSamples X (fun _ => x))
      (fun _ => 0) E ω (1+2*⌈8*E^2⌉₊*b)).mp (by
        change ((1+2*⌈8*E^2⌉₊*b : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω
        rw [hx]
        exact le_top)
    simp only [Nat.zero_add]
    apply affine_fit_three_point_block ω (x := x) (q := m) (a := m)
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hmul := Nat.mul_le_mul_left (2*⌈8*E^2⌉₊) (show j+1 ≤ b by omega)
    rw [Nat.mul_add, Nat.mul_one] at hmul
    have hmem : 1+k ∈ Finset.Icc (0+1) (1+2*⌈8*E^2⌉₊*b) :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hh := hm (1+k) hmem
    dsimp only at hh
    rw [show 1+k = k+1 by omega, nativeCarriedSamples_succ] at hh
    simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, sub_zero, zero_add] at hh
    convert hh using 1; congr 1; ring
  simpa only [ae_iff, not_forall, not_not] using hz

/-- All deterministic shifts share a full-measure set on which every possible
real state has a finite maximal prefix. -/
theorem nativeRestartLength_ae_all_shifts_states_finite
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) :
    ∀ᵐ ω ∂μ, ∀ s : ℕ, ∀ x : ℝ, nativeRestartLength (fun j => X (s+1+j)) E x ω ≠ ⊤ := by
  rw [ae_all_iff]
  intro s
  exact nativeRestartLength_ae_all_states_finite (fun j => hX (s+1+j))
    (hi.precomp (g := fun j => s+1+j) (by intro i j hij; dsimp at hij; omega))
    (fun j => hG (s+1+j)) hE

omit [MeasurableSpace Ω] in
/-- At a known recording clock the next output segment starts at that clock
and has exactly the fitted anchor used in the observed state. -/
theorem nativeStream_after_recording (X : ℕ → Ω → ℝ)
    {E : ℝ} (hE : 0 ≤ E) (ω : Ω) {k s H : ℕ}
    (hτ : nativeRecordingTime (fun j => (j : ℝ)) (cumulativeSamples X) E k ω = (s : WithTop ℕ))
    (hH : s+1 ≤ H) :
    k < (nativeStream (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω) E H).length ∧
      (nativeSegmentAt (nativeStream (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω) E H) k).start = s ∧
      (nativeSegmentAt (nativeStream (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω) E H) k).anchorValue =
        nativeCarryAnchor (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω) E s := by
  let t : ℕ → ℝ := fun j => j
  let y : ℕ → ℝ := fun j => cumulativeSamples X j ω
  have ht : StrictMono t := fun i j hij => by change (i : ℝ) < (j : ℝ); exact_mod_cast hij
  by_cases hk : k = 0
  · subst k
    have hs : s = 0 := by
      rw [nativeRecordingTime_zero] at hτ
      exact_mod_cast hτ.symm
    subst s
    have hlen : 0 < (nativeStream t y E H).length :=
      nativeStream_length_pos_of_pos t y E (by omega)
    have hc := nativeStream_spec t y ht hE H
    have ha := hc.getElem_zero hlen
    rw [← nativeSegmentAt_eq_getElem hlen] at ha
    refine ⟨hlen, ha.1, ?_⟩
    simpa [nativeCarryAnchor, nativeStream, nativeSegmentAt, nativeSegmentEndpoint, y] using ha.2
  · have hk1 : 1 ≤ k := by omega
    obtain ⟨hs, hlen, _⟩ := nativeStream_at_recordingTime t (cumulativeSamples X) E hk1 ω hτ
    have hnow := (nativeRecordingTime_le_iff t (cumulativeSamples X) E k s ω).mp hτ.le
    have hrej : nativeRejectionAt t y E s := ⟨hs, by rw [hlen]; exact hnow⟩
    have hh := nativeRejectionAt_next t y ht hE hrej hH
    change (nativeStream t y E s).length = k at hlen
    simpa only [hlen] using hh.2

omit [MeasurableSpace Ω] in
/-- Deterministically, finite local prefixes force all the actual online
recording clocks to exist. -/
theorem nativeRecordingTime_finite_of_all_restarts (X : ℕ → Ω → ℝ)
    {E : ℝ} (hE : 0 ≤ E) (ω : Ω)
    (hfinite : ∀ s : ℕ, ∀ x : ℝ, nativeRestartLength (fun j => X (s+1+j)) E x ω ≠ ⊤) :
    ∀ k : ℕ, nativeRecordingTime (fun j => (j : ℝ)) (cumulativeSamples X) E k ω ≠ ⊤ := by
  intro k
  induction k with
  | zero => simp only [nativeRecordingTime_zero, ne_eq, WithTop.zero_ne_top, not_false_eq_true]
  | succ k ih =>
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp ih
    have hsf : nativeRecordingTime (fun j => (j : ℝ)) (cumulativeSamples X) E k ω = (s : WithTop ℕ) := hs.symm
    let x := nativeRestartObservedState X E s ω
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfinite s x)
    have hn1 : 1 ≤ n := by
      have hh := one_le_nativePrefixLength (nativeCarriedSamples (fun j => X (s+1+j)) (fun _ => x))
        (fun _ => 0) hE ω
      change (1 : WithTop ℕ) ≤ nativeRestartLength (fun j => X (s+1+j)) E x ω at hh
      rw [← hn] at hh
      exact WithTop.coe_le_coe.mp hh
    let H := s+n+1
    obtain ⟨hkH, hstart, hanchor⟩ := nativeStream_after_recording X hE ω hsf (H := H) (by dsimp [H]; omega)
    have hcount : k+1 < (nativeStream (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω) E H).length := by
      by_contra hh
      have hc := nativeStream_spec (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω)
        (fun i j hij => by change (i : ℝ) < (j : ℝ); exact_mod_cast hij) hE H
      have hend := hc.getElem_last_finish hkH (by omega)
      have hf := (hc.getElem_valid hkH).feasible
      rw [← nativeSegmentAt_eq_getElem hkH] at hend hf
      rw [hstart, hanchor, hend] at hf
      have hlocal := (nativeRestart_feasible_iff X s (n+1) E
        (nativeCarryAnchor (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω) E s) ω).mp
          ⟨_, by simpa only [H, Nat.add_assoc] using hf⟩
      change ((n+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength (fun j => X (s+1+j)) E x ω at hlocal
      rw [← hn] at hlocal
      have : n+1 ≤ n := WithTop.coe_le_coe.mp hlocal
      omega
    have hbound := (nativeRecordingTime_le_iff (fun j => (j : ℝ)) (cumulativeSamples X) E (k+1) (s+n) ω).mpr hcount
    exact ne_top_of_le_ne_top WithTop.coe_ne_top hbound

/-- Almost surely every actual repeated native recording has a finite clock. -/
theorem nativeRecordingTime_ae_all_finite
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ,
      nativeRecordingTime (fun j => (j : ℝ)) (cumulativeSamples X) E k ω ≠ ⊤ := by
  filter_upwards [nativeRestartLength_ae_all_shifts_states_finite hX hi hG hE] with ω hω
  exact nativeRecordingTime_finite_of_all_restarts X hE.le ω hω

end SwingRepair
