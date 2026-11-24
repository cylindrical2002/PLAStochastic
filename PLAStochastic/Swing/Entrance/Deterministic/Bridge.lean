import PLAStochastic.Swing.Entrance.Deterministic.Cone
import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.LeastSquares

/-!
# The native first segment along the anchored path

The native first-segment objects `nativeFirstDuration`, `nativeFirstSelectedSlope` and
`nativeFirstNext` are defined from the output stream and from the rebased restart
representation.  Whenever the native feasibility test of the prefixes `1, …, j` of the
anchored path `y = entrancePath X ω` has a finite threshold `K > 1`, all of them are read off
the path: the first duration is `N = K - 1`, the selected slope is the clipped least-squares
slope `entrancePathSlope y E N` of `y_1, …, y_N` in the cone `[a_N, b_N]`, and the first
rejected residual is `y_{N+1} - N m_N`.
-/

namespace SwingRepair

noncomputable section

variable {Ω : Type*}

/-- The carried samples of the rebased first segment are the anchored path itself. -/
theorem nativeCarriedSamples_first (X : ℕ → Ω → ℝ) (ω : Ω) (i : ℕ) :
    nativeCarriedSamples (fun k => X (1 + k)) (fun _ => X 0 ω) i ω = entrancePath X ω i := by
  cases i with
  | zero => simp
  | succ i =>
    rw [nativeCarriedSamples_succ, entrancePath, Nat.add_comm i 1,
      cumulativeSamples_add_shift X 1 i ω]
    simp [cumulativeSamples]

/-- The native constrained-SSE slope of the prefix `1, …, N` of an anchored path. -/
def entrancePathSlope (y : ℕ → ℝ) (E : ℝ) (N : ℕ) : ℝ :=
  if h : (Finset.Icc 1 N).Nonempty then
    nativeSelectedSlope (Finset.Icc 1 N) h (fun j => (j : ℝ)) y 0 (y 0) E
  else 0

/-- The native slope is the least-squares slope `∑ i y_i / ∑ i²` clipped to `[a_N, b_N]`. -/
theorem entrancePathSlope_eq {y : ℕ → ℝ} {E : ℝ} (hy0 : y 0 = 0) {N : ℕ} (hN : 1 ≤ N) :
    entrancePathSlope y E N = nativeClippedSlope (entranceLower y E N) (entranceUpper y E N)
      ((∑ i ∈ Finset.Icc 1 N, (i : ℝ) * y i) / ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ 2) := by
  have h : (Finset.Icc 1 N).Nonempty := Finset.nonempty_Icc.mpr hN
  simp only [entrancePathSlope, entranceLower, entranceUpper, dif_pos h, nativeSelectedSlope]
  rw [hy0, nativeLeastSquares_Icc_formula]

/-- A finite feasibility threshold determines the rebased restart length. -/
theorem nativeRestartLength_first_of_threshold (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) {K : ℕ}
    (hcone : ∀ j, nativePrefixFeasible (fun i => (i : ℝ)) (entrancePath X ω) E 0 j
      (entrancePath X ω 0) ↔ j < K) :
    nativeRestartLength (fun k => X (1 + k)) E (X 0 ω) ω = ((K - 1 : ℕ) : WithTop ℕ) := by
  have hfeas : ∀ k : ℕ, (k : WithTop ℕ) ≤ nativeRestartLength (fun k => X (1 + k)) E (X 0 ω) ω ↔
      k < K := by
    intro k
    rw [← hcone k]
    have h := nativeRestart_feasible_iff X 0 k E 0 ω
    simp only [Nat.zero_add, sub_zero] at h
    have h1 : cumulativeSamples X 1 ω = X 0 ω := by simp [cumulativeSamples]
    rw [h1] at h
    rw [← h, entrancePath_zero]
    rfl
  cases hL : nativeRestartLength (fun k => X (1 + k)) E (X 0 ω) ω using WithTop.recTopCoe with
  | top =>
    have := (hfeas K).mp (by rw [hL]; exact le_top)
    omega
  | coe l =>
    rw [hL] at hfeas
    have h1 : l < K := (hfeas l).mp (by exact_mod_cast le_rfl)
    have h2 : ¬ l + 1 < K := fun h => by
      have h3 := (hfeas (l + 1)).mpr h
      have h4 : l + 1 ≤ l := WithTop.coe_le_coe.mp h3
      omega
    rw [show l = K - 1 by omega]
    rfl

/-- A finite threshold `K > 1` determines the native first duration and restart length. -/
theorem nativeFirst_duration_of_threshold (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) {K : ℕ}
    (hK : 1 < K)
    (hcone : ∀ j, nativePrefixFeasible (fun i => (i : ℝ)) (entrancePath X ω) E 0 j
      (entrancePath X ω 0) ↔ j < K) :
    nativeFirstDuration X E ω = K - 1 ∧
      nativeRestartLengthNat (fun k => X (1 + k)) E (X 0 ω) ω = K - 1 := by
  refine ⟨nativeFirstRecording_eq_threshold _ _ E hK hcone, ?_⟩
  change (nativeRestartLength (fun k => X (1 + k)) E (X 0 ω) ω).untopD 0 = K - 1
  rw [nativeRestartLength_first_of_threshold X E ω hcone]
  rfl

/-- Along a finite threshold the selected first slope is the path-level native slope. -/
theorem nativeFirstSelectedSlope_eq_path (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) {K : ℕ}
    (hK : 1 < K)
    (hcone : ∀ j, nativePrefixFeasible (fun i => (i : ℝ)) (entrancePath X ω) E 0 j
      (entrancePath X ω 0) ↔ j < K) :
    nativeFirstSelectedSlope X E ω =
      entrancePathSlope (entrancePath X ω) E (nativeFirstDuration X E ω) := by
  obtain ⟨hN, hL⟩ := nativeFirst_duration_of_threshold X E ω hK hcone
  have hpos : 0 < K - 1 := by omega
  have hcar : (fun i => nativeCarriedSamples (fun k => X (1 + k)) (fun _ => X 0 ω) i ω) =
      entrancePath X ω := funext (nativeCarriedSamples_first X ω)
  simp only [nativeFirstSelectedSlope, nativeRestartSlope, hL, hN, nativeRestartSlopeAt,
    dif_pos hpos, entrancePathSlope, dif_pos (Finset.nonempty_Icc.mpr (show 1 ≤ K - 1 by omega)), hcar,
    entrancePath_zero]

/-- Along a finite threshold the first rejected residual is `y_{N+1} - N m_N`. -/
theorem nativeFirstNext_eq_path (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) {K : ℕ}
    (hK : 1 < K)
    (hcone : ∀ j, nativePrefixFeasible (fun i => (i : ℝ)) (entrancePath X ω) E 0 j
      (entrancePath X ω 0) ↔ j < K) :
    nativeFirstNext X E ω = entrancePath X ω (nativeFirstDuration X E ω + 1) -
      nativeFirstSelectedSlope X E ω * nativeFirstDuration X E ω := by
  obtain ⟨hN, hL⟩ := nativeFirst_duration_of_threshold X E ω hK hcone
  have hcar := nativeCarriedSamples_first X ω (K - 1 + 1)
  rw [nativeCarriedSamples_succ] at hcar
  simp only [nativeFirstNext, nativeRestartNext, nativeFirstSelectedSlope, hL, hN]
  rw [hcar]

end

end SwingRepair
