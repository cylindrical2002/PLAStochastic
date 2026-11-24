import PLAStochastic.Swing.StationaryScale.InvariantTail

/-! # The pathwise favorable-branch geometry of Appendix `app:margins`

On the sufficient path event of `eq:stationarypathgood` the actual completion
is a favorable rejection: the accepted cone endpoint on the side of the carry
is the constrained-SSE slope, it lies in `(0,δE]`, and the rejection is on the
matching side.  Everything here is deterministic; no probability is used.
-/
noncomputable section
open MeasureTheory Set
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! ### Exact prefix sums -/

theorem sum_Icc_one_cast (N : ℕ) :
    ∑ i ∈ Finset.Icc 1 N, (i : ℝ) = (N : ℝ)*((N : ℝ)+1)/2 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1), ih]
    push_cast
    ring

theorem sum_Icc_one_sq_cast (N : ℕ) :
    ∑ i ∈ Finset.Icc 1 N, (i : ℝ)^2 = (N : ℝ)*((N : ℝ)+1)*(2*(N : ℝ)+1)/6 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1), ih]
    push_cast
    ring

theorem nativeSSETimeSquare_Icc (N : ℕ) :
    nativeSSETimeSquare (Finset.Icc 1 N) (fun i => (i : ℝ)) 0 =
      (N : ℝ)*((N : ℝ)+1)*(2*(N : ℝ)+1)/6 := by
  unfold nativeSSETimeSquare
  simpa only [sub_zero] using sum_Icc_one_sq_cast N

/-- Two-sided bound on the unconstrained least-squares slope of an accepted
prefix, from two-sided bounds on the carried observations. -/
theorem nativeLeastSquares_Icc_bounds {N : ℕ} (hN : 1 ≤ N) (D : ℕ → ℝ) {lo hi : ℝ}
    (hlo : ∀ i ∈ Finset.Icc 1 N, lo ≤ D i) (hhi : ∀ i ∈ Finset.Icc 1 N, D i ≤ hi) :
    3*lo/(2*(N : ℝ)+1) ≤
        nativeLeastSquares (Finset.Icc 1 N) (fun i => (i : ℝ)) D 0 0 ∧
      nativeLeastSquares (Finset.Icc 1 N) (fun i => (i : ℝ)) D 0 0 ≤
        3*hi/(2*(N : ℝ)+1) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hts : nativeSSETimeSquare (Finset.Icc 1 N) (fun i => (i : ℝ)) 0 =
      (N : ℝ)*((N : ℝ)+1)*(2*(N : ℝ)+1)/6 := nativeSSETimeSquare_Icc N
  have htspos : 0 < nativeSSETimeSquare (Finset.Icc 1 N) (fun i => (i : ℝ)) 0 := by
    rw [hts]; positivity
  have hcross : nativeSSECross (Finset.Icc 1 N) (fun i => (i : ℝ)) D 0 0 =
      ∑ i ∈ Finset.Icc 1 N, (i : ℝ)*D i := by
    unfold nativeSSECross
    exact Finset.sum_congr rfl (fun i _ => by rw [sub_zero, sub_zero])
  have hsum : ∑ i ∈ Finset.Icc 1 N, (i : ℝ) = (N : ℝ)*((N : ℝ)+1)/2 := sum_Icc_one_cast N
  have hup : nativeSSECross (Finset.Icc 1 N) (fun i => (i : ℝ)) D 0 0 ≤
      hi*((N : ℝ)*((N : ℝ)+1)/2) := by
    rw [hcross, ← hsum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi' => ?_
    have hipos : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    rw [mul_comm (i : ℝ) (D i)]
    exact mul_le_mul_of_nonneg_right (hhi i hi') hipos
  have hdown : lo*((N : ℝ)*((N : ℝ)+1)/2) ≤
      nativeSSECross (Finset.Icc 1 N) (fun i => (i : ℝ)) D 0 0 := by
    rw [hcross, ← hsum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi' => ?_
    have hipos : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    rw [mul_comm (i : ℝ) (D i)]
    exact mul_le_mul_of_nonneg_right (hlo i hi') hipos
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have h2N : (0 : ℝ) < 2*(N : ℝ)+1 := by linarith
  have hcancel : ∀ c : ℝ, 3*c/(2*(N : ℝ)+1)*((N : ℝ)*((N : ℝ)+1)*(2*(N : ℝ)+1)/6) =
      c*((N : ℝ)*((N : ℝ)+1)/2) := by
    intro c
    field_simp
    ring
  constructor
  · rw [nativeLeastSquares, le_div_iff₀ htspos, hts, hcancel]
    exact hdown
  · rw [nativeLeastSquares, div_le_iff₀ htspos, hts, hcancel]
    exact hup

/-! ### Cone endpoints of an accepted prefix -/

theorem nativeConeLower_Icc_le {N : ℕ} (hN : 1 ≤ N) (D : ℕ → ℝ) {E c : ℝ}
    (h : ∀ i ∈ Finset.Icc 1 N, (D i-E)/(i : ℝ) ≤ c) :
    nativeConeLower (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
      (fun i => (i : ℝ)) D 0 0 E ≤ c := by
  refine Finset.sup'_le _ _ fun i hi => ?_
  simpa only [slopeLower, sub_zero] using h i hi

theorem le_nativeConeUpper_Icc {N : ℕ} (hN : 1 ≤ N) (D : ℕ → ℝ) {E c : ℝ}
    (h : ∀ i ∈ Finset.Icc 1 N, c ≤ (D i+E)/(i : ℝ)) :
    c ≤ nativeConeUpper (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
      (fun i => (i : ℝ)) D 0 0 E := by
  refine Finset.le_inf' _ _ fun i hi => ?_
  simpa only [slopeUpper, sub_zero] using h i hi

theorem le_nativeConeLower_Icc {N : ℕ} (hN : 1 ≤ N) (D : ℕ → ℝ) {E : ℝ}
    {i : ℕ} (hi : i ∈ Finset.Icc 1 N) :
    (D i-E)/(i : ℝ) ≤ nativeConeLower (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
      (fun i => (i : ℝ)) D 0 0 E := by
  simpa only [nativeConeLower, slopeLower, sub_zero] using
    Finset.le_sup' (fun j => slopeLower ((j : ℕ) : ℝ) (D j) 0 0 E) hi

theorem nativeConeUpper_Icc_le {N : ℕ} (hN : 1 ≤ N) (D : ℕ → ℝ) {E : ℝ}
    {i : ℕ} (hi : i ∈ Finset.Icc 1 N) :
    nativeConeUpper (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
      (fun i => (i : ℝ)) D 0 0 E ≤ (D i+E)/(i : ℝ) := by
  simpa only [nativeConeUpper, slopeUpper, sub_zero] using
    Finset.inf'_le (fun j => slopeUpper ((j : ℕ) : ℝ) (D j) 0 0 E) hi

/-- A slope inside the old cone and inside the new sample interval is feasible
for the extended prefix.  This is the exact rejection criterion: no such slope
exists precisely when the two intervals are disjoint. -/
theorem feasibleSlope_Icc_succ_of_mem {N : ℕ} (D : ℕ → ℝ) {E m : ℝ}
    (hold : feasibleSlope (Finset.Icc 1 N) (fun i => (i : ℝ)) D 0 0 E m)
    (hnew : |D (N+1)-(0+m*((((N+1 : ℕ)) : ℝ)-0))| ≤ E) :
    feasibleSlope (Finset.Icc 1 (N+1)) (fun i => (i : ℝ)) D 0 0 E m := by
  intro i hi
  have hi' := Finset.mem_Icc.mp hi
  rcases Nat.lt_or_ge i (N+1) with hlt | hge
  · exact hold i (Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩)
  · have : i = N+1 := by omega
    subst this
    exact hnew

/-! ### The favorable lower branch

All carried observations of the accepted prefix and of the rejected sample are
positive and within `δE` of the tolerance.  Then the completion is a lower
rejection whose constrained-SSE slope is the old lower cone endpoint.
-/

theorem favorable_lower_geometry_core {N : ℕ} (hN : 1 ≤ N) (D : ℕ → ℝ) {E : ℝ}
    (hE : 0 < E)
    (hlo : ∀ i ∈ Finset.Icc 1 (N+1), (1-(1/20 : ℝ))*E ≤ D i)
    (hhi : ∀ i ∈ Finset.Icc 1 (N+1), D i ≤ (1+(1/20 : ℝ))*E)
    (hfeas : ∃ m, feasibleSlope (Finset.Icc 1 N) (fun i => (i : ℝ)) D 0 0 E m)
    (hrej : ¬ ∃ m, feasibleSlope (Finset.Icc 1 (N+1)) (fun i => (i : ℝ)) D 0 0 E m) :
    nativeSelectedSlope (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
          (fun i => (i : ℝ)) D 0 0 E =
        nativeConeLower (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
          (fun i => (i : ℝ)) D 0 0 E ∧
      0 < nativeConeLower (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
          (fun i => (i : ℝ)) D 0 0 E ∧
      nativeConeLower (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
          (fun i => (i : ℝ)) D 0 0 E ≤ E ∧
      D (N+1)+E < nativeConeLower (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
          (fun i => (i : ℝ)) D 0 0 E*((N : ℝ)+1) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1pos : (0 : ℝ) < (N : ℝ)+1 := by linarith
  have ht : ∀ i ∈ Finset.Icc 1 N, (0 : ℝ) < ((i : ℕ) : ℝ) := by
    intro i hi
    have := (Finset.mem_Icc.mp hi).1
    exact_mod_cast (by omega : 0 < i)
  set L := nativeConeLower (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
    (fun i => (i : ℝ)) D 0 0 E with hLdef
  set U := nativeConeUpper (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
    (fun i => (i : ℝ)) D 0 0 E with hUdef
  have hsub : ∀ i ∈ Finset.Icc 1 N, i ∈ Finset.Icc 1 (N+1) := by
    intro i hi
    have := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩
  have hLU : L ≤ U :=
    (nativeCone_nonempty_iff _ (Finset.nonempty_Icc.mpr hN) _ _ 0 0 E ht).mp hfeas
  -- the old lower endpoint is at most `δE`
  have hLδ : L ≤ (1/20 : ℝ)*E := by
    refine nativeConeLower_Icc_le hN D fun i hi => ?_
    have hi1 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by
      have := (Finset.mem_Icc.mp hi).1
      exact_mod_cast this
    have hip : (0 : ℝ) < ((i : ℕ) : ℝ) := by linarith
    have hDi : D i ≤ (1+(1/20 : ℝ))*E := hhi i (hsub i hi)
    rw [div_le_iff₀ hip]
    nlinarith
  -- the old upper endpoint is at least `(2-δ)E/N`
  have hUN : (2-(1/20 : ℝ))*E/(N : ℝ) ≤ U := by
    refine le_nativeConeUpper_Icc hN D fun i hi => ?_
    have hi1 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by
      have := (Finset.mem_Icc.mp hi).1
      exact_mod_cast this
    have hiN : ((i : ℕ) : ℝ) ≤ (N : ℝ) := by
      have := (Finset.mem_Icc.mp hi).2
      exact_mod_cast this
    have hip : (0 : ℝ) < ((i : ℕ) : ℝ) := by linarith
    have hDi : (1-(1/20 : ℝ))*E ≤ D i := hlo i (hsub i hi)
    rw [div_le_div_iff₀ hNpos hip]
    nlinarith
  -- the rejected sample
  have hmemN1 : (N+1) ∈ Finset.Icc 1 (N+1) := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hDlo : (1-(1/20 : ℝ))*E ≤ D (N+1) := hlo _ hmemN1
  have hDhi : D (N+1) ≤ (1+(1/20 : ℝ))*E := hhi _ hmemN1
  set lowNew := (D (N+1)-E)/((N : ℝ)+1) with hlowdef
  set upNew := (D (N+1)+E)/((N : ℝ)+1) with hupdef
  have hlowup : lowNew ≤ upNew := by
    rw [hlowdef, hupdef, div_le_div_iff₀ hN1pos hN1pos]
    nlinarith
  have hcastN1 : (((N+1 : ℕ)) : ℝ) = (N : ℝ)+1 := by push_cast; ring
  have hdisjoint : upNew < L ∨ U < lowNew := by
    by_contra hcon
    have h1 : L ≤ upNew := le_of_not_gt (fun h => hcon (Or.inl h))
    have h2 : lowNew ≤ U := le_of_not_gt (fun h => hcon (Or.inr h))
    refine hrej ⟨max L lowNew, ?_⟩
    have hmemold : max L lowNew ∈ Set.Icc L U :=
      ⟨le_max_left _ _, max_le hLU h2⟩
    have hold := (nativeCone_mem_iff _ (Finset.nonempty_Icc.mpr hN) _ _ 0 0 E _ ht).mp hmemold
    refine feasibleSlope_Icc_succ_of_mem D hold ?_
    have hmemnew : lowNew ≤ max L lowNew ∧ max L lowNew ≤ upNew :=
      ⟨le_max_right _ _, max_le h1 hlowup⟩
    rw [hcastN1, sub_zero, zero_add]
    rw [abs_le]
    constructor
    · have := hmemnew.2
      rw [hupdef, le_div_iff₀ hN1pos] at this
      linarith
    · have := hmemnew.1
      rw [hlowdef, div_le_iff₀ hN1pos] at this
      linarith
  -- an upper rejection is impossible
  have hlower : upNew < L := by
    rcases hdisjoint with h | h
    · exact h
    · exfalso
      have hlownew : lowNew ≤ (1/20 : ℝ)*E/((N : ℝ)+1) := by
        rw [hlowdef, div_le_div_iff₀ hN1pos hN1pos]
        nlinarith
      have hchain : (2-(1/20 : ℝ))*E/(N : ℝ) < (1/20 : ℝ)*E/((N : ℝ)+1) := by
        calc
          (2-(1/20 : ℝ))*E/(N : ℝ) ≤ U := hUN
          _ < lowNew := h
          _ ≤ (1/20 : ℝ)*E/((N : ℝ)+1) := hlownew
      rw [div_lt_div_iff₀ hNpos hN1pos] at hchain
      nlinarith
  -- the accepted prefix is long
  have hupbig : (2-(1/20 : ℝ))*E/((N : ℝ)+1) ≤ upNew := by
    rw [hupdef, div_le_div_iff₀ hN1pos hN1pos]
    nlinarith
  have hstrict : (2-(1/20 : ℝ))*E/((N : ℝ)+1) < (1/20 : ℝ)*E :=
    lt_of_le_of_lt hupbig (lt_of_lt_of_le hlower hLδ)
  have hprod : (2-(1/20 : ℝ))*E < (1/20 : ℝ)*E*((N : ℝ)+1) := by
    rw [div_lt_iff₀ hN1pos] at hstrict
    exact hstrict
  have h38 : (38 : ℝ) < (N : ℝ) := by nlinarith
  have h38' : 38 < N := by exact_mod_cast h38
  have hN39 : (39 : ℝ) ≤ (N : ℝ) := by
    have : (39 : ℕ) ≤ N := by omega
    exact_mod_cast this
  -- the unconstrained least-squares slope is below the old lower endpoint
  have hLS : nativeLeastSquares (Finset.Icc 1 N) (fun i => (i : ℝ)) D 0 0 ≤
      3*((1+(1/20 : ℝ))*E)/(2*(N : ℝ)+1) :=
    (nativeLeastSquares_Icc_bounds hN D (lo := (1-(1/20 : ℝ))*E)
      (fun i hi => hlo i (hsub i hi)) (fun i hi => hhi i (hsub i hi))).2
  have hLSlt : nativeLeastSquares (Finset.Icc 1 N) (fun i => (i : ℝ)) D 0 0 < L := by
    have hcmp := stationary_favorable_ls_lt_lower (E := E) (N := (N : ℝ)) (a := L)
      hE.le hN39 (lt_of_le_of_lt hupbig hlower)
    calc
      nativeLeastSquares (Finset.Icc 1 N) (fun i => (i : ℝ)) D 0 0
          ≤ 3*((1+(1/20 : ℝ))*E)/(2*(N : ℝ)+1) := hLS
      _ = 3*(1+(1/20 : ℝ))*E/(2*(N : ℝ)+1) := by ring
      _ < L := hcmp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nativeSelectedSlope, ← hLdef, ← hUdef, nativeClippedSlope,
      min_eq_left (hLSlt.le.trans hLU), max_eq_left hLSlt.le]
  · have hpos : 0 < (2-(1/20 : ℝ))*E/((N : ℝ)+1) :=
      div_pos (by nlinarith) hN1pos
    linarith [hupbig.trans hlower.le]
  · linarith
  · have := hlower
    rw [hupdef, div_lt_iff₀ hN1pos] at this
    linarith

/-! ### Reflection

The negative-carry branch is the exact reflection of the positive one.  These
four identities move the cone, the least-squares slope and the clipped
selection across the sign change, so the geometry is proved only once.
-/

theorem sup'_neg_eq_neg_inf' {ι : Type*} (s : Finset ι) (hne : s.Nonempty) (f : ι → ℝ) :
    s.sup' hne (fun i => -(f i)) = -(s.inf' hne f) := by
  refine le_antisymm (Finset.sup'_le _ _ fun i hi => neg_le_neg (Finset.inf'_le f hi)) ?_
  rw [neg_le]
  refine Finset.le_inf' _ _ fun i hi => ?_
  rw [neg_le]
  exact Finset.le_sup' (fun j => -(f j)) hi

theorem inf'_neg_eq_neg_sup' {ι : Type*} (s : Finset ι) (hne : s.Nonempty) (f : ι → ℝ) :
    s.inf' hne (fun i => -(f i)) = -(s.sup' hne f) := by
  refine le_antisymm ?_ (Finset.le_inf' _ _ fun i hi => neg_le_neg (Finset.le_sup' f hi))
  rw [le_neg]
  refine Finset.sup'_le _ _ fun i hi => ?_
  rw [le_neg]
  exact Finset.inf'_le (fun j => -(f j)) hi

theorem feasibleSlope_neg_iff {ι : Type*} (s : Finset ι) (t D : ι → ℝ) (t₀ ε m : ℝ) :
    feasibleSlope s t (fun i => -(D i)) t₀ 0 ε m ↔ feasibleSlope s t D t₀ 0 ε (-m) := by
  have key : ∀ i, -(D i)-(0+m*(t i-t₀)) = -(D i-(0+(-m)*(t i-t₀))) := by
    intro i; ring
  constructor
  · intro h i hi
    have hh := h i hi
    rw [key i, abs_neg] at hh
    exact hh
  · intro h i hi
    have hh := h i hi
    show |(-(D i))-(0+m*(t i-t₀))| ≤ ε
    rw [key i, abs_neg]
    exact hh

theorem nativeConeLower_neg {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (t D : ι → ℝ) (t₀ ε : ℝ) :
    nativeConeLower s hne t (fun i => -(D i)) t₀ 0 ε =
      -(nativeConeUpper s hne t D t₀ 0 ε) := by
  have hfun : (fun i => slopeLower (t i) (-(D i)) t₀ 0 ε) =
      (fun i => -(slopeUpper (t i) (D i) t₀ 0 ε)) := by
    funext i
    unfold slopeLower slopeUpper
    rw [show -(D i)-0-ε = -(D i-0+ε) by ring, neg_div]
  rw [nativeConeLower, hfun, sup'_neg_eq_neg_inf', nativeConeUpper]

theorem nativeConeUpper_neg {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (t D : ι → ℝ) (t₀ ε : ℝ) :
    nativeConeUpper s hne t (fun i => -(D i)) t₀ 0 ε =
      -(nativeConeLower s hne t D t₀ 0 ε) := by
  have hfun : (fun i => slopeUpper (t i) (-(D i)) t₀ 0 ε) =
      (fun i => -(slopeLower (t i) (D i) t₀ 0 ε)) := by
    funext i
    unfold slopeLower slopeUpper
    rw [show -(D i)-0+ε = -(D i-0-ε) by ring, neg_div]
  rw [nativeConeUpper, hfun, inf'_neg_eq_neg_sup', nativeConeLower]

theorem nativeLeastSquares_neg {ι : Type*} (s : Finset ι) (t D : ι → ℝ) (t₀ : ℝ) :
    nativeLeastSquares s t (fun i => -(D i)) t₀ 0 =
      -(nativeLeastSquares s t D t₀ 0) := by
  have hcross : nativeSSECross s t (fun i => -(D i)) t₀ 0 =
      -(nativeSSECross s t D t₀ 0) := by
    unfold nativeSSECross
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [nativeLeastSquares, nativeLeastSquares, hcross, neg_div]

theorem nativeClippedSlope_neg {L U A : ℝ} (hLU : L ≤ U) :
    nativeClippedSlope (-U) (-L) (-A) = -(nativeClippedSlope L U A) := by
  unfold nativeClippedSlope
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem nativeSelectedSlope_neg {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (t D : ι → ℝ) (t₀ ε : ℝ)
    (hLU : nativeConeLower s hne t D t₀ 0 ε ≤ nativeConeUpper s hne t D t₀ 0 ε) :
    nativeSelectedSlope s hne t (fun i => -(D i)) t₀ 0 ε =
      -(nativeSelectedSlope s hne t D t₀ 0 ε) := by
  rw [nativeSelectedSlope, nativeSelectedSlope, nativeConeLower_neg, nativeConeUpper_neg,
    nativeLeastSquares_neg, nativeClippedSlope_neg hLU]

/-! ### The favorable upper branch -/

theorem favorable_upper_geometry_core {N : ℕ} (hN : 1 ≤ N) (D : ℕ → ℝ) {E : ℝ}
    (hE : 0 < E)
    (hlo : ∀ i ∈ Finset.Icc 1 (N+1), D i ≤ -((1-(1/20 : ℝ))*E))
    (hhi : ∀ i ∈ Finset.Icc 1 (N+1), -((1+(1/20 : ℝ))*E) ≤ D i)
    (hfeas : ∃ m, feasibleSlope (Finset.Icc 1 N) (fun i => (i : ℝ)) D 0 0 E m)
    (hrej : ¬ ∃ m, feasibleSlope (Finset.Icc 1 (N+1)) (fun i => (i : ℝ)) D 0 0 E m) :
    nativeSelectedSlope (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
          (fun i => (i : ℝ)) D 0 0 E =
        nativeConeUpper (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
          (fun i => (i : ℝ)) D 0 0 E ∧
      nativeConeUpper (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
          (fun i => (i : ℝ)) D 0 0 E < 0 ∧
      -E ≤ nativeConeUpper (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
          (fun i => (i : ℝ)) D 0 0 E ∧
      nativeConeUpper (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
          (fun i => (i : ℝ)) D 0 0 E*((N : ℝ)+1) < D (N+1)-E := by
  have ht : ∀ i ∈ Finset.Icc 1 N, (0 : ℝ) < ((i : ℕ) : ℝ) := by
    intro i hi
    have := (Finset.mem_Icc.mp hi).1
    exact_mod_cast (by omega : 0 < i)
  have hLU : nativeConeLower (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
      (fun i => (i : ℝ)) D 0 0 E ≤
      nativeConeUpper (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)
        (fun i => (i : ℝ)) D 0 0 E :=
    (nativeCone_nonempty_iff _ (Finset.nonempty_Icc.mpr hN) _ _ 0 0 E ht).mp hfeas
  have hfeas' : ∃ m, feasibleSlope (Finset.Icc 1 N) (fun i => (i : ℝ))
      (fun i => -(D i)) 0 0 E m := by
    obtain ⟨m, hm⟩ := hfeas
    exact ⟨-m, (feasibleSlope_neg_iff _ _ _ _ _ _).mpr (by simpa only [neg_neg] using hm)⟩
  have hrej' : ¬ ∃ m, feasibleSlope (Finset.Icc 1 (N+1)) (fun i => (i : ℝ))
      (fun i => -(D i)) 0 0 E m := by
    rintro ⟨m, hm⟩
    exact hrej ⟨-m, (feasibleSlope_neg_iff _ _ _ _ _ _).mp hm⟩
  obtain ⟨hsel, hpos, hle, hthr⟩ := favorable_lower_geometry_core hN (fun i => -(D i)) hE
    (fun i hi => by have := hlo i hi; linarith)
    (fun i hi => by have := hhi i hi; linarith) hfeas' hrej'
  rw [nativeConeLower_neg] at hsel hpos hle hthr
  rw [nativeSelectedSlope_neg _ _ _ _ _ _ hLU] at hsel
  refine ⟨by linarith [neg_injective hsel], by linarith, by linarith, by linarith⟩

end SwingRepair
