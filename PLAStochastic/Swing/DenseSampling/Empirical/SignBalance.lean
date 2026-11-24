import PLAStochastic.Swing.DenseSampling.Empirical.LongSegmentProportion
import PLAStochastic.Swing.DenseSampling.Empirical.ShortIntervalSignReversal

/-! # A uniform balance bound for actual native boundary signs -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- Pairing adjacent values counts each interior value twice. -/
theorem sum_adjacent_identity (s : ℕ → ℝ) (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1), s k = s 0 + s n +
      ∑ k ∈ Finset.range n, (s k + s (k + 1)) := by
  induction n with
  | zero => simp [two_mul]
  | succ n ih =>
      rw [Finset.sum_range_succ (f := s) (n := n + 1),
        Finset.sum_range_succ (f := fun k => s k + s (k + 1)) (n := n)]
      linarith

/-- A telescoping cost on nonalternating edges controls the total sign sum. -/
theorem sum_sign_bound_of_adjacent_cost (s b : ℕ → ℝ) {c T : ℝ}
    (hc : 0 ≤ c) (n : ℕ) (hs : ∀ k ≤ n, |s k| ≤ 1)
    (hb : b n - b 0 ≤ T)
    (hedge : ∀ k < n, |s k + s (k + 1)| ≤ c * (b (k + 1) - b k)) :
    |∑ k ∈ Finset.range (n + 1), s k| ≤ 1 + c * T / 2 := by
  have hid := sum_adjacent_identity s n
  have htel (m : ℕ) : ∑ k ∈ Finset.range m, (b (k + 1) - b k) = b m - b 0 := by
    induction m with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hedgeSum : |∑ k ∈ Finset.range n, (s k + s (k + 1))| ≤ c * (b n - b 0) := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, |s k + s (k + 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, c * (b (k + 1) - b k) :=
        Finset.sum_le_sum (fun k hk => hedge k (Finset.mem_range.mp hk))
      _ = c * (b n - b 0) := by rw [← Finset.mul_sum, htel n]
  have hsum : |2 * ∑ k ∈ Finset.range (n + 1), s k| ≤ 2 + c * T := by
    rw [hid]
    calc
      _ ≤ |s 0 + s n| + |∑ k ∈ Finset.range n, (s k + s (k + 1))| := abs_add_le _ _
      _ ≤ |s 0| + |s n| + |∑ k ∈ Finset.range n, (s k + s (k + 1))| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 2 + c * T := by
        have h0 := hs 0 (Nat.zero_le n)
        have hn := hs n le_rfl
        have hcost := mul_le_mul_of_nonneg_left hb hc
        linarith
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsum
  linarith

def nativeRecordingPolarity (t y : ℕ → ℝ) (segs : List NativeSegment) (k : ℕ) : ℝ :=
  nativePolarity (nativeSegmentEndpoint t (nativeSegmentAt segs k) - y (nativeSegmentAt segs k).finish)

def nativeCompletedSignSum (t y : ℕ → ℝ) (segs : List NativeSegment) : ℝ :=
  ∑ k ∈ Finset.range (segs.length - 1), nativeRecordingPolarity t y segs k

/-- The sign imbalance is bounded by a constant depending only on the total
horizon and the short-segment threshold, not on the number of recordings. -/
theorem NativeChain.signSum_bound_of_short_flip {t y : ℕ → ℝ} (ht : Monotone t)
    {ε : ℝ} {s last : ℕ} {q : ℝ} {segs : List NativeSegment}
    (hc : NativeChain t y ε s q last segs) {ρ : ℝ} (hρ : 0 < ρ)
    (hflip : ∀ seg ∈ segs,
      (¬ nativePrefixFeasible t y ε seg.start (seg.finish + 1) seg.anchorValue) →
      nativeElapsedTime t seg < ρ →
      nativePolarity (nativeSegmentEndpoint t seg - y seg.finish) =
        -nativePolarity (seg.anchorValue - y seg.start)) :
    |nativeCompletedSignSum t y segs| ≤ 1 + (t last - t s) / ρ := by
  by_cases hz : segs.length - 1 = 0
  · simp only [nativeCompletedSignSum, hz, Finset.sum_range_zero, abs_zero]
    have hgap : 0 ≤ t last - t s := sub_nonneg.mpr (ht hc.start_le_finish)
    have hdiv := div_nonneg hgap hρ.le
    linarith
  let n := segs.length - 1 - 1
  have hlen : n + 1 = segs.length - 1 := by dsimp only [n]; omega
  have hn : n < segs.length := by omega
  have h0 : 0 < segs.length := by omega
  let b := fun k => t (nativeSegmentAt segs k).finish
  let p := nativeRecordingPolarity t y segs
  have hb : b n - b 0 ≤ t last - t s := by
    have hn' := ht (hc.getElem_bounds hn).2.1
    have h0' := ht ((hc.getElem_bounds h0).1.trans (hc.getElem_bounds h0).2.2.le)
    dsimp only [b]
    rw [nativeSegmentAt_eq_getElem hn, nativeSegmentAt_eq_getElem h0]
    linarith
  have hedge : ∀ k < n, |p k + p (k + 1)| ≤ (2 / ρ) * (b (k + 1) - b k) := by
    intro k hk
    have hkn : k + 1 < segs.length := by omega
    have hk0 : k < segs.length := by omega
    have hkr : (k + 1) + 1 < segs.length := by omega
    have hj := hc.getElem_succ hkn
    have hr := hc.getElem_reject hkr
    have hdt : nativeElapsedTime t segs[k + 1] = b (k + 1) - b k := by
      dsimp only [nativeElapsedTime, b]
      rw [nativeSegmentAt_eq_getElem hkn, nativeSegmentAt_eq_getElem hk0, hj.1]
    have hd0 : 0 ≤ b (k + 1) - b k := by
      rw [← hdt]
      exact sub_nonneg.mpr (ht (hc.getElem_valid hkn).positive.le)
    by_cases hshort : nativeElapsedTime t segs[k + 1] < ρ
    · have hf := hflip segs[k + 1] (List.getElem_mem hkn) hr hshort
      have hp : p (k + 1) = -p k := by
        dsimp only [p, nativeRecordingPolarity]
        rw [nativeSegmentAt_eq_getElem hkn, nativeSegmentAt_eq_getElem hk0,
          hf, hj.1, hj.2]
      rw [hp, add_neg_cancel, abs_zero]
      exact mul_nonneg (div_nonneg (by norm_num) hρ.le) hd0
    · have hbig : ρ ≤ b (k + 1) - b k := by rw [← hdt]; exact le_of_not_gt hshort
      have habs : |p k + p (k + 1)| ≤ 2 := by
        have hh := abs_add_le (p k) (p (k + 1))
        simp only [p, nativeRecordingPolarity, nativePolarity_abs] at hh
        norm_num at hh ⊢
        exact hh
      have hcancel : (2 / ρ) * ρ = 2 := div_mul_cancel₀ _ hρ.ne'
      have hm := mul_le_mul_of_nonneg_left hbig (div_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hρ.le)
      exact habs.trans (by linarith)
  have hm := sum_sign_bound_of_adjacent_cost p b (show (0 : ℝ) ≤ 2 / ρ by positivity) n
    (fun k _ => (nativePolarity_abs _).le) hb hedge
  rw [hlen] at hm
  change |nativeCompletedSignSum t y segs| ≤ 1 + (2 / ρ) * (t last - t s) / 2 at hm
  convert hm using 1
  ring

/-- Uniform short-segment reversal gives a uniform bound on the sign
imbalance of the actual output, including variable finite observation horizons. -/
theorem exists_uniform_native_signSum_bound (f : C(ℝ, ℝ)) {T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → ∀ N : ℕ, (N : ℝ) * h ≤ T →
      |nativeCompletedSignSum (fun j => (j : ℝ) * h) (fun j => f ((j : ℝ) * h))
        (nativeStream (fun j => (j : ℝ) * h) (fun j => f ((j : ℝ) * h)) ε N)| ≤ C := by
  obtain ⟨ρ, δ, hρ, hδ, hflip⟩ := exists_uniform_native_short_sign_flip f hT hε
  refine ⟨1 + T / ρ, δ, by positivity, hδ, ?_⟩
  intro h hh hhδ N hN
  have ht := strictMono_mesh_times hh
  have hc := nativeStream_spec (fun j => (j : ℝ) * h) (fun j => f ((j : ℝ) * h)) ht hε.le N
  have hb := hc.signSum_bound_of_short_flip ht.monotone hρ ?_
  · have hineq := div_le_div_of_nonneg_right hN hρ.le
    simp only [Nat.cast_zero, zero_mul, sub_zero] at hb
    linarith
  intro seg hs hr hshort
  have hbounds := hc.segment_bounds seg hs
  have heT : (seg.finish : ℝ) * h ≤ T := (mul_le_mul_of_nonneg_right (by exact_mod_cast hbounds.2.1) hh.le).trans hN
  have hq := hc.anchor_errors (by simp only [sub_self, abs_zero]; exact hε.le) seg hs
  have hv := hc.valid_segments seg hs
  exact hflip h hh hhδ seg.start seg.finish hv.positive heT hshort
    seg.anchorValue seg.slope hq hv.feasible hr

/-- Once the actual completed count diverges, its average boundary polarity
converges to zero. -/
theorem native_sign_average_tendsto_zero (f : C(ℝ, ℝ)) {T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) {ι : Type*} {l : Filter ι}
    {h : ι → ℝ} {N : ι → ℕ} (hh : ∀ i, 0 < h i) (hconv : Tendsto h l (𝓝 0))
    (hN : ∀ i, (N i : ℝ) * h i ≤ T)
    (hcount : Tendsto (fun i => nativeCompletedCount (fun j => (j : ℝ) * h i)
      (fun j => f ((j : ℝ) * h i)) ε (N i)) l atTop) :
    Tendsto (fun i => nativeCompletedSignSum (fun j => (j : ℝ) * h i)
      (fun j => f ((j : ℝ) * h i))
      (nativeStream (fun j => (j : ℝ) * h i) (fun j => f ((j : ℝ) * h i)) ε (N i)) /
      (nativeCompletedCount (fun j => (j : ℝ) * h i)
        (fun j => f ((j : ℝ) * h i)) ε (N i) : ℝ)) l (𝓝 0) := by
  obtain ⟨C, δ, hC, hδ, hbound⟩ := exists_uniform_native_signSum_bound f hT hε
  have hden := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hcount
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun i => abs_nonneg _)) _ (hden.const_div_atTop C)
  filter_upwards [hconv.eventually_lt_const hδ] with i hi
  rw [abs_div]
  rw [abs_of_nonneg (show 0 ≤ (nativeCompletedCount (fun j => (j : ℝ) * h i)
    (fun j => f ((j : ℝ) * h i)) ε (N i) : ℝ) from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (hbound (h i) (hh i) hi (N i) (hN i)) (Nat.cast_nonneg _)

theorem nativePolarity_div_pos (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    nativePolarity (x / ε) = nativePolarity x := by
  have heq : 0 ≤ x / ε ↔ 0 ≤ x := by simpa only [zero_mul] using (le_div_iff₀ hε (a := 0) (b := x))
  simp only [nativePolarity, heq]

/-- Uniform boundary concentration controls the distance from each actual
normalized recording error to its own sign. -/
theorem exists_uniform_native_rounding (f : C(ℝ, ℝ)) {T ε r : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → ∀ N : ℕ, (N : ℝ) * h ≤ T →
      ∀ k : ℕ, k < nativeCompletedCount (fun j => (j : ℝ) * h)
        (fun j => f ((j : ℝ) * h)) ε N →
      let seg := nativeSegmentAt (nativeStream (fun j => (j : ℝ) * h)
        (fun j => f ((j : ℝ) * h)) ε N) k
      let x := (nativeSegmentEndpoint (fun j => (j : ℝ) * h) seg - f ((seg.finish : ℝ) * h)) / ε
      |x - nativePolarity x| < r := by
  obtain ⟨δ, hδ, hbound⟩ := exists_uniform_native_boundary_control f hT hε (mul_pos hε hr)
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhδ N hN k hk
  have ht := strictMono_mesh_times hh
  have hc := nativeStream_spec (fun j => (j : ℝ) * h) (fun j => f ((j : ℝ) * h)) ht hε.le N
  have hk1 : k + 1 < (nativeStream (fun j => (j : ℝ) * h) (fun j => f ((j : ℝ) * h)) ε N).length := by
    unfold nativeCompletedCount at hk
    omega
  have hk0 : k < (nativeStream (fun j => (j : ℝ) * h) (fun j => f ((j : ℝ) * h)) ε N).length := by omega
  dsimp only
  rw [nativeSegmentAt_eq_getElem hk0]
  let seg := (nativeStream (fun j => (j : ℝ) * h) (fun j => f ((j : ℝ) * h)) ε N)[k]
  have hv := hc.getElem_valid hk0
  have hb := hc.getElem_bounds hk0
  have hq := hc.getElem_anchor_error (by simp only [sub_self, abs_zero]; exact hε.le) hk0
  have hrej := hc.getElem_reject hk1
  have heT : (seg.finish : ℝ) * h ≤ T :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hb.2.1) hh.le).trans hN
  have he := hv.feasible seg.finish (Finset.mem_Icc.mpr ⟨by exact hv.positive, le_rfl⟩)
  rw [abs_sub_comm] at he
  have hx : |(nativeSegmentEndpoint (fun j => (j : ℝ) * h) seg - f ((seg.finish : ℝ) * h)) / ε| ≤ 1 := by
    rw [abs_div, abs_of_pos hε]
    exact (div_le_one hε).mpr he
  rw [nativePolarity_distance hx, abs_div, abs_of_pos hε]
  have hdef := (hbound h hh hhδ seg.start seg.finish hv.positive heT seg.anchorValue seg.slope
    hq hv.feasible hrej).2.2
  change ε - |nativeSegmentEndpoint (fun j => (j : ℝ) * h) seg - f ((seg.finish : ℝ) * h)| < ε * r at hdef
  have heq : 1 - |nativeSegmentEndpoint (fun j => (j : ℝ) * h) seg - f ((seg.finish : ℝ) * h)| / ε =
      (ε - |nativeSegmentEndpoint (fun j => (j : ℝ) * h) seg - f ((seg.finish : ℝ) * h)|) / ε := by
    rw [sub_div, div_self hε.ne']
  rw [heq]
  exact (div_lt_iff₀ hε).mpr (by simpa only [mul_comm] using hdef)

end SwingRepair
