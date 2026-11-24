import PLAStochastic.Swing.DenseSampling.Segments.FirstRecordingLimit
import PLAStochastic.Affine.Pinch.SlopeCone

/-!
# Slope convergence for shrinking native cones

A grid fitted slope is trapped between lower and upper constraints evaluated
at grid points approaching any fixed positive time. This proves convergence
to the literal continuous singleton cone without assuming a limit slope or
compactness of the infinite-dimensional path space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology

namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def cappedGridIndex (h : ℝ) (N : ℕ) (t : ℝ) : ℕ := min ⌊t / h⌋₊ N

theorem cappedGridIndex_le (h : ℝ) (N : ℕ) (t : ℝ) : cappedGridIndex h N t ≤ N := min_le_right _ _

theorem tendsto_cappedGridTime {ι : Type*} {l : Filter ι} {h : ι → ℝ} {N : ι → ℕ}
    (hh : ∀ i, 0 < h i) (hconv : Tendsto h l (𝓝 0)) {σ t : ℝ}
    (hN : Tendsto (fun i => (N i : ℝ) * h i) l (𝓝 σ)) (ht : 0 ≤ t) (htσ : t ≤ σ) :
    Tendsto (fun i => (cappedGridIndex (h i) (N i) t : ℝ) * h i) l (𝓝 t) := by
  have hflo : Tendsto (fun i => (⌊t / h i⌋₊ : ℝ) * h i) l (𝓝 t) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun i => t - h i) l (𝓝 t) by simpa using tendsto_const_nhds.sub hconv)
      tendsto_const_nhds
    · intro i
      have := meshFloor_gap_lt (T := t) (hh i)
      linarith
    · intro i
      exact meshFloor_mul_le ht (hh i)
  have hm := hflo.min hN
  simpa only [min_eq_left htσ, cappedGridIndex, Nat.cast_min, min_mul_of_nonneg _ _ (hh _).le] using hm

/-- Feasible sampled slopes converge to a singleton continuous cone. The
sampled prefix length is permitted to approach the pinch from either side. -/
theorem tendsto_feasible_grid_slopes (f : C(ℝ, ℝ)) {η ε σ a : ℝ} (hσ : 0 < σ)
    (hlower : continuousLowerSlope f η ε σ = a)
    (hupper : continuousUpperSlope f η ε σ = a)
    {ι : Type*} {l : Filter ι} {h m : ι → ℝ} {N : ι → ℕ}
    (hh : ∀ i, 0 < h i) (hconv : Tendsto h l (𝓝 0))
    (hN : Tendsto (fun i => (N i : ℝ) * h i) l (𝓝 σ))
    (hfit : ∀ᶠ i in l, ∀ k : ℕ, 1 ≤ k → k ≤ N i →
      |f ((k : ℝ) * h i) - η - m i * ((k : ℝ) * h i)| ≤ ε) :
    Tendsto m l (𝓝 a) := by
  have hsample (t : Ioc (0 : ℝ) σ) :
      Tendsto (fun i => (cappedGridIndex (h i) (N i) t : ℝ) * h i) l (𝓝 (t : ℝ)) :=
    tendsto_cappedGridTime hh hconv hN t.property.1.le t.property.2
  have hineq (t : Ioc (0 : ℝ) σ) : ∀ᶠ i in l,
      (f ((cappedGridIndex (h i) (N i) t : ℝ) * h i) - η - ε) /
          ((cappedGridIndex (h i) (N i) t : ℝ) * h i) ≤ m i ∧
      m i ≤ (f ((cappedGridIndex (h i) (N i) t : ℝ) * h i) - η + ε) /
          ((cappedGridIndex (h i) (N i) t : ℝ) * h i) := by
    filter_upwards [hfit, (hsample t).eventually_const_lt t.property.1] with i hi hp
    have hk : 1 ≤ cappedGridIndex (h i) (N i) t := by
      by_contra hk
      have hzero : cappedGridIndex (h i) (N i) t = 0 := by omega
      simp only [hzero, Nat.cast_zero, zero_mul, lt_self_iff_false] at hp
    have hres := abs_le.mp (hi _ hk (cappedGridIndex_le _ _ _))
    constructor
    · apply (div_le_iff₀ hp).mpr
      linarith
    · apply (le_div_iff₀ hp).mpr
      linarith
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hne : (range (fun t : Ioc (0 : ℝ) σ => (f t - η - ε) / (t : ℝ))).Nonempty :=
      ⟨_, ⟨⟨σ, hσ, le_rfl⟩, rfl⟩⟩
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := exists_lt_of_lt_csSup hne (hlower ▸ hb)
    have hc := ((((f.continuous.tendsto t).comp (hsample t)).sub_const η).sub_const ε).div
      (hsample t) t.property.1.ne'
    filter_upwards [hc.eventually_const_lt ht, hineq t] with i hi hh
    exact hi.trans_le hh.1
  · intro b hb
    have hne : (range (fun t : Ioc (0 : ℝ) σ => (f t - η + ε) / (t : ℝ))).Nonempty :=
      ⟨_, ⟨⟨σ, hσ, le_rfl⟩, rfl⟩⟩
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := exists_lt_of_csInf_lt hne (hupper ▸ hb)
    have hc := ((((f.continuous.tendsto t).comp (hsample t)).sub_const η).add_const ε).div
      (hsample t) t.property.1.ne'
    filter_upwards [hc.eventually_lt_const ht, hineq t] with i hi hh
    exact hh.2.trans_lt hi

/-- The actual scan's first emitted segment, retaining its selected slope and
fitted anchor as well as its finish index. -/
theorem scanNative_head_segment_threshold (t y : ℕ → ℝ) (E : ℝ) (K : ℕ) (hK : 1 < K)
    (hcone : ∀ j, nativePrefixFeasible t y E 0 j (y 0) ↔ j < K)
    (fuel e : ℕ) (he : 0 < e) (heK : e < K) (hfull : K ≤ e + fuel) :
    (scanNative t y E fuel 0 e (y 0) he).head? =
      some (nativeOutputSegment t y E 0 (K - 1) (y 0) (by omega)) := by
  induction fuel generalizing e with
  | zero => omega
  | succ fuel ih =>
    by_cases haccept : nativePrefixFeasible t y E 0 (e + 1) (y 0)
    · have hn := ih (e + 1) (by omega) ((hcone _).mp haccept) (by omega)
      simpa only [scanNative, if_pos haccept] using hn
    · have hKe : K ≤ e + 1 := Nat.le_of_not_gt ((hcone _).not.mp haccept)
      have heq : e = K - 1 := by omega
      simp only [scanNative, if_neg haccept, List.head?_cons]
      subst e
      rfl

/-- Read the first segment directly from the output prefix in which the first
recording is detected. The fallback only makes never-rejecting inputs total. -/
def nativeFirstObservedSegment (t y : ℕ → ℝ) (ε : ℝ) : NativeSegment :=
  (nativeStream t y ε (nativeFirstRecording t y ε + 1)).head?.getD ⟨0, 0, 0, 0⟩

def nativeFirstSlope (t y : ℕ → ℝ) (ε : ℝ) : ℝ := (nativeFirstObservedSegment t y ε).slope

theorem nativeFirstObservedSegment_eq_threshold (t y : ℕ → ℝ) (ε : ℝ) {K : ℕ} (hK : 1 < K)
    (hcone : ∀ j, nativePrefixFeasible t y ε 0 j (y 0) ↔ j < K) :
    nativeFirstObservedSegment t y ε = nativeOutputSegment t y ε 0 (K - 1) (y 0) (by omega) := by
  have hrecord := nativeFirstRecording_eq_threshold t y ε hK hcone
  unfold nativeFirstObservedSegment
  rw [hrecord, Nat.sub_add_cancel (show 1 ≤ K by omega)]
  have heq : nativeStream t y ε K = scanNative t y ε (K - 1) 0 1 (y 0) (by omega) := by
    cases K with
    | zero => omega
    | succ k => rfl
  rw [heq, scanNative_head_segment_threshold t y ε K hK hcone (K - 1) 1 (by omega) hK (by omega)]
  rfl

/-- The observed selected coefficient satisfies every accepted full-budget
constraint; the first rejected observation is excluded. -/
theorem nativeFirstSlope_mesh_feasible (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    (h : ℝ≥0) (hh : h ≠ 0) {ε : ℝ} (hε : 0 ≤ ε)
    (hfinite : finiteMeshAnchoredLifetime f h ε ≠ ∞) :
    ∀ k : ℕ, 1 ≤ k → k ≤ nativeFirstRecording (fun n => (n : ℝ) * h)
      (fun n => f ((n : ℝ) * h)) ε →
      |f ((k : ℝ) * h) - nativeFirstSlope (fun n => (n : ℝ) * h)
        (fun n => f ((n : ℝ) * h)) ε * ((k : ℝ) * h)| ≤ ε := by
  obtain ⟨K, hK, hcone⟩ := exists_nativeGrid_threshold f hf h hh hε hfinite
  have hp : 0 < (h : ℝ) := by exact_mod_cast (pos_of_ne_zero hh)
  have hc : ∀ j, nativePrefixFeasible (fun n => (n : ℝ) * h)
      (fun n => f ((n : ℝ) * h)) ε 0 j (f ((0 : ℕ) * h)) ↔ j < K := by
    simpa only [Nat.cast_zero, zero_mul] using hcone
  have hv := nativeOutputSegment_valid (fun n => (n : ℝ) * h)
    (fun n => f ((n : ℝ) * h)) (strictMono_mesh_times hp) ε 0 (K - 1) _
      (by omega) ((hc _).mpr (by omega))
  intro k hk hkN
  rw [nativeFirstRecording_eq_threshold _ _ ε hK hc] at hkN
  have hb := hv.feasible k (Finset.mem_Icc.mpr ⟨hk, hkN⟩)
  unfold nativeFirstSlope
  rw [nativeFirstObservedSegment_eq_threshold _ _ ε hK hc]
  simpa only [nativeOutputSegment, Nat.cast_zero, zero_mul, hf, sub_zero, zero_add] using hb

/-- The actual native first selected SSE coefficient converges to the unique
continuous feasible slope. The proof uses its proved feasibility, not an
assumed convergence of the least-squares minimizer. -/
theorem tendsto_nativeFirstSlope_mesh (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    {ε : ℝ} (hε : 0 < ε) {σ : ℝ≥0} (hσ : anchoredLifetime f ε = σ)
    {a : ℝ} (ha : ∀ t : Icc (0 : ℝ) (σ : ℝ), |f t - a * (t : ℝ)| ≤ ε)
    {ι : Type*} {l : Filter ι} {h : ι → ℝ≥0} (hh : ∀ i, h i ≠ 0)
    (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    Tendsto (fun i => nativeFirstSlope (fun n => (n : ℝ) * h i)
      (fun n => f ((n : ℝ) * h i)) ε) l (𝓝 a) := by
  have hzero : |f 0| < ε := by simpa only [hf, abs_zero] using hε
  have hfinite : anchoredLifetime f ε ≠ ∞ := by rw [hσ]; exact ENNReal.coe_ne_top
  have hposE : (0 : ℝ≥0∞) < (σ : ℝ≥0∞) := by
    rw [← hσ]
    exact anchoredLifetime_pos f hf hε
  have hpos : 0 < (σ : ℝ) := ENNReal.coe_pos.mp hposE
  have herr : anchoredError (intervalPath f σ) = ε :=
    (anchoredTimeError_eq_interval σ.property f).symm.trans (anchoredTimeError_at_lifetime f hzero.le hσ)
  have hu : ∀ b, continuousSlopeFeasible f 0 ε σ b → b = a := by
    intro b hb
    have hb' : ∀ t : Icc (0 : ℝ) (σ : ℝ), |f t - b * (t : ℝ)| ≤ ε := by
      simpa only [continuousSlopeFeasible, sub_zero] using hb
    exact anchored_feasible_slope_unique σ.property hε (intervalPath f σ) hzero herr hb' ha
  have ha' : continuousSlopeFeasible f 0 ε σ a := by
    simpa only [continuousSlopeFeasible, sub_zero] using ha
  have hcone := continuousCone_eq_of_unique hpos ha' hu
  have hp (i : ι) : 0 < (h i : ℝ) := by exact_mod_cast (pos_of_ne_zero (hh i))
  apply tendsto_feasible_grid_slopes f hpos hcone.1 hcone.2
    (N := fun i => nativeFirstRecording (fun n => (n : ℝ) * h i)
      (fun n => f ((n : ℝ) * h i)) ε) hp hconv
  · have ht := tendsto_nativeFirstRecording_mesh f hf hε.le hfinite hh hconv
    simpa only [hσ, ENNReal.coe_toReal, mul_comm] using ht
  · have ht := tendsto_finiteMeshAnchoredLifetime f ε hp hconv
    filter_upwards [ht.eventually_lt_const (lt_top_iff_ne_top.mpr hfinite)] with i hi
    simpa only [sub_zero] using nativeFirstSlope_mesh_feasible f hf (h i) (hh i) hε.le hi.ne

end SwingRepair

