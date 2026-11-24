import PLAStochastic.Swing.Gaussian.HalfLine.ExponentialStopping
import PLAStochastic.Swing.Gaussian.StripExit.Ballot

/-! Stability of the actual finite hitting prefix under small changes of start and drift. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} {X : ℕ → Ω → ℝ}

/-- Each fixed walk position depends continuously on its start and drift. -/
theorem gaussianDriftWalk_tendsto_parameters {ι : Type*} {l : Filter ι}
    {x a : ι → ℝ} {w b : ℝ} (hx : Tendsto x l (𝓝 w)) (ha : Tendsto a l (𝓝 b))
    (n : ℕ) (ω : Ω) :
    Tendsto (fun i => gaussianDriftWalk X (x i) (a i) n ω) l (𝓝 (gaussianDriftWalk X w b n ω)) :=
  (hx.add_const (cumulativeSamples X n ω)).add (ha.mul_const (n : ℝ))

/-- A finite hitting prefix with no zero noninitial positions is eventually exactly unchanged. -/
theorem gaussianHalfLineExit_eventually_eq_of_no_zero {ι : Type*} {l : Filter ι}
    {x a : ι → ℝ} {w b : ℝ} (hx : Tendsto x l (𝓝 w)) (ha : Tendsto a l (𝓝 b))
    (hxn : ∀ᶠ i in l, 0 ≤ x i) (hw : 0 ≤ w) {ω : Ω}
    (ht : gaussianHalfLineExit X w b ω ≠ ⊤)
    (hz : ∀ j : ℕ, 0 < j → gaussianDriftWalk X w b j ω ≠ 0) :
    ∀ᶠ i in l, gaussianHalfLineExit X (x i) (a i) ω = gaussianHalfLineExit X w b ω := by
  have hmem : ω ∈ ⋃ n, gaussianHalfLineExitSlice X w b n := by
    rw [← gaussianHalfLineFinite_eq_iUnion hw]
    exact ht
  obtain ⟨n, hn⟩ := mem_iUnion.mp hmem
  have hτ := (gaussianHalfLineExit_eq_succ_iff X w b n ω).mpr hn
  have hs : ∀ᶠ i in l, ∀ j ∈ Finset.range (n+1), 0 ≤ gaussianDriftWalk X (x i) (a i) j ω := by
    apply (eventually_all_finset _).mpr
    intro j hj
    have hj' : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    by_cases hj0 : j = 0
    · simpa only [hj0, gaussianDriftWalk_zero] using hxn
    · have hp : 0 < gaussianDriftWalk X w b j ω :=
        lt_of_le_of_ne (hn.1 j hj') (Ne.symm (hz j (Nat.pos_of_ne_zero hj0)))
      exact ((gaussianDriftWalk_tendsto_parameters hx ha j ω).eventually (Ioi_mem_nhds hp)).mono
        (fun _ hi => hi.le)
  have he : ∀ᶠ i in l, gaussianDriftWalk X (x i) (a i) (n+1) ω < 0 :=
    (gaussianDriftWalk_tendsto_parameters hx ha (n+1) ω).eventually (Iio_mem_nhds hn.2)
  filter_upwards [hs, he] with i hi hie
  rw [hτ]
  apply (gaussianHalfLineExit_eq_succ_iff X (x i) (a i) n ω).mpr
  exact ⟨fun j hj => hi j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)), hie⟩

/-- Once the selected prefix is unchanged, its actual overshoot converges. -/
theorem gaussianHalfLineOvershoot_tendsto_of_no_zero {ι : Type*} {l : Filter ι}
    {x a : ι → ℝ} {w b : ℝ} (hx : Tendsto x l (𝓝 w)) (ha : Tendsto a l (𝓝 b))
    (hxn : ∀ᶠ i in l, 0 ≤ x i) (hw : 0 ≤ w) {ω : Ω}
    (ht : gaussianHalfLineExit X w b ω ≠ ⊤)
    (hz : ∀ j : ℕ, 0 < j → gaussianDriftWalk X w b j ω ≠ 0) :
    Tendsto (fun i => gaussianHalfLineOvershoot X (x i) (a i) ω) l
      (𝓝 (gaussianHalfLineOvershoot X w b ω)) := by
  have he := gaussianHalfLineExit_eventually_eq_of_no_zero hx ha hxn hw ht hz
  have hp := (gaussianDriftWalk_tendsto_parameters (X := X) hx ha ((gaussianHalfLineExit X w b ω).untopD 0) ω).neg
  simp only [gaussianHalfLineOvershoot, if_neg ht, gaussianHalfLineExitPosition]
  apply hp.congr'
  filter_upwards [he] with i hi
  simp only [hi, if_neg ht]

variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- The already proved ballot bound forces zero-drift hitting in finite time almost surely. -/
theorem gaussianHalfLineExit_zero_finite_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {w : ℝ} (hw : 0 ≤ w) :
    ∀ᵐ ω ∂μ, gaussianHalfLineExit X w 0 ω ≠ ⊤ := by
  have := hi.isProbabilityMeasure
  have hsub (n : ℕ) : {ω | gaussianHalfLineExit X w 0 ω = ⊤} ⊆ gaussianSurvivalEvent X w 0 n := by
    intro ω hω j hj
    have hsurv := (lt_gaussianHalfLineExit_iff X w 0 n ω).mp
      (show (n : WithTop ℕ) < gaussianHalfLineExit X w 0 ω by rw [hω]; exact WithTop.coe_lt_top n)
    exact hsurv j hj.2
  have hlim : Tendsto (fun n : ℕ => gaussianBallotConstant*(w+1)*(Real.sqrt (n : ℝ))⁻¹)
      atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using!
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).const_mul
        (gaussianBallotConstant*(w+1))
  have hz : μ.real {ω | gaussianHalfLineExit X w 0 ω = ⊤} = 0 := by
    apply le_antisymm _ measureReal_nonneg
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hb := gaussian_ballot_bound hX hi hG hw (le_refl (0 : ℝ)) (by norm_num)
      (show 0 < n by omega)
    exact (measureReal_mono (hsub n)).trans (by simpa only [zero_add] using hb)
  rw [ae_iff]
  simpa only [not_ne_iff] using (measureReal_eq_zero_iff).mp hz

/-- The noninitial positions have nondegenerate Gaussian laws, so none is exactly zero almost surely. -/
theorem gaussianDriftWalk_nonzero_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (w b : ℝ) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ, 0 < n → gaussianDriftWalk X w b n ω ≠ 0 := by
  apply ae_all_iff.mpr
  intro n
  by_cases hn : 0 < n
  · have hl : HasLaw (cumulativeSamples X n) (gaussianReal 0 (n : ℝ≥0)) μ := by
      simpa [cumulativeSamples] using! gaussian_weighted_sum_hasLaw hX hi hG (Finset.range n) (fun _ => 1)
    have hv : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have := nullSingletonClass_gaussianReal (μ := 0) hv
    have hm : μ {ω | cumulativeSamples X n ω = -(w+b*n)} = 0 := by
      rw [hl.measure_eq (p := fun z => z = -(w+b*n)) (measurableSet_singleton _)]
      exact measure_singleton _
    have he : {ω | gaussianDriftWalk X w b n ω = 0} = {ω | cumulativeSamples X n ω = -(w+b*n)} := by
      ext ω
      change _ = 0 ↔ _ = _
      unfold gaussianDriftWalk
      constructor <;> intro h <;> linarith
    have hae : ∀ᵐ ω ∂μ, gaussianDriftWalk X w b n ω ≠ 0 := by
      rw [ae_iff]
      simpa only [not_ne_iff, he] using hm
    exact hae.mono (fun _ h _ => h)
  · exact ae_of_all _ (fun _ h => (hn h).elim)

/-- Actual small-drift coupling: the hitting index is eventually equal and the selected overshoot converges. -/
theorem gaussianHalfLine_small_drift_ae {ι : Type*} {l : Filter ι}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ι → ℝ} {w : ℝ} (hx : Tendsto x l (𝓝 w)) (ha : Tendsto a l (𝓝 0))
    (hxn : ∀ᶠ i in l, 0 ≤ x i) (hw : 0 ≤ w) :
    ∀ᵐ ω ∂μ,
      (∀ᶠ i in l, gaussianHalfLineExit X (x i) (a i) ω = gaussianHalfLineExit X w 0 ω) ∧
      Tendsto (fun i => gaussianHalfLineOvershoot X (x i) (a i) ω) l
        (𝓝 (gaussianHalfLineOvershoot X w 0 ω)) := by
  filter_upwards [gaussianHalfLineExit_zero_finite_ae hX hi hG hw,
    gaussianDriftWalk_nonzero_ae hX hi hG w 0] with ω ht hz
  exact ⟨gaussianHalfLineExit_eventually_eq_of_no_zero hx ha hxn hw ht hz,
    gaussianHalfLineOvershoot_tendsto_of_no_zero hx ha hxn hw ht hz⟩

end SwingRepair
