import PLAStochastic.Swing.Entrance.Grid.RegularPath

/-!
# Grid limits of the adaptive cut, (E6) and (E9)

Fix an entrance-regular continuous path `f` with pinch `σ` and budgets `E → ∞`, and let
`y = E f(· h_E)`, `h_E = E^{-2}`, be the rescaled grid path of the exact coupling. Then

* the native first recording `N_E` of `f` on the mesh satisfies `N_E h_E → σ`, and for
  `1 ≤ j` the cone of `y` is nonempty at `j` iff `j ≤ N_E` (`J = N_E + 1` is the first
  rejection);
* eventually the cut `τ` is finite with `2 ≤ τ ≤ N_E + 1`, and `τ / E² → σ`: before any fixed
  `T < σ` the grid cone keeps rescaled width at least `c E` for some `c > 0`, because a line
  fits `f` on `[0, T]` with error strictly below one and `|f| ≤ 1/2` near the origin;
* `E a_{τ-1}`, `E b_{τ-1}` and the frozen endpoint `E β` converge to the pinch slope
  `m_* = entranceSlope f`;
* the side `s_E` eventually equals the terminal sign `entranceSign f`, since
  `s_E (f(τ h) - E β τ h) = 1 - D / E` with `0 ≤ D/E` small and `f(σ) - m_* σ = ±1`.

The area limit (E20) is in `PLAStochastic.Swing.Entrance.Grid.Area`.
-/

open MeasureTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology

namespace SwingRepair

noncomputable section

/-! ## Elementary bounds -/

theorem ne_zero_of_one_le_nnreal {E : ℝ≥0} (h : 1 ≤ E) : E ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le one_pos h)

/-- `d_E / E = E^{-3/4} → 0`. -/
theorem entranceCutLevel_div_tendsto :
    Tendsto (fun x : ℝ => entranceCutLevel x / x) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (show (0 : ℝ) < 3 / 4 by norm_num)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  unfold entranceCutLevel
  rw [← Real.rpow_sub_one hx.ne']
  norm_num

/-- Two-regime lower bound for the rescaled gap of a sampled cone before the pinch: near the
origin `|f| ≤ 1/2` forces gap at least `1/v`, and afterwards a fit with error `d₀ < 1` forces gap
at least `2 (1 - d₀)/T`. -/
theorem entrance_gap_bound {f : ℝ → ℝ} {T δ₀ d₀ a : ℝ} (hT : 0 < T) (hd : d₀ < 1)
    (hsmall : ∀ t, 0 ≤ t → t ≤ δ₀ → |f t| ≤ 1 / 2)
    (hfit : ∀ t, 0 ≤ t → t ≤ T → |f t - a * t| ≤ d₀) {s u v : ℝ} (hs : 0 < s) (hu : 0 < u)
    (hsv : s ≤ v) (huv : u ≤ v) (hv : v ≤ T) :
    min 1 (δ₀ * (2 * (1 - d₀) / T)) ≤ v * ((f u + 1) / u - (f s - 1) / s) := by
  have hvpos : 0 < v := hs.trans_le hsv
  by_cases hvδ : v ≤ δ₀
  · apply (min_le_left _ _).trans
    have hfu := abs_le.mp (hsmall u hu.le (huv.trans hvδ))
    have hfs := abs_le.mp (hsmall s hs.le (hsv.trans hvδ))
    have h1 : 1 / (2 * v) ≤ (f u + 1) / u := by
      rw [div_le_div_iff₀ (by positivity) hu]
      nlinarith
    have h2 : 1 / (2 * v) ≤ -((f s - 1) / s) := by
      rw [← neg_div, div_le_div_iff₀ (by positivity) hs]
      nlinarith
    have h3 : v * (1 / (2 * v) + 1 / (2 * v)) = 1 := by
      field_simp
      ring
    have h4 : v * (1 / (2 * v) + 1 / (2 * v)) ≤ v * ((f u + 1) / u - (f s - 1) / s) :=
      mul_le_mul_of_nonneg_left (by linarith) hvpos.le
    linarith
  · push Not at hvδ
    apply (min_le_right _ _).trans
    have hfu := abs_le.mp (hfit u hu.le (huv.trans hv))
    have hfs := abs_le.mp (hfit s hs.le (hsv.trans hv))
    have hc : 0 ≤ (1 - d₀) / T := div_nonneg (by linarith) hT.le
    have hcu : (1 - d₀) / T * u ≤ 1 - d₀ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hT]
      nlinarith
    have hcs : (1 - d₀) / T * s ≤ 1 - d₀ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hT]
      nlinarith
    have h1 : a + (1 - d₀) / T ≤ (f u + 1) / u := by
      rw [le_div_iff₀ hu]
      nlinarith
    have h2 : (f s - 1) / s ≤ a - (1 - d₀) / T := by
      rw [div_le_iff₀ hs]
      nlinarith
    have hdiff : 2 * ((1 - d₀) / T) ≤ (f u + 1) / u - (f s - 1) / s := by linarith
    calc δ₀ * (2 * (1 - d₀) / T) = δ₀ * (2 * ((1 - d₀) / T)) := by ring
      _ ≤ v * (2 * ((1 - d₀) / T)) :=
          mul_le_mul_of_nonneg_right hvδ.le (by positivity)
      _ ≤ v * ((f u + 1) / u - (f s - 1) / s) :=
          mul_le_mul_of_nonneg_left hdiff hvpos.le

/-! ## Pointwise identities on the grid path -/

/-- The native first recording of `f` on the mesh `h_E = E^{-2}` at tolerance one. -/
def entranceMeshRecording (f : ℝ → ℝ) (E : ℝ≥0) : ℕ :=
  nativeFirstRecording (fun n => (n : ℝ) * (gaussianBudgetMesh E : ℝ))
    (fun n => f ((n : ℝ) * (gaussianBudgetMesh E : ℝ))) 1

/-- `s_E (f(τ h) - E β τ h) · E = E - D` at a finite cut of the grid path. -/
theorem gridPath_side_residual {f : ℝ → ℝ} (hf : f 0 = 0) {E : ℝ≥0} (hE1 : 1 ≤ E) {n : ℕ}
    (hn : entranceCut (entranceGridPath f E) E = n) :
    (E : ℝ) * (entranceSide (entranceGridPath f E) E n *
      (f ((n : ℝ) * gaussianBudgetMesh E) -
        ((E : ℝ) * entranceFrozenSlope (entranceGridPath f E) E n) *
          ((n : ℝ) * gaussianBudgetMesh E))) =
      E - entranceWidth (entranceGridPath f E) E n := by
  have hE1' : (1 : ℝ) ≤ E := by exact_mod_cast hE1
  have hres := entranceCut_reflected_residual (entranceGridPath_zero f hf E) E.coe_nonneg
    (entranceCutLevel_lt_two_mul hE1') hn
  have hEh := sq_mul_gaussianBudgetMesh (ne_zero_of_one_le_nnreal hE1)
  rw [← hres]
  unfold entranceGridPath
  linear_combination (-(entranceSide (fun n => (E : ℝ) * f ((n : ℝ) * gaussianBudgetMesh E)) E n *
    entranceFrozenSlope (fun n => (E : ℝ) * f ((n : ℝ) * gaussianBudgetMesh E)) E n * n)) * hEh

/-! ## Limits along a family of budgets -/

section Grid

variable {f : C(ℝ, ℝ)} {σ : ℝ≥0} (hr : EntranceRegular f σ)
  {ι : Type*} {l : Filter ι} {E : ι → ℝ≥0} (hE1 : ∀ i, 1 ≤ E i)
  (hE : Tendsto (fun i => (E i : ℝ)) l atTop)
include hr hE1 hE

/-- The first recording on the mesh converges to the pinch: `N_E h_E → σ`. -/
theorem tendsto_meshRecording_mul :
    Tendsto (fun i => (gaussianBudgetMesh (E i) : ℝ) * entranceMeshRecording f (E i)) l
      (𝓝 σ) := by
  have hfin : anchoredLifetime f 1 ≠ ⊤ := by rw [hr.lifetime]; exact ENNReal.coe_ne_top
  have h := tendsto_nativeFirstRecording_mesh f hr.zero zero_le_one hfin
    (h := fun i => gaussianBudgetMesh (E i))
    (fun i => gaussianBudgetMesh_ne_zero (hE1 i)) (gaussianBudgetMesh_tendsto hE)
  rw [hr.lifetime, ENNReal.coe_toReal] at h
  exact h

/-- Eventually the cone of the grid path is nonempty exactly up to `N_E`. -/
theorem eventually_cone_iff :
    ∀ᶠ i in l, 1 ≤ entranceMeshRecording f (E i) ∧ ∀ j, 1 ≤ j →
      (entranceLower (entranceGridPath f (E i)) (E i) j ≤
          entranceUpper (entranceGridPath f (E i)) (E i) j ↔
        j ≤ entranceMeshRecording f (E i)) := by
  have hp : ∀ i, 0 < (gaussianBudgetMesh (E i) : ℝ) :=
    fun i => gaussianBudgetMesh_pos (ne_zero_of_one_le_nnreal (hE1 i))
  have hlife := tendsto_finiteMeshAnchoredLifetime f 1 hp (gaussianBudgetMesh_tendsto hE)
  have hfin : anchoredLifetime f 1 ≠ ⊤ := by rw [hr.lifetime]; exact ENNReal.coe_ne_top
  filter_upwards [hlife.eventually_lt_const (lt_top_iff_ne_top.mpr hfin)] with i hi
  obtain ⟨K, hK, hcone⟩ := exists_nativeGrid_threshold f hr.zero (gaussianBudgetMesh (E i))
    (gaussianBudgetMesh_ne_zero (hE1 i)) zero_le_one hi.ne
  have hc : ∀ j, nativePrefixFeasible (fun n => (n : ℝ) * (gaussianBudgetMesh (E i) : ℝ))
      (fun n => f ((n : ℝ) * (gaussianBudgetMesh (E i) : ℝ))) 1 0 j
      (f (((0 : ℕ) : ℝ) * (gaussianBudgetMesh (E i) : ℝ))) ↔ j < K := by
    simpa only [Nat.cast_zero, zero_mul] using hcone
  have hrec : entranceMeshRecording f (E i) = K - 1 :=
    nativeFirstRecording_eq_threshold _ _ 1 hK hc
  refine ⟨by omega, fun j hj => ?_⟩
  rw [entranceGridPath_cone_iff hr.zero (ne_zero_of_one_le_nnreal (hE1 i)) hj,
    ← nativePrefixFeasible_mesh_iff hr.zero, hcone j, hrec]
  constructor <;> intro <;> omega

/-- Eventually the native first recording of the grid path itself is `N_E`. -/
theorem eventually_unitRecording_eq :
    ∀ᶠ i in l, nativeFirstRecording (fun n => (n : ℝ)) (entranceGridPath f (E i)) (E i) =
      entranceMeshRecording f (E i) := by
  filter_upwards [eventually_cone_iff hr hE1 hE] with i hi
  obtain ⟨h1, hiff⟩ := hi
  have hK : 1 < entranceMeshRecording f (E i) + 1 := by omega
  have h := nativeFirstRecording_eq_threshold (fun n => (n : ℝ)) (entranceGridPath f (E i))
    (E i) hK (fun j => by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp only [nativePrefixFeasible_unit_zero, true_iff]
        omega
      · rw [nativePrefixFeasible_unit_iff _ _ hj, hiff j hj]
        omega)
  simpa using h

/-- Eventually the cut is finite, `2 ≤ τ`, and `τ ≤ N_E + 1 = J`. -/
theorem eventually_cut_le :
    ∀ᶠ i in l, ∃ n : ℕ, entranceCut (entranceGridPath f (E i)) (E i) = n ∧ 2 ≤ n ∧
      n ≤ entranceMeshRecording f (E i) + 1 := by
  filter_upwards [eventually_cone_iff hr hE1 hE] with i hi
  obtain ⟨h1, hiff⟩ := hi
  set y := entranceGridPath f (E i)
  set N := entranceMeshRecording f (E i)
  have hlt : entranceUpper y (E i) (N + 1) < entranceLower y (E i) (N + 1) :=
    lt_of_not_ge fun h => by
      have := (hiff (N + 1) (by omega)).mp h
      omega
  have hd := entranceCutLevel_nonneg (E i).coe_nonneg
  have hw : entranceWidth y (E i) (N + 1) ≤ entranceCutLevel (E i) := by
    unfold entranceWidth
    have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hle := entranceCut_le_of_width_le y (E i) (by omega) hw
  have hne : entranceCut y (E i) ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle
  refine ⟨(entranceCut y (E i)).toNat, (ENat.natCast_toNat hne).symm, ?_, ?_⟩
  · exact entranceCut_ge_two (entranceCutLevel_lt_two_mul (by exact_mod_cast hE1 i))
      (ENat.natCast_toNat hne).symm
  · have := ENat.natCast_toNat hne ▸ hle
    exact_mod_cast this

/-- For every `0 < T < σ`, eventually the cut lies after `T` on the mesh time scale. -/
theorem eventually_lt_cut {T : ℝ} (hT : 0 < T) (hTσ : T < σ) :
    ∀ᶠ i in l, ∀ n : ℕ, entranceCut (entranceGridPath f (E i)) (E i) = n →
      T < (n : ℝ) * gaussianBudgetMesh (E i) := by
  have hlt : T.toNNReal < σ := by
    rw [Real.toNNReal_lt_iff_lt_coe hT.le]
    exact hTσ
  have herr : anchoredTimeError f T < 1 := by
    have h := hr.error_lt hlt
    rwa [Real.coe_toNNReal _ hT.le] at h
  obtain ⟨a, ha⟩ := (anchoredError_le_iff_exists_fit hT.le (intervalPath f T)).mp
    (le_of_eq (anchoredTimeError_eq_interval hT.le f).symm)
  have hfit : ∀ t, 0 ≤ t → t ≤ T → |f t - a * t| ≤ anchoredTimeError f T :=
    fun t h0 hT => ha ⟨t, h0, hT⟩
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp f.continuous.continuousAt (1 / 2 : ℝ)
    (by norm_num)
  set δ₀ := min (δ / 2) T with hδ₀def
  have hsmall : ∀ t, 0 ≤ t → t ≤ δ₀ → |f t| ≤ 1 / 2 := by
    intro t h0 ht
    have hd : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
      exact lt_of_le_of_lt (ht.trans (min_le_left _ _)) (by linarith)
    have := hδf hd
    rw [Real.dist_eq, hr.zero, sub_zero] at this
    exact this.le
  set c := min 1 (δ₀ * (2 * (1 - anchoredTimeError f T) / T)) with hcdef
  have hc : 0 < c := lt_min one_pos (by
    have : 0 < 1 - anchoredTimeError f T := by linarith
    positivity)
  have hlevel : ∀ᶠ i in l, entranceCutLevel (E i) / (E i) < c :=
    (entranceCutLevel_div_tendsto.comp hE).eventually_lt_const hc
  filter_upwards [hlevel] with i hi n hn
  have hE0 := ne_zero_of_one_le_nnreal (hE1 i)
  have hEpos : (0 : ℝ) < E i := by exact_mod_cast pos_iff_ne_zero.mpr hE0
  have hE1' : (1 : ℝ) ≤ E i := by exact_mod_cast hE1 i
  by_contra hle
  push Not at hle
  have h2 := entranceCut_ge_two (entranceCutLevel_lt_two_mul hE1') hn
  have hn1 : 1 ≤ n := by omega
  obtain ⟨k, hk1, hkn, hku⟩ := exists_mul_entranceUpper_eq hr.zero hE0 hn1
  obtain ⟨j, hj1, hjn, hjl⟩ := exists_mul_entranceLower_eq hr.zero hE0 hn1
  set h := (gaussianBudgetMesh (E i) : ℝ) with hhdef
  have hpos : 0 < h := gaussianBudgetMesh_pos hE0
  have hkh : 0 < (k : ℝ) * h := mul_pos (by exact_mod_cast hk1) hpos
  have hjh : 0 < (j : ℝ) * h := mul_pos (by exact_mod_cast hj1) hpos
  have hkn' : (k : ℝ) * h ≤ (n : ℝ) * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hkn) hpos.le
  have hjn' : (j : ℝ) * h ≤ (n : ℝ) * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hjn) hpos.le
  have hgap := entrance_gap_bound hT herr hsmall hfit hjh hkh hjn' hkn' hle
  have hu' : slopeUpper ((k : ℝ) * h) (f ((k : ℝ) * h)) 0 0 1 =
      (f ((k : ℝ) * h) + 1) / ((k : ℝ) * h) := by
    unfold slopeUpper
    simp only [sub_zero]
  have hl' : slopeLower ((j : ℝ) * h) (f ((j : ℝ) * h)) 0 0 1 =
      (f ((j : ℝ) * h) - 1) / ((j : ℝ) * h) := by
    unfold slopeLower
    simp only [sub_zero]
  rw [← hu', ← hl', ← hku, ← hjl] at hgap
  have hEh := sq_mul_gaussianBudgetMesh hE0
  have hwidth : entranceWidth (entranceGridPath f (E i)) (E i) n =
      (E i : ℝ) * (((n : ℝ) * h) *
        ((E i : ℝ) * entranceUpper (entranceGridPath f (E i)) (E i) n -
          (E i : ℝ) * entranceLower (entranceGridPath f (E i)) (E i) n)) := by
    unfold entranceWidth
    linear_combination (-((n : ℝ) * (entranceUpper (entranceGridPath f (E i)) (E i) n -
      entranceLower (entranceGridPath f (E i)) (E i) n))) * hEh
  have hw := entranceCut_width_le hn
  have hdc : entranceCutLevel (E i) < c * E i := (div_lt_iff₀ hEpos).mp hi
  have hge : c * E i ≤ entranceWidth (entranceGridPath f (E i)) (E i) n := by
    rw [hwidth, mul_comm c]
    exact mul_le_mul_of_nonneg_left hgap hEpos.le
  linarith

/-- The cut on the mesh time scale converges to the pinch: `τ h_E → σ`. -/
theorem tendsto_cut_mul_mesh :
    Tendsto (fun i => ((entranceCut (entranceGridPath f (E i)) (E i)).toNat : ℝ) *
      gaussianBudgetMesh (E i)) l (𝓝 σ) := by
  have hcut := eventually_cut_le hr hE1 hE
  have hN := tendsto_meshRecording_mul hr hE1 hE
  have hmesh := gaussianBudgetMesh_tendsto hE
  have hN1 : Tendsto (fun i => ((entranceMeshRecording f (E i) + 1 : ℕ) : ℝ) *
      gaussianBudgetMesh (E i)) l (𝓝 σ) := by
    have := hN.add hmesh
    simp only [add_zero] at this
    refine this.congr fun i => ?_
    push_cast
    ring
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨T, hT1, hT2⟩ := exists_between (max_lt hb hr.pos_real)
    filter_upwards [hcut, eventually_lt_cut hr hE1 hE
      (lt_of_le_of_lt (le_max_right _ _) hT1) hT2] with i hi hgt
    obtain ⟨n, hn, _, _⟩ := hi
    rw [hn, ENat.toNat_natCast]
    exact lt_of_le_of_lt (le_max_left _ _) (hT1.trans (hgt n hn))
  · filter_upwards [hcut, hN1.eventually_lt_const hb] with i hi hlt
    obtain ⟨n, hn, _, hle⟩ := hi
    rw [hn, ENat.toNat_natCast]
    refine lt_of_le_of_lt ?_ hlt
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (NNReal.coe_nonneg _)

/-- (E6), time part: `τ / E² → σ`, the Brownian first pinch. -/
theorem tendsto_cut_div_sq :
    Tendsto (fun i => ((entranceCut (entranceGridPath f (E i)) (E i)).toNat : ℝ) /
      (E i : ℝ) ^ 2) l (𝓝 (entrancePinch f)) := by
  rw [hr.pinch_eq]
  refine (tendsto_cut_mul_mesh hr hE1 hE).congr fun i => ?_
  rw [coe_gaussianBudgetMesh, div_eq_mul_inv]

theorem tendsto_cut_sub_one_mul_mesh :
    Tendsto (fun i => (((entranceCut (entranceGridPath f (E i)) (E i)).toNat - 1 : ℕ) : ℝ) *
      gaussianBudgetMesh (E i)) l (𝓝 σ) := by
  have h := (tendsto_cut_mul_mesh hr hE1 hE).sub (gaussianBudgetMesh_tendsto hE)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_cut_le hr hE1 hE] with i hi
  obtain ⟨n, hn, h2, _⟩ := hi
  rw [hn, ENat.toNat_natCast, Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring

/-- (E6), endpoint part: `E a_{τ-1} → m_*`. -/
theorem tendsto_mul_entranceLower_prev :
    Tendsto (fun i => (E i : ℝ) * entranceLower (entranceGridPath f (E i)) (E i)
      ((entranceCut (entranceGridPath f (E i)) (E i)).toNat - 1)) l (𝓝 (entranceSlope f)) := by
  apply tendsto_feasible_grid_slopes f hr.pos_real hr.lowerSlope_eq hr.upperSlope_eq
    (h := fun i => (gaussianBudgetMesh (E i) : ℝ))
    (N := fun i => (entranceCut (entranceGridPath f (E i)) (E i)).toNat - 1)
    (fun i => gaussianBudgetMesh_pos (ne_zero_of_one_le_nnreal (hE1 i)))
    (gaussianBudgetMesh_tendsto hE) (tendsto_cut_sub_one_mul_mesh hr hE1 hE)
  filter_upwards [eventually_cut_le hr hE1 hE, eventually_cone_iff hr hE1 hE] with i hi hc
  obtain ⟨n, hn, h2, hle⟩ := hi
  obtain ⟨_, hiff⟩ := hc
  simp only [hn, ENat.toNat_natCast, sub_zero]
  intro k hk1 hkn
  have hcone := (hiff (n - 1) (by omega)).mpr (by omega)
  exact gridFit_of_mem_cone hr.zero (ne_zero_of_one_le_nnreal (hE1 i)) (by omega) le_rfl hcone
    k hk1 hkn

/-- (E6), endpoint part: `E b_{τ-1} → m_*`. -/
theorem tendsto_mul_entranceUpper_prev :
    Tendsto (fun i => (E i : ℝ) * entranceUpper (entranceGridPath f (E i)) (E i)
      ((entranceCut (entranceGridPath f (E i)) (E i)).toNat - 1)) l (𝓝 (entranceSlope f)) := by
  apply tendsto_feasible_grid_slopes f hr.pos_real hr.lowerSlope_eq hr.upperSlope_eq
    (h := fun i => (gaussianBudgetMesh (E i) : ℝ))
    (N := fun i => (entranceCut (entranceGridPath f (E i)) (E i)).toNat - 1)
    (fun i => gaussianBudgetMesh_pos (ne_zero_of_one_le_nnreal (hE1 i)))
    (gaussianBudgetMesh_tendsto hE) (tendsto_cut_sub_one_mul_mesh hr hE1 hE)
  filter_upwards [eventually_cut_le hr hE1 hE, eventually_cone_iff hr hE1 hE] with i hi hc
  obtain ⟨n, hn, h2, hle⟩ := hi
  obtain ⟨_, hiff⟩ := hc
  simp only [hn, ENat.toNat_natCast, sub_zero]
  intro k hk1 hkn
  have hcone := (hiff (n - 1) (by omega)).mpr (by omega)
  exact gridFit_of_mem_cone hr.zero (ne_zero_of_one_le_nnreal (hE1 i)) (by omega) hcone le_rfl
    k hk1 hkn

/-- (E9), slope part: the frozen endpoint at the cut satisfies `E β → m_*`. -/
theorem tendsto_mul_entranceFrozenSlope :
    Tendsto (fun i => (E i : ℝ) * entranceFrozenSlope (entranceGridPath f (E i)) (E i)
      (entranceCut (entranceGridPath f (E i)) (E i)).toNat) l (𝓝 (entranceSlope f)) := by
  have hev : ∀ᶠ i in l,
      (E i : ℝ) * entranceLower (entranceGridPath f (E i)) (E i)
          ((entranceCut (entranceGridPath f (E i)) (E i)).toNat - 1) ≤
        (E i : ℝ) * entranceFrozenSlope (entranceGridPath f (E i)) (E i)
          (entranceCut (entranceGridPath f (E i)) (E i)).toNat ∧
      (E i : ℝ) * entranceFrozenSlope (entranceGridPath f (E i)) (E i)
          (entranceCut (entranceGridPath f (E i)) (E i)).toNat ≤
        (E i : ℝ) * entranceUpper (entranceGridPath f (E i)) (E i)
          ((entranceCut (entranceGridPath f (E i)) (E i)).toNat - 1) := by
    filter_upwards [eventually_cut_le hr hE1 hE, eventually_cone_iff hr hE1 hE] with i hi hc
    obtain ⟨n, hn, h2, hle⟩ := hi
    obtain ⟨_, hiff⟩ := hc
    rw [hn, ENat.toNat_natCast]
    have hcone := (hiff (n - 1) (by omega)).mpr (by omega)
    have hE1' : (1 : ℝ) ≤ E i := by exact_mod_cast hE1 i
    have hE0 : (0 : ℝ) ≤ E i := (E i).coe_nonneg
    rcases entranceCut_frozen_eq hE0 (entranceCutLevel_lt_two_mul hE1') hn with h | h <;>
      rw [h] <;> constructor <;> gcongr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_mul_entranceLower_prev hr hE1 hE)
    (tendsto_mul_entranceUpper_prev hr hE1 hE) (hev.mono fun _ h => h.1)
    (hev.mono fun _ h => h.2)

/-- (E9), side part: the refreshed side eventually equals the terminal sign `s`. -/
theorem eventually_entranceSide_eq :
    ∀ᶠ i in l, entranceSide (entranceGridPath f (E i)) (E i)
      (entranceCut (entranceGridPath f (E i)) (E i)).toNat = entranceSign f := by
  have hτ := tendsto_cut_mul_mesh hr hE1 hE
  have hR : Tendsto (fun i =>
      f (((entranceCut (entranceGridPath f (E i)) (E i)).toNat : ℝ) * gaussianBudgetMesh (E i)) -
        ((E i : ℝ) * entranceFrozenSlope (entranceGridPath f (E i)) (E i)
          (entranceCut (entranceGridPath f (E i)) (E i)).toNat) *
        (((entranceCut (entranceGridPath f (E i)) (E i)).toNat : ℝ) * gaussianBudgetMesh (E i)))
      l (𝓝 (entranceSign f)) := by
    rw [hr.sign_eq]
    exact ((f.continuous.tendsto σ).comp hτ).sub
      ((tendsto_mul_entranceFrozenSlope hr hE1 hE).mul hτ)
  have hlevel : ∀ᶠ i in l, entranceCutLevel (E i) / (E i) < 1 :=
    (entranceCutLevel_div_tendsto.comp hE).eventually_lt_const one_pos
  have hpos : ∀ᶠ i in l, 0 < entranceSide (entranceGridPath f (E i)) (E i)
      (entranceCut (entranceGridPath f (E i)) (E i)).toNat *
      (f (((entranceCut (entranceGridPath f (E i)) (E i)).toNat : ℝ) * gaussianBudgetMesh (E i)) -
        ((E i : ℝ) * entranceFrozenSlope (entranceGridPath f (E i)) (E i)
          (entranceCut (entranceGridPath f (E i)) (E i)).toNat) *
        (((entranceCut (entranceGridPath f (E i)) (E i)).toNat : ℝ) *
          gaussianBudgetMesh (E i))) := by
    filter_upwards [eventually_cut_le hr hE1 hE, hlevel] with i hi hl
    obtain ⟨n, hn, _, _⟩ := hi
    rw [hn, ENat.toNat_natCast]
    have hEpos : (0 : ℝ) < E i := lt_of_lt_of_le one_pos (by exact_mod_cast hE1 i)
    have hkey := gridPath_side_residual hr.zero (hE1 i) hn
    have hw := entranceCut_width_le hn
    have hd : entranceCutLevel (E i) < E i := by
      have := (div_lt_iff₀ hEpos).mp hl
      linarith
    have hprod : 0 < (E i : ℝ) * (entranceSide (entranceGridPath f (E i)) (E i) n *
        (f ((n : ℝ) * gaussianBudgetMesh (E i)) -
          ((E i : ℝ) * entranceFrozenSlope (entranceGridPath f (E i)) (E i) n) *
            ((n : ℝ) * gaussianBudgetMesh (E i)))) := by
      rw [hkey]
      linarith
    exact pos_of_mul_pos_right hprod hEpos.le
  rcases hr.sign_eq_one_or with hS | hS
  · filter_upwards [hpos, hR.eventually_const_lt (show (0 : ℝ) < entranceSign f by
      rw [hS]; norm_num)] with i hp hRpos
    rcases entranceSide_eq_one_or (y := entranceGridPath f (E i)) (E := E i)
      (entranceCut (entranceGridPath f (E i)) (E i)).toNat with h | h
    · rw [h, hS]
    · rw [h] at hp
      linarith
  · filter_upwards [hpos, hR.eventually_lt_const (show entranceSign f < 0 by
      rw [hS]; norm_num)] with i hp hRneg
    rcases entranceSide_eq_one_or (y := entranceGridPath f (E i)) (E := E i)
      (entranceCut (entranceGridPath f (E i)) (E i)).toNat with h | h
    · rw [h] at hp
      linarith
    · rw [h, hS]

/-- The first native recording of the grid path, rescaled, converges to the pinch. -/
theorem tendsto_unitRecording_div_sq :
    Tendsto (fun i => (nativeFirstRecording (fun n => (n : ℝ)) (entranceGridPath f (E i))
      (E i) : ℝ) / (E i : ℝ) ^ 2) l (𝓝 (entrancePinch f)) := by
  rw [hr.pinch_eq]
  apply (tendsto_meshRecording_mul hr hE1 hE).congr'
  filter_upwards [eventually_unitRecording_eq hr hE1 hE] with i hi
  rw [hi, coe_gaussianBudgetMesh, div_eq_mul_inv, mul_comm]

end Grid

end

end SwingRepair
