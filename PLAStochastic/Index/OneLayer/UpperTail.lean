import PLAStochastic.Index.Model.GapLaw
import PLAStochastic.ForMathlib.Probability.Moments.PaleyZygmund

/-!
# Geometric upper tail of the one-layer segment length (`lem:condtail`, iid case)

Fix `h > 0` and the block length `L = 2 h`.  Under the four size conditions

* (H1) `5184 μ² eps² < σ² L`,  (H2) `κ² ≤ σ⁶ L`,  (H3) `4 eps ≤ L`,  (H4) `288 σ² ≤ μ² L`,

the keys `0, …, L` of an iid gap walk are `eps`-feasible with probability at most `71/72`
(`measureReal_block_feasible_le`).  On that event the second-difference criterion
(`second_difference_of_feasible`) forces either a large endpoint `|S_L| > μ L / 2`
(Chebyshev: probability `≤ 1/72`) or a small signed block sum `|S_L - 2 S_h| ≤ 12 μ eps`
(anti-concentration from second and third moments: probability `≤ 35/36`).

Splitting the first `j L + 1` keys into `j` consecutive windows of `L + 1` keys, each
window is the first block of the shifted gaps and is independent of the earlier windows,
which gives the geometric tail `P(T > j L) ≤ (71/72)^j` (`measureReal_layerSegLen_gt_le`)
and `T < ∞` almost surely (`measureReal_layerSegLen_eq_top`).
-/

namespace PGM

open MeasureTheory ProbabilityTheory Finset Filter Topology

/-- The deterministic signs `-1` on `[0, h)` and `+1` from `h` on. -/
def blockSign {α : Type*} (h : ℕ) : ℕ → α → ℝ := fun t _ => if t < h then -1 else 1

theorem abs_blockSign {α : Type*} (h t : ℕ) (a : α) : |blockSign h t a| = 1 := by
  unfold blockSign; split_ifs <;> simp

theorem blockSign_sq {α : Type*} (h t : ℕ) (a : α) : blockSign h t a ^ 2 = 1 := by
  rw [← sq_abs, abs_blockSign]; norm_num

/-- The signed sum with weights `blockSign h` over `2 h` steps is `S_{2h} - 2 S_h`. -/
theorem weightedSum_blockSign {α : Type*} (Y : ℕ → α → ℝ) (h : ℕ) (a : α) :
    weightedSum (blockSign h) Y (2 * h) a = partialSum Y (2 * h) a - 2 * partialSum Y h a := by
  simp only [weightedSum, partialSum, blockSign, two_mul, sum_range_add]
  have h1 : ∑ x ∈ range h, (if x < h then (-1 : ℝ) else 1) * Y x a =
      -∑ x ∈ range h, Y x a := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun x hx => by rw [if_pos (mem_range.1 hx)]; ring
  have h2 : ∑ x ∈ range h, (if h + x < h then (-1 : ℝ) else 1) * Y (h + x) a =
      ∑ x ∈ range h, Y (h + x) a :=
    sum_congr rfl fun x _ => by rw [if_neg (by omega)]; ring
  rw [h1, h2]
  ring

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {μ σ κ : ℝ}

theorem blockSign_predictable (F : Filtration ℕ mΩ) (h : ℕ) :
    PredictableWeight F (blockSign h) :=
  ⟨fun _ => measurable_const, fun t ω => (abs_blockSign h t ω).le⟩

/-- **One block.** The keys `0, …, L` (`L = 2 h`) of the iid gap walk are `eps`-feasible
with probability at most `71/72`. -/
theorem measureReal_block_feasible_le [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ)
    {eps : ℝ} {h L : ℕ} (hh : 0 < h) (hL : L = 2 * h)
    (H1 : 5184 * μ ^ 2 * eps ^ 2 < σ ^ 2 * L) (H2 : κ ^ 2 ≤ σ ^ 6 * L)
    (H3 : 4 * eps ≤ L) (H4 : 288 * σ ^ 2 ≤ μ ^ 2 * L) (heps : 0 ≤ eps) :
    P.real {ω | prefixAffineFeasible eps (gapKeys (seq X ω)) (L + 1)} ≤ 71 / 72 := by
  set Y := centred X μ with hYdef
  have hinc : IndepIncrements P (gapFiltration X hX.iid.measurable) Y := hX.indepIncrements
  have hY3 : ∀ t, MemLp (Y t) 3 P := hX.memLp_centred
  have hY2 : ∀ t, MemLp (Y t) 2 P := fun t => (hY3 t).mono_exponent (by norm_num)
  have hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0 := hX.integral_centred
  have hYsq : ∀ t, ∫ ω, Y t ω ^ 2 ∂P = σ ^ 2 := hX.integral_centred_sq
  have hYcube : ∀ t, ∫ ω, |Y t ω| ^ 3 ∂P ≤ κ := hX.integral_centred_abs_cube
  have hμ := hX.mu_pos
  have hσ := hX.sigma_pos
  have hκ0 := hX.kappa_nonneg
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := by omega
    exact_mod_cast this
  have hc := blockSign_predictable (gapFiltration X hX.iid.measurable) h
  have hMdef : ∀ ω, weightedSum (blockSign h) Y L ω =
      partialSum Y L ω - 2 * partialSum Y h ω := by
    intro ω; subst hL; exact weightedSum_blockSign Y h ω
  -- the feasibility event lies in the union of a large endpoint and a small signed sum
  have hsub : {ω | prefixAffineFeasible eps (gapKeys (seq X ω)) (L + 1)} ⊆
      {ω | μ * L / 2 < |partialSum Y L ω|} ∪
        {ω | |weightedSum (blockSign h) Y L ω| ≤ 12 * μ * eps} := by
    intro ω hω
    by_cases hA : μ * L / 2 < |partialSum Y L ω|
    · exact Or.inl hA
    · right
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have hkey := gapKeys_eq_centred X μ ω
      have hp0 := gapKeys_zero (seq X ω)
      have hA' : |partialSum Y L ω| ≤ μ * L / 2 := not_lt.mp hA
      have hend : |gapKeys (seq X ω) L / μ - (L : ℝ)| ≤ (L : ℝ) / 2 := by
        rw [hkey]
        have : ((L : ℝ) * μ + partialSum (centred X μ) L ω) / μ - (L : ℝ) =
            partialSum Y L ω / μ := by
          field_simp; ring
        rw [this, abs_div, abs_of_pos hμ, div_le_iff₀ hμ]
        linarith
      have hsd : |(gapKeys (seq X ω) L / μ - (L : ℝ)) - 2 * (gapKeys (seq X ω) h / μ - h)|
          ≤ 12 * eps := by
        subst hL
        exact second_difference_of_feasible hμ hh hp0 hω hend H3
      have : (gapKeys (seq X ω) L / μ - (L : ℝ)) - 2 * (gapKeys (seq X ω) h / μ - h) =
          weightedSum (blockSign h) Y L ω / μ := by
        rw [hkey, hkey, hMdef]
        field_simp
        ring
      rw [this, abs_div, abs_of_pos hμ, div_le_iff₀ hμ] at hsd
      linarith
  -- Chebyshev for the endpoint
  have hS2 : MemLp (partialSum Y L) 2 P := by
    rw [partialSum_eq_weightedSum_one]
    exact memLp_weightedSum hinc (PredictableWeight.one _) hY2 L
  have hES : ∫ ω, partialSum Y L ω ^ 2 ∂P = L * σ ^ 2 := by
    rw [partialSum_eq_weightedSum_one,
      integral_weightedSum_sq hinc (PredictableWeight.one _) hY2 hY0]
    simp [hYsq]
  have hA : P.real {ω | μ * L / 2 < |partialSum Y L ω|} ≤ 1 / 72 := by
    have hmark := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun ω => sq_nonneg (partialSum Y L ω))
      hS2.integrable_sq ((μ * L / 2) ^ 2)
    rw [hES] at hmark
    have hmono : P.real {ω | μ * L / 2 < |partialSum Y L ω|} ≤
        P.real {ω | (μ * L / 2) ^ 2 ≤ partialSum Y L ω ^ 2} := by
      refine measureReal_mono fun ω hω => ?_
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have h0 : 0 ≤ μ * L / 2 := by positivity
      rw [← sq_abs (partialSum Y L ω)]
      exact pow_le_pow_left₀ h0 hω.le 2
    have hc0 : 0 < (μ * L / 2) ^ 2 := by positivity
    have hkey : (L : ℝ) * σ ^ 2 * 72 ≤ (μ * L / 2) ^ 2 := by
      have : (L : ℝ) * (288 * σ ^ 2) ≤ L * (μ ^ 2 * L) := mul_le_mul_of_nonneg_left H4 hLpos.le
      nlinarith
    have hp : (μ * L / 2) ^ 2 * P.real {ω | μ * L / 2 < |partialSum Y L ω|} ≤
        (μ * L / 2) ^ 2 * (1 / 72) := by
      calc (μ * L / 2) ^ 2 * P.real {ω | μ * L / 2 < |partialSum Y L ω|}
          ≤ (μ * L / 2) ^ 2 * P.real {ω | (μ * L / 2) ^ 2 ≤ partialSum Y L ω ^ 2} :=
            mul_le_mul_of_nonneg_left hmono hc0.le
        _ ≤ L * σ ^ 2 := hmark
        _ ≤ (μ * L / 2) ^ 2 * (1 / 72) := by linarith
    exact le_of_mul_le_mul_left hp hc0
  -- anti-concentration for the signed block sum
  set M := weightedSum (blockSign h) Y L with hM
  have hMm : Measurable M := weightedSum_measurable hinc hc L
  have hM3 : MemLp M 3 P := memLp_weightedSum hinc hc hY3 L
  set s : ℝ := σ * Real.sqrt L with hs
  have hsqrt := Real.sq_sqrt hLpos.le
  have hsqrt0 : 0 < Real.sqrt L := Real.sqrt_pos.2 hLpos
  have hs0 : 0 < s := mul_pos hσ hsqrt0
  have hEM : ∫ ω, M ω ^ 2 ∂P = L * σ ^ 2 := by
    rw [hM, integral_weightedSum_sq hinc hc hY2 hY0]
    simp [hYsq, blockSign_sq]
  have h2 : s ^ 2 ≤ ∫ ω, M ω ^ 2 ∂P := by
    rw [hEM, hs, mul_pow, hsqrt]; linarith
  have hκle : κ ≤ σ ^ 3 * Real.sqrt L := by
    by_contra hcon
    have hlt : σ ^ 3 * Real.sqrt L < κ := not_le.mp hcon
    have h0 : 0 ≤ σ ^ 3 * Real.sqrt L := by positivity
    have : (σ ^ 3 * Real.sqrt L) ^ 2 < κ ^ 2 := pow_lt_pow_left₀ hlt h0 (by norm_num)
    rw [mul_pow, hsqrt] at this
    nlinarith
  have h3 : ∫ ω, |M ω| ^ 3 ∂P ≤ 3 * s ^ 3 := by
    have hb := integral_abs_weightedSum_cube_le_of_unit hinc hc (abs_blockSign h) hY3 hY0
      hσ.le (fun t => (hYsq t).le) hYcube L
    have hs3 : s ^ 3 = σ ^ 3 * L * Real.sqrt L := by
      rw [hs, mul_pow, pow_succ (Real.sqrt L) 2, hsqrt]; ring
    rw [hs3]
    have : (L : ℝ) * κ ≤ L * (σ ^ 3 * Real.sqrt L) := mul_le_mul_of_nonneg_left hκle hLpos.le
    nlinarith
  have hanti := anticoncentration_of_moments hs0 hMm hM3 h2 h3
  have hsmall : 12 * μ * eps < s / 6 := by
    have h0 : 0 ≤ 72 * μ * eps := by positivity
    have hlt : (72 * μ * eps) ^ 2 < s ^ 2 := by
      rw [hs, mul_pow σ (Real.sqrt L), hsqrt]; nlinarith
    have := lt_of_pow_lt_pow_left₀ 2 hs0.le hlt
    linarith
  have hB : P.real {ω | |M ω| ≤ 12 * μ * eps} ≤ 35 / 36 := by
    have hmeas : MeasurableSet {ω | |M ω| ≤ 12 * μ * eps} :=
      measurableSet_le (continuous_abs.measurable.comp hMm) measurable_const
    have hcompl := probReal_compl_eq_one_sub (μ := P) hmeas
    have hmono : P.real {ω | s / 6 < |M ω|} ≤ P.real {ω | |M ω| ≤ 12 * μ * eps}ᶜ := by
      refine measureReal_mono fun ω hω => ?_
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff] at hω ⊢
      linarith
    linarith
  calc P.real {ω | prefixAffineFeasible eps (gapKeys (seq X ω)) (L + 1)}
      ≤ P.real ({ω | μ * L / 2 < |partialSum Y L ω|} ∪ {ω | |M ω| ≤ 12 * μ * eps}) :=
        measureReal_mono hsub
    _ ≤ P.real {ω | μ * L / 2 < |partialSum Y L ω|} + P.real {ω | |M ω| ≤ 12 * μ * eps} :=
        measureReal_union_le _ _
    _ ≤ 71 / 72 := by linarith

omit mΩ in
/-- `T > t` exactly when the first `t + 1` keys are feasible. -/
theorem setOf_lt_layerSegLen (eps : ℝ) (X : ℕ → Ω → ℝ) (t : ℕ) :
    {ω | (t : ℕ∞) < layerSegLen eps X ω} =
      {ω | prefixAffineFeasible eps (gapKeys (seq X ω)) (t + 1)} := by
  ext ω
  simp only [Set.mem_ofPred_eq, layerSegLen, gapSegLen, lt_segLen_iff]

/-- **Geometric upper tail** (`lem:condtail`, iid case): `P(T > j L) ≤ (71/72)^j`. -/
theorem measureReal_layerSegLen_gt_le [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ)
    {eps : ℝ} {h L : ℕ} (hh : 0 < h) (hL : L = 2 * h)
    (H1 : 5184 * μ ^ 2 * eps ^ 2 < σ ^ 2 * L) (H2 : κ ^ 2 ≤ σ ^ 6 * L)
    (H3 : 4 * eps ≤ L) (H4 : 288 * σ ^ 2 ≤ μ ^ 2 * L) (heps : 0 ≤ eps) :
    ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < layerSegLen eps X ω} ≤ (71 / 72 : ℝ) ^ j := by
  intro j
  rw [setOf_lt_layerSegLen]
  induction j with
  | zero => simp [measureReal_le_one]
  | succ j ih =>
    -- the block of keys `j L, …, j L + L` read through the shifted gaps
    let B : Set (ℕ → ℝ) := {g | prefixAffineFeasible eps (gapKeys g) (L + 1)}
    have hB : MeasurableSet B :=
      measurable_gapKeys (measurableSet_prefixAffineFeasible eps (L + 1))
    let G : Set Ω := {ω | prefixAffineFeasible eps (gapKeys (seq X ω)) (j * L + 1)}
    have hG : MeasurableSet[gapFiltration X hX.iid.measurable (j * L)] G := by
      have := gapSegLen_lt_measurable hX.iid.measurable eps (j * L)
      have heq : G = {ω | ((j * L : ℕ) : ℕ∞) < gapSegLen eps (seq X ω)} := by
        ext ω
        simp only [G, Set.mem_ofPred_eq, gapSegLen, lt_segLen_iff]
      rw [heq]
      exact this
    have hsub : {ω | prefixAffineFeasible eps (gapKeys (seq X ω)) ((j + 1) * L + 1)} ⊆
        (fun ω t => X (j * L + t) ω) ⁻¹' B ∩ G := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      refine ⟨?_, prefixAffineFeasible_mono hω (by rw [add_mul]; omega)⟩
      have hw := prefixAffineFeasible_window (r := j * L) (w := L + 1) hω
        (by rw [add_mul]; omega)
      show prefixAffineFeasible eps (gapKeys (fun t => X (j * L + t) ω)) (L + 1)
      refine (prefixAffineFeasible_affine_iff (p := gapKeys (fun t => X (j * L + t) ω))
        (s := 1) (c := gapKeys (seq X ω) (j * L)) one_ne_zero).mp
        ((prefixAffineFeasible_congr fun i _ => ?_).mp hw)
      show gapKeys (seq X ω) (j * L + i) =
        1 * gapKeys (fun t => seq X ω (j * L + t)) i + gapKeys (seq X ω) (j * L)
      rw [gapKeys_shift]
      ring
    have hprod : P.real ((fun ω t => X (j * L + t) ω) ⁻¹' B ∩ G) =
        P.real ((fun ω t => X (j * L + t) ω) ⁻¹' B) * P.real G := by
      simp only [measureReal_def]
      rw [measure_future_inter_gapFiltration hX.iid (j * L) hB hG, ENNReal.toReal_mul]
    have hblock : P.real ((fun ω t => X (j * L + t) ω) ⁻¹' B) ≤ 71 / 72 :=
      measureReal_block_feasible_le (hX.shift (j * L)) hh hL H1 H2 H3 H4 heps
    calc P.real {ω | prefixAffineFeasible eps (gapKeys (seq X ω)) ((j + 1) * L + 1)}
        ≤ P.real ((fun ω t => X (j * L + t) ω) ⁻¹' B ∩ G) := measureReal_mono hsub
      _ = P.real ((fun ω t => X (j * L + t) ω) ⁻¹' B) * P.real G := hprod
      _ ≤ 71 / 72 * (71 / 72 : ℝ) ^ j :=
          mul_le_mul hblock ih measureReal_nonneg (by norm_num)
      _ = (71 / 72 : ℝ) ^ (j + 1) := (pow_succ' _ _).symm

/-- The first segment is almost surely finite. -/
theorem measureReal_layerSegLen_eq_top [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ)
    {eps : ℝ} {h L : ℕ} (hh : 0 < h) (hL : L = 2 * h)
    (H1 : 5184 * μ ^ 2 * eps ^ 2 < σ ^ 2 * L) (H2 : κ ^ 2 ≤ σ ^ 6 * L)
    (H3 : 4 * eps ≤ L) (H4 : 288 * σ ^ 2 ≤ μ ^ 2 * L) (heps : 0 ≤ eps) :
    P.real {ω | layerSegLen eps X ω = ⊤} = 0 := by
  have htail := measureReal_layerSegLen_gt_le hX hh hL H1 H2 H3 H4 heps
  have hle : ∀ j : ℕ, P.real {ω | layerSegLen eps X ω = ⊤} ≤ (71 / 72 : ℝ) ^ j := by
    intro j
    refine (measureReal_mono fun ω hω => ?_).trans (htail j)
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hω]
    exact ENat.natCast_lt_top _
  have hlim : Tendsto (fun j : ℕ => (71 / 72 : ℝ) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact le_antisymm (ge_of_tendsto' hlim hle) measureReal_nonneg

end PGM
