import PLAStochastic.Swing.Ladder.ZeroDrift.Regeneration
import PLAStochastic.Swing.Entrance.Defs

/-!
# The crossing of a level: age and residual

For a real path `q` and a level `D` the crossing time, overshoot and undershoot are

`T_D = inf {j ≥ 1 : q_j > D}`, `O_D = q_{T_D} - D`, `U_D = D - max_{0 ≤ j < T_D} q_j`,

with the conventions of the shared entrance definitions (`0` when there is no crossing).
`levelCrossing`, `levelOvershoot` and `levelUndershoot` are exactly the pattern of
`entranceCrossing`, `entranceOvershoot` and `entranceUndershoot`, which are these objects
for the reflected local residual at the adaptive cut and the cut width; with a zero frozen
slope and an upper side the local residual is the zero-drift walk after the cut.

For the zero-drift walk `W = cumulativeSamples X` (`entrancePath X ω`) this file proves the
pathwise identity behind (E15): if `0 ≤ u < D`, `o ≥ 0` and the walk never visits `D - u`
after time `0`, then

`U_D > u ∧ O_D > o  ⟺  O_{D-u} > u + o`,

together with positivity, the identification of `O_D` with `gaussianWalkOvershoot`, and the
measurability of `T_D`, `O_D`, `U_D`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-! ### The crossing of a level by a path -/

/-- The first index `j ≥ 1` with `q j > D`, `⊤` if there is none. -/
def levelCrossing (q : ℕ → ℝ) (D : ℝ) : ℕ∞ := by
  classical
  exact if h : ∃ j : ℕ, 1 ≤ j ∧ D < q j then (Nat.find h : ℕ∞) else ⊤

/-- The overshoot `q_T - D` at the crossing (`0` if there is no crossing). -/
def levelOvershoot (q : ℕ → ℝ) (D : ℝ) : ℝ :=
  match levelCrossing q D with
  | ⊤ => 0
  | (T : ℕ) => q T - D

/-- The undershoot `D - max_{0 ≤ j < T} q_j` at the crossing (`0` if there is none). -/
def levelUndershoot (q : ℕ → ℝ) (D : ℝ) : ℝ :=
  match levelCrossing q D with
  | ⊤ => 0
  | (T : ℕ) =>
    if hT : 0 < T then
      D - (Finset.range T).sup' (Finset.nonempty_range_iff.mpr hT.ne') q
    else 0

/-- The shared entrance crossing is the crossing of the cut width by the local residual. -/
theorem entranceCrossing_eq_levelCrossing (y : ℕ → ℝ) (E : ℝ) (n : ℕ) :
    entranceCrossing y E n = levelCrossing (entranceLocal y E n) (entranceWidth y E n) := rfl

theorem entranceOvershoot_eq_levelOvershoot (y : ℕ → ℝ) (E : ℝ) (n : ℕ) :
    entranceOvershoot y E n = levelOvershoot (entranceLocal y E n) (entranceWidth y E n) := rfl

theorem entranceUndershoot_eq_levelUndershoot (y : ℕ → ℝ) (E : ℝ) (n : ℕ) :
    entranceUndershoot y E n = levelUndershoot (entranceLocal y E n) (entranceWidth y E n) := rfl

theorem levelCrossing_eq_coe_iff (q : ℕ → ℝ) (D : ℝ) (T : ℕ) :
    levelCrossing q D = (T : ℕ∞) ↔ 1 ≤ T ∧ D < q T ∧ ∀ j, 1 ≤ j → j < T → q j ≤ D := by
  unfold levelCrossing
  split_ifs with h
  · rw [ENat.natCast_inj, Nat.find_eq_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, fun j hj1 hjT => le_of_not_gt fun hc => h3 j hjT ⟨hj1, hc⟩⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun j hjT hj => not_lt.mpr (h3 j hj.1 hjT) hj.2⟩
  · simp only [ENat.top_ne_natCast, false_iff]
    rintro ⟨h1, h2, -⟩
    exact h ⟨T, h1, h2⟩

theorem levelCrossing_eq_top_iff (q : ℕ → ℝ) (D : ℝ) :
    levelCrossing q D = ⊤ ↔ ∀ j, 1 ≤ j → q j ≤ D := by
  unfold levelCrossing
  split_ifs with h
  · simp only [ENat.natCast_ne_top, false_iff]
    intro hall
    obtain ⟨j, hj1, hj⟩ := h
    exact absurd (hall j hj1) (not_le.mpr hj)
  · simp only [true_iff]
    intro j hj
    exact le_of_not_gt fun hc => h ⟨j, hj, hc⟩

theorem levelOvershoot_of_eq {q : ℕ → ℝ} {D : ℝ} {T : ℕ} (h : levelCrossing q D = T) :
    levelOvershoot q D = q T - D := by
  unfold levelOvershoot
  rw [h]

theorem levelOvershoot_of_top {q : ℕ → ℝ} {D : ℝ} (h : levelCrossing q D = ⊤) :
    levelOvershoot q D = 0 := by
  unfold levelOvershoot
  rw [h]
  rfl

theorem levelUndershoot_of_eq {q : ℕ → ℝ} {D : ℝ} {T : ℕ} (h : levelCrossing q D = T)
    (hT : 0 < T) :
    levelUndershoot q D = D - (Finset.range T).sup' (Finset.nonempty_range_iff.mpr hT.ne') q := by
  unfold levelUndershoot
  rw [h]
  simp only [dif_pos hT]

theorem levelUndershoot_of_top {q : ℕ → ℝ} {D : ℝ} (h : levelCrossing q D = ⊤) :
    levelUndershoot q D = 0 := by
  unfold levelUndershoot
  rw [h]
  rfl

theorem levelOvershoot_pos {q : ℕ → ℝ} {D : ℝ} (hcross : levelCrossing q D ≠ ⊤) :
    0 < levelOvershoot q D := by
  obtain ⟨T, hT⟩ := ENat.ne_top_iff_exists.mp hcross
  rw [levelOvershoot_of_eq hT.symm]
  linarith [((levelCrossing_eq_coe_iff q D T).mp hT.symm).2.1]

/-- The undershoot is strictly positive when the path never sits exactly on the level. -/
theorem levelUndershoot_pos {q : ℕ → ℝ} (hq0 : q 0 = 0) {D : ℝ} (hD : 0 < D)
    (hcross : levelCrossing q D ≠ ⊤) (hne : ∀ j, 1 ≤ j → q j ≠ D) :
    0 < levelUndershoot q D := by
  obtain ⟨T, hT⟩ := ENat.ne_top_iff_exists.mp hcross
  have hc := (levelCrossing_eq_coe_iff q D T).mp hT.symm
  rw [levelUndershoot_of_eq hT.symm hc.1, sub_pos, Finset.sup'_lt_iff]
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [hq0]
    exact hD
  · exact lt_of_le_of_ne (hc.2.2 j hj0 (Finset.mem_range.mp hj)) (hne j hj0)

/-- **The age/residual shift identity.**  For `0 ≤ u < D`, `o ≥ 0` and a path started at
`0` that never visits `D - u` after time `0`, the age at `D` exceeds `u` and the residual
at `D` exceeds `o` exactly when the residual at `D - u` exceeds `u + o`. -/
theorem level_age_residual_iff {q : ℕ → ℝ} (hq0 : q 0 = 0) {D u o : ℝ} (hu : 0 ≤ u)
    (ho : 0 ≤ o) (huD : u < D) (hne : ∀ j, 1 ≤ j → q j ≠ D - u) :
    (u < levelUndershoot q D ∧ o < levelOvershoot q D) ↔ u + o < levelOvershoot q (D - u) := by
  constructor
  · rintro ⟨hU, hO⟩
    by_cases h : levelCrossing q D = ⊤
    · rw [levelUndershoot_of_top h] at hU
      linarith
    obtain ⟨T, hT⟩ := ENat.ne_top_iff_exists.mp h
    have hc := (levelCrossing_eq_coe_iff q D T).mp hT.symm
    rw [levelUndershoot_of_eq hT.symm hc.1] at hU
    rw [levelOvershoot_of_eq hT.symm] at hO
    have hsup : (Finset.range T).sup' (Finset.nonempty_range_iff.mpr (show 0 < T from hc.1).ne') q < D - u := by
      linarith
    have hlt : ∀ j, j < T → q j < D - u := fun j hj =>
      lt_of_le_of_lt (Finset.le_sup' q (Finset.mem_range.mpr hj)) hsup
    have hT' : levelCrossing q (D - u) = T :=
      (levelCrossing_eq_coe_iff q (D - u) T).mpr
        ⟨hc.1, by linarith [hc.2.1], fun j _ hjT => (hlt j hjT).le⟩
    rw [levelOvershoot_of_eq hT']
    linarith
  · intro hO
    by_cases h : levelCrossing q (D - u) = ⊤
    · rw [levelOvershoot_of_top h] at hO
      linarith
    obtain ⟨T, hT⟩ := ENat.ne_top_iff_exists.mp h
    have hc := (levelCrossing_eq_coe_iff q (D - u) T).mp hT.symm
    rw [levelOvershoot_of_eq hT.symm] at hO
    have hTD : levelCrossing q D = T :=
      (levelCrossing_eq_coe_iff q D T).mpr
        ⟨hc.1, by linarith, fun j hj1 hjT => by linarith [hc.2.2 j hj1 hjT]⟩
    refine ⟨?_, ?_⟩
    · rw [levelUndershoot_of_eq hTD hc.1]
      have hsup : (Finset.range T).sup' (Finset.nonempty_range_iff.mpr (show 0 < T from hc.1).ne') q < D - u := by
        rw [Finset.sup'_lt_iff]
        intro j hj
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · rw [hq0]
          linarith
        · exact lt_of_le_of_ne (hc.2.2 j hj0 (Finset.mem_range.mp hj)) (hne j hj0)
      linarith
    · rw [levelOvershoot_of_eq hTD]
      linarith

/-! ### The zero-drift walk -/

variable {Ω : Type*}

/-- The crossing time `T_D = inf {j ≥ 1 : W_j > D}` of the zero-drift walk. -/
def zeroDriftCrossing (X : ℕ → Ω → ℝ) (D : ℝ) (ω : Ω) : ℕ∞ := levelCrossing (entrancePath X ω) D

/-- The residual `O_D = W_{T_D} - D` of the zero-drift walk. -/
def zeroDriftOvershoot (X : ℕ → Ω → ℝ) (D : ℝ) (ω : Ω) : ℝ :=
  levelOvershoot (entrancePath X ω) D

/-- The age `U_D = D - max_{0 ≤ j < T_D} W_j` of the zero-drift walk. -/
def zeroDriftUndershoot (X : ℕ → Ω → ℝ) (D : ℝ) (ω : Ω) : ℝ :=
  levelUndershoot (entrancePath X ω) D

theorem gaussianDriftWalk_zero_zero (X : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) :
    gaussianDriftWalk X 0 0 m ω = entrancePath X ω m := by
  simp [gaussianDriftWalk, entrancePath]

/-- The residual is the overshoot of `gaussianWalkOvershoot` once the walk exceeds `D ≥ 0`. -/
theorem zeroDriftOvershoot_eq_walkOvershoot (X : ℕ → Ω → ℝ) {D : ℝ} (hD : 0 ≤ D) {ω : Ω}
    (hex : ∃ m : ℕ, D < cumulativeSamples X m ω) :
    zeroDriftOvershoot X D ω = gaussianWalkOvershoot X 0 D ω := by
  have hex' : ∃ m : ℕ, D < gaussianDriftWalk X 0 0 m ω := by
    obtain ⟨m, hm⟩ := hex
    exact ⟨m, by rw [gaussianDriftWalk_zero_zero]; exact hm⟩
  have hm : D < entrancePath X ω (Nat.find hex') := by
    rw [← gaussianDriftWalk_zero_zero]
    exact Nat.find_spec hex'
  have hm1 : 1 ≤ Nat.find hex' := by
    by_contra hcon
    have h0 : Nat.find hex' = 0 := by omega
    rw [h0, entrancePath_zero] at hm
    linarith
  have hT : levelCrossing (entrancePath X ω) D = (Nat.find hex' : ℕ) :=
    (levelCrossing_eq_coe_iff _ _ _).mpr ⟨hm1, hm, fun j _ hjm => by
      have := Nat.find_min hex' hjm
      rw [gaussianDriftWalk_zero_zero] at this
      exact le_of_not_gt this⟩
  rw [zeroDriftOvershoot, levelOvershoot_of_eq hT, gaussianWalkOvershoot, gaussianWalkPassage,
    dif_pos hex', gaussianDriftWalk_zero_zero]

/-! ### Measurability -/

theorem zeroDriftCrossing_eq_hittingAfter (X : ℕ → Ω → ℝ) (D : ℝ) (ω : Ω) :
    zeroDriftCrossing X D ω = hittingAfter (gaussianDriftWalk X 0 0) (Ioi D) 1 ω := by
  rw [hittingAfter_def]
  simp only [gaussianDriftWalk_zero_zero, Set.mem_Ioi]
  unfold zeroDriftCrossing levelCrossing
  by_cases h : ∃ j : ℕ, 1 ≤ j ∧ D < entrancePath X ω j
  · rw [dif_pos h, if_pos h]
    have heq : Nat.find h = sInf {i : ℕ | 1 ≤ i ∧ D < entrancePath X ω i} :=
      le_antisymm (Nat.find_min' h (Nat.sInf_mem h)) (Nat.sInf_le (Nat.find_spec h))
    rw [heq]
    rfl
  · rw [dif_neg h, if_neg h]

/-- A function that is constant on `{T = ⊤}` and equals a measurable `g n` on each
`{T = n}` is measurable, when the fibres of `T` are measurable. -/
theorem measurable_of_crossing_pieces [MeasurableSpace Ω] {T : Ω → ℕ∞}
    (hT : ∀ n, MeasurableSet {ω | T ω = n}) {f : Ω → ℝ} {g : ℕ → Ω → ℝ}
    (hg : ∀ n, Measurable (g n)) {c : ℝ} (hf_top : ∀ ω, T ω = ⊤ → f ω = c)
    (hf_coe : ∀ ω (n : ℕ), T ω = n → f ω = g n ω) : Measurable f := by
  intro S hS
  have hset : f ⁻¹' S = ({ω | T ω = ⊤} ∩ (fun _ : Ω => c) ⁻¹' S) ∪
      ⋃ n : ℕ, ({ω | T ω = n} ∩ g n ⁻¹' S) := by
    ext ω
    constructor
    · intro h
      by_cases ht : T ω = ⊤
      · left
        refine ⟨ht, ?_⟩
        show c ∈ S
        rw [← hf_top ω ht]
        exact h
      · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ht
        right
        refine Set.mem_iUnion.mpr ⟨n, hn.symm, ?_⟩
        show g n ω ∈ S
        rw [← hf_coe ω n hn.symm]
        exact h
    · rintro (⟨ht, h⟩ | h)
      · show f ω ∈ S
        rw [hf_top ω ht]
        exact h
      · obtain ⟨n, hn, h⟩ := Set.mem_iUnion.mp h
        show f ω ∈ S
        rw [hf_coe ω n hn]
        exact h
  rw [hset]
  exact ((hT ⊤).inter (measurable_const hS)).union
    (MeasurableSet.iUnion fun n => (hT n).inter (hg n hS))

variable [MeasurableSpace Ω] {X : ℕ → Ω → ℝ}

theorem zeroDriftCrossing_measurableSet (hX : ∀ n, Measurable (X n)) (D : ℝ) (n : WithTop ℕ) :
    MeasurableSet {ω | zeroDriftCrossing X D ω = n} := by
  have hτ := (gaussianDriftWalk_adapted hX 0 0).isStoppingTime_hittingAfter
    (s := Ioi D) (n := 1) measurableSet_Ioi
  have hset : {ω | zeroDriftCrossing X D ω = n} =
      hittingAfter (gaussianDriftWalk X 0 0) (Ioi D) 1 ⁻¹' {n} := by
    ext ω
    simp [zeroDriftCrossing_eq_hittingAfter]
  rw [hset]
  exact hτ.measurable' (measurableSet_singleton n)

theorem entrancePath_measurable (hX : ∀ n, Measurable (X n)) (m : ℕ) :
    Measurable (fun ω => entrancePath X ω m) := by
  have heq : (fun ω => entrancePath X ω m) = gaussianDriftWalk X 0 0 m :=
    funext fun ω => (gaussianDriftWalk_zero_zero X m ω).symm
  rw [heq]
  exact gaussianDriftWalk_measurable hX 0 0 m

theorem zeroDriftOvershoot_measurable (hX : ∀ n, Measurable (X n)) (D : ℝ) :
    Measurable (zeroDriftOvershoot X D) :=
  measurable_of_crossing_pieces (T := zeroDriftCrossing X D) (zeroDriftCrossing_measurableSet hX D)
    (g := fun n ω => entrancePath X ω n - D) (fun n => (entrancePath_measurable hX n).sub_const D)
    (c := 0) (fun _ h => levelOvershoot_of_top h) (fun _ _ h => levelOvershoot_of_eq h)

theorem zeroDriftUndershoot_measurable (hX : ∀ n, Measurable (X n)) (D : ℝ) :
    Measurable (zeroDriftUndershoot X D) := by
  set g : ℕ → Ω → ℝ := fun n ω => if hn : 0 < n then
      D - (Finset.range n).sup' (Finset.nonempty_range_iff.mpr hn.ne') (entrancePath X ω)
    else 0 with hgdef
  have hg : ∀ n, Measurable (g n) := by
    intro n
    by_cases hn : 0 < n
    · have hsup := Finset.measurable_sup' (Finset.nonempty_range_iff.mpr hn.ne')
        (f := fun j ω => entrancePath X ω j) (fun j _ => entrancePath_measurable hX j)
      have heq : g n = fun ω => D - ((Finset.range n).sup' (Finset.nonempty_range_iff.mpr hn.ne')
          (fun j ω => entrancePath X ω j)) ω := by
        funext ω
        rw [hgdef]
        simp only [dif_pos hn, Finset.sup'_apply]
      rw [heq]
      exact measurable_const.sub hsup
    · have heq : g n = fun _ => 0 := by
        funext ω
        rw [hgdef]
        simp only [dif_neg hn]
      rw [heq]
      exact measurable_const
  refine measurable_of_crossing_pieces (T := zeroDriftCrossing X D)
    (zeroDriftCrossing_measurableSet hX D) hg (c := 0) (fun _ h => levelUndershoot_of_top h) ?_
  intro ω n h
  have hn : 0 < n := ((levelCrossing_eq_coe_iff _ _ _).mp h).1
  rw [hgdef]
  simp only [dif_pos hn]
  exact levelUndershoot_of_eq h hn

end SwingRepair
