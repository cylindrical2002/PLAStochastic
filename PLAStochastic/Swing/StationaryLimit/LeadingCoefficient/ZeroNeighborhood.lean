import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.ConcreteBounds

/-!
# Zero-neighbourhoods for absolutely continuous limit laws

The leading-coefficient transfer has a separate contribution from a small
interval around the discontinuity at the origin.  The limit law supplied by
the margin theorem is absolutely continuous with respect to Lebesgue measure;
this file records the elementary consequence in a form that can be called by
the final cutoff argument.  No density formula is needed: continuity from
above for finite measures, together with `ν ≪ volume`, is enough.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
namespace LeadingCoefficient
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The canonical shrinking intervals form an antitone family whose
intersection is the singleton at the discontinuity. -/
def zeroNeighbourhood (n : ℕ) : Set ℝ :=
  Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))

theorem zeroNeighbourhood_antitone : Antitone zeroNeighbourhood := by
  intro m n hmn x hx
  have hxn : x ≤ 1 / ((n : ℝ) + 1) := (mem_Icc.mp hx).2
  have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ hmn
  have hposm : 0 < (m : ℝ) + 1 := by positivity
  have hrad : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
    exact one_div_le_one_div_of_le hposm hmn'
  have hneg : -(1 / ((m : ℝ) + 1)) ≤ -(1 / ((n : ℝ) + 1)) := neg_le_neg hrad
  exact mem_Icc.mpr ⟨hneg.trans (mem_Icc.mp hx).1, hxn.trans hrad⟩

theorem zeroNeighbourhood_iInter :
    (⋂ n : ℕ, zeroNeighbourhood n) = ({0} : Set ℝ) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxn
    have hxabs : 0 < |x| := abs_pos.mpr hxn
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / |x|)
    have hnp : 0 < (n : ℝ) + 1 := by positivity
    have hsmall : 1 / ((n : ℝ) + 1) < |x| := by
      have hn' : 1 / |x| < (n : ℝ) + 1 := by linarith
      have hmul : 1 < |x| * ((n : ℝ) + 1) := by
        calc
          1 = |x| * (1 / |x|) := by field_simp
          _ < |x| * ((n : ℝ) + 1) := by
            exact mul_lt_mul_of_pos_left hn' hxabs
      exact (div_lt_iff₀ hnp).2 (by simpa [mul_comm] using hmul)
    have hxi := Set.mem_iInter.mp hx n
    have hleabs : |x| ≤ 1 / ((n : ℝ) + 1) := by
      rcases mem_Icc.mp hxi with ⟨hl, hu⟩
      rw [abs_le]
      exact ⟨by linarith, hu⟩
    linarith
  · intro x hx
    have hx0 : x = 0 := by simpa using hx
    subst x
    refine Set.mem_iInter.mpr ?_
    intro n
    exact mem_Icc.mpr ⟨neg_nonpos.mpr (by positivity), by positivity⟩

/-- For a finite measure absolutely continuous with respect to Lebesgue
measure, the mass of the canonical shrinking zero-neighbourhood tends to
zero. -/
theorem tendsto_measureReal_zeroNeighbourhood
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hνac : ν ≪ volume) :
    Tendsto (fun n : ℕ => ν.real (zeroNeighbourhood n)) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := ν)
    (fun n => (measurableSet_Icc).nullMeasurableSet)
    zeroNeighbourhood_antitone
    ⟨0, measure_ne_top ν _⟩
  have hinter : (⋂ n : ℕ,
      Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))) = ({0} : Set ℝ) := by
    simpa [zeroNeighbourhood] using zeroNeighbourhood_iInter
  rw [hinter] at h
  have hzero : ν ({0} : Set ℝ) = 0 := hνac (by simp)
  rw [hzero] at h
  have hreal : Tendsto (fun n : ℕ => ν.real (zeroNeighbourhood n)) atTop (𝓝 0) := by
    have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp h
    simpa [Measure.real, zeroNeighbourhood, Function.comp_def] using ht
  exact hreal

/-- Every positive tolerance admits a positive zero-neighbourhood with less
than that much limit mass. -/
theorem exists_measureReal_zeroNeighbourhood_lt
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hνac : ν ≪ volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ν.real (Icc (-δ) δ) < ε := by
  have hlim := tendsto_measureReal_zeroNeighbourhood hνac
  obtain ⟨n, hn⟩ :=
    (hlim.eventually (eventually_lt_nhds hε)).exists
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_⟩
  simpa [zeroNeighbourhood] using hn

/-- A bounded reward contributes at most its uniform bound times the mass of a
zero-neighbourhood.  This is the small-interval half of the usual cutoff
decomposition; it is useful independently of the particular frozen reward. -/
theorem abs_setIntegral_Icc_le_of_norm_le
    {ν : Measure ℝ} [IsFiniteMeasure ν] {f : ℝ → ℝ}
    (hf : Integrable f ν) {δ B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ Icc (-δ) δ, |f x| ≤ B) :
    |∫ x in Icc (-δ) δ, f x ∂ν| ≤ B * ν.real (Icc (-δ) δ) := by
  have hfi : IntegrableOn f (Icc (-δ) δ) ν := hf.integrableOn
  have hci : IntegrableOn (fun _ : ℝ => B) (Icc (-δ) δ) ν :=
    (integrable_const B).integrableOn
  have hni : IntegrableOn (fun _ : ℝ => -B) (Icc (-δ) δ) ν :=
    (integrable_const (-B)).integrableOn
  have hu := setIntegral_mono_on hfi hci measurableSet_Icc (fun x hx =>
    le_of_abs_le (hbound x hx))
  have hl := setIntegral_mono_on hni hfi measurableSet_Icc (fun x hx =>
    neg_le_of_abs_le (hbound x hx))
  rw [setIntegral_const, smul_eq_mul] at hu hl
  rw [abs_le]
  have hmass : 0 ≤ ν.real (Icc (-δ) δ) := by
    exact ENNReal.toReal_nonneg
  have hprod : 0 ≤ B * ν.real (Icc (-δ) δ) :=
    mul_nonneg hB hmass
  constructor
  · nlinarith [hl]
  · nlinarith [hu]

end LeadingCoefficient
end SwingRepair
