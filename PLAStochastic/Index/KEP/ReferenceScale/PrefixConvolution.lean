import PLAStochastic.Index.GEP.Response.Score.ChangeOfMeasure
import PLAStochastic.Index.GEP.DirectTerm.CoarseBound
import PLAStochastic.Index.GEP.RawDisc.ProductLaws

/-!
# Identifying the free next gap on an actual independent prefix

The survival event of a greedy prefix is unchanged by its next gap. Single-gap
insertion and Fubini therefore identify its one-step output increment with the
convolution increment. The stopped complement has the same identity.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepPrefixConvolutionIncrement (ν : ProbabilityMeasure ℝ) (C : ℝ)
    (φ : ℝ → ℝ) (k : ℕ) (g : ℕ → ℝ) : ℝ :=
  (∫ x, φ ((gapKeys g k + x) / C) ∂(ν : Measure ℝ)) - φ (gapKeys g k / C)

theorem integral_prefix_next_gap (ν : ProbabilityMeasure ℝ) {s : Set (ℕ → ℝ)}
    (hs : MeasurableSet s) (k : ℕ)
    (hind : ∀ g x, Function.update g k x ∈ s ↔ g ∈ s)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |φ x| ≤ B)
    (C : ℝ) :
    (∫ g in s, φ (gapKeys g (k + 1) / C) ∂iidLaw ν) =
      ∫ g in s, (∫ x, φ ((gapKeys g k + x) / C) ∂(ν : Measure ℝ)) ∂iidLaw ν := by
  let G := s.indicator (fun g => φ (gapKeys g (k + 1) / C))
  have hG : Measurable G :=
    (hφ.comp (((measurable_pi_apply (k + 1)).comp measurable_gapKeys).div_const C)).indicator hs
  have hGb (g : ℕ → ℝ) : |G g| ≤ B := by
    by_cases hg : g ∈ s
    · simpa only [G, indicator_of_mem hg] using hb (gapKeys g (k + 1) / C)
    · simpa only [G, indicator_of_notMem hg, abs_zero] using hB
  have hiG : Integrable G (iidLaw ν) :=
    (integrable_const B).mono' hG.aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by simpa only [Real.norm_eq_abs] using hGb g)
  have hI : Integrable (fun z : ℝ × (ℕ → ℝ) => G (Function.update z.2 k z.1))
      ((ν : Measure ℝ).prod (iidLaw ν)) :=
    (integrable_const B).mono' (hG.comp (measurable_update_pair k)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hGb _)
  rw [← integral_indicator hs, ← integral_indicator hs]
  change (∫ g, G g ∂iidLaw ν) = _
  rw [integral_update ν k hG hiG, integral_integral_swap hI]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun g => by
    by_cases hg : g ∈ s
    · rw [indicator_of_mem hg]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only [G]
        rw [indicator_of_mem ((hind g x).mpr hg), gapKeys_update_succ]
    · rw [indicator_of_notMem hg]
      have hz : ∀ x, G (Function.update g k x) = 0 := fun x => by
        dsimp only [G]
        rw [indicator_of_notMem (fun h => hg ((hind g x).mp h))]
      simp_rw [hz]
      exact integral_zero _ _

theorem integrable_kep_prefix_free_test (ν : ProbabilityMeasure ℝ)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |φ x| ≤ B)
    (C : ℝ) (k : ℕ) :
    Integrable (fun g => φ (gapKeys g k / C)) (iidLaw ν) ∧
      Integrable (fun g => ∫ x, φ ((gapKeys g k + x) / C) ∂(ν : Measure ℝ)) (iidLaw ν) := by
  have hnormB : |B| = B := abs_of_nonneg hB
  have hm : Measurable (fun g : ℕ → ℝ => φ (gapKeys g k / C)) :=
    hφ.comp (((measurable_pi_apply k).comp measurable_gapKeys).div_const C)
  have hmix : Measurable (fun z : (ℕ → ℝ) × ℝ => φ ((gapKeys z.1 k + z.2) / C)) :=
    hφ.comp (((((measurable_pi_apply k).comp measurable_gapKeys).comp measurable_fst).add
      measurable_snd).div_const C)
  have hmI : Measurable (fun g => ∫ x, φ ((gapKeys g k + x) / C) ∂(ν : Measure ℝ)) :=
    hmix.stronglyMeasurable.integral_prod_right'.measurable
  have hbI (g : ℕ → ℝ) : |∫ x, φ ((gapKeys g k + x) / C) ∂(ν : Measure ℝ)| ≤ B := by
    have hi : Integrable (fun x => φ ((gapKeys g k + x) / C)) (ν : Measure ℝ) :=
      (integrable_const |B|).mono'
        (hφ.comp ((measurable_const.add measurable_id).div_const C)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, hnormB] using hb _)
    calc
      _ ≤ ∫ x, |φ ((gapKeys g k + x) / C)| ∂(ν : Measure ℝ) := by
        simpa only [Real.norm_eq_abs, hnormB] using norm_integral_le_integral_norm (μ := (ν : Measure ℝ))
          (fun x : ℝ => φ ((gapKeys g k + x) / C))
      _ ≤ ∫ _x, B ∂(ν : Measure ℝ) := integral_mono hi.abs (integrable_const B) (fun x => hb _)
      _ = B := by simp
  refine ⟨(integrable_const |B|).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => by simpa only [Real.norm_eq_abs, hnormB] using hb _),
    (integrable_const |B|).mono' hmI.aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by simpa only [Real.norm_eq_abs, hnormB] using hbI g)⟩

theorem integral_prefix_convolution_increment (ν : ProbabilityMeasure ℝ)
    {s : Set (ℕ → ℝ)} (hs : MeasurableSet s) (k : ℕ)
    (hind : ∀ g x, Function.update g k x ∈ s ↔ g ∈ s)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |φ x| ≤ B)
    (C : ℝ) :
    (∫ g in s, (φ (gapKeys g (k + 1) / C) - φ (gapKeys g k / C)) ∂iidLaw ν) =
      ∫ g in s, kepPrefixConvolutionIncrement ν C φ k g ∂iidLaw ν := by
  obtain ⟨hiK, hiMix⟩ := integrable_kep_prefix_free_test ν hφ hB hb C k
  have hiNext := (integrable_kep_prefix_free_test ν hφ hB hb C (k + 1)).1
  unfold kepPrefixConvolutionIncrement
  rw [integral_sub hiNext.integrableOn hiK.integrableOn,
    integral_sub hiMix.integrableOn hiK.integrableOn,
    integral_prefix_next_gap ν hs k hind hφ hB hb C]

theorem integral_surviving_prefix_convolution_increment (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |φ x| ≤ B)
    (C : ℝ) (k : ℕ) :
    (∫ g in {g | (k : ℕ∞) < gapSegLen eps g},
      (φ (gapKeys g (k + 1) / C) - φ (gapKeys g k / C)) ∂iidLaw ν) =
      ∫ g in {g | (k : ℕ∞) < gapSegLen eps g},
        kepPrefixConvolutionIncrement ν C φ k g ∂iidLaw ν :=
  integral_prefix_convolution_increment ν (measurableSet_lt_gapSegLen eps k) k
    (fun _ _ => lt_gapSegLen_update_iff) hφ hB hb C

theorem integral_stopped_prefix_convolution_increment (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |φ x| ≤ B)
    (C : ℝ) (k : ℕ) :
    (∫ g in {g | gapSegLen eps g ≤ (k : ℕ∞)},
      (φ (gapKeys g (k + 1) / C) - φ (gapKeys g k / C)) ∂iidLaw ν) =
      ∫ g in {g | gapSegLen eps g ≤ (k : ℕ∞)},
        kepPrefixConvolutionIncrement ν C φ k g ∂iidLaw ν := by
  have hs : MeasurableSet {g : ℕ → ℝ | gapSegLen eps g ≤ (k : ℕ∞)} := by
    convert (measurableSet_lt_gapSegLen eps k).compl using 1
    ext g
    simp only [mem_compl_iff, mem_ofPred_eq, not_lt]
  apply integral_prefix_convolution_increment ν hs k _ hφ hB hb C
  intro g x
  change gapSegLen eps (Function.update g k x) ≤ (k : ℕ∞) ↔ gapSegLen eps g ≤ (k : ℕ∞)
  simpa only [not_lt] using not_congr (lt_gapSegLen_update_iff (eps := eps) (g := g) (i := k) (x := x))

end

end PGM
