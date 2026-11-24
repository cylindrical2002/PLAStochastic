import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Shifting a vertical line of integration

`integral_vertical_eq_of_tendsto`: if `f` is continuous on the closed strip `a ≤ Re z ≤ b`,
complex differentiable in the open strip, integrable on both boundary lines, and the horizontal
segment integrals tend to zero along heights `T_k → +∞` and `-S_k → -∞`, then
`∫ f(a + i t) dt = ∫ f(b + i t) dt`.

`integral_vertical_eq_of_lintegral`: the horizontal condition follows from
`∫_ℝ ∫_{(a,b]} |f(σ + i t)| dσ dt < ∞` (the double integral over the strip is finite), along a
subsequence of heights.
-/

noncomputable section

open MeasureTheory Complex Filter Topology Set intervalIntegral
open scoped ENNReal

namespace PGM.WienerHopf

/-- Line shift under vanishing horizontal edges along given heights. -/
theorem integral_vertical_eq_of_tendsto {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f {z | z.re ∈ Icc a b})
    (hd : ∀ z : ℂ, z.re ∈ Ioo a b → DifferentiableAt ℂ f z)
    (ha : Integrable fun t : ℝ => f (a + t * I)) (hb : Integrable fun t : ℝ => f (b + t * I))
    {T S : ℕ → ℝ} (hT : Tendsto T atTop atTop) (hS : Tendsto S atTop atTop)
    (hTop : Tendsto (fun k => ∫ σ in a..b, f (σ + T k * I)) atTop (𝓝 0))
    (hBot : Tendsto (fun k => ∫ σ in a..b, f (σ + ((-S k : ℝ) : ℂ) * I)) atTop (𝓝 0)) :
    ∫ t : ℝ, f (a + t * I) = ∫ t : ℝ, f (b + t * I) := by
  have hrect : ∀ k, (∫ σ in a..b, f (σ + ((-S k : ℝ) : ℂ) * I)) -
      (∫ σ in a..b, f (σ + T k * I)) +
      I • (∫ t in (-S k)..(T k), f (b + t * I)) - I • (∫ t in (-S k)..(T k), f (a + t * I)) = 0 := by
    intro k
    have h := integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f
      (⟨a, -S k⟩ : ℂ) (⟨b, T k⟩ : ℂ) ∅ countable_empty ?_ ?_
    · simpa using h
    · refine hc.mono fun z hz => ?_
      rw [mem_reProdIm] at hz
      rw [Set.mem_ofPred_eq]
      have := hz.1
      rwa [uIcc_of_le hab] at this
    · intro z hz
      refine hd z ?_
      have := hz.1
      rw [mem_reProdIm] at this
      have h2 := this.1
      simpa [min_eq_left hab, max_eq_right hab] using h2
  have hlimB : Tendsto (fun k => ∫ t in (-S k)..(T k), f (b + t * I)) atTop
      (𝓝 (∫ t : ℝ, f (b + t * I))) :=
    intervalIntegral_tendsto_integral hb (tendsto_neg_atTop_atBot.comp hS) hT
  have hlimA : Tendsto (fun k => ∫ t in (-S k)..(T k), f (a + t * I)) atTop
      (𝓝 (∫ t : ℝ, f (a + t * I))) :=
    intervalIntegral_tendsto_integral ha (tendsto_neg_atTop_atBot.comp hS) hT
  have hlim := ((hBot.sub hTop).add (hlimB.const_smul I)).sub (hlimA.const_smul I)
  have h0 : (0 : ℂ) - 0 + I • (∫ t : ℝ, f (b + t * I)) - I • (∫ t : ℝ, f (a + t * I)) = 0 :=
    tendsto_nhds_unique hlim (by simp only [hrect]; exact tendsto_const_nhds)
  have : I * ((∫ t : ℝ, f (b + t * I)) - ∫ t : ℝ, f (a + t * I)) = 0 := by
    rw [mul_sub]; simpa using h0
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h I_ne_zero
  · exact (sub_eq_zero.mp h).symm

/-- A finite lower integral forces small values at arbitrarily large points. -/
theorem exists_seq_tendsto_atTop_of_lintegral_ne_top {h : ℝ → ℝ≥0∞} (hh : ∫⁻ t, h t ≠ ⊤) :
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧ Tendsto (fun k => h (T k)) atTop (𝓝 0) := by
  have hex : ∀ k : ℕ, ∃ t : ℝ, (k : ℝ) ≤ t ∧ h t ≤ ((k : ℝ≥0∞) + 1)⁻¹ := by
    intro k
    by_contra hcon
    push Not at hcon
    have hle : ∫⁻ t in Ici (k : ℝ), ((k : ℝ≥0∞) + 1)⁻¹ ≤ ∫⁻ t, h t :=
      (setLIntegral_mono' measurableSet_Ici fun t ht => (hcon t ht).le).trans
        (setLIntegral_le_lintegral _ _)
    rw [setLIntegral_const, Real.volume_Ici, ENNReal.mul_top (by simp)] at hle
    exact hh (top_le_iff.mp hle)
  choose T hT1 hT2 using hex
  refine ⟨T, tendsto_atTop_mono hT1 tendsto_natCast_atTop_atTop, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ENNReal.tendsto_inv_nat_nhds_zero (fun k => bot_le) (fun k => ?_)
  exact (hT2 k).trans (ENNReal.inv_le_inv.mpr le_self_add)

/-- Line shift when the double integral of `|f|` over the strip is finite. -/
theorem integral_vertical_eq_of_lintegral {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f {z | z.re ∈ Icc a b})
    (hd : ∀ z : ℂ, z.re ∈ Ioo a b → DifferentiableAt ℂ f z)
    (ha : Integrable fun t : ℝ => f (a + t * I)) (hb : Integrable fun t : ℝ => f (b + t * I))
    (hfin : ∫⁻ t : ℝ, ∫⁻ σ in Ioc a b, ENNReal.ofReal ‖f (σ + t * I)‖ ≠ ⊤) :
    ∫ t : ℝ, f (a + t * I) = ∫ t : ℝ, f (b + t * I) := by
  set h : ℝ → ℝ≥0∞ := fun t => ∫⁻ σ in Ioc a b, ENNReal.ofReal ‖f (σ + t * I)‖
  obtain ⟨T, hT, hTh⟩ := exists_seq_tendsto_atTop_of_lintegral_ne_top hfin
  have hfin' : ∫⁻ t : ℝ, h (-t) ≠ ⊤ := by
    rwa [lintegral_neg_eq_self (μ := volume) h]
  obtain ⟨S, hS, hSh⟩ := exists_seq_tendsto_atTop_of_lintegral_ne_top hfin'
  have hedge : ∀ {U : ℕ → ℝ}, Tendsto (fun k => h (U k)) atTop (𝓝 0) →
      Tendsto (fun k => ∫ σ in a..b, f (σ + U k * I)) atTop (𝓝 0) := by
    intro U hU
    refine squeeze_zero_norm (fun k => ?_) ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hU
      |>.trans (by simp))
    rw [integral_of_le hab]
    exact norm_integral_le_lintegral_norm _
  exact integral_vertical_eq_of_tendsto hab hc hd ha hb hT hS (hedge hTh)
    (hedge (U := fun k => -S k) hSh)

end PGM.WienerHopf
