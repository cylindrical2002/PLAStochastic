import PLAStochastic.Index.GEP.Kernel.Insertion.LogScale
import PLAStochastic.Index.GEP.Kernel.FarSlope.LogWindow

/-! # The exact near/far slope partition used by the actual influence kernels -/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

def kernelNearSlopes (w A : ℝ) : Set ℝ := Ioo (1-A/w) (1+A/w)

theorem measurableSet_kernelNearSlopes (w A : ℝ) : MeasurableSet (kernelNearSlopes w A) :=
  measurableSet_Ioo

theorem kernelNearSlopes_iff {w A a : ℝ} (hw : 0 < w) :
    a ∈ kernelNearSlopes w A ↔ w*|a-1| < A := by
  rw [kernelNearSlopes,mem_Ioo]
  constructor
  · rintro ⟨hl,hu⟩
    have hh : |a-1| < A/w := abs_lt.mpr ⟨by linarith,by linarith⟩
    simpa only [mul_comm] using (lt_div_iff₀ hw).mp hh
  · intro hh
    have hh' : |a-1| < A/w := (lt_div_iff₀ hw).mpr (by simpa only [mul_comm] using hh)
    have hh'' := abs_lt.mp hh'
    exact ⟨by linarith [hh''.1],by linarith [hh''.2]⟩

theorem kernelNearSlopes_nonempty {w A : ℝ} (hw : 0 < w) (hA : 0 < A) :
    (kernelNearSlopes w A).Nonempty := by
  refine ⟨1,(kernelNearSlopes_iff hw).mpr ?_⟩
  simpa using hA

theorem kernelNearSlopes_subset {w A : ℝ} (hw : 0 < w) (hA : A ≤ w/4) :
    kernelNearSlopes w A ⊆ Ioo (1/2 : ℝ) 2 := by
  have hdiv : A/w ≤ 1/4 := (div_le_iff₀ hw).mpr (by linarith)
  intro a ha
  change 1-A/w < a ∧ a < 1+A/w at ha
  exact ⟨by linarith [ha.1],by linarith [ha.2]⟩

theorem kernelNearSlopes_partition {w A : ℝ} (hw : 0 < w) (hA : A ≤ w/4) :
    Disjoint (kernelNearSlopes w A) (kernelFarSlopes w A) ∧
      kernelNearSlopes w A ∪ kernelFarSlopes w A = Ioi 0 := by
  constructor
  · apply Set.disjoint_left.mpr
    intro a hn hf
    exact (not_le_of_gt ((kernelNearSlopes_iff hw).mp hn)) hf.2
  · ext a
    constructor
    · rintro (hn|hf)
      · exact lt_trans (by norm_num) ((kernelNearSlopes_subset hw hA) hn).1
      · exact hf.1
    · intro ha
      by_cases hfar : A ≤ w*|a-1|
      · exact Or.inr ⟨ha,hfar⟩
      · exact Or.inl ((kernelNearSlopes_iff hw).mpr (lt_of_not_ge hfar))

end
end PGM
