import PLAStochastic.Index.KEP.ReferenceScale.LongCoreCutoff
import PLAStochastic.Index.KEP.ReferenceScale.SurvivingCore

/-!
# Summing the original certificate pairs over all prefix lengths

The original pair maps injectively to its left length, right length and excess
long-bridge length. Thus its full nonnegative series is bounded by the proved
three-length graph series without paying a spurious multiplicity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

def kepLongCertificatePairs (eps : ℝ) (M k : ℕ) : Finset (ℕ × ℕ) :=
  (certPairs eps k).filter (fun ij => M ≤ ij.2 - ij.1)

def kepLongCertificateTriple {eps : ℝ} {M : ℕ}
    (d : Σ k : ℕ, {ij : ℕ × ℕ // ij ∈ kepLongCertificatePairs eps M k}) : ℕ × ℕ × ℕ :=
  (d.2.val.1, d.1 - d.2.val.2, d.2.val.2 - d.2.val.1 - M)

theorem kepLongCertificateTriple_injective (eps : ℝ) (M : ℕ) :
    Function.Injective (kepLongCertificateTriple (eps := eps) (M := M)) := by
  intro a b hab
  rcases a with ⟨k, ij, hij⟩
  rcases b with ⟨l, uv, huv⟩
  obtain ⟨hijmem, hMij⟩ := Finset.mem_filter.mp hij
  obtain ⟨huvmem, hMuv⟩ := Finset.mem_filter.mp huv
  obtain ⟨hijlt, hjk, _⟩ := mem_certPairs.mp hijmem
  obtain ⟨huvlt, hvl, _⟩ := mem_certPairs.mp huvmem
  have h1 := congrArg Prod.fst hab
  have h2 := congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) hab
  have h3 := congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) hab
  dsimp [kepLongCertificateTriple] at h1 h2 h3
  have hkl : k = l := by omega
  subst l
  have hpair : ij = uv := Prod.ext h1 (by omega)
  subst uv
  rfl

theorem kep_certificate_length_series {eps : ℝ} (M : ℕ) {H : ℕ × ℕ × ℕ → ℝ}
    (hH : ∀ z, 0 ≤ H z) (hsH : Summable H) :
    let F := fun k : ℕ => ∑ ij ∈ kepLongCertificatePairs eps M k,
      H (ij.1, k - ij.2, ij.2 - ij.1 - M)
    Summable F ∧ (∑' k : ℕ, F k) ≤ ∑' z : ℕ × ℕ × ℕ, H z := by
  classical
  dsimp only
  let β := fun k : ℕ => {ij : ℕ × ℕ // ij ∈ kepLongCertificatePairs eps M k}
  let G := fun d : Σ k : ℕ, β k => H (kepLongCertificateTriple d)
  have hi := kepLongCertificateTriple_injective eps M
  have hsG : Summable G := hsH.comp_injective hi
  have hsFib := (summable_sigma_of_nonneg (fun d => hH (kepLongCertificateTriple d))).mp hsG
  have hfinite (k : ℕ) : (∑' ij : β k, G ⟨k, ij⟩) =
      ∑ ij ∈ kepLongCertificatePairs eps M k, H (ij.1, k - ij.2, ij.2 - ij.1 - M) := by
    exact Finset.tsum_subtype (kepLongCertificatePairs eps M k)
      (fun ij : ℕ × ℕ => H (ij.1, k - ij.2, ij.2 - ij.1 - M))
  have hsOuter : Summable (fun k : ℕ => ∑ ij ∈ kepLongCertificatePairs eps M k,
      H (ij.1, k - ij.2, ij.2 - ij.1 - M)) := by
    have hh : Summable (fun k : ℕ => ∑' ij : β k, G ⟨k, ij⟩) := hsFib.2
    simpa only [hfinite] using hh
  refine ⟨hsOuter, ?_⟩
  have hsum : (∑' d : Σ k : ℕ, β k, G d) = ∑' k : ℕ,
      ∑ ij ∈ kepLongCertificatePairs eps M k, H (ij.1, k - ij.2, ij.2 - ij.1 - M) := by
    rw [Summable.tsum_sigma' hsFib.1 hsG]
    simp only [hfinite]
  rw [← hsum]
  exact tsum_comp_le_tsum_of_inj hsH hH hi

end

end PGM
