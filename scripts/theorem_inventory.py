#!/usr/bin/env python3
"""Ask Lean to resolve the public result declarations, keeping their statements visible."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile

PACKAGE = Path(__file__).resolve().parents[1]
DECLARATIONS = {
    "B-MOM": ["BrownianAffine.anchoredUnitLifetime_moment_eq_coeff_readout", "BrownianAffine.optimalUnitLifetime_moment_eq",
              "BrownianAffine.optimalUnitLifetime_variance_eq_constant",
              "BrownianAffine.optimalUnitLifetime_fourth_central_eq_constant"],
    "S-SCALE": ["SwingRepair.secondSegment_mean_le", "SwingRepair.secondSegment_mean_ge", "SwingRepair.theorem_4_4_swing_gaussian",
                "SwingRepair.nativeTransientMarginProb_tendsto_entranceLaw", "SwingRepair.swing_transient_coefficients"],
    "S-BRACKET (actual coefficients; kernel-iteration evaluation)": ["SwingRepair.swing_transient_brackets", "SwingRepair.theorem_I1_swing_gaussian"],
    "P-GRE": ["PGM.G_RE_exact", "PGM.G_RE_exact_integral", "PGM.G_RE_exact_limit"],
    "P-KRE": ["PGM.K_RE_uniform", "PGM.K_RE_uniform_integral", "PGM.K_RE_exact",
              "PGM.K_RE_exact_probability", "PGM.K_RE_exact_integral"],
    "P-GEP": ["PGM.H_G_EP_additive", "PGM.H_G_EP_additive_law"],
    "P-KEP": ["PGM.H_K_EP_additive", "PGM.H_K_EP_additive_law",
              "PGM.H_K_EP", "PGM.H_K_EP_const_additive"],
    "P-CEPS": ["PGM.gepC_asymptoticExpansion", "PGM.cepsKernelPackages_holds",
               "PGM.cepsKernelJetRepresentation_holds", "PGM.cepsTransformInterfaces_holds"],
}

# A direct assignment checks the original constant, all quantifiers, and the absence of premises.
CEPS_SIGNATURE_CHECK = """
example :
    ∃! a : ℕ → ℝ, (∀ M : ℕ, ∃ K eps0 : ℝ, ∀ eps : ℝ, eps0 ≤ eps →
      |PGM.gepC eps / eps ^ 2 - ∑ j ∈ Finset.range (M + 1), a j * eps ^ (-(j : ℤ))| ≤
        K * eps ^ (-((M : ℤ) + 1))) ∧
      a 0 = BrownianAffine.optimalMeanConstant / BrownianAffine.optimalDispersionConstant :=
  PGM.gepC_asymptoticExpansion
"""


def main():
    source = "import PLAStochastic\n"
    for names in DECLARATIONS.values():
        source += "".join(f"#check {name}\n" for name in names)
    source += CEPS_SIGNATURE_CHECK
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
    with tempfile.TemporaryDirectory(prefix="pla-theorem-inventory-") as temp:
        path = Path(temp) / "TheoremInventory.lean"
        path.write_text(source)
        result = subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", str(path)],
                                cwd=PACKAGE, env=env, text=True, capture_output=True)
    print(result.stdout, end="")
    print(result.stderr, end="", file=sys.stderr)
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
