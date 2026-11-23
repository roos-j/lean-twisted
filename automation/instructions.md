# Formalization instructions

Recorded at 2026-11-22T14:20:17-05:00. See [raw.md](raw.md) for the user's requests.

Formalize [the blueprint](../tp_blueprint.tex), including the Fourier and
principal-value conclusions and their prerequisites. Use at most one Lean file
per source section. Keep the standard library root as an import module.
The pinned toolchain and lean-spherical revision follow the blueprint.
Run the default Lake build and audit the public theorems with #print axioms.

The files in [TwistedParaproduct/Auto](../TwistedParaproduct/Auto) follow the
five mathematical sections of the blueprint. Section 1 contains the model
and the proposition in the Lean appendix. Section 5 proves that proposition as
Auto.proveBanachTarget and proves the physical kernel and principal-value
results. The source-map names correspond to declarations in namespace Auto.
Auto.separatedConeLp extends the separated profile estimate to arbitrary Lp
inputs. Auto.homogeneousPrincipalValueDistribution identifies the compensated
pairing as a tempered distribution on the whole space.

The Git manifest pins lean-spherical and its transitive dependencies. The
local build used the ignored .lake/local-packages.json override with the
existing sibling lean-spherical checkout at the pinned revision and cached
dependencies. A clean dependency download could not be verified because
GitHub was unreachable in the environment.

Recorded at 2026-11-22T14:45:07-05:00. Continue through the entire blueprint.

Recorded at 2026-11-22T21:00:14-05:00. Continue proof development through the
physical kernel and principal-value conclusions.

Verified at 2026-11-22T21:15:50-05:00. The default Lake build completed 3546 jobs with
the local package override. All 41 blueprint names resolved through the root
import. The 173 public theorem axiom checks reported only propext,
Classical.choice and Quot.sound.

Recorded at 2026-11-22T22:06:30-05:00 (recording time). Expose the proved main results in
Auto/Theorems.lean and define the isotropic operators, including twisted, in
Auto/Defs.lean using the lean-dfr style. Copy the blueprint and Lean project
to the standalone sibling repository lean-twisted.
