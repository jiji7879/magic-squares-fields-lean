import MagicSquares.Stepanov.Lemma652.Counts
import MagicSquares.Stepanov.Lemma652.System
import MagicSquares.Stepanov.Lemma653.Core
namespace MagicSquares
namespace LN97

/-!
# LN97 6.52--6.53 assembly checkpoint

This module intentionally contains no new axioms or hypotheses.
It imports the three new pieces of the batch:

1. the arithmetic implication from `(M+3)^2`,
2. the homogeneous linear-system / constraint-system assembly, and
3. the multiplicity-versus-degree counting step used in Theorem 6.53.

The remaining mathematical work for a literal formalization of Lemma 6.52
is now concentrated in two concrete constructions:

* instantiate `StepanovConstraintSystem` with the actual `s_{t,n}` of
  equations (6.24)--(6.26), and prove the concrete `S < A` estimate;
* discharge `QuotientPowerIndependent` from the Kummer /
  absolute-irreducibility argument of Lemma 6.46.

Keeping those two hard inputs isolated lets the rest of the proof build
and be tested independently.
-/

end LN97
end MagicSquares
