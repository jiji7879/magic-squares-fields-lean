import MagicSquares

-- Run only after `lake build`. These commands ask Lean for transitive axioms.
#print axioms MagicSquares.squareParker_iff
#print axioms MagicSquares.squareParker_iff_of_char_ne_two
#print axioms MagicSquares.cubeParker_iff_of_char_ne_two
#print axioms MagicSquares.finite_nParker_cardinalities
#print axioms MagicSquares.isNParker_of_charTwo
#print axioms MagicSquares.Square3.exists_magic_of_powers_of_card_gt_bound
