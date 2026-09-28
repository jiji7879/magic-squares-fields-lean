import MagicSquares.NormalizedSearch

namespace MagicSquares

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The arithmetic power test, including zero. -/
def powerEntryTest (n : ℕ) (x : F) : Prop :=
  x = 0 ∨ x ^ ((Fintype.card F - 1) / powerIndex n (Fintype.card F)) = 1

instance (n : ℕ) (x : F) : Decidable (powerEntryTest n x) :=
  inferInstanceAs (Decidable (x = 0 ∨ x ^
    ((Fintype.card F - 1) / powerIndex n (Fintype.card F)) = 1))

/-- Both entries opposite the center must be powers. Filtering these offsets
before the two-parameter search substantially reduces finite certificates. -/
def centerOnePowerOffsets (n : ℕ) : Finset F :=
  Finset.univ.filter fun u => powerEntryTest n (1 + u) ∧ powerEntryTest n (1 - u)

theorem centerOne_offsets_of_conditions {n : ℕ} {u v : F}
    (h : normalizedPowerConditions n (Square3.centerOne u v)) :
    u ∈ centerOnePowerOffsets n ∧ v ∈ centerOnePowerOffsets n := by
  have h0 := h.2 (0 : Fin 9)
  have h8 := h.2 (8 : Fin 9)
  have h2 := h.2 (2 : Fin 9)
  have h6 := h.2 (6 : Fin 9)
  constructor
  · simpa [centerOnePowerOffsets, powerEntryTest, Square3.centerOne,
      Square3.parametrized, Square3.entries] using And.intro h0 h8
  · simpa [centerOnePowerOffsets, powerEntryTest, Square3.centerOne,
      Square3.parametrized, Square3.entries] using And.intro h2 h6

/-- An equivalent search that restricts both center-one parameters to offsets
whose opposite entries pass the power test. -/
def prunedPowerSearchSucceeds (n : ℕ) : Bool :=
  decide ((∃ x : F, normalizedPowerConditions n (Square3.centerZero x)) ∨
    (∃ u ∈ centerOnePowerOffsets (F := F) n,
      ∃ v ∈ centerOnePowerOffsets (F := F) n,
        normalizedPowerConditions n (Square3.centerOne u v)))

/-- Pruning cannot discard a valid square. -/
theorem prunedPowerSearchSucceeds_eq_normalized (n : ℕ) :
    prunedPowerSearchSucceeds (F := F) n = normalizedPowerSearchSucceeds (F := F) n := by
  unfold prunedPowerSearchSucceeds normalizedPowerSearchSucceeds
  congr 1
  apply propext
  constructor
  · rintro (hz | ⟨u, _, v, _, h⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨u, v, h⟩
  · rintro (hz | ⟨u, v, h⟩)
    · exact Or.inl hz
    · have hm := centerOne_offsets_of_conditions h
      exact Or.inr ⟨u, hm.1, v, hm.2, h⟩

/-- Kernel reduction of the pruned Boolean certifies the full Parker property. -/
theorem isNParker_iff_prunedPowerSearch_eq_false {n : ℕ} (hn : 0 < n) :
    IsNParker F n ↔ prunedPowerSearchSucceeds (F := F) n = false := by
  rw [prunedPowerSearchSucceeds_eq_normalized,
    ← isNParker_iff_normalizedPowerSearch_eq_false hn]

end MagicSquares
