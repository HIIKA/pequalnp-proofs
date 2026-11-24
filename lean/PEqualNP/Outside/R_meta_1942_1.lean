import Mathlib
import PEqualNP.Defs

-- Reduction of L-meta-1942 into four sub-goals. First: on any two-sided incidence structure in
-- which no two points share two lines, every AND/OR fan-in-two circuit of positive size that
-- computes the incidence and reads each variable of a prime implicant at most twice has at most
-- a hundredth of the incident pairs in gates. Second: two distinct points of a plane lie on
-- exactly one line, so no two points share two lines. Third: the incident pairs of a plane
-- number N times q + 1. Fourth: a plane's incidence is computed by no circuit without gates, so
-- a computing circuit has positive size. The four give the row, since N q is at most the pair
-- count, which is at most a hundredth of the size. The pair counts are written as the
-- cardinality of the subtype of incident pairs, so that each sub-goal prints as text that reads
-- back as the same term.
theorem PEqualNP.Outside.R_meta_1942_1 :
    (∀ (n : ℕ) (R : Fin n → Fin n → Prop) [DecidableRel R]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (p p' : Fin n) (l l' : Fin n), R p l → R p l' → R p' l → R p' l' →
        p = p' ∨ l = l') →
      PEqualNP.TopForm.IsAO2 (n + n) C →
      (∀ z : Fin (n + n) → Bool,
        PEqualNP.MetaComplexity.circuitFun (n + n) C z =
          decide (∃ p l : Fin n, R p l ∧ z (Fin.castAdd n p) = true ∧
            z (Fin.natAdd n l) = true)) →
      PEqualNP.ReadK.IsReadK (n + n) C 2 →
      1 ≤ C.size →
      Fintype.card {pl : Fin n × Fin n // R pl.1 pl.2} ≤ 100 * C.size) →
    (∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      ∀ (p p' : Fin N) (l l' : Fin N), I p l → I p l' → I p' l → I p' l' →
        p = p' ∨ l = l') →
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      Fintype.card {pl : Fin N × Fin N // I pl.1 pl.2} = N * (q + 1)) →
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q →
      N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) C z =
          decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
            z (Fin.natAdd N l) = true)) →
      1 ≤ C.size) →
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * q ≤ 100 * C.size := by
  intro hCrux hFree hCount hPos q N I _inst C hq hN hline huniq hAO2 hcirc hread
  have hline' : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1 := by
    intro l
    rw [Fintype.card_subtype]
    exact hline l
  have hsize : 1 ≤ C.size := hPos q N I C hq hN hline' hcirc
  have hfree : ∀ (p p' : Fin N) (l l' : Fin N), I p l → I p l' → I p' l → I p' l' →
      p = p' ∨ l = l' :=
    hFree N I huniq
  have hbound :
      Fintype.card {pl : Fin N × Fin N // I pl.1 pl.2} ≤ 100 * C.size :=
    hCrux N I C hfree hAO2 hcirc hread hsize
  rw [hCount q N I hline'] at hbound
  exact le_trans (Nat.mul_le_mul_left N (by omega)) hbound
