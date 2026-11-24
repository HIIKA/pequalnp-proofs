import Mathlib
import PEqualNP.Defs

/-!
# L-meta-1208: an explicit ten-gate circuit at the cover count

The row's context hands over a gate list; this file unfolds it and checks it.

* `ckt` is that list verbatim (inputs are wires `0`–`7`, the output is the last wire `17`).
* `keval` evaluates it on all `2 ^ 8` inputs at once (`decide`, no free variable).
* `mono` checks `Monotone2` gate by gate: every gate is an AND or an OR reading two wires.
* `C.size = 10 ≤ 10`.

Imports are only `Mathlib` and `PEqualNP.Defs`; every declaration sits in a namespace of the file.
-/

namespace PEqualNP.Outside.L_meta_1208_aux

open PEqualNP.CircuitLowerBounds

/-- The circuit of the row, gate by gate. -/
def ckt : Circuit :=
  { gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.and, [5, 13]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], output := 17 }

theorem ofFn8 (x : Fin 8 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

/-- The truth table of the circuit, on all eight inputs at once. -/
theorem keval : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
    ckt.eval [a0, a1, a2, a3, a4, a5, a6, a7] =
      ((a0 && a1) || (a0 && a2) || (a1 && a3) || (a2 && a4) || (a3 && a5) || (a4 && a6) || (a5 && a7)) := by
  decide

theorem mono : PEqualNP.MetaComplexity.Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem size_le : ckt.size ≤ 10 := by
  simp [ckt, Circuit.size]

end PEqualNP.Outside.L_meta_1208_aux

theorem PEqualNP.Outside.L_meta_1208 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1208_aux.ckt, PEqualNP.Outside.L_meta_1208_aux.mono,
    PEqualNP.Outside.L_meta_1208_aux.size_le, ?_⟩
  intro x
  rw [PEqualNP.Outside.L_meta_1208_aux.ofFn8 x]
  exact PEqualNP.Outside.L_meta_1208_aux.keval (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
