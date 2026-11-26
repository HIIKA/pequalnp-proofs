import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24095
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [5, 7]⟩,
    ⟨GateOp.or, [5, 0]⟩, ⟨GateOp.or, [9, 3]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [8, 11]⟩,
    ⟨GateOp.not, [12]⟩], 13⟩

theorem ok : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev : ∀ i j : Fin 5,
    C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j))
      = (807519 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24095

theorem PEqualNP.Outside.L_meta_24095 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (807519 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24095.C, PEqualNP.Outside.L_meta_24095.ok, by decide,
    PEqualNP.Outside.L_meta_24095.ev⟩