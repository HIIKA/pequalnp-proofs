import Mathlib
import PEqualNP.Defs

/-!
L-meta-8849: an AND/OR circuit of fan-in two is monotone on incidence inputs.

If C is in the model IsAO2 (AND and OR gates only, each reading exactly two earlier wires) and it
accepts the incidence input of (X, Y), then it accepts the incidence input of any (X, Y) grown
pointwise. The proof carries the pointwise implication of the wire values through the gate list;
each AND or OR gate of two wires preserves it.
-/

namespace PEqualNP.Outside.L_meta_8849

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.GenericRejection
  PEqualNP.TopForm

/-- Pointwise implication of Boolean lists of equal length, read through `getD`: a missing entry
counts as false. The length is carried along because the gate list appends one entry per gate. -/
def Pw (l l' : List Bool) : Prop :=
  l.length = l'.length ∧ ∀ i, l.getD i false = true → l'.getD i false = true

lemma Pw.refl (l : List Bool) : Pw l l := ⟨rfl, fun _ h => h⟩

lemma Pw.trans {a b c : List Bool} (h1 : Pw a b) (h2 : Pw b c) : Pw a c :=
  ⟨h1.1.trans h2.1, fun i h => h2.2 i (h1.2 i h)⟩

/-- Appending one entry preserves the pointwise implication when the entries do. -/
lemma Pw.append {w w' : List Bool} (h : Pw w w') (b b' : Bool) (hb : b = true → b' = true) :
    Pw (w ++ [b]) (w' ++ [b']) := by
  have hlen : w.length = w'.length := h.1
  refine ⟨by simp [hlen], ?_⟩
  intro i hi
  by_cases hlt : i < w.length
  · have hlt' : i < w'.length := by omega
    rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ hlt']
    exact h.2 i hi
  · have hge : w.length ≤ i := by omega
    have hge' : w'.length ≤ i := by omega
    rw [List.getD_append_right _ _ _ _ hge] at hi
    rw [List.getD_append_right _ _ _ _ hge']
    have hi0 : i - w.length = 0 := by
      by_contra hne
      have hpos : 1 ≤ i - w.length := by omega
      rw [List.getD_eq_default _ _ (by simpa using hpos)] at hi
      exact absurd hi (by simp)
    have hi0' : i - w'.length = 0 := by omega
    rw [hi0] at hi
    rw [hi0']
    simpa using hb hi

/-- One AND gate of two wires preserves the pointwise implication. -/
lemma and_step {w w' : List Bool} (h : Pw w w') (g : Gate) (hop : g.op = GateOp.and) :
    Pw (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) := by
  refine Pw.append h _ _ ?_
  intro hb
  rw [hop] at hb ⊢
  have hall : ∀ x ∈ g.inputs.map (fun i => w.getD i false), x = true := by
    simpa [GateOp.eval] using (List.all_eq_true.mp hb)
  rw [GateOp.eval, List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact h.2 i (hall _ (List.mem_map.mpr ⟨i, hi, rfl⟩))

/-- One OR gate of two wires preserves the pointwise implication. -/
lemma or_step {w w' : List Bool} (h : Pw w w') (g : Gate) (hop : g.op = GateOp.or) :
    Pw (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) := by
  refine Pw.append h _ _ ?_
  intro hb
  rw [hop] at hb ⊢
  rw [GateOp.eval] at hb
  obtain ⟨x, hx, hxt⟩ := List.any_eq_true.mp hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact List.any_eq_true.mpr ⟨w'.getD i false, List.mem_map.mpr ⟨i, hi, rfl⟩, h.2 i hxt⟩

/-- The gate list of an AND/OR circuit preserves the pointwise implication. -/
lemma fold_Pw (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {w w' : List Bool} (h : Pw w w') :
    Pw (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs generalizing w w' with
  | nil => exact h
  | cons g gs ih =>
    rcases hAO g (List.mem_cons_self) with hg | hg
    · exact ih (fun g' hg' => hAO g' (List.mem_cons_of_mem g hg')) (and_step h g hg)
    · exact ih (fun g' hg' => hAO g' (List.mem_cons_of_mem g hg')) (or_step h g hg)

lemma wires_Pw (C : Circuit) (hAO : AndOrOnly C) {w w' : List Bool} (h : Pw w w') :
    Pw (C.wires w) (C.wires w') :=
  fold_Pw C.gates hAO h

/-- An AND/OR circuit that is true on an input is true on every pointwise larger input. -/
lemma eval_Pw (C : Circuit) (hAO : AndOrOnly C) {w w' : List Bool} (h : Pw w w')
    (hev : C.eval w = true) : C.eval w' = true :=
  (wires_Pw C hAO h).2 C.output hev

lemma ofFn_getD_pos {m : ℕ} (f : Fin m → Bool) {i : ℕ} (h : i < m) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]

lemma ofFn_getD_neg {m : ℕ} (f : Fin m → Bool) {i : ℕ} (h : m ≤ i) :
    (List.ofFn f).getD i false = false := by
  rw [List.getD_eq_default _ _ (by simpa using h)]

/-- Growing both sides of an incidence input grows the input list pointwise. -/
lemma incidenceInput_Pw {n : ℕ} {X X' Y Y' : Finset (Fin n)} (hX : X ⊆ X') (hY : Y ⊆ Y') :
    Pw (incidenceInput X Y) (incidenceInput X' Y') := by
  have hlen : (incidenceInput X Y).length = (incidenceInput X' Y').length := by
    simp [incidenceInput]
  refine ⟨hlen, ?_⟩
  intro i hi
  unfold incidenceInput at hi ⊢
  by_cases hlt : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using hlt)] at hi
    rw [List.getD_append _ _ _ _ (by simpa using hlt)]
    rw [ofFn_getD_pos _ hlt] at hi ⊢
    simpa using decide_eq_true (hX (of_decide_eq_true hi))
  · have hge : n ≤ i := by omega
    rw [List.getD_append_right _ _ _ _ (by simpa using hge)] at hi
    rw [List.getD_append_right _ _ _ _ (by simpa using hge)]
    simp only [List.length_ofFn] at hi ⊢
    by_cases h2 : i - n < n
    · rw [ofFn_getD_pos _ h2] at hi ⊢
      simpa using decide_eq_true (hY (of_decide_eq_true hi))
    · have h2' : n ≤ i - n := by omega
      rw [ofFn_getD_neg _ h2'] at hi
      rw [ofFn_getD_neg _ h2']
      exact absurd hi (by simp)

end PEqualNP.Outside.L_meta_8849

theorem PEqualNP.Outside.L_meta_8849 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 (x1 + x1) x2 →
      ∀ (x4 x5 x6 x7 : Finset (Fin x1)), x4 ⊆ x6 → x5 ⊆ x7 →
        x2.eval (PEqualNP.GenericRejection.incidenceInput x4 x5) = Bool.true →
        x2.eval (PEqualNP.GenericRejection.incidenceInput x6 x7) = Bool.true := by
  intro x1 x2 hAO x4 x5 x6 x7 h4 h5 hev
  exact PEqualNP.Outside.L_meta_8849.eval_Pw x2 hAO.1
    (PEqualNP.Outside.L_meta_8849.incidenceInput_Pw h4 h5) hev
