import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1872_1
    (t1 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C →
      (∀ (p l : Fin (13 : ℕ)), p - l = (0 : Fin (13 : ℕ)) ∨ p - l = (1 : Fin (13 : ℕ)) ∨ p - l = (3 : Fin (13 : ℕ)) ∨ p - l = (9 : Fin (13 : ℕ)) →
        C.eval ((List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x = p)) ++ List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x = l)) = Bool.true) →
      (∀ (Q : Finset (Fin (13 : ℕ))), Q.card = (4 : ℕ) →
        (∀ (l : Fin (13 : ℕ)), {q ∈ Q | q - l = (0 : Fin (13 : ℕ)) ∨ q - l = (1 : Fin (13 : ℕ)) ∨ q - l = (3 : Fin (13 : ℕ)) ∨ q - l = (9 : Fin (13 : ℕ))}.card ≤ (2 : ℕ)) →
        C.eval ((List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x ∈ Q)) ++ List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (∀ q ∈ Q, ¬(q - x = (0 : Fin (13 : ℕ)) ∨ q - x = (1 : Fin (13 : ℕ)) ∨ q - x = (3 : Fin (13 : ℕ)) ∨ q - x = (9 : Fin (13 : ℕ))))) = Bool.false) →
      (64 : ℕ) ≤ C.size)
    (t2 : ∀ (p l : Fin (13 : ℕ)),
      (p - l = (0 : Fin (13 : ℕ)) ∨ p - l = (1 : Fin (13 : ℕ)) ∨ p - l = (3 : Fin (13 : ℕ)) ∨ p - l = (9 : Fin (13 : ℕ))) ↔
      p ∈ PEqualNP.HeptadCover.singerLines3 l)
    (t3 : ∀ (Q : Finset (Fin (13 : ℕ))) (l : Fin (13 : ℕ)),
      l ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q ↔
      ∀ q ∈ Q, ¬(q - l = (0 : Fin (13 : ℕ)) ∨ q - l = (1 : Fin (13 : ℕ)) ∨ q - l = (3 : Fin (13 : ℕ)) ∨ q - l = (9 : Fin (13 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∨ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∧ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Fin (13 : ℕ)) (x16 : Fin (13 : ℕ)), x15 - x16 ∈ x8 ∧ x12 x2 (x9 x15 x16) = Bool.true ∧ x12 x3 (x9 x15 x16) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x8 ∧ x12 x3 (x9 x16 x17) = Bool.true ∧ x12 x2 (x9 x16 x17) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro C k m hM hRB hk hm x8v x9v x10v x11v x12v hpos hquad hcomp1 hcomp2
  have hsz : C.size = C.gates.length := rfl
  have hx8mem : ∀ (a : Fin (13 : ℕ)),
      (a ∈ x8v) ↔
      (a = (0 : Fin (13 : ℕ)) ∨ a = (1 : Fin (13 : ℕ)) ∨ a = (3 : Fin (13 : ℕ)) ∨ a = (9 : Fin (13 : ℕ))) := by
    intro a
    show (a ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) ↔ _
    simp
  set g0 : PEqualNP.CircuitLowerBounds.Gate :=
    { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [k, m] } with hg0
  set C' : PEqualNP.CircuitLowerBounds.Circuit :=
    { gates := C.gates ++ [g0], output := (26 : ℕ) + C.size } with hC'
  have hgen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (M : List Bool),
      ((gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) M).length) =
      M.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro M; simp
    | cons g gs' ih =>
        intro M
        rw [List.foldl_cons, ih]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
  have hwlen : ∀ L : List Bool, (C.wires L).length = L.length + C.gates.length := by
    intro L
    have h2 : C.wires L = C.gates.foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) L := rfl
    rw [h2, hgen]
  have hx3eq : ∀ (kk : ℕ) (L : List Bool), x12v kk L = (C.wires L).getD kk Bool.false := fun _ _ => rfl
  have hor2 : ∀ (a b : Bool),
      PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.or [a, b] = (a || b) := by
    intro a b
    cases a <;> cases b <;> rfl
  have hx9len : ∀ (p l : Fin (13 : ℕ)), (x9v p l).length = (26 : ℕ) := by
    intro p l
    have h3 : (x9v p l).length = ((List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = p)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = l)).length := rfl
    rw [h3, List.length_append, List.length_ofFn, List.length_ofFn]
  have hx10len : ∀ (Q : Finset (Fin (13 : ℕ))), (x10v Q).length = (26 : ℕ) := by
    intro Q
    have h3 : (x10v Q).length = ((List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ Q)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ Q, x12 - x11 ∉ x8v)).length := rfl
    rw [h3, List.length_append, List.length_ofFn, List.length_ofFn]
  have hC'len : C'.gates.length = C.gates.length + 1 := by
    show (C.gates ++ [g0]).length = C.gates.length + 1
    rw [List.length_append, List.length_singleton]
  have hw : ∀ L : List Bool, C'.wires L = C.wires L ++
      [((C.wires L).getD k Bool.false) || ((C.wires L).getD m Bool.false)] := by
    intro L
    have h1 : C'.wires L = (C.gates ++ [g0]).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) L := rfl
    have h2 : C.gates.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) L = C.wires L := rfl
    rw [h1, List.foldl_append, h2, List.foldl_cons, List.foldl_nil, hg0]
    show C.wires L ++ [PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.or
      [((C.wires L).getD k Bool.false), ((C.wires L).getD m Bool.false)]] = _
    rw [hor2]
  have hev : ∀ L : List Bool, L.length = (26 : ℕ) →
      C'.eval L = (((C.wires L).getD k Bool.false) || ((C.wires L).getD m Bool.false)) := by
    intro L hL26
    have he : C'.eval L = (C'.wires L).getD ((26 : ℕ) + C.size) Bool.false := rfl
    have hidx : ((26 : ℕ) + C.size) = (C.wires L).length := by
      rw [hwlen L, hL26, hsz]
    rw [he, hw L, hidx, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
    rfl
  have hM' : PEqualNP.MetaComplexity.Monotone2 C' := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hM g h
    · have hg0' : g = g0 := by simpa using h
      subst hg0'
      refine ⟨Or.inr rfl, ?_⟩
      rfl
  have hRB' : PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C' := by
    intro j hj
    rcases Nat.lt_or_ge j C.gates.length with hlt | hge
    · have hgt : PEqualNP.MetaComplexity.NestedCover.gateAt C' j =
        PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
        show (C.gates ++ [g0]).getD j _ = C.gates.getD j _
        exact List.getD_append _ _ _ _ hlt
      intro i hi
      rw [hgt] at hi
      exact hRB j hlt i hi
    · have hj' : j = C.gates.length := by omega
      subst hj'
      intro i hi
      have hgt : PEqualNP.MetaComplexity.NestedCover.gateAt C' C.gates.length = g0 := by
        show (C.gates ++ [g0]).getD C.gates.length _ = g0
        rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
        rfl
      rw [hgt, hg0] at hi
      rcases List.mem_cons.mp hi with rfl | hi'
      · omega
      · have hix : i = m := by simpa using hi'
        subst hix
        omega
  -- positive spec transfer: x9 is already the two-hot form
  have hpos' : ∀ (p l : Fin (13 : ℕ)), p - l = (0 : Fin (13 : ℕ)) ∨ p - l = (1 : Fin (13 : ℕ)) ∨ p - l = (3 : Fin (13 : ℕ)) ∨ p - l = (9 : Fin (13 : ℕ)) →
      C'.eval ((List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x = p)) ++ List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x = l)) = Bool.true := by
    intro p l hpl
    have hin : (p - l ∈ x8v) := (hx8mem (p - l)).mpr hpl
    have hL : ((List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x = p)) ++ List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x = l)) = x9v p l := rfl
    rw [hL, hev _ (hx9len p l)]
    rcases hpos p l hin with h | h
    · simp only [hx3eq] at h; rw [h, Bool.true_or]
    · simp only [hx3eq] at h; rw [h, Bool.or_true]
  -- quadrangle spec transfer
  have hquad' : ∀ (Q : Finset (Fin (13 : ℕ))), Q.card = (4 : ℕ) →
      (∀ (l : Fin (13 : ℕ)), {q ∈ Q | q - l = (0 : Fin (13 : ℕ)) ∨ q - l = (1 : Fin (13 : ℕ)) ∨ q - l = (3 : Fin (13 : ℕ)) ∨ q - l = (9 : Fin (13 : ℕ))}.card ≤ (2 : ℕ)) →
      C'.eval ((List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x ∈ Q)) ++ List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (∀ q ∈ Q, ¬(q - x = (0 : Fin (13 : ℕ)) ∨ q - x = (1 : Fin (13 : ℕ)) ∨ q - x = (3 : Fin (13 : ℕ)) ∨ q - x = (9 : Fin (13 : ℕ))))) = Bool.false := by
    intro Q hcard hper
    have hper' : ∀ (l : Fin (13 : ℕ)), {q ∈ Q | q - l ∈ x8v}.card ≤ (2 : ℕ) := by
      intro l
      have hfe : {q ∈ Q | q - l ∈ x8v} =
          {q ∈ Q | q - l = (0 : Fin (13 : ℕ)) ∨ q - l = (1 : Fin (13 : ℕ)) ∨ q - l = (3 : Fin (13 : ℕ)) ∨ q - l = (9 : Fin (13 : ℕ))} :=
        Finset.filter_congr fun q hq => hx8mem (q - l)
      rw [hfe]
      exact hper l
    have hor := hquad Q ⟨hcard, hper'⟩
    -- the second-block predicates agree via the membership bridge
    have hpb : (List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (∀ q ∈ Q, ¬(q - x = (0 : Fin (13 : ℕ)) ∨ q - x = (1 : Fin (13 : ℕ)) ∨ q - x = (3 : Fin (13 : ℕ)) ∨ q - x = (9 : Fin (13 : ℕ))))) =
        (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ Q, x12 - x11 ∉ x8v)) := by
      congr 1
      funext x
      simp only [hx8mem]
    have hL : ((List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x ∈ Q)) ++ (List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (∀ q ∈ Q, ¬(q - x = (0 : Fin (13 : ℕ)) ∨ q - x = (1 : Fin (13 : ℕ)) ∨ q - x = (3 : Fin (13 : ℕ)) ∨ q - x = (9 : Fin (13 : ℕ)))))) = x10v Q := by
      rw [hpb]
    rw [hL, hev _ (hx10len Q)]
    simp only [hx3eq] at hor
    obtain ⟨hk, hm2⟩ := hor
    rw [hk, hm2, Bool.false_or]
  have h64 := t1 C' hM' hRB' hpos' hquad'
  have hC'sz : C'.size = C.size + 1 := by
    show (C.gates ++ [g0]).length = C.gates.length + 1
    rw [List.length_append, List.length_singleton]
  omega