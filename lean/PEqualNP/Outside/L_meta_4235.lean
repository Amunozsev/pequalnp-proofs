import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4235

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pushGate (wires : List Bool) (g : Gate) : List Bool :=
  wires ++ [g.op.eval (g.inputs.map fun i => wires.getD i false)]

lemma pushGate_length (gates : List Gate) (wires : List Bool) :
    (gates.foldl pushGate wires).length = wires.length + gates.length := by
  induction gates generalizing wires with
  | nil => simp
  | cons g gates ih =>
    simp only [List.foldl_cons, ih, pushGate, List.length_append, List.length_nil, List.length_cons]
    omega

lemma snoc_read (xs : List Bool) (b : Bool) (i : Nat) :
    (xs ++ [b]).getD i false =
      if i < xs.length then xs.getD i false else if i = xs.length then b else false := by
  by_cases h : i < xs.length
  · rw [ite_eq_left h, List.getD_append _ _ _ _ h]
  · rw [ite_eq_right h, List.getD_append_right _ _ _ _ (by omega)]
    by_cases he : i = xs.length
    · subst i
      simp
    · rw [ite_eq_right he]
      have hi : 1 ≤ i - xs.length := by omega
      exact List.getD_eq_default _ _ (by simpa using hi)

lemma input_read (x : Fin n → Bool) (i : Nat) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
  simp only [Option.getD_some, List.getElem_ofFn]

-- Replacing the requested output of one gate by its input wires costs at most one wire.
lemma support (n : Nat) (gates : List Gate) (T : Finset Nat)
    (hFan : ∀ g ∈ gates, g.inputs.length ≤ 2) :
    ∃ S : Finset Nat, S.card ≤ T.card + gates.length ∧
      ∀ x y : Fin n → Bool, (∀ v : Fin n, v.val ∈ S → x v = y v) →
        ∀ i ∈ T, (gates.foldl pushGate (List.ofFn x)).getD i false =
          (gates.foldl pushGate (List.ofFn y)).getD i false := by
  induction gates using List.reverseRecOn generalizing T with
  | nil =>
    refine ⟨T, by simp, ?_⟩
    intro x y hxy i hi
    simp only [List.foldl_nil]
    by_cases hin : i < n
    · rw [input_read x i hin, input_read y i hin]
      exact hxy ⟨i, hin⟩ hi
    · rw [List.getD_eq_default _ _ (by simpa using hin),
          List.getD_eq_default _ _ (by simpa using hin)]
  | append_singleton gs g ih =>
    let w := n + gs.length
    let T' := if w ∈ T then T.erase w ∪ g.inputs.toFinset else T
    have keep (i : Nat) (hi : i ∈ T) (hne : i ≠ w) : i ∈ T' := by
      by_cases hw : w ∈ T
      · simpa only [T', ite_eq_left hw] using
          Finset.mem_union_left g.inputs.toFinset (Finset.mem_erase.mpr ⟨hne, hi⟩)
      · simpa [T', hw] using hi
    have pins (hw : w ∈ T) (i : Nat) (hi : i ∈ g.inputs) : i ∈ T' := by
      simpa [T', hw] using Finset.mem_union_right (T.erase w) (List.mem_toFinset.mpr hi)
    have hsize : T'.card ≤ T.card + 1 := by
      by_cases hw : w ∈ T
      · rw [show T' = _ from ite_eq_left hw]
        have hu := Finset.card_union_le (T.erase w) g.inputs.toFinset
        have hd := Finset.card_erase_add_one hw
        have hg := hFan g (by simp)
        have hl := List.toFinset_card_le g.inputs
        omega
      · simp [T', hw]
    obtain ⟨S, hS, agrees⟩ := ih T' (fun q hq => hFan q (List.mem_append_left _ hq))
    refine ⟨S, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hxy i hi
    let X := gs.foldl pushGate (List.ofFn x)
    let Y := gs.foldl pushGate (List.ofFn y)
    have hx : X.length = w := by simp [X, w, pushGate_length]
    have hy : Y.length = w := by simp [Y, w, pushGate_length]
    have ha := agrees x y hxy
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (pushGate X g).getD i false = (pushGate Y g).getD i false
    simp only [pushGate, snoc_read, hx, hy]
    split_ifs with hlt heq
    · exact ha i (keep i hi (by omega))
    · congr 1
      apply List.map_congr_left
      intro j hj
      exact ha j (pins (heq ▸ hi) j hj)
    · rfl

lemma neighbors_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hMono : Monotone2 C) (hComputes : circuitFun n C = NestedCover.graphFun G ∅) :
    (Finset.univ.filter fun v => ∃ u, G.Adj v u).card ≤ C.size + 1 := by
  classical
  obtain ⟨S, hS, agrees⟩ := support n C.gates {C.output} (fun g hg => (hMono g hg).2)
  let V := Finset.univ.filter fun v => ∃ u, G.Adj v u
  have hsub : V.image Fin.val ⊆ S := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨u, huv⟩ := (Finset.mem_filter.mp hv).2
    by_contra hn
    let x : Fin n → Bool := fun j => decide (j = v ∨ j = u)
    let y : Fin n → Bool := fun j => decide (j = u)
    have hxy : ∀ j : Fin n, j.val ∈ S → x j = y j := by
      intro j hj
      have hjv : j ≠ v := by
        rintro rfl
        exact hn hj
      simp [x, y, hjv]
    have he : circuitFun n C x = circuitFun n C y :=
      agrees x y hxy C.output (Finset.mem_singleton_self _)
    have hx : NestedCover.graphFun G ∅ x = true := by
      simp only [NestedCover.graphFun, Finset.notMem_empty, false_and, exists_false,
        decide_false, Bool.false_or, decide_eq_true_eq]
      exact ⟨v, u, huv, by simp [x], by simp [x]⟩
    have hy : NestedCover.graphFun G ∅ y = false := by
      simp only [NestedCover.graphFun, Finset.notMem_empty, false_and, exists_false,
        decide_false, Bool.false_or, decide_eq_false_iff_not]
      rintro ⟨a, b, hab, ha, hb⟩
      simp only [y, decide_eq_true_eq] at ha hb
      exact G.irrefl (ha ▸ hb ▸ hab)
    rw [hComputes, hx, hy] at he
    contradiction
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective V Fin.val_injective] at hcard
  simpa [V, Circuit.size, Nat.add_comm] using hcard.trans hS

-- A vertex removed at degree at most d can account for at most d lost edges.
lemma peel {α : Type} [DecidableEq α] (d : Nat) (V : Finset α) (E : Finset (Sym2 α))
    (hCover : ∀ e ∈ E, ∀ v ∈ e, v ∈ V) :
    ∃ H ⊆ E, E.card ≤ d * V.card + H.card ∧
      ∀ v : α, (H.filter fun e => v ∈ e).card = 0 ∨ d < (H.filter fun e => v ∈ e).card := by
  classical
  induction V using Finset.strongInductionOn generalizing E
  rename_i V ih
  by_cases ht : ∃ v : α, 0 < (E.filter fun e => v ∈ e).card ∧
        (E.filter fun e => v ∈ e).card ≤ d
  · obtain ⟨v, hv, hd⟩ := ht
    have hvV : v ∈ V := by
      obtain ⟨e, he⟩ := Finset.card_pos.mp hv
      exact hCover e (Finset.mem_filter.mp he).1 v (Finset.mem_filter.mp he).2
    let E' := E.filter fun e => v ∉ e
    have hCover' : ∀ e ∈ E', ∀ i ∈ e, i ∈ V.erase v := by
      intro e he i hi
      obtain ⟨heE, hev⟩ := Finset.mem_filter.mp he
      exact Finset.mem_erase.mpr ⟨fun eq => hev (eq ▸ hi), hCover e heE i hi⟩
    obtain ⟨H, hH, hb, hdeg⟩ := ih (V.erase v) (Finset.erase_ssubset hvV) E' hCover'
    refine ⟨H, hH.trans (Finset.filter_subset _ _), ?_, hdeg⟩
    have hsplit := Finset.card_filter_add_card_filter_not (s := E) (fun e => v ∈ e)
    have hV := Finset.card_erase_add_one hvV
    change (E.filter fun e => v ∈ e).card + E'.card = E.card at hsplit
    calc
      E.card ≤ d + E'.card := by omega
      _ ≤ d + (d * (V.erase v).card + H.card) := Nat.add_le_add_left hb d
      _ = d * V.card + H.card := by rw [← hV, Nat.mul_add, Nat.mul_one]; omega
  · refine ⟨E, Finset.Subset.rfl, Nat.le_add_left _ _, ?_⟩
    intro v
    by_contra hn
    push Not at hn
    exact ht ⟨v, Nat.pos_of_ne_zero hn.1, hn.2⟩

end PEqualNP.Outside.L_meta_4235

open PEqualNP.Outside.L_meta_4235 in
theorem PEqualNP.Outside.L_meta_4235 :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj]
      (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 →
      PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
      ∀ x7 ⊆ x2.edgeFinset, ∀ (x9 : ℕ), ∃ x10 ⊆ x7,
        x7.card ≤ x9 * (x4.size + (1 : ℕ)) + x10.card ∧
        ∀ (x11 : Fin x1), {x12 ∈ x10 | x11 ∈ x12}.card = (0 : ℕ) ∨
          x9 < {x12 ∈ x10 | x11 ∈ x12}.card := by
  intro n G dec C hMono hComputes E hE d
  classical
  let V := Finset.univ.filter fun v => ∃ u, G.Adj v u
  have hCover : ∀ e ∈ E, ∀ v ∈ e, v ∈ V := by
    intro e he v hv
    have hg := G.mem_edgeFinset.mp (hE he)
    rw [← Sym2.other_spec hv, SimpleGraph.mem_edgeSet] at hg
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Sym2.Mem.other hv, hg⟩
  obtain ⟨H, hH, hprice, hdegree⟩ := peel d V E hCover
  have hV : V.card ≤ C.size + 1 := neighbors_bound G C hMono hComputes
  exact ⟨H, hH, hprice.trans (Nat.add_le_add_right (Nat.mul_le_mul_left d hV) _), hdegree⟩
