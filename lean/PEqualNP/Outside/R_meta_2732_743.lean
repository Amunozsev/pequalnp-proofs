import PEqualNP.Defs

set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.R_meta_2732_743
    (hSearch : have x2 : (Fin (14 : ℕ) → Bool) → Bool := fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (14 * (↑x3 : ℕ) + ↑x4) ∈ [7, 8, 10, 21, 23, 27, 36, 40, 41, 49, 53, 54, 66, 67, 69, 79, 80, 82, 92, 93, 95] ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true);

        have x3 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x3 x4 x5 x6 : ℕ) => ((15 : ℕ) * Min.min x3 x4 + Max.max x3 x4) * (225 : ℕ) + ((15 : ℕ) * Min.min x5 x6 + Max.max x5 x6);

        have x4 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x4 : Equiv.Perm (Fin (14 : ℕ))) (x5 : Fin (15 : ℕ)) => if ↑x5 < (14 : ℕ) then ↑(x4 (Fin.ofNat (14 : ℕ) ↑x5)) else (14 : ℕ);

        ∃ (x5 : Fin (14 : ℕ)) (x6 : Fin (14 : ℕ)) (x7 : Fin (15 : ℕ)) (x8 : Fin (15 : ℕ)) (x9 : PEqualNP.CircuitLowerBounds.GateOp) (x10 : PEqualNP.CircuitLowerBounds.GateOp) (x11 : PEqualNP.CircuitLowerBounds.Circuit),
        x5 < x6 ∧
        x7 < x8 ∧
        (x9 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x9 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        (x10 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x10 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        (∀ (x12 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x13 : Fin (14 : ℕ) → Bool), x2 (x13 ∘ ⇑x12) = x2 x13) → x3 ↑x5 ↑x6 ↑x7 ↑x8 ≤ x3 (↑(x12 x5)) (↑(x12 x6)) (x4 x12 x7) (x4 x12 x8)) ∧
        PEqualNP.MetaComplexity.Monotone2 x11 ∧
        x11.size ≤ (24 : ℕ) ∧
        ∀ (x12 : Fin (14 : ℕ) → Bool),

        ((x2 x12 = true ∧ ∀ y : Fin 14 → Bool, y < x12 → x2 y = false) ∨

        (x2 x12 = false ∧ ∀ y : Fin 14 → Bool, x12 < y → x2 y = true)) →
        have x13 : List Bool := List.ofFn x12 ++ [x9.eval [x12 x5, x12 x6]];
        x11.eval (x13 ++ [x10.eval [x13.getD (↑x7) Bool.false, x13.getD (↑x8) Bool.false]]) = x2 x12)
    (hMono : ∀ (a b : Fin 14) (c d : Fin 15)
    (u v : PEqualNP.CircuitLowerBounds.GateOp) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (u = PEqualNP.CircuitLowerBounds.GateOp.and ∨ u = PEqualNP.CircuitLowerBounds.GateOp.or) →
  (v = PEqualNP.CircuitLowerBounds.GateOp.and ∨ v = PEqualNP.CircuitLowerBounds.GateOp.or) →
  PEqualNP.MetaComplexity.Monotone2 C →
  Monotone (fun x : Fin 14 → Bool =>
    let w := List.ofFn x ++ [u.eval [x a, x b]]
    C.eval (w ++ [v.eval [w.getD c.val false, w.getD d.val false]]))) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)),
        ((0 : ℕ), (8 : ℕ)),
        ((0 : ℕ), (10 : ℕ)),
        ((1 : ℕ), (7 : ℕ)),
        ((1 : ℕ), (9 : ℕ)),
        ((1 : ℕ), (13 : ℕ)),
        ((2 : ℕ), (8 : ℕ)),
        ((2 : ℕ), (12 : ℕ)),
        ((2 : ℕ), (13 : ℕ)),
        ((3 : ℕ), (7 : ℕ)),
        ((3 : ℕ), (11 : ℕ)),
        ((3 : ℕ), (12 : ℕ)),
        ((4 : ℕ), (10 : ℕ)),
        ((4 : ℕ), (11 : ℕ)),
        ((4 : ℕ), (13 : ℕ)),
        ((5 : ℕ), (9 : ℕ)),
        ((5 : ℕ), (10 : ℕ)),
        ((5 : ℕ), (12 : ℕ)),
        ((6 : ℕ), (8 : ℕ)),
        ((6 : ℕ), (9 : ℕ)),
        ((6 : ℕ), (11 : ℕ))];

        have x2 : (Fin (14 : ℕ) → Bool) → Bool := fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true);

        have x3 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x3 x4 x5 x6 : ℕ) => ((15 : ℕ) * Min.min x3 x4 + Max.max x3 x4) * (225 : ℕ) + ((15 : ℕ) * Min.min x5 x6 + Max.max x5 x6);

        have x4 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x4 : Equiv.Perm (Fin (14 : ℕ))) (x5 : Fin (15 : ℕ)) => if ↑x5 < (14 : ℕ) then ↑(x4 (Fin.ofNat (14 : ℕ) ↑x5)) else (14 : ℕ);

        ∃ (x5 : Fin (14 : ℕ)) (x6 : Fin (14 : ℕ)) (x7 : Fin (15 : ℕ)) (x8 : Fin (15 : ℕ)) (x9 : PEqualNP.CircuitLowerBounds.GateOp) (x10 : PEqualNP.CircuitLowerBounds.GateOp) (x11 : PEqualNP.CircuitLowerBounds.Circuit),
        x5 < x6 ∧
        x7 < x8 ∧
        (x9 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x9 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        (x10 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x10 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        (∀ (x12 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x13 : Fin (14 : ℕ) → Bool), x2 (x13 ∘ ⇑x12) = x2 x13) → x3 ↑x5 ↑x6 ↑x7 ↑x8 ≤ x3 (↑(x12 x5)) (↑(x12 x6)) (x4 x12 x7) (x4 x12 x8)) ∧
        PEqualNP.MetaComplexity.Monotone2 x11 ∧
        x11.size ≤ (24 : ℕ) ∧
        ∀ (x12 : Fin (14 : ℕ) → Bool),
        have x13 : List Bool := List.ofFn x12 ++ [x9.eval [x12 x5, x12 x6]];
        x11.eval (x13 ++ [x10.eval [x13.getD (↑x7) Bool.false, x13.getD (↑x8) Bool.false]]) = x2 x12 := by
  classical
  have hedge : ∀ i j : Fin 14, (i.val, j.val) ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))] ↔
      14 * i.val + j.val ∈ [7, 8, 10, 21, 23, 27, 36, 40, 41, 49, 53, 54, 66, 67, 69, 79, 80, 82, 92, 93, 95] := by decide
  let f : (Fin 14 → Bool) → Bool := fun x =>
    decide (∃ i j : Fin 14, (i.val, j.val) ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x i = true ∧ x j = true)
  let f' : (Fin 14 → Bool) → Bool := fun x =>
    decide (∃ i j : Fin 14, 14 * i.val + j.val ∈ [7, 8, 10, 21, 23, 27, 36, 40, 41, 49, 53, 54, 66, 67, 69, 79, 80, 82, 92, 93, 95] ∧
      x i = true ∧ x j = true)
  have heq : f' = f := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [f', f, decide_eq_true_eq, hedge]
  obtain ⟨a, b, c, d, u, v, C, hab, hcd, hu, hv, hcanon, hC, hsize, hborder⟩ := hSearch
  let g : (Fin 14 → Bool) → Bool := fun x =>
    let w := List.ofFn x ++ [u.eval [x a, x b]]
    C.eval (w ++ [v.eval [w.getD c.val false, w.getD d.val false]])
  refine ⟨a, b, c, d, u, v, C, hab, hcd, hu, hv, ?_, hC, hsize, ?_⟩
  · intro p hp
    apply hcanon p
    intro x
    change f' (x ∘ ⇑p) = f' x
    rw [heq]
    exact hp x
  have hg : Monotone g := hMono a b c d u v C hu hv hC
  have hboundary : ∀ x,
      ((f' x = true ∧ ∀ y, y < x → f' y = false) ∨
       (f' x = false ∧ ∀ y, x < y → f' y = true)) → g x = f' x := hborder
  rw [heq] at hboundary
  intro x
  change g x = f x
  cases hx : f x with
  | true =>
    obtain ⟨y, hyx, hy⟩ := exists_minimal_le_of_wellFoundedLT (fun y => f y = true) x hx
    have hytrue : f y = true := hy.prop
    have hby : g y = f y := hboundary y (Or.inl ⟨hytrue, fun z hz => by
      cases h : f z with
      | false => rfl
      | true => exact (hy.not_lt h hz).elim⟩)
    apply Bool.eq_true_of_true_le
    have hle := hg hyx
    rwa [hby, hytrue] at hle
  | false =>
    obtain ⟨y, hyx, hy⟩ := exists_maximal_ge_of_wellFoundedGT (fun y => f y = false) x hx
    have hyfalse : f y = false := hy.prop
    have hby : g y = f y := hboundary y (Or.inr ⟨hyfalse, fun z hz => by
      cases h : f z with
      | false => exact (hy.not_gt h hz).elim
      | true => rfl⟩)
    apply Bool.eq_false_of_le_false
    have hle := hg hyx
    rwa [hby, hyfalse] at hle
