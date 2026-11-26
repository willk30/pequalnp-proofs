import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24517 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2149567 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [8, 9]⟩, ⟨.not, [10]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [11, 12]⟩], 13⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
