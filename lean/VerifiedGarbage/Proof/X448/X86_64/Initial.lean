import VerifiedGarbage.Proof.X448.X86_64.Env

/-!
# X448 on x86-64: initial field values

Untrusted: everything here is checked by Lean. Every slot starts with
bounded limbs. The decoded coordinates are retained, and the ladder starts
with X2 = 1, Z2 = 0, Z3 = 1, and a zero swap bit.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

def zeroSlots : List Instr :=
  [.mov32 .rax (.imm 0)] ++ (List.range 32).map (fun i => .store (sc (X2 + 8 * i)) .rax) ++
    (List.range 288).map (fun i => .store (sc (Z3 + 8 * i)) .rax)

theorem zeroSlots_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block zeroSlots) s fun t =>
      (∀ i : Index, ∀ j < 16, limbs t.mem base (slot i.val) j =
        if i = 0 ∨ i = 3 then limbs s.mem base (slot i.val) j else 0) ∧
      t.gpr .rax = 0 ∧ Outside base X2 2688 s.mem t.mem ∧ Keeps [.rax] s t := by
  rw [zeroSlots, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zeroRax_ok s) fun t ⟨tz, tm, tk⟩ => ?_
  have ts := hs.of_keeps tk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fill_ok ts (by decide : X2 + 8 * 32 ≤ 8192) tz) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (fill_ok (ts.of_keeps uk (by decide)) (by decide : Z3 + 8 * 288 ≤ 8192)
    ((uk.1 _ (by decide)).trans tz)) fun v ⟨vf, vm, vk⟩ => ?_
  refine ⟨?_, (vk.1 _ (by decide)).trans ((uk.1 _ (by decide)).trans tz), ?_, ?_⟩
  · intro i j hj
    have il := i.isLt
    by_cases h0 : i = 0
    · subst i
      rw [ite_eq_left (Or.inl rfl)]
      change (word v.mem base (64 + 8 * j)).toNat = _
      rw [vm.word (by change 64 + 8 * j + 8 ≤ 576 ∨ _; omega) (by omega),
        um.word (by change 64 + 8 * j + 8 ≤ 192 ∨ _; omega) (by omega), tm]
      rfl
    · by_cases h3 : i = 3
      · subst i
        rw [ite_eq_left (Or.inr rfl)]
        change (word v.mem base (448 + 8 * j)).toNat = _
        rw [vm.word (by change 448 + 8 * j + 8 ≤ 576 ∨ _; omega) (by omega),
          um.word (by change _ ∨ 192 + 8 * 32 ≤ 448 + 8 * j; omega) (by omega), tm]
        rfl
      · rw [ite_eq_right (not_or_intro h0 h3)]
        have i0 : i.val ≠ 0 := fun h => h0 (Fin.ext h)
        have i3 : i.val ≠ 3 := fun h => h3 (Fin.ext h)
        rcases Nat.lt_or_ge i.val 3 with h | h
        · have index : slot i.val + 8 * j = X2 + 8 * (16 * (i.val - 1) + j) := by
            simp only [slot, X2]; omega
          change (word v.mem base (slot i.val + 8 * j)).toNat = 0
          rw [vm.word (Or.inl (by simp only [slot, Z3]; omega)) (by simp only [slot]; omega), index]
          exact uf _ (by omega)
        · have index : slot i.val + 8 * j = Z3 + 8 * (16 * (i.val - 4) + j) := by
            simp only [slot, Z3]; omega
          change (word v.mem base (slot i.val + 8 * j)).toNat = 0
          rw [index]
          exact vf _ (by omega)
  · rw [← tm]
    exact (um.mono (by omega) (by omega)).trans (vm.mono (by decide) (by decide))
  · exact tk.trans ((uk.trans vk).mono (fun _ hr => False.elim (List.not_mem_nil hr)))

def initialMem (m : Mem) (base : Addr) : Mem :=
  ((m.writeW (off base SWAP) (0 : BitVec 64)).writeW (off base X2) (1 : BitVec 64)).writeW
    (off base Z3) (1 : BitVec 64)

theorem initialStores_ok {s : State} {base : Addr} (hs : Scr s base) (hz : s.gpr .rax = 0) :
    WP isa (.block [.store (sc SWAP) .rax, .mov32 .rax (.imm 1), .store (sc X2) .rax, .store (sc Z3) .rax]) s
      fun t => t.mem = initialMem s.mem base ∧ Keeps [.rax] s t := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 := fun _ hd => hs.write hd
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, State.store64,
    ea_sc, RegUpd.gpr_setReg, RegUpd.wr_setReg, hs.rdi, hz,
    w SWAP (by decide), w X2 (by decide), w Z3 (by decide),
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem initialMem_limb (m : Mem) (base : Addr) (i : Index) {j : Nat} (hj : j < 16) :
    limbs (initialMem m base) base (slot i.val) j =
      if (i = 1 ∨ i = 4) ∧ j = 0 then 1 else limbs m base (slot i.val) j := by
  have il := i.isLt
  have hd : slot i.val + 8 * j + 8 ≤ 8192 := by simp only [slot]; omega
  have hm : (slot i.val + 8 * j) % 8 = 0 := by simp only [slot]; omega
  have es : slot i.val + 8 * j ≠ SWAP := by simp only [slot, SWAP]; omega
  have ex : slot i.val + 8 * j = X2 ↔ i = 1 ∧ j = 0 := by
    simp only [slot, X2]
    constructor
    · intro h; exact ⟨Fin.ext (by omega), by omega⟩
    · rintro ⟨rfl, rfl⟩; rfl
  have ez : slot i.val + 8 * j = Z3 ↔ i = 4 ∧ j = 0 := by
    simp only [slot, Z3]
    constructor
    · intro h; exact ⟨Fin.ext (by omega), by omega⟩
    · rintro ⟨rfl, rfl⟩; rfl
  simp only [limbs, initialMem]
  rw [word_write_aligned _ base (by decide) hd (by decide) hm,
    word_write_aligned _ base (by decide) hd (by decide) hm,
    word_write_aligned _ base (by decide) hd (by decide) hm, ite_eq_right es]
  simp only [ex, ez]
  by_cases h1 : i = 1 <;> by_cases h4 : i = 4 <;> by_cases h0 : j = 0 <;>
    simp only [h1, h4, h0, and_true, and_false, or_true, or_false,
      true_or, ite_true, ite_false] <;> rfl

theorem initialMem_outside (m : Mem) (base : Addr) : Outside base 16 2864 m (initialMem m base) := by
  intro p hp
  simp only [initialMem]
  rw [writeW_outside _ _ _ (by decide : Z3 + 8 ≤ 8192) p (by simp only [Z3, slot]; omega),
    writeW_outside _ _ _ (by decide : X2 + 8 ≤ 8192) p (by simp only [X2, slot]; omega),
    writeW_outside _ _ _ (by decide : SWAP + 8 ≤ 8192) p (by simp only [SWAP]; omega)]

theorem initSlots_ok {s : State} {base : Addr} (hs : Scr s base)
    (h0 : Bounded s.mem base X1) (h3 : Bounded s.mem base X3) :
    WP isa (.block initSlots) s fun t =>
      BoundedEnv t.mem base ∧ E t.mem base 0 = E s.mem base 0 ∧ E t.mem base 1 = 1 ∧
      E t.mem base 2 = 0 ∧ E t.mem base 3 = E s.mem base 3 ∧ E t.mem base 4 = 1 ∧
      word t.mem base SWAP = 0 ∧ Outside base 16 2864 s.mem t.mem ∧ Keeps [.rax] s t := by
  change WP isa (.block (zeroSlots ++ [.store (sc SWAP) .rax, .mov32 .rax (.imm 1),
    .store (sc X2) .rax, .store (sc Z3) .rax])) s _
  rw [WP.block_append_iff]
  refine WP.mono (zeroSlots_ok hs) fun t ⟨tf, tz, tm, tk⟩ => ?_
  refine WP.mono (initialStores_ok (hs.of_keeps tk (by decide)) tz) fun u ⟨um, uk⟩ => ?_
  have lf : ∀ i : Index, ∀ j < 16, limbs u.mem base (slot i.val) j =
      if (i = 1 ∨ i = 4) ∧ j = 0 then 1 else
        if i = 0 ∨ i = 3 then limbs s.mem base (slot i.val) j else 0 := by
    intro i j hj
    rw [um, initialMem_limb _ _ i hj, tf i j hj]
  have zval : valN (fun _ => 0) 16 = 0 := by decide
  have oval : valN (fun j => if j = 0 then 1 else 0) 16 = 1 := by decide +kernel
  have l0 : ∀ j < 16, limbs u.mem base X1 j = limbs s.mem base X1 j := by
    intro j hj
    have h := lf (⟨0, by decide⟩ : Index) j hj
    dsimp only [X1]
    simpa (config := {decide := true}) only [false_or, false_and, ite_true, ite_false] using h
  have l1 : ∀ j < 16, limbs u.mem base X2 j = if j = 0 then 1 else 0 := by
    intro j hj
    have h := lf (⟨1, by decide⟩ : Index) j hj
    dsimp only [X2]
    simpa (config := {decide := true}) only [true_or, true_and, ite_false] using h
  have l2 : ∀ j < 16, limbs u.mem base Z2 j = 0 := by
    intro j hj
    have h := lf (⟨2, by decide⟩ : Index) j hj
    dsimp only [Z2]
    simpa (config := {decide := true}) only [false_or, false_and, ite_false] using h
  have l3 : ∀ j < 16, limbs u.mem base X3 j = limbs s.mem base X3 j := by
    intro j hj
    have h := lf (⟨3, by decide⟩ : Index) j hj
    dsimp only [X3]
    simpa (config := {decide := true}) only [false_or, false_and, ite_true, ite_false] using h
  have l4 : ∀ j < 16, limbs u.mem base Z3 j = if j = 0 then 1 else 0 := by
    intro j hj
    have h := lf (⟨4, by decide⟩ : Index) j hj
    dsimp only [Z3]
    simpa (config := {decide := true}) only [or_true, true_and, ite_false] using h
  refine ⟨?_, congrArg toFe (valN_congr l0), ?_, ?_, congrArg toFe (valN_congr l3), ?_, ?_, ?_, tk.trans uk⟩
  · intro i j hj
    rw [lf i j hj]
    split
    · decide
    · split
      · rename_i h
        rcases h with rfl | rfl
        · exact h0 j hj
        · exact h3 j hj
      · decide
  · change toFe (fe u.mem base X2) = 1
    rw [show fe u.mem base X2 = valN (fun j => if j = 0 then 1 else 0) 16 from valN_congr l1, oval]
    exact toFe_one
  · change toFe (fe u.mem base Z2) = 0
    rw [show fe u.mem base Z2 = valN (fun _ => 0) 16 from valN_congr l2, zval]
    exact toFe_zero
  · change toFe (fe u.mem base Z3) = 1
    rw [show fe u.mem base Z3 = valN (fun j => if j = 0 then 1 else 0) 16 from valN_congr l4, oval]
    exact toFe_one
  · rw [um, initialMem,
      word_write_aligned _ base (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide),
      word_write_aligned _ base (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  · rw [um]
    exact (tm.mono (by decide) (by decide)).trans (initialMem_outside _ _)

end VG.Proof.X448.X86_64
