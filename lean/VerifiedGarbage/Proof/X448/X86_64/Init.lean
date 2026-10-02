import VerifiedGarbage.Proof.X448.X86_64.Mem
import VerifiedGarbage.Proof.Framework.Range

/-!
# X448 on x86-64: initializing coefficient arrays

Zeroing a bounded range of words preserves all other memory and the registers.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

theorem store_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192) (r : Reg) :
    WP isa (.block [.store (sc d) r]) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_sc, hs.rdi, State.store64,
    hs.write hd, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun _ _ => rfl, rfl, rfl⟩

theorem zeroRax_ok (s : State) :
    WP isa (.block [.mov32 .rax (.imm 0)]) s fun t =>
      t.gpr .rax = 0 ∧ t.mem = s.mem ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_setReg_of_ne _ _ hr

theorem fill_ok {s : State} {base : Addr} (hs : Scr s base) {o n : Nat} (ho : o + 8 * n ≤ 8192)
    (hz : s.gpr .rax = 0) :
    WP isa (.block ((List.range n).map (fun i => .store (sc (o + 8 * i)) .rax))) s fun t =>
      (∀ i < n, limbs t.mem base o i = 0) ∧ Outside base o (8 * n) s.mem t.mem ∧ Keeps [] s t := by
  let inv := fun k (t : State) =>
    (∀ i < k, limbs t.mem base o i = 0) ∧ Outside base o (8 * n) s.mem t.mem ∧ Keeps [] s t
  have step : ∀ k t, k < n → inv k t →
      WP isa (.block [.store (sc (o + 8 * k)) .rax]) t (inv (k + 1)) := by
    intro k t hk ⟨tf, tm, tk⟩
    have ts := hs.of_keeps tk (by decide)
    refine WP.mono (store_ok ts (by omega) .rax) fun u ⟨um, uk⟩ => ?_
    rw [tk.1 .rax (by decide), hz] at um
    have out : Outside base (o + 8 * k) 8 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (word u.mem base (o + 8 * i)).toNat = _
    rw [um, word_write t.mem base (by omega) (by omega)]
    by_cases h : i = k
    · rw [ite_eq_left h]; rfl
    · rw [ite_eq_right h]; exact tf i (by omega)
  rw [List.map_eq_flatMap]
  exact wp_range_flatMap (M := isa) (N := n) inv step n (by omega) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- The row counter starts at zero and its pointer at the scratch base. -/
theorem counters_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block [.mov32 .r10 (.imm 0), .mov .r11 (.reg .rdi)]) s fun t =>
      t.gpr .r10 = 0 ∧ t.gpr .r11 = base ∧ t.mem = s.mem ∧ Keeps [.r10, .r11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, readSrc, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, hs.rdi,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, trivial, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem mulInit_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (([.mov32 .rax (.imm 0)] : List Instr) ++
      (List.range 32).map (fun i => .store (sc (ACC + 8 * i)) .rax) ++
      ([.mov32 .r10 (.imm 0), .mov .r11 (.reg .rdi)] : List Instr))) s fun t =>
      (∀ i < 32, limbs t.mem base ACC i = 0) ∧ t.gpr .r10 = 0 ∧ t.gpr .r11 = base ∧
      Outside base ACC 256 s.mem t.mem ∧ Keeps [.rax, .r10, .r11] s t := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (zeroRax_ok s) fun t ⟨tz, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (fill_ok (hs.of_keeps tk (by decide)) (by decide : ACC + 8 * 32 ≤ 8192) tz)
    fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (counters_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide)))
    fun v ⟨vc, vr, vm, vk⟩ => ?_
  refine ⟨?_, vc, vr, ?_, ?_⟩
  · intro i hi; rw [vm]; exact uf i hi
  · rw [vm, ← tm]; exact um
  · refine (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_))
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
    · intro r hr; exact False.elim (List.not_mem_nil hr)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide

end VG.Proof.X448.X86_64
