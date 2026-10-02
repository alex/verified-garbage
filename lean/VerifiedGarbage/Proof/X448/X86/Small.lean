import VerifiedGarbage.Proof.X448.X86.Columns

/-!
# X448 on x86 (32-bit): multiplication by a24

The 16-bit limbs keep multiplication by 39081 within a 32-bit word.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem smallStep_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat}
    (ha : Slot a) (hi : i < 28) (hc : (s.gpr .ecx).toNat = 39081) :
    WP isa (.block [ld .eax (a + 4 * i), .mul .ecx, st .eax (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * i)) (BitVec.ofNat 32 (39081 * limbs s.mem base a i)) ∧
      Keeps [.eax, .edx] s t := by
  have ha' : a + 112 ≤ 3584 := ha
  refine load_ok hs (by omega) fun t ht => ?_
  have ts := hs.of_upd ht (by decide)
  refine wp_mul fun u uv um uk => ?_
  refine store_ok (ts.of_keeps uk (by decide)) (by simp only [TMP]; omega) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, um, ht.mem, uv, ht.gpr, ht.other .ecx (by decide), hc, Nat.mul_comm _ 39081]
  · exact (ht.rest (by decide)).trans (uk.trans (hv.rest _))

theorem smallInit_ok (s : State) :
    WP isa (.block [.mov .ecx (.imm 39081)]) s fun t =>
      (t.gpr .ecx).toNat = 39081 ∧ t.mem = s.mem ∧ Keeps [.ecx] s t := by
  refine wp_mov rfl fun t ht => WP.block_nil ⟨?_, ht.mem, ht.rest (by decide)⟩
  rw [ht.gpr]
  rfl


theorem mulSmall_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Slot o) (ha : Slot a) (ab : Bounded s.mem base a) :
    WP isa (.block (mulSmall o a)) s fun t => Op base o s t ∧ Bounded t.mem base o ∧
      F t.mem base o = Spec.X448.a24 * F s.mem base a := by
  let f := fun i => 39081 * limbs s.mem base a i
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - radix := by
    intro i hi
    have h := Nat.mul_le_mul_left 39081 (Nat.le_of_lt (ab i hi))
    have hr : 39081 * radix ≤ 2 ^ 32 - radix := by decide
    exact Nat.le_trans h hr
  refine WP.mono (columns_normalize hs ho fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_a24 ?_⟩
  · rw [WP.block_append_iff]
    refine WP.mono (smallInit_ok s) fun t ⟨tc, tm, tk⟩ => ?_
    have ts := hs.of_keeps tk (by decide)
    refine WP.mono (columns_ok ts (by decide : Reg.edi ∉ [Reg.eax, Reg.edx]) fb ?_) fun u ⟨uf, um, uk⟩ => ?_
    · intro i hi u us um uk
      have uc : (u.gpr .ecx).toNat = 39081 := by rw [uk.1 _ (by decide), tc]
      refine WP.mono (smallStep_ok us ha hi uc) fun v ⟨vm, vk⟩ => ⟨?_, vk⟩
      rw [input_limb um ha hi, tm] at vm
      exact vm
    · refine ⟨uf, ?_, (tk.mono ?_).trans (uk.mono ?_)⟩
      · rw [← tm]; exact um
      · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> decide
  · rw [tv, valN_scale]

end VG.Proof.X448.X86
