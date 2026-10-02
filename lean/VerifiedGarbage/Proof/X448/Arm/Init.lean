import VerifiedGarbage.Proof.X448.Arm.RowMem

/-!
# X448 on ARMv7: initialize multiplication

The first 28 accumulator words are zero; subsequent rows initialize the
remaining words.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X25519.Arm

variable {b : BitVec 32}

theorem rowStore_ok {s : State} (hc : RowCtx b s) {t : Reg} {d : Nat}
    (hd : d + 4 ≤ 4096) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Mupd s s' (s.mem.writeW (State.addr b + BitVec.ofNat 64 d) (s.gpr t)) →
      WP isa (.block is) s' Q) : WP isa (.block (st t d :: is)) s Q :=
  wp_str (by omega) (hc.ea (by omega)) (hc.inW hd) k

theorem zeroAcc_ok {s : State} (hc : RowCtx b s) :
    WP isa (.block zeroAcc) s fun s' => (∀ j < 28, accw s'.mem (State.addr b) j = 0) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 112⟩] s.mem s'.mem ∧ Rest [.r3] s s' := by
  have hA := ACC_eq
  unfold zeroAcc
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  have hc1 := hc.of_rest (u1.rest (ws := [.r3]) (by decide)) (by decide)
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ j < n, accw s'.mem (State.addr b) j = 0) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 112⟩] s1.mem s'.mem ∧ Rest [] s1 s' ∧ s'.gpr .r3 = 0)
    (fun n s' hn ⟨h1, h2, h3, h4⟩ => ?_) 28 (Nat.le_refl _) s1
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, Rest.refl _ _, u1.gpr⟩)
    fun s' ⟨h1, h2, h3, _⟩ => ⟨h1, by rw [← u1.mem]; exact h2,
      (u1.rest (by decide)).trans (h3.mono (by decide))⟩
  refine rowStore_ok (hc1.of_rest h3 (by decide)) (d := ACC + 4 * n) (by omega) fun s2 u2 =>
    WP.block_nil ⟨fun j hj => ?_, ?_, h3.trans (u2.rest _), by rw [u2.gpr, h4]⟩
  · rw [accw, u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h1 j hj
    · rw [wd_write_self, h4]; rfl
  · rw [u2.mem]
    exact h2.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

theorem mulPre_ok {x y : Nat} {s : State} (hc : RowCtx b s) (h6 : s.gpr .r6 = mask16) :
    WP isa (.block mulPre) s (RowInv b x y s 0) := by
  unfold mulPre
  refine WP.append (zeroAcc_ok hc) fun s1 ⟨hz, hf, hr⟩ => ?_
  have hc1 := hc.of_rest hr (by decide)
  refine wp_mov (op2_reg _ _) fun s2 h2 => wp_mov (op2_imm (by decide)) fun s3 h3 => WP.block_nil ?_
  have hr3 : Rest clob s s3 :=
    (hr.mono (by decide)).trans ((h2.rest (by decide)).trans (h3.rest (by decide)))
  have hm3 : s3.mem = s1.mem := by rw [h3.mem, h2.mem]
  refine ⟨hc.of_rest hr3 (by decide), hr3, (hr3.gpr _ (by decide)).trans h6,
    ?_, h3.gpr, ?_, fun k hk => ?_, ?_⟩
  · rw [h3.other .r7 (by decide), h2.gpr, hc1.r0]
    exact (BitVec.add_zero b).symm
  · rw [hm3]
    exact hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩
  · rw [hm3, hz k hk]; decide
  · rw [hm3, Radix16.valN_congr (g := fun _ => 0) (fun k hk => hz k hk), Radix16.valN_zero]
    exact (Nat.zero_mul _).symm

end VG.Proof.X448.Arm
