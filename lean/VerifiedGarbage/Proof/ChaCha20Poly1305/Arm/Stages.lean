import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.MacPad

/-!
# ChaCha20-Poly1305 on ARMv7: the other parts

Untrusted: everything here is checked by Lean. The encryption, the lengths
block, the arguments of `vg_poly1305_finalize` and the tag, copying and
comparing tags, and restoring the registers.
-/

namespace VG.Proof.ChaCha20Poly1305.Arm

open VG VG.Arm VG.Impl.ChaCha20Poly1305.Arm
open VG.Proof.Sha256.Arm.Stream (Upd Mupd Fupd wp_mov wp_add wp_sub wp_and wp_orr wp_ldr wp_str
  op2_imm op2_reg op2_lsr op2_lsl saveMem restoreList_ok)
open VG.Proof.ChaCha20.Arm.Xor (stateAt_writeW_counter wp_eor)
open VG.Proof.ChaCha20.Arm (toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream)

/-! ## Encrypting -/

theorem set12_initState (key nonce : List Byte) :
    (Spec.ChaCha20.initState key 0 nonce).set 12 1 = Spec.ChaCha20.initState key 1 nonce := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_set, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  by_cases h : 12 = i
  · subst h; simp
  · simp only [h, ite_false, show ¬ i = 12 from fun h' => h h'.symm]

theorem cryptA_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block [.mov .r12 (.imm 1), .str .r12 .r7 (stOff + 48),
      .dp .add .r0 .r7 (.imm (BitVec.ofNat 32 stOff)), .mov .r1 (.reg .r10), .mov .r2 (.reg .r11),
      .mov .r3 (.reg .r7)]) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) (stOff + 48)) (1 : BitVec 32) ∧ s'.gpr .r0 = ptr s₀ stOff ∧
      s'.gpr .r1 = dP s₀ ∧ s'.gpr .r2 = stackArg s₀ 0 ∧ s'.gpr .r3 = cP s₀ ∧
      Kept [sub s₀ stOff 64] s s' := by
  have o := hp.in_ctx (a := stOff + 48) (w := 4) (by simp [stOff])
  rw [← h.wr] at o
  have core : WP isa (.block [.mov .r12 (.imm 1), .str .r12 .r7 (stOff + 48),
      .dp .add .r0 .r7 (.imm (BitVec.ofNat 32 stOff)), .mov .r1 (.reg .r10), .mov .r2 (.reg .r11),
      .mov .r3 (.reg .r7)]) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) (stOff + 48)) (1 : BitVec 32) ∧ s'.gpr .r0 = ptr s₀ stOff ∧
      s'.gpr .r1 = dP s₀ ∧ s'.gpr .r2 = stackArg s₀ 0 ∧ s'.gpr .r3 = cP s₀ ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
    refine wp_str (a := off (cx s₀) (stOff + 48)) (by simp [stOff])
      (by rw [u₁.other _ (by decide), hr7 h]; exact hp.addr_cP_off (by simp [stOff])) (by rw [u₁.wr]; exact o)
      fun s₂ g₂ => ?_
    refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
      wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr,
        u₁.other _ (by decide), hr7 h]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide), h.regs.r10]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide), h.regs.r11]
    · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide), hr7 h]
    · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd]
    · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr]
  refine WP.mono (WP.kept core (by simp [dstOf, preserved]))
    fun s' ⟨⟨hm, h0, h1, h2, h3, hrd, hwr⟩, hg, hsp⟩ => ⟨hm, h0, h1, h2, h3, Kept.of hg hsp hrd hwr ?_⟩
  rw [hm]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (contains_sub s₀ (w := 32 / 8) (by simp [stOff]) (by simp [stOff]) (by simp [stOff]))

theorem hL (s₀ : State) : stackArg s₀ 0 = BitVec.ofNat 32 (L s₀) := by simp [L]

theorem length_encrypt (key nonce m : List Byte) : (Spec.ChaCha20.encrypt key 1 nonce m).length = m.length := by
  rw [encrypt_eq, List.length_zipWith, VG.Proof.ChaCha20.length_keystream, Nat.min_self]

/-- The data encrypted (or decrypted) from block counter 1, with the ChaCha20
state for counter 0 at `ctx + stOff`. -/
theorem crypt_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)) :
    WP isa crypt s fun s' => Inv s₀ s' ∧ Kept [sub s₀ 0 (stOff + 64), dR s₀] s s' ∧
      bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  unfold crypt
  refine WP.seq (WP.mono (cryptA_ok hp h) fun s₁ ⟨m₁, h0, h1, h2, h3, k₁⟩ => ?_)
  have i₁ := h.step1 k₁ (by simp [stOff]) (by simp [stOff, savOff])
  have hw : Covers [⟨State.addr (ptr s₀ stOff), 64⟩, ⟨State.addr (dP s₀), L s₀⟩, ⟨State.addr (cP s₀), 320⟩]
      s₁.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by simp [i₁.wr, hp.wr], stOff, by rw [hp.addr_ptr (by simp [stOff])], by simp [stOff]⟩
    · exact ⟨dR s₀, by simp [i₁.wr, hp.wr], 0, by simp, by simp⟩
    · exact ⟨ctxR s₀, by simp [i₁.wr, hp.wr], 0, by simp, by simp⟩
  refine WP.seq (xor_call h0 h1 (by rw [h2]; exact hL s₀) h3 (stackArg s₀ 0).isLt
    (by rw [hp.addr_ptr (by simp [stOff])]; exact hp.c_d.sub_left (sub_ctx s₀ (by simp [stOff])))
    (by rw [hp.addr_ptr (by simp [stOff]), ← sub_zero]
        exact sub_disj s₀ (a := stOff) (n := 64) (b := 0) (m := 320) (by simp [stOff]) (by simp [stOff])
          (by omega))
    (by rw [← sub_zero]; exact (hp.c_d.symm.sub_right (sub_ctx s₀ (by omega))))
    (by rw [hp.ptr_toNat (by simp [stOff])]; have := hp.fit_c; simp [stOff]; omega)
    hp.fit_d (by have := hp.fit_c; omega)
    (by simpa using covers_left _ hw) hw fun s₂ k₂ r1₂ data₂ => ?_)
  have hsub : ∀ r ∈ [⟨State.addr (ptr s₀ stOff), 64⟩, ⟨State.addr (dP s₀), L s₀⟩, ⟨State.addr (cP s₀), 320⟩],
      ∃ r' ∈ [sub s₀ 0 (stOff + 64), dR s₀], Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨sub s₀ 0 (stOff + 64), by simp, ?_⟩
      rw [hp.addr_ptr (by simp [stOff])]; exact sub_sub s₀ (by omega) (by simp [stOff]) (by simp [stOff])
    · exact ⟨dR s₀, by simp, fun _ h => h⟩
    · refine ⟨sub s₀ 0 (stOff + 64), by simp, ?_⟩
      rw [← sub_zero]; exact sub_sub s₀ le_rfl (by simp [stOff]) (by simp [stOff])
  have k₁₂ : Kept [sub s₀ 0 (stOff + 64), dR s₀] s s₂ :=
    (k₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 0 (stOff + 64), by simp, sub_sub s₀ (by omega) (by simp [stOff]) (by simp [stOff])⟩).trans
    (k₂.sub hsub)
  have i₂ := h.step k₁₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_inv s₀ (by simp [stOff])
      · exact ⟨dR s₀, by simp, fun _ h => h⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by simp [stOff, savOff]) (by simp [savOff]) (by simp [stOff])
      · exact hp.c_d.sub_left (sub_ctx s₀ (by simp [savOff])))
  refine WP.mono (anchor_ok i₂ r1₂) fun s₃ ⟨i₃, k₃⟩ => ⟨i₃, k₁₂.trans (k₃.sub fun _ hr => absurd hr List.not_mem_nil), ?_⟩
  have d₁ : bytesAt s₁.mem (dp s₀) (L s₀) = bytesAt s.mem (dp s₀) (L s₀) :=
    bytesAt_frame k₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.c_d.sub_left (sub_ctx s₀ (by simp [stOff]))).symm)
      (by simp only [L]; have := (stackArg s₀ 0).isLt; omega)
  have st₁ : stateAt s₁.mem (State.addr (ptr s₀ stOff)) = Spec.ChaCha20.initState (K s₀) 1 (N s₀) := by
    rw [m₁, hp.addr_ptr (by simp [stOff]), show off (cx s₀) (stOff + 48) = off (cx s₀) stOff + BitVec.ofNat 64 48 from
      (off_off _ _ _).symm, stateAt_writeW_counter, hst, show (1 : BitVec 32) = 1 from rfl, set12_initState]
  rw [k₃.mem_eq, show Spec.ChaCha20.bytesAt = bytesAt from rfl] at *
  rw [data₂, st₁, d₁, encrypt_eq, VG.Proof.Poly1305.length_bytesAt]

/-! ## The lengths block -/

theorem bytesAt_leBytes_32 (m : Mem) (p : Addr) : bytesAt m p 4 = leBytes 4 (m.readW p 32).toNat := by
  rw [VG.Proof.Poly1305.bytesAt_leBytes]; simp [Mem.readW]

/-- A 32-bit length, zero-extended to 64 bits. -/
theorem bytesAt_len {m : Mem} {p : Addr} {x : Nat} (hx : x < 2 ^ 32) (h0 : (m.readW p 32).toNat = x)
    (h1 : m.readW (p + BitVec.ofNat 64 4) 32 = 0) : bytesAt m p 8 = leBytes 8 x := by
  rw [show 8 = 4 + 4 from rfl, VG.Proof.Poly1305.bytesAt_add, bytesAt_leBytes_32, bytesAt_leBytes_32, h0, h1,
    VG.Proof.Poly1305.leBytes_add, Nat.div_eq_of_lt (by norm_num; omega)]
  rfl

theorem lengthsA_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block [.str .r9 .r7 lenOff, .mov .r12 (.imm 0), .str .r12 .r7 (lenOff + 4),
      .str .r11 .r7 (lenOff + 8), .str .r12 .r7 (lenOff + 12),
      .dp .add .r1 .r7 (.imm (BitVec.ofNat 32 lenOff)), .mov .r2 (.imm 1)]) s fun s' =>
      s'.gpr .r1 = ptr s₀ lenOff ∧ s'.gpr .r2 = BitVec.ofNat 32 1 ∧ Kept [sub s₀ lenOff 16] s s' ∧
      bytesAt s'.mem (off (cx s₀) lenOff) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
  have o : ∀ d, d < 4 → InRegions s.wr (off (cx s₀) (lenOff + 4 * d)) 4 := fun d hd => by
    rw [h.wr]; exact hp.in_ctx (by simp [lenOff]; omega)
  have ea : ∀ d, d < 4 → State.addr (cP s₀ + BitVec.ofNat 32 (lenOff + 4 * d)) = off (cx s₀) (lenOff + 4 * d) :=
    fun d hd => hp.addr_cP_off (by simp [lenOff]; omega)
  have core : WP isa (.block [.str .r9 .r7 lenOff, .mov .r12 (.imm 0), .str .r12 .r7 (lenOff + 4),
      .str .r11 .r7 (lenOff + 8), .str .r12 .r7 (lenOff + 12),
      .dp .add .r1 .r7 (.imm (BitVec.ofNat 32 lenOff)), .mov .r2 (.imm 1)]) s fun s' =>
      s'.gpr .r1 = ptr s₀ lenOff ∧ s'.gpr .r2 = BitVec.ofNat 32 1 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = (((s.mem.writeW (off (cx s₀) (lenOff + 4 * 0)) (s₀.gpr .r2)).writeW (off (cx s₀) (lenOff + 4 * 1))
        (0 : BitVec 32)).writeW (off (cx s₀) (lenOff + 4 * 2)) (stackArg s₀ 0)).writeW
        (off (cx s₀) (lenOff + 4 * 3)) (0 : BitVec 32) := by
    refine wp_str (a := off (cx s₀) (lenOff + 4 * 0)) (by simp [lenOff]) (by rw [hr7 h]; exact ea 0 (by omega))
      (o 0 (by omega)) fun s₁ g₁ => ?_
    refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
    have h7 : s₂.gpr .r7 = cP s₀ := by rw [u₂.other _ (by decide), g₁.gpr, hr7 h]
    refine wp_str (a := off (cx s₀) (lenOff + 4 * 1)) (by simp [lenOff]) (by rw [h7]; exact ea 1 (by omega))
      (by rw [u₂.wr, g₁.wr]; exact o 1 (by omega)) fun s₃ g₃ => ?_
    refine wp_str (a := off (cx s₀) (lenOff + 4 * 2)) (by simp [lenOff]) (by rw [g₃.gpr, h7]; exact ea 2 (by omega))
      (by rw [g₃.wr, u₂.wr, g₁.wr]; exact o 2 (by omega)) fun s₄ g₄ => ?_
    refine wp_str (a := off (cx s₀) (lenOff + 4 * 3)) (by simp [lenOff])
      (by rw [g₄.gpr, g₃.gpr, h7]; exact ea 3 (by omega))
      (by rw [g₄.wr, g₃.wr, u₂.wr, g₁.wr]; exact o 3 (by omega)) fun s₅ g₅ => ?_
    refine wp_add (op2_imm (by decide)) fun s₆ u₆ => wp_mov (op2_imm (by decide)) fun s₇ u₇ =>
      WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [u₇.other _ (by decide), u₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, h7]
    · rw [u₇.gpr]; rfl
    · rw [u₇.rd, u₆.rd, g₅.rd, g₄.rd, g₃.rd, u₂.rd, g₁.rd]
    · rw [u₇.wr, u₆.wr, g₅.wr, g₄.wr, g₃.wr, u₂.wr, g₁.wr]
    · have x12 : s₂.gpr .r12 = 0 := u₂.gpr
      rw [u₇.mem, u₆.mem, g₅.mem, g₄.mem, g₃.mem, u₂.mem, g₁.mem, g₄.gpr, g₃.gpr, x12, u₂.other _ (by decide),
        g₁.gpr, h.regs.r11, h.regs.r9]
  refine WP.mono (WP.kept core (by simp [dstOf, preserved]))
    fun s' ⟨⟨h1, h2, hrd, hwr, hm⟩, hg, hsp⟩ => ⟨h1, h2, Kept.of hg hsp hrd hwr ?_, ?_⟩
  · rw [hm]
    have c : ∀ d, d < 4 → (sub s₀ lenOff 16).Contains (off (cx s₀) (lenOff + 4 * d)) (32 / 8) :=
      fun d hd => contains_sub s₀ (by omega) (by omega) (by simp [lenOff])
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by omega))
      |>.writeW (List.mem_singleton_self _) _ (c 1 (by omega))
      |>.writeW (List.mem_singleton_self _) _ (c 2 (by omega))
      |>.writeW (List.mem_singleton_self _) _ (c 3 (by omega))
  · have r : ∀ d, d < 4 → ∀ e, e < 4 → d ≠ e → ∀ (m : Mem) (v : BitVec 32),
        (m.writeW (off (cx s₀) (lenOff + 4 * e)) v).readW (off (cx s₀) (lenOff + 4 * d)) 32 =
          m.readW (off (cx s₀) (lenOff + 4 * d)) 32 :=
      fun d hd e he hde m v => readW_off m _ v (by simp [lenOff]; omega) (by simp [lenOff]; omega) (by omega)
    rw [show (16 : Nat) = 8 + 8 from rfl, VG.Proof.Poly1305.bytesAt_add, hm]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · refine bytesAt_len (s₀.gpr .r2).isLt ?_ ?_
      · rw [show off (cx s₀) lenOff = off (cx s₀) (lenOff + 4 * 0) from rfl,
          r 0 (by omega) 3 (by omega) (by omega), r 0 (by omega) 2 (by omega) (by omega),
          r 0 (by omega) 1 (by omega) (by omega), Mem.readW_writeW_self32]
      · rw [off_add, show lenOff + 4 = lenOff + 4 * 1 from rfl, r 1 (by omega) 3 (by omega) (by omega),
          r 1 (by omega) 2 (by omega) (by omega), Mem.readW_writeW_self32]
    · rw [off_add]
      refine bytesAt_len (stackArg s₀ 0).isLt ?_ ?_
      · rw [show lenOff + 8 = lenOff + 4 * 2 from rfl, r 2 (by omega) 3 (by omega) (by omega),
          Mem.readW_writeW_self32]
      · rw [off_add, show lenOff + 8 + 4 = lenOff + 4 * 3 from rfl, Mem.readW_writeW_self32]

theorem lengths_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa lengths s fun s' => Inv s₀ s' ∧ Kept [sub s₀ 0 128, sub s₀ lenOff 16] s s' ∧
      ∀ key msg, Repr s.mem (cx s₀) key msg →
        Repr s'.mem (cx s₀) key (msg ++ (leBytes 8 (AL s₀) ++ leBytes 8 (L s₀))) := by
  unfold lengths
  refine WP.seq (WP.mono (lengthsA_ok hp h) fun s₁ ⟨h1, h2, k₁, len₁⟩ => ?_)
  have i₁ := h.step1 k₁ (by simp [lenOff]) (by simp [lenOff, savOff])
  refine WP.mono (absorb_ok hp i₁ (n := 1) h1 h2 (by omega)
    (by rw [hp.addr_ptr (by simp [lenOff])]
        exact sub_disj s₀ (a := 0) (n := 128) (by simp [lenOff]) (by omega) (by simp [lenOff]))
    (by rw [hp.ptr_toNat (by simp [lenOff])]; have := hp.fit_c; simp [lenOff]; omega)
    (by rw [hp.addr_ptr (by simp [lenOff])]
        exact covers_left _ (covers1 hp rfl (a := lenOff) (n := 16 * 1) (by simp [lenOff]))))
    fun s₂ ⟨i₂, k₂, repr₂⟩ => ⟨i₂, (k₁.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans
      (k₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩), fun key msg hr => ?_⟩
  have hr₁ : Repr s₁.mem (cx s₀) key msg := Repr.frame k₁.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [← sub_zero]; exact sub_disj s₀ (by simp [lenOff]) (by omega) (by simp [lenOff])) hr
  have := repr₂ key msg hr₁
  rwa [hp.addr_ptr (by simp [lenOff]), show 16 * 1 = 16 from rfl, len₁] at this

/-! ## The length of the message authenticated -/

theorem length_pad (x : List Byte) : (x ++ Spec.ChaCha20Poly1305.pad16 x).length = 16 * ((x.length + 15) / 16) := by
  simp only [List.length_append, Spec.ChaCha20Poly1305.pad16]
  split
  · simp; omega
  · simp; omega

theorem length_macData (a c : List Byte) :
    (Spec.ChaCha20Poly1305.macData a c).length = 16 * ((a.length + 15) / 16 + (c.length + 15) / 16 + 1) := by
  have ha := length_pad a
  have hc := length_pad c
  simp only [List.length_append] at ha hc
  simp only [Spec.ChaCha20Poly1305.macData, List.length_append, leBytes, List.length_map, List.length_range]
  omega

/-- `⌈x / 16⌉`, as `ceil16` computes it. -/
theorem ceil16_val (x : BitVec 32) :
    x >>> 4 + ((x &&& 15) + 15) >>> 4 = BitVec.ofNat 32 ((x.toNat + 15) / 16) := by
  have hx := x.isLt
  apply BitVec.eq_of_toNat_eq
  have e : (x &&& 15).toNat = x.toNat % 16 := by
    rw [BitVec.toNat_and, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, e, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  rw [show (15 : BitVec 32).toNat = 15 from rfl]
  omega

/-- `r3:r2 = 16 n`, from `n` in `r2`. -/
theorem count_val (n : BitVec 32) : n >>> 28 ++ n <<< 4 = BitVec.ofNat 64 (16 * n.toNat) := by
  have hn := n.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    ← Nat.shiftLeft_add_eq_or_of_lt (by exact Nat.mod_lt _ (by norm_num)), Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem finArgs_ok {s₀ : State} {s : State} (h : Inv s₀ s) :
    WP isa (.block finalizeArgs) s fun s' => Inv s₀ s' ∧ Kept [] s s' ∧ s'.gpr .r0 = cP s₀ ∧
      s'.gpr .r1 = ptr s₀ tagOff ∧ s'.gpr .r12 = ptr s₀ scrOff ∧
      Proof.Poly1305.countArm s' = BitVec.ofNat 64 (16 * ((AL s₀ + 15) / 16 + (L s₀ + 15) / 16 + 1)) := by
  have core : WP isa (.block finalizeArgs) s fun s' => s'.gpr .r0 = cP s₀ ∧
      s'.gpr .r1 = ptr s₀ tagOff ∧ s'.gpr .r12 = ptr s₀ scrOff ∧
      s'.gpr .r3 ++ s'.gpr .r2 = BitVec.ofNat 64 (16 * ((AL s₀ + 15) / 16 + (L s₀ + 15) / 16 + 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
    unfold finalizeArgs ceil16
    simp only [List.cons_append, List.nil_append]
    refine wp_mov (op2_lsr (by decide)) fun s₁ u₁ => wp_and (op2_imm (by decide)) fun s₂ u₂ =>
      wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_add (op2_lsr (by decide)) fun s₄ u₄ =>
      wp_mov (op2_lsr (by decide)) fun s₅ u₅ => wp_and (op2_imm (by decide)) fun s₆ u₆ =>
      wp_add (op2_imm (by decide)) fun s₇ u₇ => wp_add (op2_lsr (by decide)) fun s₈ u₈ =>
      wp_add (op2_reg _ _) fun s₉ u₉ => wp_add (op2_imm (by decide)) fun s₁₀ u₁₀ =>
      wp_mov (op2_lsr (by decide)) fun s₁₁ u₁₁ => wp_mov (op2_lsl (by decide)) fun s₁₂ u₁₂ =>
      wp_mov (op2_reg _ _) fun s₁₃ u₁₃ => wp_add (op2_imm (by decide)) fun s₁₄ u₁₄ =>
      wp_add (op2_imm (by decide)) fun s₁₅ u₁₅ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide),
        u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hr7 h]
    · rw [u₁₅.other _ (by decide), u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide),
        u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hr7 h]
    · rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide),
        u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hr7 h]
    · -- `r2` = ⌈aad_len / 16⌉ + ⌈len / 16⌉ + 1, then shifted into `r3:r2`.
      have cA : s₄.gpr .r2 = BitVec.ofNat 32 ((AL s₀ + 15) / 16) := by
        rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₃.gpr, u₂.gpr,
          u₁.other _ (by decide), h.regs.r9, ceil16_val]
      have cL : s₈.gpr .r0 = BitVec.ofNat 32 ((L s₀ + 15) / 16) := by
        rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₇.gpr, u₆.gpr,
          u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.regs.r11, ceil16_val]
      have cN : s₁₀.gpr .r2 = BitVec.ofNat 32 ((AL s₀ + 15) / 16 + (L s₀ + 15) / 16 + 1) := by
        rw [u₁₀.gpr, u₉.gpr, cL, u₈.other .r2 (by decide), u₇.other .r2 (by decide),
          u₆.other .r2 (by decide), u₅.other .r2 (by decide), cA]
        rw [← BitVec.ofNat_add, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
      have hN : ((AL s₀ + 15) / 16 + (L s₀ + 15) / 16 + 1) < 2 ^ 32 := by
        have := (s₀.gpr .r2).isLt; have := (stackArg s₀ 0).isLt; simp only [AL, L]; omega
      have c3 : s₁₅.gpr .r3 = s₁₀.gpr .r2 >>> 28 := by
        rw [u₁₅.other .r3 (by decide), u₁₄.other .r3 (by decide), u₁₃.other .r3 (by decide),
          u₁₂.other .r3 (by decide), u₁₁.gpr]
      have c2 : s₁₅.gpr .r2 = s₁₀.gpr .r2 <<< 4 := by
        rw [u₁₅.other .r2 (by decide), u₁₄.other .r2 (by decide), u₁₃.other .r2 (by decide), u₁₂.gpr,
          u₁₁.other .r2 (by decide)]
      rw [c3, c2, cN, count_val, toNat32 hN]
    · rw [u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd,
        u₂.rd, u₁.rd]
    · rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr,
        u₂.wr, u₁.wr]
    · rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem,
        u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (WP.kept core (by simp [finalizeArgs, ceil16, dstOf, preserved]))
    fun s' ⟨⟨h0, h1, h12, hc, hrd, hwr, hm⟩, hg, hsp⟩ => ?_
  have hk : Kept [] s s' := Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)
  exact ⟨h.step0 hk, hk, h0, h1, h12, hc⟩

/-! ## The tag -/

theorem fin_args {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) (h0 : s.gpr .r0 = cP s₀)
    (h1 : s.gpr .r1 = ptr s₀ tagOff) (h12 : s.gpr .r12 = ptr s₀ scrOff) :
    FinArgs s (cP s₀) (ptr s₀ tagOff) (ptr s₀ scrOff) := by
  have et := hp.addr_ptr (k := tagOff) (by simp [tagOff])
  have es := hp.addr_ptr (k := scrOff) (by simp [scrOff])
  have hsp := h.sp
  have bc : ∀ k n, k + n ≤ 1024 → (⟨State.addr s.sp - 8, 8⟩ : Region).Disjoint (sub s₀ k n) := fun k n hk => by
    rw [hsp]; exact hp.b_c.sub_right (sub_ctx s₀ hk)
  exact ⟨h0, h1, h12, by rw [hsp]; exact hp.sp8,
    by rw [et, ← sub_zero]; exact sub_disj s₀ (by simp [tagOff]) (by omega) (by simp [tagOff]),
    by rw [es, ← sub_zero]; exact sub_disj s₀ (by simp [scrOff]) (by omega) (by simp [scrOff]),
    by rw [et, es]; exact sub_disj s₀ (by simp [tagOff, scrOff]) (by simp [tagOff]) (by simp [scrOff]),
    by rw [← sub_zero]; exact bc 0 128 (by omega),
    by rw [et]; exact bc _ _ (by simp [tagOff]),
    by rw [es]; exact bc _ _ (by simp [scrOff]),
    by have := hp.fit_c; simp only [cP] at this ⊢; omega,
    by rw [hp.ptr_toNat (by simp [tagOff])]; have := hp.fit_c; simp [tagOff]; omega,
    by rw [hp.ptr_toNat (by simp [scrOff])]; have := hp.fit_c; simp [scrOff]; omega,
    covers_sub hp h.wr _ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨0, by rw [← sub_zero], by simp⟩
      · exact ⟨tagOff, by rw [et], by simp [tagOff]⟩
      · exact ⟨scrOff, by rw [es], by simp [scrOff]⟩⟩

theorem fin_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) (h0 : s.gpr .r0 = cP s₀)
    (h1 : s.gpr .r1 = ptr s₀ tagOff) (h12 : s.gpr .r12 = ptr s₀ scrOff) :
    WP isa finalize s fun s' => Inv s₀ s' ∧
      Kept [sub s₀ 0 128, sub s₀ tagOff 16, sub s₀ scrOff 128, belR s₀] s s' ∧
      ∀ key msg, Repr s.mem (cx s₀) key msg → Proof.Poly1305.countArm s = BitVec.ofNat 64 msg.length →
        bytesAt s'.mem (off (cx s₀) tagOff) 16 = mac key msg := by
  have et := hp.addr_ptr (k := tagOff) (by simp [tagOff])
  have es := hp.addr_ptr (k := scrOff) (by simp [scrOff])
  have hsp := h.sp
  refine finalize_ok (fin_args hp h h0 h1 h12) fun s' hk htag => ?_
  rw [et, es, ← sub_zero, hsp] at hk
  refine ⟨h.step hk (fun r hr => ?_) (fun r hr => ?_), hk, fun key msg hr hc => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact sub_inv s₀ (by omega)
    · exact sub_inv s₀ (by simp [tagOff])
    · exact sub_inv s₀ (by simp [scrOff])
    · exact ⟨belR s₀, by simp, fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact sub_disj s₀ (by simp [savOff]) (by simp [savOff]) (by omega)
    · exact sub_disj s₀ (by simp [savOff, tagOff]) (by simp [savOff]) (by simp [tagOff])
    · exact sub_disj s₀ (by simp [savOff, scrOff]) (by simp [savOff]) (by simp [scrOff])
    · exact (hp.b_c.sub_right (sub_ctx s₀ (by simp [savOff]))).symm
  · have := htag key msg hr hc
    rwa [et] at this

/-! ## Restoring the registers -/

theorem restoreList_ok {b : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ b ∧ p.2 < 4096 ∧ (s.gpr b).toNat + p.2 < 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.ldr p.1 b p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h1, h2, h3⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_ldr h1 (addr_add h2) h3 fun s₁ u₁ => ?_
    have eb : s₁.gpr b = s.gpr b := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr hsp => k s' (fun q hq => ?_)
      (fun r hr => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd) (hwr.trans u₁.wr) (hsp.trans u₁.sp)
    · rw [eb, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, eb]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

theorem preserved_eq : preserved = saved.map Prod.fst := rfl

/-- Restoring `r4`–`r11` and `lr` from `ctx[480, 516)`, through `r12`. -/
theorem restore_ok {s₀ : State} (hp : APre s₀) {s : State} (h7 : s.gpr .r7 = cP s₀) (hsv : Saved s₀ s.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block restore) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ preserved → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold restore
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = cP s₀ := by rw [u₁.gpr, h7]
  rw [← List.append_nil (saved.map _)]
  refine restoreList_ok (b := .r12) saved s₁ _ (by decide) (fun p hp' => ?_)
    fun s' ho hr hm hrd' hwr' hsp => WP.block_nil ⟨fun r hr' => ?_, fun r hr' h12' => ?_, ?_, ?_, ?_, ?_⟩
  · have hb := saved_bound p hp'
    simp only [savOff] at hb
    have := hp.fit_c
    simp only [cP] at this
    refine ⟨fun e => by simp [saved] at hp'; rcases hp' with h | h | h | h | h | h | h | h | h <;>
      simp_all, by omega, by rw [h12]; simp only [cP]; omega, ?_⟩
    rw [h12, u₁.rd, u₁.wr, hrd, hwr]; exact hp.in_ctx' (by omega)
  · rw [preserved_eq] at hr'
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr'
    rw [ho p hp', h12, u₁.mem]; exact hsv p hp'
  · rw [hr r (by rwa [← preserved_eq]), u₁.other r h12']
  · rw [hm, u₁.mem]
  · rw [hsp, u₁.sp]
  · rw [hrd', u₁.rd]
  · rw [hwr', u₁.wr]

/-! ## Comparing the tags -/

theorem compare_eq : compare =
    [.ldr .r0 .r7 448, .ldr .r1 .r7 464, .dp .eor .r0 .r0 (.reg .r1),
     .ldr .r1 .r7 452, .ldr .r2 .r7 468, .dp .eor .r1 .r1 (.reg .r2), .dp .orr .r0 .r0 (.reg .r1),
     .ldr .r1 .r7 456, .ldr .r2 .r7 472, .dp .eor .r1 .r1 (.reg .r2), .dp .orr .r0 .r0 (.reg .r1),
     .ldr .r1 .r7 460, .ldr .r2 .r7 476, .dp .eor .r1 .r1 (.reg .r2), .dp .orr .r0 .r0 (.reg .r1),
     .mov .r1 (.imm 0), .dp .sub .r1 .r1 (.reg .r0), .dp .orr .r0 .r0 (.reg .r1),
     .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (.imm 1), .dp .sub .r0 .r1 (.reg .r0)] := rfl

/-- `(x | -x) >> 31` is 0 if `x = 0` and 1 otherwise. -/
theorem nz_bit (x : BitVec 32) : (x ||| (0 - x)) >>> 31 = if x = 0 then 0 else 1 := by
  by_cases h : x = 0
  · subst h; rfl
  · simp only [h, ↓reduceIte]
    have hx : x.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
    have hlt := x.isLt
    have hneg : (0 - x).toNat = 2 ^ 32 - x.toNat := by
      rw [BitVec.toNat_sub, show (0 : BitVec 32).toNat = 0 from rfl]; omega
    have h1 : 2 ^ 31 ≤ (x ||| (0 - x)).toNat := by
      rw [BitVec.toNat_or]
      rcases Nat.lt_or_ge x.toNat (2 ^ 31) with h2 | h2
      · exact le_trans (by omega) (Nat.right_le_or (n := x.toNat))
      · exact le_trans h2 Nat.left_le_or
    have h2 := (x ||| (0 - x)).isLt
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl]
    omega

theorem sel_eq {x : BitVec 32} {p : Prop} [Decidable p] (h : x = 0 ↔ p) :
    ((1 : BitVec 32) - if x = 0 then 0 else 1) = if p then 1 else 0 := by
  by_cases hp : p
  · have hx : x = 0 := h.mpr hp
    simp only [hx, hp, ↓reduceIte]
    decide
  · have hx : ¬ x = 0 := fun e => hp (h.mp e)
    simp only [hx, hp, ↓reduceIte]
    decide

/-- Words equal are bytes equal, and conversely. -/
theorem words_iff_bytes (m : Mem) (p q : Addr) :
    (∀ k < 4, m.readW (p + BitVec.ofNat 64 (4 * k)) 32 = m.readW (q + BitVec.ofNat 64 (4 * k)) 32) ↔
      bytesAt m p 16 = bytesAt m q 16 := by
  constructor
  · intro h; exact bytes_of_words (n := 4) h
  · intro h k hk
    have hb : ∀ i < 16, m (p + BitVec.ofNat 64 i) = m (q + BitVec.ofNat 64 i) := fun i hi => by
      have := congrArg (fun l => l.getD i 0) h
      simpa [bytesAt, hi] using this
    rw [readW32, readW32]
    have e : ∀ (a : Addr) (j : Nat), a + BitVec.ofNat 64 (4 * k) + (BitVec.ofNat 64 j) =
        a + BitVec.ofNat 64 (4 * k + j) := fun a j => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have e3 := e p 3; have e2 := e p 2; have e1 := e p 1
    have f3 := e q 3; have f2 := e q 2; have f1 := e q 1
    simp only [show (3 : Addr) = BitVec.ofNat 64 3 from rfl, show (2 : Addr) = BitVec.ofNat 64 2 from rfl,
      show (1 : Addr) = BitVec.ofNat 64 1 from rfl, e3, e2, e1, f3, f2, f1]
    rw [hb _ (by omega), hb _ (by omega), hb _ (by omega), hb _ (by omega)]

/-- The tags differ in no bit if and only if they are equal. -/
theorem tag_eq (m : Mem) (c : Addr) :
    ((m.readW (off c 448) 32 ^^^ m.readW (off c 464) 32) |||
      (m.readW (off c 452) 32 ^^^ m.readW (off c 468) 32) |||
      (m.readW (off c 456) 32 ^^^ m.readW (off c 472) 32) |||
      (m.readW (off c 460) 32 ^^^ m.readW (off c 476) 32)) = 0#32 ↔
      bytesAt m (off c tagOff) 16 = bytesAt m (off c rtagOff) 16 := by
  rw [← words_iff_bytes, BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff,
    BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff]
  simp only [off_add]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro h
    exact ⟨⟨⟨h 0 (by omega), h 1 (by omega)⟩, h 2 (by omega)⟩, h 3 (by omega)⟩

theorem compare_ok {s₀ : State} (hp : APre s₀) {s : State} (h7 : s.gpr .r7 = cP s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block compare) s fun s' =>
      s'.gpr .r0 = (if bytesAt s.mem (off (cx s₀) tagOff) 16 = bytesAt s.mem (off (cx s₀) rtagOff) 16
        then 1 else 0) ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have i : ∀ d, d + 4 ≤ 1024 → InRegions (s.rd ++ s.wr) (off (cx s₀) d) 4 := fun d h => by
    rw [hrd, hwr]; exact hp.in_ctx' h
  have ea : ∀ d, d < 1024 → ∀ t : State, t.gpr .r7 = cP s₀ →
      State.addr (t.gpr .r7 + BitVec.ofNat 32 d) = off (cx s₀) d := fun d hd t ht => by
    rw [ht]; exact hp.addr_cP_off hd
  let x : BitVec 32 := (s.mem.readW (off (cx s₀) 448) 32 ^^^ s.mem.readW (off (cx s₀) 464) 32) |||
      (s.mem.readW (off (cx s₀) 452) 32 ^^^ s.mem.readW (off (cx s₀) 468) 32) |||
      (s.mem.readW (off (cx s₀) 456) 32 ^^^ s.mem.readW (off (cx s₀) 472) 32) |||
      (s.mem.readW (off (cx s₀) 460) 32 ^^^ s.mem.readW (off (cx s₀) 476) 32)
  have core : WP isa (.block compare) s fun s' =>
      s'.gpr .r0 = 1 - (x ||| (0 - x)) >>> 31 ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    rw [compare_eq]
    refine wp_ldr (a := off (cx s₀) 448) (by decide) (ea 448 (by omega) s h7) (i 448 (by omega)) fun s₁ u₁ => ?_
    have r7₁ : s₁.gpr .r7 = cP s₀ := by rw [u₁.other _ (by decide), h7]
    refine wp_ldr (a := off (cx s₀) 464) (by decide) (ea 464 (by omega) s₁ r7₁)
      (by rw [u₁.rd, u₁.wr]; exact i 464 (by omega)) fun s₂ u₂ => ?_
    have r7₂ : s₂.gpr .r7 = cP s₀ := by rw [u₂.other _ (by decide), r7₁]
    refine wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
    have r7₃ : s₃.gpr .r7 = cP s₀ := by rw [u₃.other _ (by decide), r7₂]
    have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
    have x₃ : s₃.gpr .r0 = s.mem.readW (off (cx s₀) 448) 32 ^^^ s.mem.readW (off (cx s₀) 464) 32 := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem]
    -- One more pair of words: `r0 |= [r7 + a] ^ [r7 + b]`.
    have step : ∀ (a b : Nat), a + 4 ≤ 1024 → b + 4 ≤ 1024 → ∀ (t : State) (rest : List Instr) (Q : State → Prop),
        t.gpr .r7 = cP s₀ → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr →
        (∀ t', t'.gpr .r0 = t.gpr .r0 ||| (s.mem.readW (off (cx s₀) a) 32 ^^^ s.mem.readW (off (cx s₀) b) 32) →
          t'.gpr .r7 = cP s₀ → t'.mem = s.mem → t'.rd = s.rd → t'.wr = s.wr → WP isa (.block rest) t' Q) →
        WP isa (.block (.ldr .r1 .r7 a :: .ldr .r2 .r7 b :: .dp .eor .r1 .r1 (.reg .r2) ::
          .dp .orr .r0 .r0 (.reg .r1) :: rest)) t Q := by
      intro a b ha hb t rest Q t7 tm trd twr k
      refine wp_ldr (a := off (cx s₀) a) (by omega) (ea a (by omega) t t7)
        (by rw [trd, twr]; exact i a ha) fun t₁ v₁ => ?_
      refine wp_ldr (a := off (cx s₀) b) (by omega) (ea b (by omega) t₁ (by rw [v₁.other _ (by decide), t7]))
        (by rw [v₁.rd, v₁.wr, trd, twr]; exact i b hb) fun t₂ v₂ => ?_
      refine wp_eor (op2_reg _ _) fun t₃ v₃ => wp_orr (op2_reg _ _) fun t₄ v₄ => k t₄ ?_ ?_ ?_ ?_ ?_
      · rw [v₄.gpr, v₃.gpr, v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide),
          v₂.other _ (by decide), v₁.gpr, v₂.gpr, v₁.mem, tm]
      · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), t7]
      · rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, tm]
      · rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, trd]
      · rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, twr]
    refine step 452 468 (by omega) (by omega) s₃ _ _ r7₃ m₃ (by rw [u₃.rd, u₂.rd, u₁.rd])
      (by rw [u₃.wr, u₂.wr, u₁.wr]) fun t₁ w₁ r7t₁ mt₁ rdt₁ wrt₁ => ?_
    refine step 456 472 (by omega) (by omega) t₁ _ _ r7t₁ mt₁ rdt₁ wrt₁ fun t₂ w₂ r7t₂ mt₂ rdt₂ wrt₂ => ?_
    refine step 460 476 (by omega) (by omega) t₂ _ _ r7t₂ mt₂ rdt₂ wrt₂ fun t₃ w₃ _ mt₃ rdt₃ wrt₃ => ?_
    refine wp_mov (op2_imm (by decide)) fun t₄ v₄ => wp_sub (op2_reg _ _) fun t₅ v₅ =>
      wp_orr (op2_reg _ _) fun t₆ v₆ => wp_mov (op2_lsr (by decide)) fun t₇ v₇ =>
      wp_mov (op2_imm (by decide)) fun t₈ v₈ => wp_sub (op2_reg _ _) fun t₉ v₉ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
    · have hx : t₃.gpr .r0 = x := by rw [w₃, w₂, w₁, x₃]
      rw [v₉.gpr, v₈.gpr, v₈.other _ (by decide), v₇.gpr, v₆.gpr, v₅.gpr, v₅.other _ (by decide), v₄.gpr,
        v₄.other _ (by decide), hx]
      rfl
    · rw [v₉.mem, v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, mt₃]
    · rw [v₉.rd, v₈.rd, v₇.rd, v₆.rd, v₅.rd, v₄.rd, rdt₃]
    · rw [v₉.wr, v₈.wr, v₇.wr, v₆.wr, v₅.wr, v₄.wr, wrt₃]
  refine WP.mono (WP.kept core (by simp [compare_eq, dstOf, preserved]))
    fun s' ⟨⟨h0, hm, hrd', hwr'⟩, hg, hsp⟩ => ⟨?_, hg, hsp, hm, hrd', hwr'⟩
  rw [h0, nz_bit]
  exact sel_eq (tag_eq s.mem (cx s₀))

end VG.Proof.ChaCha20Poly1305.Arm
