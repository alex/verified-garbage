import VerifiedGarbage.Proof.Sha512.Arm.Stream.Init

/-!
# Streaming SHA-512 on ARMv7: common lemmas

Untrusted: everything here is checked by Lean. Saving and restoring our
caller's registers, the call of the compression function in the terms of
the streaming proofs, and arithmetic on 32-bit values.
-/

namespace VG.Proof.Sha512.Arm.Stream

open VG VG.Arm VG.Impl.Sha512.Arm.Stream
open VG.Proof.MdStream.Arm (contains_offset)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd saveMem saveList_ok restoreList_ok readW_writeW_save
  sub_offset wp_add wp_mov op2_imm)
open VG.Proof.Sha512.Arm (temps)
open VG.Proof.Sha512.Arm.Compress (compress_verified)
open VG.Spec.Sha512 (HashValue stateAt blockAt compress compressBlocks)

/-! ## Saving and restoring our caller's registers -/

theorem save_eq (b : Reg) : save b = saved.map (fun p => Instr.str p.1 b p.2) := rfl

/-- Saving `r4`–`r11` and `lr` with the scratch pointer in `b`. -/
theorem save_ok {b : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hfit : (s.gpr b).toNat + 272 ≤ 2 ^ 32)
    (hin : ∀ d, 224 ≤ d → d + 4 ≤ 260 → InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 d) 4)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem s.mem (State.addr (s.gpr b)) s.gpr saved → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q := by
  rw [save_eq]
  refine saveList_ok saved s Q (fun p hp => ?_) k
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  exact ⟨by decide, by simp only; omega, hin _ (by decide) (by decide)⟩

set_option simprocs false in
theorem saveMem_saved (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ p ∈ saved, (saveMem m B g saved).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1 := by
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [saved, saveMem, Mem.readW_writeW_self32, readW_writeW_save]

theorem saveMem_frame (m : Mem) (B : Addr) (g : Reg → BitVec 32) {N : Nat} (hN : N < 2 ^ 64) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, p.2 + 4 ≤ N) → Frame [⟨B, N⟩] m (saveMem m B g l) := by
  intro l
  induction l generalizing m with
  | nil => intro _; exact Frame.refl _ _
  | cons p l ih =>
    intro hl
    have h := hl p (by simp)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_offset (n := 32 / 8) h (by omega))).trans (ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem saved_bound : ∀ p ∈ saved, 224 ≤ p.2 ∧ p.2 + 4 ≤ 260 := by decide

theorem restore_eq : restore = saved.map (fun p => Instr.ldr p.1 .r3 p.2) := rfl

/-- Restoring `r4`–`r11` and `lr` from the save area at `scratch`. -/
theorem restore_ok {s : State} {scr : BitVec 32} (h3 : s.gpr .r3 = scr) (hfit : scr.toNat + 272 ≤ 2 ^ 32)
    (hin : ∀ d, 224 ≤ d → d + 4 ≤ 260 → InRegions (s.rd ++ s.wr) (State.addr scr + BitVec.ofNat 64 d) 4)
    (g : Reg → BitVec 32) (hsv : ∀ p ∈ saved, s.mem.readW (State.addr scr + BitVec.ofNat 64 p.2) 32 = g p.1)
    {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved, s'.gpr p.1 = g p.1) → (∀ r, r ∉ saved.map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block restore) s Q := by
  rw [restore_eq, ← List.append_nil (saved.map _)]
  refine restoreList_ok saved s Q (by decide) (fun p hp => ?_)
    fun s' ho hr hm hrd hwr hsp => WP.block_nil (k s' (fun p hp => ?_) hr hm hrd hwr hsp)
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rw [h3]
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by simp only; omega, hin _ (by decide) (by decide)⟩
  · rw [ho p hp, h3, hsv p hp]

/-- The saved registers are preserved by the ABI. -/
theorem preserved_saved {s₀ s' : State} (hs : ∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) :
    ∀ r ∈ preserved, s'.gpr r = s₀.gpr r := by
  intro r hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hs (.r4, 224) (by simp [saved])
  · exact hs (.r5, 228) (by simp [saved])
  · exact hs (.r6, 232) (by simp [saved])
  · exact hs (.r7, 236) (by simp [saved])
  · exact hs (.r8, 240) (by simp [saved])
  · exact hs (.r9, 244) (by simp [saved])
  · exact hs (.r10, 248) (by simp [saved])
  · exact hs (.r11, 252) (by simp [saved])
  · exact hs (.lr, 256) (by simp [saved])

/-! ## The call of the compression function -/

theorem compressBlocks_one (H : HashValue) (m : Mem) (p : Addr) :
    compressBlocks H m p 1 = compress H (blockAt m p) := by
  simp [compressBlocks]

theorem r0_ok : ∀ i ∈ instrs Impl.Sha512.Arm.compress, dstOf i ≠ some .r0 := by
  have : ((instrs Impl.Sha512.Arm.compress).all fun i => dstOf i != some .r0) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp this i hi

theorem r3_ok : ∀ i ∈ instrs Impl.Sha512.Arm.compress, dstOf i ≠ some .r3 := by
  have : ((instrs Impl.Sha512.Arm.compress).all fun i => dstOf i != some .r3) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp this i hi

/-- The registers the compression function's contract accounts for: every
register but its temporaries and `lr` is `r0`, `r3` or callee-saved. -/
theorem regs_split (r : Reg) (ht : r ∉ temps) (hl : r ≠ .lr) : r = .r0 ∨ r = .r3 ∨ r ∈ preserved := by
  revert ht hl; cases r <;> decide

/-- Compressing the buffer of the state at `r0` into its hash value, with
the scratch space (272 bytes, of which the compression function uses 224) at
`r3`. -/
theorem compressBuf_ok {s : State} {st scr : BitVec 32}
    (h0 : s.gpr .r0 = st) (h3 : s.gpr .r3 = scr)
    (f₀ : st.toNat + 192 ≤ 2 ^ 32) (f₃ : scr.toNat + 272 ≤ 2 ^ 32)
    (d : Region.Disjoint ⟨State.addr st, 192⟩ ⟨State.addr scr, 272⟩)
    (hS : ⟨State.addr st, 192⟩ ∈ s.wr) (hV : ⟨State.addr scr, 272⟩ ∈ s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r, r ∉ temps → r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨State.addr st, 192⟩, ⟨State.addr scr, 224⟩] s.mem s'.mem →
      stateAt s'.mem (State.addr st) =
        compress (stateAt s.mem (State.addr st)) (blockAt s.mem (State.addr st + 64)) → Q s') :
    WP isa compressAt s Q := by
  unfold compressAt compressCall
  refine WP.seq (wp_add (op2_imm (by decide)) fun s₁ u₁ =>
    wp_mov (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil ?_)
  have e0 : s₂.gpr .r0 = st := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h0]
  have e1 : s₂.gpr .r1 = st + 64 := by rw [u₂.other _ (by decide), u₁.gpr, h0]
  have e2 : s₂.gpr .r2 = 1 := u₂.gpr
  have e3 : s₂.gpr .r3 = scr := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h3]
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have c : ∀ r, r ∉ linkRegs → s₂.callEntry.gpr r = s₂.gpr r := fun r h => State.callEntry_gpr s₂ h
  have hb : State.addr (st + 64) = State.addr st + BitVec.ofNat 64 64 := addr_add (k := 64) (by omega)
  have hbt : (st + 64).toNat = st.toNat + 64 := by
    rw [BitVec.toNat_add, show (64 : BitVec 32).toNat = 64 from rfl, Nat.mod_eq_of_lt (by omega)]
  have sS : Region.Sub ⟨State.addr st, 64⟩ ⟨State.addr st, 192⟩ := Region.sub_prefix (by omega)
  have sB : Region.Sub ⟨State.addr (st + 64), 128 * 1⟩ ⟨State.addr st, 192⟩ := by
    rw [hb]; exact sub_offset (off := 64) (len := 128 * 1) (len' := 192) (by decide) (by decide)
  have sV : Region.Sub ⟨State.addr scr, 224⟩ ⟨State.addr scr, 272⟩ := Region.sub_prefix (by omega)
  have dBS : Region.Disjoint ⟨State.addr (st + 64), 128 * 1⟩ ⟨State.addr st, 64⟩ := by
    intro a h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    rw [hb] at h₁
    generalize State.addr st = B at *
    bv_omega
  refine WP.call (k := Proof.Sha512.compressArm) compress_verified.1
    (rd := [⟨State.addr (st + 64), 128 * 1⟩]) (wr := [⟨State.addr st, 64⟩, ⟨State.addr scr, 224⟩])
    ?_ ?_ ?_ ?_
  · simp only [Proof.Sha512.compressArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c _ (show Reg.r0 ∉ linkRegs by decide), c _ (show Reg.r1 ∉ linkRegs by decide),
      c _ (show Reg.r2 ∉ linkRegs by decide), c _ (show Reg.r3 ∉ linkRegs by decide), e0, e1, e2, e3]
    exact ⟨rfl, trivial, (d.sub_left sS).sub_right sV, dBS, (d.sub_left sB).sub_right sV, by omega,
      by rw [hbt]; simp only [show (1 : BitVec 32).toNat = 1 from rfl]; omega, by omega⟩
  · rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_right _ hS, 64, hb, by simp⟩
    · exact ⟨_, List.mem_append_right _ hS, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ hV, 0, by simp, by simp⟩
  · rw [u₂.wr, u₁.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hS, 0, by simp, by simp⟩
    · exact ⟨_, hV, 0, by simp, by simp⟩
  · intro s' hrd hwr hsp hf hcs hg hpost
    simp only [Proof.Sha512.compressArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      c _ (show Reg.r0 ∉ linkRegs by decide), c _ (show Reg.r1 ∉ linkRegs by decide),
      c _ (show Reg.r2 ∉ linkRegs by decide), e0, e1, e2, m₂] at hpost
    rw [show (BitVec.toNat (1 : BitVec 32)) = 1 from rfl, compressBlocks_one, hb] at hpost
    refine hQ s' (hrd.trans (u₂.rd.trans u₁.rd)) (hwr.trans (u₂.wr.trans u₁.wr)) (fun r hr hlr => ?_)
      (hsp.trans (u₂.sp.trans u₁.sp)) ?_ hpost
    · rcases regs_split r hr hlr with rfl | rfl | hp
      · rw [hg _ r0_ok (by decide), e0, h0]
      · rw [hg _ r3_ok (by decide), e3, h3]
      · have h1 : r ≠ .r1 := by rintro rfl; simp [preserved] at hp
        have h2 : r ≠ .r2 := by rintro rfl; simp [preserved] at hp
        rw [hcs r hp hlr, u₂.other r h2, u₁.other r h1]
    · rw [← m₂]
      refine hf.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, sS⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-! ## Arithmetic -/

theorem and127 (x : BitVec 32) : x &&& 127 = BitVec.ofNat 32 (x.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (127 : BitVec 32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

end VG.Proof.Sha512.Arm.Stream
