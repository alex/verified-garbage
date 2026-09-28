import VerifiedGarbage.Proof.Sha512.Arm.Stream.Init

/-!
# Streaming SHA-512 on ARMv7: common lemmas

Untrusted: everything here is checked by Lean. Saving and restoring our
caller's registers, the inlined compression function in the terms of the
streaming proofs, and arithmetic on 32-bit values.
-/

namespace VG.Proof.Sha512.Arm.Stream

open VG VG.Arm VG.Impl.Sha512.Arm.Stream
open VG.Proof.Sha256.Arm (contains_offset)
open VG.Proof.Sha256.Arm.Stream (Upd Mupd Fupd saveMem saveList_ok restoreList_ok readW_writeW_save
  sub_offset)
open VG.Spec.Sha512 (HashValue stateAt blockAt compress)

/-! ## Saving and restoring our caller's registers -/

theorem save_eq (b : Reg) : save b = saved.map (fun p => Instr.str p.1 b p.2) := rfl

/-- Saving `r4`–`r11` with the scratch pointer in `b`. -/
theorem save_ok {b : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hfit : (s.gpr b).toNat + 224 ≤ 2 ^ 32)
    (hin : ∀ d, 64 ≤ d → d + 4 ≤ 96 → InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 d) 4)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem s.mem (State.addr (s.gpr b)) s.gpr saved → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q := by
  rw [save_eq]
  refine saveList_ok saved s Q (fun p hp => ?_) k
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  exact ⟨by decide, by simp only; omega, hin _ (by decide) (by decide)⟩

set_option simprocs false in
theorem saveMem_saved (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ p ∈ saved, (saveMem m B g saved).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1 := by
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
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

theorem saved_bound : ∀ p ∈ saved, 64 ≤ p.2 ∧ p.2 + 4 ≤ 96 := by decide

theorem restore_eq : restore = saved.map (fun p => Instr.ldr p.1 .r3 p.2) := rfl

/-- Restoring `r4`–`r11` from the save area at `scratch`. -/
theorem restore_ok {s : State} {scr : BitVec 32} (h3 : s.gpr .r3 = scr) (hfit : scr.toNat + 224 ≤ 2 ^ 32)
    (hin : ∀ d, 64 ≤ d → d + 4 ≤ 96 → InRegions (s.rd ++ s.wr) (State.addr scr + BitVec.ofNat 64 d) 4)
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
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by simp only; omega, hin _ (by decide) (by decide)⟩
  · rw [ho p hp, h3, hsv p hp]

/-- The saved registers are preserved by the ABI. -/
theorem preserved_saved {s₀ s' : State} (hs : ∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1)
    (hlr : s'.gpr .lr = s₀.gpr .lr) : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r := by
  intro r hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hs (.r4, 64) (by simp [saved])
  · exact hs (.r5, 68) (by simp [saved])
  · exact hs (.r6, 72) (by simp [saved])
  · exact hs (.r7, 76) (by simp [saved])
  · exact hs (.r8, 80) (by simp [saved])
  · exact hs (.r9, 84) (by simp [saved])
  · exact hs (.r10, 88) (by simp [saved])
  · exact hs (.r11, 92) (by simp [saved])
  · exact hlr

/-! ## The inlined compression function -/

theorem Reg64.of_sub {wr : List Region} {B : BitVec 32} {N N' : Nat} (h : ⟨State.addr B, N'⟩ ∈ wr)
    (hN : N ≤ N') (hfit : B.toNat + N' ≤ 2 ^ 32) : Reg64 wr B N :=
  fun _ ho => ⟨⟨_, h, contains_A hfit (by omega)⟩, ⟨_, h, contains_A hfit (by omega)⟩⟩

/-- Compressing the buffer of the state at `r0` into its hash value, with
the scratch space (224 bytes) at `r3`. -/
theorem compressBuf_ok {s : State} {st scr : BitVec 32}
    (h0 : s.gpr .r0 = st) (h3 : s.gpr .r3 = scr)
    (f₀ : st.toNat + 192 ≤ 2 ^ 32) (f₃ : scr.toNat + 224 ≤ 2 ^ 32)
    (d : Region.Disjoint ⟨State.addr st, 192⟩ ⟨State.addr scr, 224⟩)
    (hS : ⟨State.addr st, 192⟩ ∈ s.wr) (hV : ⟨State.addr scr, 224⟩ ∈ s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r, r ∉ temps → s'.gpr r = s.gpr r) → s'.sp = s.sp →
      Frame [⟨State.addr st, 192⟩, ⟨State.addr scr, 64⟩] s.mem s'.mem →
      stateAt s'.mem (State.addr st) =
        compress (stateAt s.mem (State.addr st)) (blockAt s.mem (State.addr st + 64)) → Q s') :
    WP isa Impl.Sha512.Arm.compress s Q :=
  compress_ok ⟨h0, h3, f₀, by omega, d.sub_right (Region.sub_prefix (by omega)),
    Reg64.of_mem hS f₀, Reg64.of_sub hV (by omega) f₃⟩
    fun s' hg hrd hwr hsp hf hst => hQ s' hrd hwr hg hsp hf hst

/-! ## Arithmetic -/

theorem and127 (x : BitVec 32) : x &&& 127 = BitVec.ofNat 32 (x.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (127 : BitVec 32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

end VG.Proof.Sha512.Arm.Stream
