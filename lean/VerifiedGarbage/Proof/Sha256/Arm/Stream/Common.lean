import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Sha256.Arm.Compress
import VerifiedGarbage.Impl.Sha256.Arm.Stream
import VerifiedGarbage.Proof.Sha256.Arm.Lit

/-!
# Streaming SHA-256 on ARMv7: calling the compression function, and saving registers

What HMAC and PBKDF2, which call SHA-256's compression function themselves and
save our caller's registers where its streaming code does, use: the call
(`compressAt`), and saving and restoring the registers (`save`, `restore`). The
streaming `update` and `finalize` are proven generically
(`Proof/Sha256/Arm/Stream/Md.lean`), and the per-instruction rules are
`VG.Proof.MdStream.Arm`'s.
-/

namespace VG.Proof.Sha256.Arm.Stream

open VG VG.Arm VG.Impl.Sha256.Arm.Stream
open VG.Proof.Sha256.Arm (compress_verified contains_offset)
open VG.Proof.MdStream.Arm (Upd WP.cons op2_imm wp_mov wp_ldr wp_str saveList_ok
  readW_writeW_save restoreList_ok)
open VG.Spec.Sha256 (HashValue stateAt blockAt compressBlocks compress parseBlock bytesAt)

/-! ## The compression function -/

theorem compressBlocks_one (H : HashValue) (m : Mem) (p : Addr) :
    compressBlocks H m p 1 = compress H (blockAt m p) := by
  simp [compressBlocks]

theorem r0_ok : ∀ i ∈ instrs Impl.Sha256.Arm.compress, dstOf i ≠ some .r0 := by
  have : ((instrs Impl.Sha256.Arm.compress).all fun i => dstOf i != some .r0) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp this i hi

theorem r3_ok : ∀ i ∈ instrs Impl.Sha256.Arm.compress, dstOf i ≠ some .r3 := by
  have : ((instrs Impl.Sha256.Arm.compress).all fun i => dstOf i != some .r3) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp this i hi

/-- Compressing the block at `r1` into the hash value at `r0`, with scratch
space at `r3`. -/
theorem compressAt_ok {s : State} {st scr src : BitVec 32}
    (h0 : s.gpr .r0 = st) (h3 : s.gpr .r3 = scr) (h1 : s.gpr .r1 = src)
    (f₀ : st.toNat + 32 ≤ 2 ^ 32) (f₁ : src.toNat + 64 ≤ 2 ^ 32) (f₃ : scr.toNat + 112 ≤ 2 ^ 32)
    (d₁ : Region.Disjoint ⟨State.addr st, 32⟩ ⟨State.addr scr, 112⟩)
    (d₂ : Region.Disjoint ⟨State.addr src, 64⟩ ⟨State.addr st, 32⟩)
    (d₃ : Region.Disjoint ⟨State.addr src, 64⟩ ⟨State.addr scr, 112⟩)
    (hc : Covers [⟨State.addr src, 64⟩, ⟨State.addr st, 32⟩, ⟨State.addr scr, 112⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr st, 32⟩, ⟨State.addr scr, 112⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.gpr .r0 = st → s'.gpr .r3 = scr → s'.sp = s.sp →
      Frame [⟨State.addr st, 32⟩, ⟨State.addr scr, 112⟩] s.mem s'.mem →
      stateAt s'.mem (State.addr st) =
        compress (stateAt s.mem (State.addr st)) (blockAt s.mem (State.addr src)) → Q s') :
    WP isa compressAt s Q := by
  unfold compressAt compressCall
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil ?_)
  have e0 : s₁.gpr .r0 = st := by rw [u₁.other _ (by decide), h0]
  have e1 : s₁.gpr .r1 = src := by rw [u₁.other _ (by decide), h1]
  have e2 : s₁.gpr .r2 = 1 := u₁.gpr
  have e3 : s₁.gpr .r3 = scr := by rw [u₁.other _ (by decide), h3]
  have c : ∀ r, r ∉ linkRegs → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr s₁ h
  refine WP.call (k := Proof.Sha256.compressArm) compress_verified.1
    (rd := [⟨State.addr src, 64 * 1⟩]) (wr := [⟨State.addr st, 32⟩, ⟨State.addr scr, 112⟩]) ?_ ?_ ?_ ?_
  · simp only [Proof.Sha256.compressArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c _ (show Reg.r0 ∉ linkRegs by decide), c _ (show Reg.r1 ∉ linkRegs by decide),
      c _ (show Reg.r2 ∉ linkRegs by decide), c _ (show Reg.r3 ∉ linkRegs by decide), e0, e1, e2, e3]
    exact ⟨rfl, trivial, d₁, d₂, d₃, f₀, by simpa using f₁, f₃⟩
  · rw [u₁.rd, u₁.wr]; simpa using hc
  · rw [u₁.wr]; exact hw
  · intro s' hrd hwr hsp hf hcs hg hpost
    simp only [Proof.Sha256.compressArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      c _ (show Reg.r0 ∉ linkRegs by decide), c _ (show Reg.r1 ∉ linkRegs by decide),
      c _ (show Reg.r2 ∉ linkRegs by decide), e0, e1, e2, u₁.mem] at hpost
    rw [show (BitVec.toNat (1 : BitVec 32)) = 1 from rfl, compressBlocks_one] at hpost
    refine hQ s' (hrd.trans u₁.rd) (hwr.trans u₁.wr) (fun r hr hlr => ?_) (by rw [hg _ r0_ok (by decide), e0])
      (by rw [hg _ r3_ok (by decide), e3]) (hsp.trans u₁.sp) (u₁.mem ▸ hf) hpost
    have : r ≠ .r2 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hcs r hr hlr, u₁.other r this]

/-! ## Saving and restoring our caller's registers -/

theorem save_eq (b : Reg) : save b = saved.map (fun p => Instr.str p.1 b p.2) := rfl

/-- Saving `r4`–`r11` and `lr` with the scratch pointer in `b`. -/
theorem save_ok {b : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hfit : (s.gpr b).toNat + 160 ≤ 2 ^ 32)
    (hin : ∀ d, 112 ≤ d → d + 4 ≤ 148 → InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 d) 4)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = Proof.MdStream.Arm.saveMem s.mem (State.addr (s.gpr b)) s.gpr saved → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q := by
  rw [save_eq]
  refine saveList_ok saved s Q (fun p hp => ?_) k
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  exact ⟨by decide, by simp only; omega, hin _ (by decide) (by decide)⟩

theorem saveMem_saved (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ p ∈ saved, (Proof.MdStream.Arm.saveMem m B g saved).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1 :=
  Proof.MdStream.Arm.saveMem_saved (P := params) ⟨.inl rfl, by decide, by decide, by decide, by decide, by decide⟩ m B g

theorem saveMem_frame (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, p.2 + 4 ≤ 160) → Frame [⟨B, 160⟩] m (Proof.MdStream.Arm.saveMem m B g l) := by
  intro l
  induction l generalizing m with
  | nil => intro _; exact Frame.refl _ _
  | cons p l ih =>
    intro hl
    have h := hl p (by simp)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (n := 32 / 8) h (by omega))).trans
      (ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem saved_bound : ∀ p ∈ saved, p.2 + 4 ≤ 160 ∧ 112 ≤ p.2 := by decide

theorem restore_eq : restore = saved.map (fun p => Instr.ldr p.1 .r3 p.2) := rfl

/-- Restoring `r4`–`r11` and `lr` from the save area at `scratch`. -/
theorem restore_ok {s : State} {scr : BitVec 32} (h3 : s.gpr .r3 = scr) (hfit : scr.toNat + 160 ≤ 2 ^ 32)
    (hin : ∀ d, 112 ≤ d → d + 4 ≤ 148 → InRegions (s.rd ++ s.wr) (State.addr scr + BitVec.ofNat 64 d) 4)
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

end VG.Proof.Sha256.Arm.Stream
