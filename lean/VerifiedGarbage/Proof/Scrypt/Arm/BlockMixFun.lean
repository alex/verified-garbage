import VerifiedGarbage.Proof.Scrypt.Arm.BlockMix

/-!
# scryptBlockMix on 32-bit ARM: the whole function

Untrusted: everything here is checked by Lean. The prologue loads the
scratch pointer from the stack, saves our caller's `r4`–`r9` and our return
address in `scratch` and sets up the loop's registers; the loop runs the
`r` pairs; the epilogue restores the registers. There is no stack frame.
-/

namespace VG.Proof.Scrypt.Arm.BlockMix

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Spec.Scrypt (bytesAt blk blockMix)
open VG.Proof.Scrypt (yAt xBefore blockMix_eq flatMap_congr)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add wp_sub wp_ldr wp_ldrSp op2_reg op2_imm op2_lsl
  eval_ne ofNat_beq_zero saveMem saveList_ok readW_writeW_save)
open VG.Proof.Scrypt.X86_64.BlockMix (add_ofNat InRegions.of_mem frame_bytesAt bytesAt_add
  bytesAt_blocks)

/-! ## The prologue -/

/-- The prologue's register moves. -/
def bmSetup : List Instr :=
  [.mov .r8 (.reg .r1), .mov .r4 (.reg .r0), .mov .r5 (.reg .r2), .mov .r7 (.reg .r12),
   .dp .add .r6 .r2 (.shifted .r1 .lsl 6), .dp .add .r9 .r0 (.shifted .r1 .lsl 7),
   .dp .sub .r9 .r9 (.imm 64)]

theorem prologue_eq : bmPrologue =
    .ldrSp .r12 0 :: (bmSaved.map (fun p => Instr.str p.1 .r12 p.2) ++ bmSetup) := rfl

set_option simprocs false in
theorem saveMem_saved (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ p ∈ bmSaved, (saveMem m B g bmSaved).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1 := by
  intro p hp
  simp only [bmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [bmSaved, saveMem, Mem.readW_writeW_self32,
    readW_writeW_save]

theorem bmSaved_bound : ∀ p ∈ bmSaved, p.2 + 4 ≤ 128 ∧ 64 ≤ p.2 ∧ p.1 ≠ .r12 := by decide

theorem bmSaved_r7 : ∀ p ∈ bmSaved.take 6, p.1 ≠ .r7 := by decide

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, (∀ r, r ≠ .r12 → s₁.gpr r = s₀.gpr r) → s₁.gpr .r12 = sc s₀ → s₁.rd = s₀.rd →
      s₁.wr = s₀.wr → s₁.sp = s₀.sp → Frame [scR s₀] s₀.mem s₁.mem → Saved s₀ s₁.mem →
      WP isa (.block rest) s₁ Q) :
    WP isa (.block (.ldrSp .r12 0 :: (bmSaved.map (fun p => Instr.str p.1 .r12 p.2) ++ rest)))
      s₀ Q := by
  have hs := hp.s_nw
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl ?_ fun s₁ u₁ => ?_
  · rw [hp.rd]
    refine InRegions.of_mem (R := argR s₀) (by simp) ?_
    show (stackArgAddr s₀ 0 - stackArgAddr s₀ 0).toNat + 4 ≤ 4
    rw [BitVec.sub_self, BitVec.toNat_zero]
  have e12 : s₁.gpr .r12 = sc s₀ := u₁.gpr
  refine saveList_ok bmSaved s₁ Q (fun p hp' => ?_) fun s₂ g rd wr sp m => ?_
  · obtain ⟨h1, h2, -⟩ := bmSaved_bound p hp'
    rw [e12, u₁.wr, hp.wr]
    exact ⟨by omega, by omega, InRegions.of_mem (by simp) (in_s s₀ h1)⟩
  refine k s₂ (fun r hr => by rw [g, u₁.other r hr]) (by rw [g, e12]) (by rw [rd, u₁.rd])
    (by rw [wr, u₁.wr]) (by rw [sp, u₁.sp]) ?_ ?_
  · rw [m, e12, u₁.mem]
    exact saveMem_frame' _ _ _ fun p hp' => in_s s₀ (bmSaved_bound p hp').1
  · intro p hp'
    rw [m, e12, saveMem_saved, u₁.other _ (bmSaved_bound p hp').2.2]
    exact hp'

/-- The registers the loop starts with. -/
theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : ∀ r, r ≠ .r12 → s₁.gpr r = s₀.gpr r)
    (g12 : s₁.gpr .r12 = sc s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp)
    (hf : Frame [scR s₀] s₀.mem s₁.mem) (hsv : Saved s₀ s₁.mem) :
    WP isa (.block bmSetup) s₁ (Inv s₀ 0) := by
  have lt := r_lt hp
  have pos := hp.pos
  refine wp_mov (op2_reg _ _) fun a ua => wp_mov (op2_reg _ _) fun b ub =>
    wp_mov (op2_reg _ _) fun c uc => wp_mov (op2_reg _ _) fun d ud =>
    wp_add (op2_lsl (by decide)) fun e ue => wp_add (op2_lsl (by decide)) fun f uf =>
    wp_sub (op2_imm (by decide)) fun i ui => WP.block_nil ?_
  have hm : i.mem = s₁.mem := by
    rw [ui.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
  have k : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → r ≠ .r12 →
      i.gpr r = s₀.gpr r := fun r h4 h5 h6 h7 h8 h9 h12 => by
    rw [ui.other _ h9, uf.other _ h9, ue.other _ h6, ud.other _ h7, uc.other _ h5, ub.other _ h4,
      ua.other _ h8, g _ h12]
  have hr : rr s₀ = (s₀.gpr .r1).toNat := rfl
  have x1 : d.gpr .r1 = s₀.gpr .r1 := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), g _ (by decide)]
  have e0 : e.gpr .r0 = bP s₀ := by
    rw [ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g _ (by decide)]
  have e1 : e.gpr .r1 = s₀.gpr .r1 := by rw [ue.other _ (by decide), x1]
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hi => absurd hi (by omega), ?_⟩
  · rw [ui.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd, hrd]
  · rw [ui.wr, uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr, hwr]
  · rw [ui.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp, hsp]
  · rw [ui.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.gpr, ua.other _ (by decide),
      g _ (by decide)]
    simp
  · rw [ui.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.gpr, ub.other _ (by decide), ua.other _ (by decide),
      g _ (by decide)]
    simp
  · rw [ui.other _ (by decide), uf.other _ (by decide), ue.gpr, x1, ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g _ (by decide),
      shl32 (by omega)]
    congr 2; omega
  · rw [ui.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide), ud.gpr,
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g12]
  · rw [ui.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.gpr,
      g _ (by decide), Nat.sub_zero]
    exact ofNat_toNat32 _
  · rw [ui.gpr, uf.gpr, e0, e1, shl32 (by omega),
      show (s₀.gpr .r1).toNat * 2 ^ 7 = 128 * rr s₀ by omega, sub32 _ (by omega)]
    rfl
  · intro r hr
    simp only [others, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact k _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · rw [hm]; exact hf.mono (by simp)
  · rw [hm]; exact hsv
  · rw [hm]
    show bytesAt s₁.mem (bA s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 =
      blk (B s₀) (2 * rr s₀ - 1)
    rw [blk_B s₀ (by omega), show 64 * (2 * rr s₀ - 1) = 128 * rr s₀ - 64 by omega]
    exact b_frame hp (hf.mono (by simp)) (by omega)

/-! ## The loop -/

theorem loop_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv s₀ 0 s) : WP isa (.loop (bmBody c) .ne) s (Inv s₀ (rr s₀)) := by
  refine WP.loop (M := isa) (fun n s => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s) ?_ (rr s₀) s
    ⟨0, rfl, hp.pos, h⟩
  rintro n s ⟨k, rfl, hk, hi⟩
  refine WP.mono (body_ok hS hp hk hi) fun s' ⟨hi', hz⟩ => ?_
  have he : isa.eval .ne s' = some (!decide (k + 1 = rr s₀)) := by
    rw [← hz]; exact eval_ne s'
  by_cases hl : k + 1 = rr s₀
  · refine .inl ⟨by rw [he]; simp [hl], ?_⟩
    rwa [hl] at hi'
  · exact .inr ⟨by rw [he]; simp [hl], rr s₀ - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## The epilogue -/

theorem epilogue_eq : bmEpilogue =
    (bmSaved.take 6).map (fun p => Instr.ldr p.1 .r7 p.2) ++ ([.ldr .r7 .r7 88] : List Instr) := rfl

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ (rr s₀) s) :
    WP isa (.block bmEpilogue) s fun s' => s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) := by
  have hs := hp.s_nw
  have hin : ∀ d, d + 4 ≤ 128 → ∀ t : State, t.rd = s.rd → t.wr = s.wr →
      InRegions (t.rd ++ t.wr) (scA s₀ + BitVec.ofNat 64 d) 4 := fun d hd t hr hw => by
    rw [hr, hw, h.rd, h.wr, hp.rd, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ hd)
  rw [epilogue_eq]
  refine restoreList_ok _ s _ (by decide) (fun p hp' => ?_) fun s₁ hl ho hm hrd hwr hsp => ?_
  · have hb := bmSaved_bound p (List.mem_of_mem_take hp')
    rw [h.r7]
    exact ⟨bmSaved_r7 p hp', by omega, by omega, hin _ hb.1 _ rfl rfl⟩
  have e7 : s₁.gpr .r7 = sc s₀ := by rw [ho _ (by decide), h.r7]
  refine wp_ldr (a := scA s₀ + BitVec.ofNat 64 88) (by decide) (by rw [e7, addr_add (by omega)])
    (hin _ (by omega) _ hrd hwr) fun s₂ u₂ => WP.block_nil ?_
  refine ⟨by rw [u₂.mem, hm], by rw [u₂.sp, hsp], fun r hr => ?_⟩
  have sv : ∀ p ∈ bmSaved, s.mem.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1 := h.saved
  have lo : ∀ p ∈ bmSaved.take 6, s₂.gpr p.1 = s₀.gpr p.1 := fun p hp' => by
    rw [u₂.other _ (bmSaved_r7 p hp'), hl p hp', h.r7]
    exact sv p (List.mem_of_mem_take hp')
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lo (.r4, 64) (by decide)
  · exact lo (.r5, 68) (by decide)
  · exact lo (.r6, 72) (by decide)
  · rw [u₂.gpr, hm, sv (.r7, 88) (by decide)]
  · exact lo (.r8, 76) (by decide)
  · exact lo (.r9, 80) (by decide)
  · rw [u₂.other _ (by decide), ho _ (by decide)]; exact h.keep _ (by decide)
  · rw [u₂.other _ (by decide), ho _ (by decide)]; exact h.keep _ (by decide)
  · exact lo (.lr, 84) (by decide)

/-! ## The whole function -/

/-- The output, from the blocks the loop wrote. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ i < rr s₀, bytesAt m (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt m (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)) :
    bytesAt m (yA s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀) := by
  rw [blockMix_eq, show 128 * rr s₀ = 64 * rr s₀ + 64 * rr s₀ by omega, bytesAt_add,
    bytesAt_blocks, bytesAt_blocks]
  congr 1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    exact (h i hi).1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [add_ofNat, ← Nat.mul_add]
    exact (h i hi).2

theorem pre_of {s₀ : State} (h : Proof.Scrypt.blockMixArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  rw [h12] at h2 h3 h4 h6 h9
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem correct {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) :
    WP isa (blockMixWith c) s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Scrypt.blockMixArm.post s₀ s' := by
  unfold blockMixWith
  refine WP.seq ?_
  rw [prologue_eq]
  refine save_ok hp fun s₁ g g12 hrd hwr hsp hf hsv => ?_
  refine WP.mono (setup_ok hp g g12 hrd hwr hsp hf hsv) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (loop_ok hS hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (restore_ok hp h₃) fun s' ⟨hm', hsp', hg'⟩ => ⟨⟨hg', hsp'.trans h₃.sp⟩, ?_⟩
  show bytesAt s'.mem (yA s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀)
  rw [hm']
  exact post_of fun i hi => h₃.done i hi

end VG.Proof.Scrypt.Arm.BlockMix
