import VerifiedGarbage.Proof.Scrypt.AArch64.BlockMix

/-!
# scryptBlockMix on AArch64: the whole function

Untrusted: everything here is checked by Lean. The prologue saves our
caller's `x19`–`x24` in `scratch` and sets up the loop's registers; the loop
runs the `r` pairs; the epilogue restores the registers. Around all of it, a
frame saves `x30`, which the calls replace.
-/

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blk blockMix)
open VG.Proof.Scrypt (yAt xBefore blockMix_eq flatMap_congr)
open VG.Proof.Md5.AArch64.Stream (Upd Mupd wp_mov wp_add wp_addImm wp_subImm wp_ldr wp_str
  eval_nonzero ofNat_beq_zero readW_writeW_save write_frame_bytes)
open VG.Proof.Scrypt.X86_64.BlockMix (toNat_ofNat_lt add_ofNat InRegions.of_mem frame_bytesAt
  bytesAt_add bytesAt_blocks bytesAt_congr)

/-! ## The prologue -/

/-- The memory after the prologue's stores. -/
def saveMem (s₀ : State) : Mem :=
  (((((s₀.mem.writeW (sc s₀ + BitVec.ofNat 64 64) (s₀.gpr .x19)).writeW
    (sc s₀ + BitVec.ofNat 64 72) (s₀.gpr .x20)).writeW (sc s₀ + BitVec.ofNat 64 80)
    (s₀.gpr .x21)).writeW (sc s₀ + BitVec.ofNat 64 88) (s₀.gpr .x23)).writeW
    (sc s₀ + BitVec.ofNat 64 96) (s₀.gpr .x24)).writeW (sc s₀ + BitVec.ofNat 64 104)
    (s₀.gpr .x22)

set_option simprocs false in
theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := by
  intro p hp
  simp only [bmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [saveMem, Mem.readW_writeW_self64, readW_writeW_save]

theorem saveMem_frame (s₀ : State) : Frame [scR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 8 ≤ 128 → (scR s₀).Contains (sc s₀ + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => in_s s₀ hd
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 64 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 72 (by omega))).writeW (List.mem_singleton_self _) _
    (c 80 (by omega))).writeW (List.mem_singleton_self _) _ (c 88 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 96 (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c 104 (by omega))

theorem prologue_eq : bmPrologue =
    [.str .x .x19 .x4 64, .str .x .x20 .x4 72, .str .x .x21 .x4 80, .str .x .x23 .x4 88,
     .str .x .x24 .x4 96, .str .x .x22 .x4 104] ++
    [mov .x23 .x1, mov .x19 .x0, mov .x20 .x2, mov .x22 .x4,
     .lsl .x .x9 .x1 6, .add .x .x21 .x2 .x9,
     .lsl .x .x9 .x1 7, .add .x .x24 .x0 .x9, .subImm .x .x24 .x24 64] := rfl

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.sp = s₀.sp →
      s₁.mem = saveMem s₀ → WP isa (.block rest) s₁ Q) :
    WP isa (.block ([.str .x .x19 .x4 64, .str .x .x20 .x4 72, .str .x .x21 .x4 80,
      .str .x .x23 .x4 88, .str .x .x24 .x4 96, .str .x .x22 .x4 104] ++ rest)) s₀ Q := by
  have o : ∀ d, d + 8 ≤ 128 → ∀ s : State, s.wr = s₀.wr →
      InRegions s.wr (sc s₀ + BitVec.ofNat 64 d) 8 := fun d hd s hw => by
    rw [hw, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ hd)
  simp only [List.cons_append, List.nil_append]
  refine wp_str (by decide) rfl (o 64 (by omega) _ rfl) fun s1 u1 => ?_
  refine wp_str (by decide) (by rw [u1.gpr]) (o 72 (by omega) _ u1.wr) fun s2 u2 => ?_
  refine wp_str (by decide) (by rw [u2.gpr, u1.gpr]) (o 80 (by omega) _ (u2.wr.trans u1.wr))
    fun s3 u3 => ?_
  refine wp_str (by decide) (by rw [u3.gpr, u2.gpr, u1.gpr])
    (o 88 (by omega) _ (u3.wr.trans (u2.wr.trans u1.wr))) fun s4 u4 => ?_
  refine wp_str (by decide) (by rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr])
    (o 96 (by omega) _ (u4.wr.trans (u3.wr.trans (u2.wr.trans u1.wr)))) fun s5 u5 => ?_
  refine wp_str (by decide) (by rw [u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr])
    (o 104 (by omega) _ (u5.wr.trans (u4.wr.trans (u3.wr.trans (u2.wr.trans u1.wr)))))
    fun s6 u6 => ?_
  exact k s6 (by rw [u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr])
    (by rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd])
    (u6.wr.trans (u5.wr.trans (u4.wr.trans (u3.wr.trans (u2.wr.trans u1.wr)))))
    (by rw [u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp])
    (by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
        rfl)

theorem shl_eq {x : BitVec 64} {n : Nat} (h : x.toNat * 2 ^ n < 2 ^ 64) :
    x <<< n = BitVec.ofNat 64 (x.toNat * 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, toNat_ofNat_lt h, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem add_sub64 (a : Addr) {n : Nat} (h : 64 ≤ n) :
    a + BitVec.ofNat 64 n - BitVec.ofNat 64 64 = a + BitVec.ofNat 64 (n - 64) := by
  rw [show n = (n - 64) + 64 by omega, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel,
    BitVec.add_sub_cancel]

/-- The registers the loop starts with. -/
theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp) (hm : s₁.mem = saveMem s₀) :
    WP isa (.block [mov .x23 .x1, mov .x19 .x0, mov .x20 .x2, mov .x22 .x4,
     .lsl .x .x9 .x1 6, .add .x .x21 .x2 .x9,
     .lsl .x .x9 .x1 7, .add .x .x24 .x0 .x9, .subImm .x .x24 .x24 64]) s₁ (Inv s₀ 0) := by
  have lt : 128 * (s₀.gpr .x1).toNat < 2 ^ 64 := r_lt hp
  have pos := hp.pos
  refine wp_mov fun a ua => wp_mov fun b ub => wp_mov fun c uc => wp_mov fun d ud =>
    wp_lsl (by decide) fun e ue => wp_add fun f uf => wp_lsl (by decide) fun g' ug =>
    wp_add fun h uh => wp_subImm (by decide) fun i ui => WP.block_nil ?_
  have x1 : d.gpr .x1 = s₀.gpr .x1 := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), g]
  have e9 : e.gpr .x9 = BitVec.ofNat 64 (64 * rr s₀) := by
    rw [ue.gpr, x1, shl_eq (by simp; omega), Nat.mul_comm]; rfl
  have g9 : g'.gpr .x9 = BitVec.ofNat 64 (128 * rr s₀) := by
    rw [ug.gpr, uf.other _ (by decide), ue.other _ (by decide), x1, shl_eq (by simp; omega),
      Nat.mul_comm]; rfl
  have hm' : i.mem = saveMem s₀ := by
    rw [ui.mem, uh.mem, ug.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  have k : ∀ r, r ≠ .x9 → r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 →
      i.gpr r = s₀.gpr r := fun r h9 h19 h20 h21 h22 h23 h24 => by
    rw [ui.other _ h24, uh.other _ h24, ug.other _ h9, uf.other _ h21, ue.other _ h9,
      ud.other _ h22, uc.other _ h20, ub.other _ h19, ua.other _ h23, g]
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega), ?_⟩
  · rw [ui.rd, uh.rd, ug.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd, hrd]
  · rw [ui.wr, uh.wr, ug.wr, uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr, hwr]
  · rw [ui.sp, uh.sp, ug.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp, hsp]
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.gpr, ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), uc.gpr,
      ub.other _ (by decide), ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide), uf.gpr, e9,
      ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g]
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.gpr, g]
    simp
  · rw [ui.gpr, uh.gpr, g9, ug.other _ (by decide), uf.other _ (by decide),
      ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g, add_sub64 _ (by omega)]
    rfl
  · intro r hr
    have : r ≠ .x9 ∧ r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x24 := by
      simp only [others, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨h9, h19, h20, h21, h22, h23, h24⟩ := this
    exact k r h9 h19 h20 h21 h22 h23 h24
  · rw [hm']; exact (saveMem_frame s₀).mono (by simp)
  · rw [hm']; exact saveMem_saved s₀
  · rw [hm']
    show bytesAt (saveMem s₀) (bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 =
      blk (B s₀) (2 * rr s₀ - 1)
    rw [blk_B s₀ (by omega), show 64 * (2 * rr s₀ - 1) = 128 * rr s₀ - 64 by omega]
    refine frame_bytesAt (saveMem_frame s₀) (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub hp (by omega))

/-! ## The loop -/

theorem loop_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv s₀ 0 s) : WP isa (.loop (bmBody c) (.nonzero .x .x23)) s (Inv s₀ (rr s₀)) := by
  have lt := r_lt hp
  refine WP.loop (M := isa) (fun n s => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s) ?_ (rr s₀) s
    ⟨0, rfl, hp.pos, h⟩
  rintro n s ⟨k, rfl, hk, hi⟩
  refine WP.mono (body_ok hS hp hk hi) fun s' hi' => ?_
  have hz : isa.eval (.nonzero .x .x23) s' = some (decide (rr s₀ - (k + 1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x .x23) s' = _
    rw [eval_nonzero, hi'.x23, bne, ofNat_beq_zero (by omega)]
    simp
  by_cases hl : rr s₀ - (k + 1) = 0
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [show k + 1 = rr s₀ by omega] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl], rr s₀ - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ (rr s₀) s) :
    WP isa (.block bmEpilogue) s fun s' => s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) := by
  have hin : ∀ d, d + 8 ≤ 128 → ∀ t : State, t.rd = s.rd → t.wr = s.wr →
      InRegions (t.rd ++ t.wr) (sc s₀ + BitVec.ofNat 64 d) 8 := fun d hd t hr hw => by
    rw [hr, hw, h.rd, h.wr, hp.rd, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ hd)
  have sv : ∀ p ∈ bmSaved, s.mem.readW (sc s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1 := h.saved
  simp only [bmEpilogue, bmSaved, List.map_cons, List.map_nil]
  refine wp_ldr (by decide) (by rw [h.x22]) (hin 64 (by omega) _ rfl rfl) fun a ua => ?_
  refine wp_ldr (by decide) (by rw [ua.other _ (by decide), h.x22])
    (hin 72 (by omega) _ ua.rd ua.wr) fun b ub => ?_
  refine wp_ldr (by decide) (by rw [ub.other _ (by decide), ua.other _ (by decide), h.x22])
    (hin 80 (by omega) _ (ub.rd.trans ua.rd) (ub.wr.trans ua.wr)) fun c uc => ?_
  refine wp_ldr (by decide) (by rw [uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.x22])
    (hin 88 (by omega) _ (uc.rd.trans (ub.rd.trans ua.rd)) (uc.wr.trans (ub.wr.trans ua.wr)))
    fun d ud => ?_
  refine wp_ldr (by decide) (by rw [ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), h.x22])
    (hin 96 (by omega) _ (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd)))
      (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr)))) fun e ue => ?_
  refine wp_ldr (by decide) (by rw [ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.x22])
    (hin 104 (by omega) _ (ue.rd.trans (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd))))
      (ue.wr.trans (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr))))) fun f uf => WP.block_nil ?_
  have hm : f.mem = s.mem := by rw [uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
  refine ⟨hm, by rw [uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp], fun r hr h30 => ?_⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.gpr, sv (.x19, 64) (by simp [bmSaved])]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.gpr, ua.mem, sv (.x20, 72) (by simp [bmSaved])]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.gpr, ub.mem, ua.mem, sv (.x21, 80) (by simp [bmSaved])]
  · rw [uf.gpr, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, sv (.x22, 104) (by simp [bmSaved])]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.mem, ub.mem, ua.mem,
      sv (.x23, 88) (by simp [bmSaved])]
  · rw [uf.other _ (by decide), ue.gpr, ud.mem, uc.mem, ub.mem, ua.mem,
      sv (.x24, 96) (by simp [bmSaved])]
  all_goals first
    | exact absurd rfl h30
    | rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
        uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide)]
      exact h.keep _ (by simp [others])

/-! ## The body of the frame -/

/-- The output, from the blocks the loop wrote. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ i < rr s₀, bytesAt m (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt m (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)) :
    bytesAt m (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀) := by
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

theorem correctMain {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) :
    WP isa (blockMixMain c) s₀ fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ bytesAt s'.mem (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀) := by
  unfold blockMixMain
  refine WP.seq ?_
  rw [prologue_eq]
  refine save_ok hp fun s₁ g hrd hwr hsp hm => ?_
  refine WP.mono (setup_ok hp g hrd hwr hsp hm) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (loop_ok hS hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (restore_ok hp h₃) fun s' ⟨hm', hsp', hg'⟩ => ⟨hg', hsp'.trans h₃.sp, ?_⟩
  rw [hm']
  exact post_of fun i hi => h₃.done i hi

/-! ## The whole function -/

/-- The frame's 16 bytes are free. -/
structure Stack (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  b : Region.Disjoint ⟨s₀.sp - 16, 16⟩ (bR s₀)
  y : Region.Disjoint ⟨s₀.sp - 16, 16⟩ (yR s₀)
  s : Region.Disjoint ⟨s₀.sp - 16, 16⟩ (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Scrypt.blockMixAArch64.pre s₀) : Pre s₀ ∧ Stack s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  rw [h13] at h2 h3 h4 h8 h11
  exact ⟨⟨h1, h2, h3, h4, h5, h10, h11, h12, h13, h14⟩, ⟨h6, h7, h8, h9⟩⟩

/-- The state the body starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct {c : Prog isa} (hS : SalsaSpec c)
    (hd : 16 * (blockMixMain c).fdepth + 16 < 2 ^ 64) {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) :
    WP isa (blockMixWith c) s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Scrypt.blockMixAArch64.post s₀ s' := by
  have hpi : Pre (inner s₀) := ⟨hp.rd, hp.wr, hp.y_s, hp.b_y, hp.b_s, hp.b_nw, hp.y_nw, hp.s_nw,
    hp.x3, hp.pos⟩
  refine WP.frameReg hs.sp16 (fun R hR => ?_) (WP.mono (correctMain hS hpi) fun s' ⟨hk, hsp, hpost⟩ => ?_) hd
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hs.y
    · exact hs.s
  · refine ⟨⟨fun r hr => ?_, rfl⟩, ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · have e : B (inner s₀) = bytesAt s₀.mem (bP s₀) (128 * rr s₀) :=
        bytesAt_congr fun i hi => by
          have hi' : i < 128 * rr s₀ := hi
          exact write_frame_bytes (R := bR s₀) hs.b (by have := r_lt hp; simp only; omega)
            (by simp only; omega)
      show bytesAt s'.mem (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (bytesAt s₀.mem (bP s₀) (128 * rr s₀))
      rw [← e]
      exact hpost

end VG.Proof.Scrypt.AArch64.BlockMix
