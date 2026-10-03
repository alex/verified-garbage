import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
import VerifiedGarbage.Proof.Framework.X86_64.Frame

/-!
# AES-GCM on x86-64: the whole blocks of `seal` and `open` in one call

Untrusted: everything here is checked by Lean. `oneBlocks f` keeps the
length at `W + 192` and computes the number of whole blocks (`ob1_ok`); if
there are any, it sets the arguments (`ob2_ok`), pushes `scratch` and calls
`f` (`vg_aes_gcm_encrypt_blocks` or `_decrypt_blocks`), then keeps the data
left after the whole blocks at `W + 200` and `W + 208` (`ob3_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith ctr32)

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

omit L in
/-- The length kept, and the number of whole blocks. -/
theorem ob1_ok {n : Nat} (hn : n < 2 ^ 64) {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)), .store (at_ .r15 tlenO) .rax, .shift .shr .rax 4,
      .alu .test .rax (.reg .rax)]) s fun s₁ => s₁.gpr .rax = BitVec.ofNat 64 (n / 16) ∧
      s₁.zf = some (decide (n / 16 = 0)) ∧ (∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem.writeW (W + BitVec.ofNat 64 192) (BitVec.ofNat 64 n) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have q₁ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 192 + 8 ≤ 2560 by decide)
  have h4 := shr4 n hn
  have hz := and_self_beq (show n / 16 < 2 ^ 64 by omega)
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, w₁, hlen, h4], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, h4]
  · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, ite_true, h4, hz]
  · intro r hr; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr]
  all_goals simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
    wr_setReg, wr_setFlags, he.r15, hlen]

omit L in
/-- The arguments of the call. -/
theorem ob2_ok {R : Nat} {D : Addr} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hR : RoundsAt s.mem W R) (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D) :
    WP isa (.block (([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++
      ptr .rdx .r14 48 ++ ptr .rcx .r14 16 ++ ([.mov .r8 (.mem (at_ .r15 dataO)), .mov .r9 (.reg .rax)] : List Instr) ++
      ptr .rax .r15 bScrO)) s fun s₂ => s₂.gpr .rdi = Ctx ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧
      s₂.gpr .rdx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48 ∧
      s₂.gpr .rcx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16 ∧ s₂.gpr .r8 = D ∧ s₂.gpr .r9 = s.gpr .rax ∧
      s₂.gpr .rax = W + BitVec.ofNat 64 448 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .rax → s₂.gpr r = s.gpr r) ∧
      s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  have q₁ := he.perm.wR (show 176 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r13, he.r14, he.r15, q₁, q₂, hR.1, hdat], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, he.r13]
  · simp [gpr_setReg, gpr_arithFlags, he.r15, hR.1]
  · simp [gpr_setReg, gpr_arithFlags, he.r14, imm_eq]
  · simp [gpr_setReg, gpr_arithFlags, he.r14, imm_eq]
  · simp [gpr_setReg, gpr_arithFlags, he.r15, hdat]
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags, he.r15, imm_eq, bScrO]
  · intro r a b c d e f g; simp [gpr_setReg, gpr_arithFlags, a, b, c, d, e, f, g]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

omit L in
/-- The data left after the whole blocks, kept. -/
theorem ob3_ok {D : Addr} {n : Nat} (hn : n < 2 ^ 64) {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)), .mov .rcx (.reg .rax), .alu .and .rcx (imm 15),
      .store (at_ .r15 lenO) .rcx, .alu .sub .rax (.reg .rcx), .alu .add .rax (.mem (at_ .r15 dataO)),
      .store (at_ .r15 dataO) .rax]) s fun s₅ =>
      (∀ r, r ≠ .rax → r ≠ .rcx → s₅.gpr r = s.gpr r) ∧
      s₅.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (n / 16)) ∧
      s₅.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n % 16) ∧
      Frame [⟨W + BitVec.ofNat 64 200, 16⟩] s.mem s₅.mem ∧ s₅.rd = s.rd ∧ s₅.wr = s.wr := by
  have q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 200 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 208 + 8 ≤ 2560 by decide)
  have e15 := and15 (BitVec.ofNat 64 n)
  rw [toNat_ofNat_of_lt hn, imm_eq (by decide)] at e15
  have esub : BitVec.ofNat 64 n - BitVec.ofNat 64 (n % 16) = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [ofNat_sub (Nat.mod_le _ _) hn]; congr 1; omega
  have sep : Mem.Sep (W + BitVec.ofNat 64 200) (64 / 8) (W + BitVec.ofNat 64 208) (64 / 8) :=
    Offset.sep _ (.inl (by decide)) (by have := he.perm; omega) (by omega)
  have hdat' : (s.mem.writeW (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 (n % 16))).readW
      (W + BitVec.ofNat 64 200) 64 = D := by rw [Mem.readW_writeW_sep sep (by decide), hdat]
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, q₂, w₁, w₂, hlen, e15, esub, hdat'], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
  · simp [mem_arithFlags, mem_setReg, Mem.readW_writeW_self64, BitVec.add_comm]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_sep (sep_of_disj (Offset.disjoint _ (.inr (by decide)) (by omega) (by omega)))
      (by decide), Mem.readW_writeW_self64]
  · have c : ∀ d, 200 ≤ d → d + 8 ≤ 216 → (⟨W + BitVec.ofNat 64 200, 16⟩ : Region).Contains
        (W + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    simp only [mem_arithFlags, mem_setReg]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))
  all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

omit L in
theorem covers_cons_r {rs ts : List Region} (r : Region) (h : Covers rs ts) : Covers rs (r :: ts) :=
  fun a m hi => by obtain ⟨x, hx, hc⟩ := h a m hi; exact ⟨x, List.mem_cons_of_mem _ hx, hc⟩

/-- What the frame of the call needs. -/
structure ObIn (Ctx W SP : Addr) (R : Nat) (D : Addr) (n q : Nat) (s : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  data : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n
  q_le : 16 * q ≤ n
  t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩
  t_w : (below SP 24).Disjoint ⟨W, 2560⟩
  t_d : (below SP 24).Disjoint ⟨D, n⟩
  sp24 : 24 ≤ SP.toNat
  rdi : s.gpr .rdi = Ctx
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48
  rcx : s.gpr .rcx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16
  r8 : s.gpr .r8 = D
  r9 : s.gpr .r9 = BitVec.ofNat 64 q
  rax : s.gpr .rax = W + BitVec.ofNat 64 448
  rounds : R = 10 ∨ R = 12 ∨ R = 14

/-- The regions the call writes. -/
abbrev obFrame (W SP D : Addr) (q : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩, ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩,
    ⟨D, q * 16⟩, ⟨W + BitVec.ofNat 64 448, 2112⟩, below SP 24]

/-- The call, from the frame's push. -/
theorem ObIn.call {R : Nat} {D : Addr} {n q : Nat} {s : State} (h : ObIn Ctx W SP R D n q s) :
    BlkCall (pushed [.rax] s) Ctx (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)
      (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) D (W + BitVec.ofNat 64 448) R q := by
  have hsp := h.env.rsp
  have psp : (pushed [.rax] s).gpr .rsp = SP - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  have e24 : SP - BitVec.ofNat 64 8 - 16 = SP - BitVec.ofNat 64 24 := by rw [← Offset.sub_add_eq]; rfl
  have hn8 : 8 * [Reg.rax].length ≤ (s.gpr .rsp).toNat := by rw [hsp]; have := h.sp24; simp; omega
  obtain ⟨-, hpj⟩ := pushRegs_mem s [.rax] (by decide) hn8
  have harg : (pushed [.rax] s).mem.readW (SP - BitVec.ofNat 64 8) 64 = W + BitVec.ofNat 64 448 := by
    have := hpj 0 (by decide); rw [hsp] at this; rw [← h.rax]; exact this
  have ww := L.ww
  have sw := L.sw
  have hw := h.data.ok.wrap
  have hq := h.q_le
  have qd : Region.Sub ⟨D, q * 16⟩ ⟨D, n⟩ := Region.sub_prefix (by omega)
  have sS : Region.Sub ⟨W + BitVec.ofNat 64 448, 2112⟩ ⟨W, 2560⟩ := Lay.wSub (by decide)
  have sC : Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ ⟨W, 2560⟩ := by
    rw [add_ofNat_assoc]; exact Lay.wSub (by decide)
  have sY : Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩ ⟨W, 2560⟩ := by
    rw [add_ofNat_assoc]; exact Lay.wSub (by decide)
  have tS : Region.Sub ⟨(pushed [.rax] s).gpr .rsp - 16, 24⟩ (below SP 24) := by
    rw [psp, e24]; exact fun _ h => h
  have toN : ∀ d, d < 2560 → (W + BitVec.ofNat 64 d).toNat = W.toNat + d := fun d hd => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]
  have pc := pushed_gpr [.rax] s (r := .rdi) (by decide)
  refine ⟨by rw [pushed_gpr _ _ (by decide)]; exact h.rdi, by rw [pushed_gpr _ _ (by decide)]; exact h.rsi,
    by rw [pushed_gpr _ _ (by decide)]; exact h.rdx, by rw [pushed_gpr _ _ (by decide)]; exact h.rcx,
    by rw [pushed_gpr _ _ (by decide)]; exact h.r8, by rw [pushed_gpr _ _ (by decide)]; exact h.r9,
    by rw [psp]; exact harg, h.rounds, L.cw, ?_, ?_, by omega, by rw [toN 448 (by decide)]; omega, ?_,
    L.ctx_st (a := 0) (n := 256) (d := 48) (k := 16) (by decide) (by decide) |> fun h => by simpa using h,
    L.ctx_st (a := 0) (n := 256) (d := 16) (k := 16) (by decide) (by decide) |> fun h => by simpa using h,
    h.data.ctx.sub_right qd, (L.cw'.sub_right sS),
    L.st_st (.inr (by decide)) (by decide) (by decide), (h.data.ok.st.sub_right (Lay.stSub (by decide))).symm.sub_right qd,
    L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
    (h.data.ok.st.sub_right (Lay.stSub (by decide))).symm.sub_right qd,
    L.st_w (by decide) (.inr ⟨by decide, by decide⟩), (h.data.ok.w.sub_left qd).sub_right sS,
    h.t_c.sub_left tS, (h.t_w.sub_left tS).sub_right sC, (h.t_w.sub_left tS).sub_right sY,
    (h.t_d.sub_left tS).sub_right qd, (h.t_w.sub_left tS).sub_right sS, ?_, ?_⟩
  · rw [add_ofNat_assoc, toN (16 + 48) (by decide)]; omega
  · rw [add_ofNat_assoc, toN (16 + 16) (by decide)]; omega
  · have e16 : SP - BitVec.ofNat 64 8 - 8 = SP - BitVec.ofNat 64 16 := by rw [← Offset.sub_add_eq]; rfl
    rw [psp, e16]; have := h.sp24
    rw [toNat_sub_ofNat (by omega)]; omega
  · simp only [pushed_rd, pushed_wr, psp, hsp]
    refine covers_cons ?_ (covers_cons ?_ (covers_cons ?_ (covers_cons ?_ (covers_cons ?_ ?_))))
    · exact fun a m hi => by
        obtain ⟨x, hx, hc⟩ := h.env.perm.ctx a m hi
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨x, List.mem_append_left _ hx, hc⟩
        · exact ⟨x, List.mem_append_right _ (List.mem_cons_of_mem _ hx), hc⟩
    · rw [show 8 * [Reg.rax].length = 8 from rfl]
      exact covers_of_mem (List.mem_append_right _ (List.mem_cons_self ..))
    all_goals refine covers_left (Covers.trans ?_ (covers_cons_r _ (Covers.refl _)))
    · rw [add_ofNat_assoc]; exact h.env.perm.wC (by decide)
    · rw [add_ofNat_assoc]; exact h.env.perm.wC (by decide)
    · exact Blocks.covers_prefix h.data.wr (by omega)
    · exact h.env.perm.wC (by decide)
  · simp only [pushed_wr, hsp]
    refine Covers.trans ?_ (covers_cons_r _ (Covers.refl _))
    refine covers_cons ?_ (covers_cons ?_ (covers_cons ?_ ?_))
    · rw [add_ofNat_assoc]; exact h.env.perm.wC (by decide)
    · rw [add_ofNat_assoc]; exact h.env.perm.wC (by decide)
    · exact Blocks.covers_prefix h.data.wr (by omega)
    · exact h.env.perm.wC (by decide)

/-- What the frame's push writes is apart from what the call reads. -/
theorem ObIn.push_eqs {R : Nat} {D : Addr} {n q : Nat} {s : State} (h : ObIn Ctx W SP R D n q s) :
    Frame (obFrame W SP D q) s.mem (pushed [.rax] s).mem ∧
    bytesAt (pushed [.rax] s).mem Ctx (16 * (R + 1)) = bytesAt s.mem Ctx (16 * (R + 1)) ∧
    blockAt (pushed [.rax] s).mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) ∧
    blockAt (pushed [.rax] s).mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) =
      blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) ∧
    blocksAt (pushed [.rax] s).mem D q = blocksAt s.mem D q ∧
    blockAt (pushed [.rax] s).mem (Ctx + 240) = blockAt s.mem (Ctx + 240) := by
  have hsp := h.env.rsp
  have hn8 : 8 * [Reg.rax].length ≤ (s.gpr .rsp).toNat := by rw [hsp]; have := h.sp24; simp; omega
  obtain ⟨hf, -⟩ := pushRegs_mem s [.rax] (by decide) hn8
  have hf' : Frame [below SP 8] s.mem (pushed [.rax] s).mem := by
    have := hf; rw [hsp] at this; exact this
  have b8 : Region.Sub (below SP 8) (below SP 24) := below_sub (by decide) (by decide)
  have hq := h.q_le
  have hRb : 16 * (R + 1) ≤ 256 := by rcases h.rounds with h | h | h <;> subst h <;> decide
  have sC : Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ ⟨W, 2560⟩ := by
    rw [add_ofNat_assoc]; exact Lay.wSub (by decide)
  have sY : Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩ ⟨W, 2560⟩ := by
    rw [add_ofNat_assoc]; exact Lay.wSub (by decide)
  have one : ∀ {r : Region}, (below SP 24).Disjoint r → ∀ r' ∈ [below SP 8], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hd.sub_left b8).symm
  refine ⟨hf'.sub fun r hr => ⟨below SP 24, by simp [obFrame], by simp only [List.mem_singleton] at hr; subst hr; exact b8⟩,
    bytesAt_frame hf' (one (h.t_c.sub_right (Region.sub_prefix hRb))) (by have := L.cw; omega),
    blockAt_frame hf' (one (h.t_w.sub_right sC)), blockAt_frame hf' (one (h.t_w.sub_right sY)),
    blocksAt_frame hf' (one (h.t_d.sub_right (Region.sub_prefix (by omega)))) (by have := h.data.ok.wrap; omega),
    blockAt_frame hf' (one (h.t_c.sub_right (Offset.sub_base (d := 240) _ (by decide))))⟩

/-- The registers, permissions and memory after the frame of a call. -/
theorem ObIn.popped {R : Nat} {D : Addr} {n q : Nat} {s s₃ : State} (h : ObIn Ctx W SP R D n q s)
    (bp : BlkPost (pushed [.rax] s) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)
      (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) D (W + BitVec.ofNat 64 448) q s₃) :
    s₃.gpr .rsp = (pushed [.rax] s).gpr .rsp ∧ s₃.wr = (pushed [.rax] s).wr ∧
    (∀ r ∈ calleeSaved, (popped .rax 1 s₃).gpr r = s.gpr r) ∧ (popped .rax 1 s₃).rd = s.rd ∧
    (popped .rax 1 s₃).wr = s.wr ∧ Frame (obFrame W SP D q) s.mem (popped .rax 1 s₃).mem := by
  have hsp := h.env.rsp
  have psp : (pushed [.rax] s).gpr .rsp = SP - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  have r₃ := bp.saved _ (by decide : Reg.rsp ∈ calleeSaved)
  refine ⟨r₃, bp.wr, fun r hr => ?_, by rw [popped_rd, bp.rd, pushed_rd], by rw [popped_wr, bp.wr, pushed_wr]; rfl, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, psp, hsp]; exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), bp.saved r hr, pushed_gpr _ _ hr']
  · rw [popped_mem]
    refine (ObIn.push_eqs L h).1.trans (bp.frame.sub fun r hr => ?_)
    simp only [BlkCall.wr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [obFrame], fun _ h => h⟩
    · exact ⟨_, by simp [obFrame], fun _ h => h⟩
    · exact ⟨_, by simp [obFrame], fun _ h => h⟩
    · exact ⟨_, by simp [obFrame], fun _ h => h⟩
    · refine ⟨below SP 24, by simp [obFrame], ?_⟩
      have e : SP - BitVec.ofNat 64 8 - BitVec.ofNat 64 16 = SP - BitVec.ofNat 64 24 := by
        rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
      show Region.Sub ⟨(pushed [.rax] s).gpr .rsp - BitVec.ofNat 64 16, 16⟩ _
      rw [psp, e]; exact Region.sub_prefix (by decide)

/-- The frame of the call of `vg_aes_gcm_encrypt_blocks`. -/
theorem obFrameE_ok (v : GcmImpl) {R : Nat} {D : Addr} {n q : Nat} {s : State} (h : ObIn Ctx W SP R D n q s) :
    WP isa (.frame (.push [.rax]) (.call v.callees.enc.name v.callees.enc.code) (.pop .rax 1)) s fun s₄ =>
      (∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r) ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      Frame (obFrame W SP D q) s.mem s₄.mem ∧
      blocksAt s₄.mem D q = ctr32 (aesWith R (bytesAt s.mem Ctx (16 * (R + 1))))
        (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)) (blocksAt s.mem D q) ∧
      blockAt s₄.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
        Nat.repeat Spec.Gcm.inc32 q (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)) ∧
      blockAt s₄.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) = Spec.Gcm.ghashFrom (blockAt s.mem (Ctx + 240))
        (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16)) (blocksAt s₄.mem D q) := by
  have hsp := h.env.rsp
  have hn8 : 8 * [Reg.rax].length ≤ (s.gpr .rsp).toNat := by rw [hsp]; have := h.sp24; simp; omega
  obtain ⟨-, eK, eC, eY, eD, eH⟩ := ObIn.push_eqs L h
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.mono (blkE_call v (ObIn.call L h)) fun s₃ ⟨bp, o₁, o₂, o₃⟩ => ?_)
  obtain ⟨r₃, w₃, cs, rd, wr, fr⟩ := ObIn.popped L h bp
  rw [eK, eC, eD] at o₁
  rw [eC] at o₂
  rw [eH, eY] at o₃
  exact ⟨r₃, w₃, cs, rd, wr, fr, by rw [popped_mem]; exact o₁, by rw [popped_mem]; exact o₂,
    by rw [popped_mem]; exact o₃⟩

/-- The frame of the call of `vg_aes_gcm_decrypt_blocks`. -/
theorem obFrameD_ok (v : GcmImpl) {R : Nat} {D : Addr} {n q : Nat} {s : State} (h : ObIn Ctx W SP R D n q s) :
    WP isa (.frame (.push [.rax]) (.call v.callees.dec.name v.callees.dec.code) (.pop .rax 1)) s fun s₄ =>
      (∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r) ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      Frame (obFrame W SP D q) s.mem s₄.mem ∧
      blocksAt s₄.mem D q = ctr32 (aesWith R (bytesAt s.mem Ctx (16 * (R + 1))))
        (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)) (blocksAt s.mem D q) ∧
      blockAt s₄.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
        Nat.repeat Spec.Gcm.inc32 q (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)) ∧
      blockAt s₄.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) = Spec.Gcm.ghashFrom (blockAt s.mem (Ctx + 240))
        (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16)) (blocksAt s.mem D q) := by
  have hsp := h.env.rsp
  have hn8 : 8 * [Reg.rax].length ≤ (s.gpr .rsp).toNat := by rw [hsp]; have := h.sp24; simp; omega
  obtain ⟨-, eK, eC, eY, eD, eH⟩ := ObIn.push_eqs L h
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.mono (blkD_call v (ObIn.call L h)) fun s₃ ⟨bp, o₁, o₂, o₃⟩ => ?_)
  obtain ⟨r₃, w₃, cs, rd, wr, fr⟩ := ObIn.popped L h bp
  rw [eK, eC, eD] at o₁
  rw [eC] at o₂
  rw [eH, eY, eD] at o₃
  exact ⟨r₃, w₃, cs, rd, wr, fr, by rw [popped_mem]; exact o₁, by rw [popped_mem]; exact o₂,
    by rw [popped_mem]; exact o₃⟩

/-- What `oneBlocks` needs: the state of `seal` or `open` after `oneAad`. -/
structure ObPre (Ctx W SP : Addr) (R : Nat) (D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  rounds : RoundsAt s.mem W R
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  data : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n
  t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩
  t_w : (below SP 24).Disjoint ⟨W, 2560⟩
  t_d : (below SP 24).Disjoint ⟨D, n⟩
  sp24 : 24 ≤ SP.toNat

/-- What `oneBlocks` leaves, but its result: the data left kept, and the
regions written. -/
structure ObPost (Ctx W SP : Addr) (D : Addr) (n : Nat) (s s' : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame (⟨W + BitVec.ofNat 64 192, 24⟩ :: obFrame W SP D (n / 16)) s.mem s'.mem
  tlen : s'.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n
  dat : s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (n / 16))
  len : s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n % 16)

/-- The slots of `W` that `oneBlocks` reads are apart from what its call writes. -/
theorem ob_slots {D : Addr} {n q : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hq : q * 16 ≤ n)
    (t_w : (below SP 24).Disjoint ⟨W, 2560⟩) {d : Nat} (h₁ : 176 ≤ d) (h₂ : d + 8 ≤ 240) :
    ∀ r ∈ obFrame W SP D q, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [add_ofNat_assoc]; exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · rw [add_ofNat_assoc]; exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · exact (hD.sub_left (Region.sub_prefix hq)).symm.sub_left (Lay.wSub (by omega)) |>.symm |> fun h => h.symm
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (t_w.sub_right (Lay.wSub (by omega))).symm

end

end VG.Proof.AesGcm.X86_64
