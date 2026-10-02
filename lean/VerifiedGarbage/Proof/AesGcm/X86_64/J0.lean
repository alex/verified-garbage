import VerifiedGarbage.Proof.AesGcm.X86_64.Tag
import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Cmac.Dbl32

/-!
# AES-GCM on x86-64: the pre-counter block (`j0`)

Untrusted: everything here is checked by Lean. `j0` writes `J₀` for the
`rbp`-byte nonce at `r12` to the state: its words and `0x00000001` for a
12-byte nonce (`j012_ok`), and otherwise GHASH of the nonce padded with
zeros and the lengths block, with `absorb`, `flush` and `lens` on the
accumulator at the state's first block (`j0hash_ok`). `initState` then
zeroes the accumulator and writes the first counter block `inc₃₂(J₀)`
(`initState_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32)
open VG.Proof.Gcm (Absorbed lensBlock)
open VG.Proof.Cmac (le4 store4)

theorem inc32_words (a b c d : BitVec 32) : inc32 (a ++ b ++ c ++ d) = a ++ b ++ c ++ (d + 1) := by
  have h₁ : (a ++ b ++ c ++ d).extractLsb' 32 96 = a ++ b ++ c := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    simp only [show ¬ (32 + i < 32) by omega, ite_false, show 32 + i - 32 = i by omega]
  have h₂ : (a ++ b ++ c ++ d).extractLsb' 0 32 = d := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]; simp [hi]
  simp only [inc32, h₁, h₂]

theorem ww32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (show x.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt this]

theorem bswap32_eq : X86_64.bswap32 = byteRev32 := rfl

theorem le4_one : le4 (BitVec.ofNat 32 0x01000000) = [0, 0, 0, 1] := by decide

/-- A block from the bytes of its four little-endian words. -/
theorem ofBytes_le4 (a b c d : BitVec 32) :
    ofBytes (le4 a ++ le4 b ++ le4 c ++ le4 d) = byteRev32 a ++ byteRev32 b ++ byteRev32 c ++ byteRev32 d := by
  have h := Cmac.le4_rev4 (byteRev32 a) (byteRev32 b) (byteRev32 c) (byteRev32 d)
  rw [Cmac.byteRev32_byteRev32, Cmac.byteRev32_byteRev32, Cmac.byteRev32_byteRev32,
    Cmac.byteRev32_byteRev32] at h
  rw [h, Cmac.ofBytes_toBytes]

/-- The regions `j0` writes. -/
abbrev j0Frame (St W SP : Addr) : List Region :=
  [⟨St, 80⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 512, 256⟩,
    below SP 8]

/-- Before `j0`: the `n`-byte nonce at `Np`. -/
structure J0In (Ctx St W SP : Addr) (H : Block) (Np : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  r12 : s.gpr .r12 = Np
  rbp : s.gpr .rbp = BitVec.ofNat 64 n
  data : DataOk St W SP s Np n

/-- `J₀` written, from `m₀`. -/
structure J0Mid (Ctx St W SP : Addr) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem St = Spec.Gcm.j0 H iv
  frame : Frame (j0Frame St W SP) m₀ s.mem

/-- After `j0`: `J₀`, the accumulator zeroed and the first counter block. -/
structure J0Out (Ctx St W SP : Addr) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem St = Spec.Gcm.j0 H iv
  y : blockAt s.mem (St + BitVec.ofNat 64 16) = 0
  cb : blockAt s.mem (St + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  frame : Frame (j0Frame St W SP) m₀ s.mem

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

theorem ctx_j0Frame : ∀ r ∈ j0Frame St W SP, (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.cs.sub_left (Lay.ctxSub (by decide))
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

omit L in
theorem st_j0Frame {m m' : Mem} {d k : Nat} (h : Frame [⟨St + BitVec.ofNat 64 d, k⟩] m m') (hk : d + k ≤ 80) :
    Frame (j0Frame St W SP) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Lay.stSub hk⟩

/-- `J₀` of a 12-byte nonce. -/
theorem j012_ok {H : Block} {Np : Addr} {s : State} (h : J0In Ctx St W SP H Np 12 s) :
    WP isa (.block j012) s (J0Mid Ctx St W SP H (bytesAt s.mem Np 12) s.mem) := by
  have he := h.env
  have h14 := he.r14
  have hd := h.data
  have r₀ := in_off hd.rd (show 0 + 4 ≤ 12 by decide) (by decide)
  have r₁ := in_off hd.rd (show 4 + 4 ≤ 12 by decide) (by decide)
  have r₂ := in_off hd.rd (show 8 + 4 ≤ 12 by decide) (by decide)
  have w₀ := he.perm.stW (show 0 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 4 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 8 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 12 + 4 ≤ 80 by decide)
  have h12 := h.r12
  obtain ⟨s', run, hm, hg, hrd, hwr⟩ : ∃ s', runBlock isa j012 s = some s' ∧
      s'.mem = store4 s.mem St (s.mem.readW Np 32) (s.mem.readW (Np + BitVec.ofNat 64 4) 32)
        (s.mem.readW (Np + BitVec.ofNat 64 8) 32) (BitVec.ofNat 32 0x01000000) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by simp only [j012]; xrun [h12, h14, r₀, r₁, r₂, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, ww32, store4, h12, h14,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    all_goals rfl
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have f : Frame [⟨St + BitVec.ofNat 64 0, 16⟩] s.mem s'.mem := by
    rw [hm]; simpa using Cmac.frame_store4 (m := s.mem) St _ _ _ _
  refine ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide) (by decide)) hrd hwr,
    ?_, ?_, st_j0Frame f (by decide)⟩
  · rw [blockAt_frame f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide), h.hH]
  · have hb : bytesAt s.mem Np 12 = bytesAt s.mem Np 4 ++ bytesAt s.mem (Np + BitVec.ofNat 64 4) 4 ++
        bytesAt s.mem (Np + BitVec.ofNat 64 8) 4 := by
      rw [show (12 : Nat) = 4 + 8 from rfl, bytesAt_add, show (8 : Nat) = 4 + 4 from rfl, bytesAt_add,
        add_ofNat_assoc, List.append_assoc]
    rw [Proof.Gcm.j0_12 _ (length_bytesAt _ _ _), blockAt, hm, Cmac.bytesAt_store4, Cmac.le4_readW,
      Cmac.le4_readW, Cmac.le4_readW, le4_one, hb]

/-- The first counter block, and the accumulator zeroed. -/
theorem initState_ok {H : Block} {iv : List Byte} {m₀ : Mem} {s : State} (h : J0Mid Ctx St W SP H iv m₀ s) :
    WP isa (.block initState) s (J0Out Ctx St W SP H iv m₀) := by
  have he := h.env
  have h14 := he.r14
  have r₀ := he.perm.stR (show 0 + 4 ≤ 80 by decide)
  have r₁ := he.perm.stR (show 4 + 4 ≤ 80 by decide)
  have r₂ := he.perm.stR (show 8 + 4 ≤ 80 by decide)
  have r₃ := he.perm.stR (show 12 + 4 ≤ 80 by decide)
  have w₀ := he.perm.stW (show 48 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 52 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 56 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 60 + 4 ≤ 80 by decide)
  have z₀ := he.perm.stW (show 16 + 8 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 24 + 8 ≤ 80 by decide)
  generalize hw : s.mem.readW (St + BitVec.ofNat 64 12) 32 = w
  have split : initState =
      [.mov32 .rax (.mem (at_ .r14 0)), .mov32 .rcx (.mem (at_ .r14 4)), .mov32 .rdx (.mem (at_ .r14 8)),
        .mov32 .rsi (.mem (at_ .r14 12)), .bswap32 .rsi, .alu32 .add .rsi (imm 1), .bswap32 .rsi] ++
      [.store32 (at_ .r14 48) .rax, .store32 (at_ .r14 52) .rcx, .store32 (at_ .r14 56) .rdx,
        .store32 (at_ .r14 60) .rsi, .mov32 .rax (imm 0), .store (at_ .r14 16) .rax, .store (at_ .r14 24) .rax] := rfl
  obtain ⟨s₁, run₁, ax, cx, dx, si, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov32 .rax (.mem (at_ .r14 0)), .mov32 .rcx (.mem (at_ .r14 4)), .mov32 .rdx (.mem (at_ .r14 8)),
        .mov32 .rsi (.mem (at_ .r14 12)), .bswap32 .rsi, .alu32 .add .rsi (imm 1), .bswap32 .rsi] s = some s₁ ∧
      s₁.gpr .rax = (s.mem.readW St 32).setWidth 64 ∧
      s₁.gpr .rcx = (s.mem.readW (St + BitVec.ofNat 64 4) 32).setWidth 64 ∧
      s₁.gpr .rdx = (s.mem.readW (St + BitVec.ofNat 64 8) 32).setWidth 64 ∧
      s₁.gpr .rsi = (byteRev32 (byteRev32 w + 1)).setWidth 64 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h14, r₀, r₁, r₂, r₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, BitVec.add_zero]
    · simp [gpr_setReg, gpr_arithFlags]
    · simp [gpr_setReg, gpr_arithFlags]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ww32, bswap32_eq, hw]; rfl
    · intro r a b c d; simp [gpr_setReg, gpr_arithFlags, a, b, c, d]
    all_goals rfl
  have h14' : s₁.gpr .r14 = St := by rw [hg₁ _ (by decide) (by decide) (by decide) (by decide), h14]
  obtain ⟨s', run, hm, hg, hrd, hwr⟩ : ∃ s', runBlock isa
      [.store32 (at_ .r14 48) .rax, .store32 (at_ .r14 52) .rcx, .store32 (at_ .r14 56) .rdx,
        .store32 (at_ .r14 60) .rsi, .mov32 .rax (imm 0), .store (at_ .r14 16) .rax, .store (at_ .r14 24) .rax] s₁ =
        some s' ∧
      s'.mem = ((store4 s.mem (St + BitVec.ofNat 64 48) (s.mem.readW St 32) (s.mem.readW (St + BitVec.ofNat 64 4) 32)
        (s.mem.readW (St + BitVec.ofNat 64 8) 32) (byteRev32 (byteRev32 w + 1))).writeW (St + BitVec.ofNat 64 16)
          (0 : BitVec 64)).writeW (St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    rw [← hwr₁] at w₀ w₁ w₂ w₃ z₀ z₁
    refine ⟨_, by xrun [h14', w₀, w₁, w₂, w₃, z₀, z₁], ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, ww32, store4, ax, cx, dx, si, hm₁,
        add_ofNat_assoc]
      rfl
    · intro r a b c d; simp [gpr_setReg, a, b, c, d, hg₁]
    · simp [rd_setReg, hrd₁]
    · simp [wr_setReg, hwr₁]
  rw [split]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s', run, ?_⟩⟩)
  have f₄ := Cmac.frame_store4 (m := s.mem) (St + BitVec.ofNat 64 48) (s.mem.readW St 32)
    (s.mem.readW (St + BitVec.ofNat 64 4) 32) (s.mem.readW (St + BitVec.ofNat 64 8) 32) (byteRev32 (byteRev32 w + 1))
  have fz := zeroT_frame (store4 s.mem (St + BitVec.ofNat 64 48) (s.mem.readW St 32)
    (s.mem.readW (St + BitVec.ofNat 64 4) 32) (s.mem.readW (St + BitVec.ofNat 64 8) 32) (byteRev32 (byteRev32 w + 1)))
    (St + BitVec.ofNat 64 16)
  rw [← hm] at fz
  have dz : (⟨St + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 16, 16⟩ :=
    L.st_st (.inr (by decide)) (by decide) (by decide)
  have ff : Frame [⟨St + BitVec.ofNat 64 0, 80⟩] s.mem s'.mem := by
    refine (f₄.sub fun r hr => ?_).trans (fz.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;>
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hJ : blockAt s'.mem St = blockAt s.mem St := by
    rw [blockAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using L.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)),
      blockAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using L.st_st (a := 0) (n := 16) (d := 48) (k := 16) (.inl (by decide)) (by decide) (by decide))]
  refine ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide) (by decide)) hrd hwr,
    ?_, by rw [hJ, h.j0], ?_, ?_, h.frame.trans (st_j0Frame ff (by decide))⟩
  · rw [blockAt_frame ff (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide)), h.hH]
  · rw [blockAt, hm, zeroT_bytes]; decide
  · rw [blockAt, bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dz) (by decide),
      Cmac.bytesAt_store4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, ← h.j0, blockAt,
      Cmac.ofBytes_rev4, ← Cmac.le4_readW s.mem St, ← Cmac.le4_readW, ← Cmac.le4_readW, ofBytes_le4, hw,
      Cmac.byteRev32_byteRev32, inc32_words]

end

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

omit L in
theorem abs_j0Frame {m m' : Mem} (h : Frame (absFrame St W SP 0) m m') : Frame (j0Frame St W SP) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

omit L in
theorem t_j0Frame {m m' : Mem} (h : Frame (tFrame St W SP 0) m m') : Frame (j0Frame St W SP) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- `aux` is apart from what `absorb 0`, `flush 0` and `lens 0` write. -/
theorem aux_absFrame : ∀ r ∈ absFrame St W SP 0, (⟨W + BitVec.ofNat 64 216, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem aux_tFrame : ∀ r ∈ tFrame St W SP 0, (⟨W + BitVec.ofNat 64 216, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

/-- `J₀` of a nonce of any length but 12: GHASH of the nonce padded and of
the lengths block. -/
theorem j0hash_ok {H : Block} {Np : Addr} {n : Nat} {s : State} (h : J0In Ctx St W SP H Np n s) (hn : n ≠ 12) :
    WP isa (j0hash v.callees) s (J0Mid Ctx St W SP H (bytesAt s.mem Np n) s.mem) := by
  have he := h.env
  have hd := h.data
  have hlt := hd.lt
  have h14 := he.r14; have h15 := he.r15
  have z₀ := he.perm.stW (show 0 + 8 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 8 + 8 ≤ 80 by decide)
  have wa := he.perm.wW (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hm₁, hbx₁, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov32 .rax (imm 0), .store (at_ .r14 0) .rax,
      .store (at_ .r14 8) .rax, .store (at_ .r15 auxO) .rbp, .mov32 .rbx (imm 0)] s = some s₁ ∧
      s₁.mem = ((s.mem.writeW (St + BitVec.ofNat 64 0) (0 : BitVec 64)).writeW
        (St + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 216)
        (BitVec.ofNat 64 n) ∧
      s₁.gpr .rbx = BitVec.ofNat 64 0 ∧ (∀ r, r ≠ .rax → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h14, h15, z₀, z₁, wa], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, h.rbp, add_ofNat_assoc]; rfl
    · simp [gpr_setReg]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  have fz := zeroT_frame s.mem (St + BitVec.ofNat 64 0)
  have fa : Frame [⟨W + BitVec.ofNat 64 216, 8⟩] ((s.mem.writeW (St + BitVec.ofNat 64 0) (0 : BitVec 64)).writeW
      (St + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) (0 : BitVec 64)) s₁.mem := by
    rw [hm₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have f₁ : Frame [⟨St + BitVec.ofNat 64 0, 16⟩, ⟨W + BitVec.ofNat 64 216, 8⟩] s.mem s₁.mem :=
    (fz.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp).trans
      (fa.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)
  have dD : ∀ r ∈ [(⟨St + BitVec.ofNat 64 0, 16⟩ : Region), ⟨W + BitVec.ofNat 64 216, 8⟩],
      (⟨Np, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd.st.sub_right (Lay.stSub (by decide))
    · exact hd.w.sub_right (Lay.wSub (by decide))
  have dH : ∀ r ∈ [(⟨St + BitVec.ofNat 64 0, 16⟩ : Region), ⟨W + BitVec.ofNat 64 216, 8⟩],
      (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.ctx_st (by decide) (by decide)
    · exact L.ctx_w (by decide) (by decide)
  have hiv : bytesAt s₁.mem Np n = bytesAt s.mem Np n := bytesAt_frame f₁ dD (by omega)
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = H := by rw [blockAt_frame f₁ dH, h.hH]
  have hY₁ : blockAt s₁.mem (St + BitVec.ofNat 64 0) = 0 := by
    rw [blockAt, bytesAt_frame fa (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.st_w (a := 0) (n := 16) (d := 216) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)) (by decide),
      zeroT_bytes]
    decide
  have hai : AbsIn Ctx St W SP 0 H [] Np n s₁ :=
    ⟨he₁, by rw [hg₁ _ (by decide) (by decide), h.r12], by rw [hg₁ _ (by decide) (by decide), h.rbp],
      by rw [hbx₁]; rfl, hd.of_eq hrd₁ hwr₁, hH₁, Proof.Gcm.absorbed_nil H hY₁⟩
  refine WP.seq (WP.mono (absorb_ok v L (yo := 0) (.inl rfl) hai) fun s₂ ho => ?_)
  rw [List.nil_append, hiv] at ho
  have he₂ := ho.env
  have hn₂ : s₂.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n := by
    rw [ho.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (aux_absFrame L) (by decide),
      hm₁, Mem.readW_writeW_self64]
  have hH₂ : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ho.frame (ctx_absFrame L (.inl rfl)), hH₁]
  have ra := he₂.perm.wR (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 auxO)),
      .alu .and .rbx (imm 15)] s₂ = some s₃ ∧
      s₃.gpr .rbx = BitVec.ofNat 64 (n % 16) ∧ (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    have hand := and15 (BitVec.ofNat 64 n)
    rw [toNat_ofNat_of_lt hlt, imm_eq (by decide)] at hand
    refine ⟨_, by xrun [he₂.r15, ra], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hn₂, hand]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ : Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  have hfi : FlIn Ctx St W SP 0 H (bytesAt s.mem Np n) s₃ :=
    ⟨he₃, by rw [hm₃, hH₂], by rw [hm₃]; exact ho.abs⟩
  refine WP.seq (WP.mono (flush_ok v L (yo := 0) (.inl rfl) hfi (by rw [hbx₃, length_bytesAt])) fun s₄ hf => ?_)
  have he₄ := hf.env
  have hn₄ : s₄.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n := by
    rw [hf.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (aux_tFrame L) (by decide),
      hm₃, hn₂]
  have ra₄ := he₄.perm.wR (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₅, run₅, hbx₅, hbp₅, hg₅, hm₅, hrd₅, hwr₅⟩ : ∃ s₅, runBlock isa [.mov32 .rbx (imm 0),
      .mov .rbp (.mem (at_ .r15 auxO))] s₄ = some s₅ ∧
      s₅.gpr .rbx = BitVec.ofNat 64 0 ∧ s₅.gpr .rbp = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by xrun [he₄.r15, ra₄], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg, hn₄]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ : Env Ctx St W SP s₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide)) hrd₅ hwr₅
  refine WP.mono (lens_ok v L (yo := 0) (.inl rfl) (H := H) he₅ (by rw [hm₅]; exact hf.hH)) fun s₆ ⟨he₆, hH₆, hY₆, f₆⟩ => ?_
  refine ⟨he₆, hH₆, ?_, ?_⟩
  · have hw := (hf.abs).whole_eq (by
      simp only [List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod n)
    rw [Proof.Gcm.j0_eq H (by rw [length_bytesAt]; exact hn), length_bytesAt, ← hw, ← hm₅,
      hbx₅, hbp₅, toNat_ofNat_of_lt (by decide), toNat_ofNat_of_lt hlt] at *
    simpa using hY₆
  · have g₁ : Frame (j0Frame St W SP) s.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    have g₄ := t_j0Frame hf.frame
    have g₆ := t_j0Frame f₆
    rw [hm₃] at g₄
    rw [hm₅] at g₆
    exact ((g₁.trans (abs_j0Frame ho.frame)).trans g₄).trans g₆

/-- `j0`: the streaming state's `J₀`, accumulator and first counter block. -/
theorem j0_ok {H : Block} {Np : Addr} {n : Nat} {s : State} (h : J0In Ctx St W SP H Np n s) :
    WP isa (j0 v.callees) s (J0Out Ctx St W SP H (bytesAt s.mem Np n) s.mem) := by
  have hlt := h.data.lt
  obtain ⟨s₁, run₁, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.alu .cmp .rbp (imm 12)] s = some s₁ ∧
      s₁.zf = some (decide (n = 12)) ∧ s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
    · rw [zf_arithFlags, h.rbp]
      exact congrArg some (sub_beq hlt (by decide))
    all_goals rfl
  have h₁ : J0In Ctx St W SP H Np n s₁ :=
    ⟨h.env.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁, by rw [hm₁]; exact h.hH, by rw [hg₁]; exact h.r12,
      by rw [hg₁]; exact h.rbp, h.data.of_eq hrd₁ hwr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  rw [← hm₁]
  refine WP.seq (WP.ite (decide (n = 12)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_))
  · have h12 : n = 12 := by simpa using ht
    subst h12
    exact WP.mono (j012_ok L h₁) fun _ hm => initState_ok L hm
  · exact WP.mono (j0hash_ok v L h₁ (by simpa using hf)) fun _ hm => initState_ok L hm

end

end VG.Proof.AesGcm.X86_64
