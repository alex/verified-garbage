import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Cmac.Frame

/-!
# AES-GCM on x86-64: padding the buffer (`flush`) and the lengths block (`lens`)

Untrusted: everything here is checked by Lean. `flush yo` pads the `rbx`
buffered bytes with zeros in `T` and absorbs them (`flush_ok`); `lens yo`
stores the lengths block of `rbx` and `rbp` bytes in `T` and absorbs it
(`lens_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ghash blocks zeros padLen)
open VG.Proof.Gcm (Absorbed lensBlock)

/-- The regions `flush` and `lens` write. -/
abbrev tFrame (St W SP : Addr) (yo : Nat) : List Region :=
  [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩, below SP 8]

theorem gh_tFrame {St W SP : Addr} {yo : Nat} {m m' : Mem}
    (h : Frame [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩, below SP 8] m m') :
    Frame (tFrame St W SP yo) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

/-- Zeroing `T`: two stores. -/
theorem zeroT_ok (s : State) {W : Addr} (h15 : s.gpr .r15 = W)
    (hw : Covers [⟨W, 2560⟩] s.wr) :
    ∃ s', runBlock isa [.mov32 .rax (imm 0), .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax] s =
        some s' ∧
      s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 96) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w₁ := in_off hw (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₂ := in_off hw (show 104 + 8 ≤ 2560 by decide) (by decide)
  refine ⟨_, by xrun [h15, w₁, w₂], ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, add_ofNat_assoc]; rfl
  · intro r hr; simp [gpr_setReg, hr]
  all_goals rfl

/-- The 16 bytes after zeroing. -/
theorem zeroT_bytes (m : Mem) (p : Addr) :
    bytesAt ((m.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)) p 16 = zeros 16 := by
  rw [Cmac.bytesAt_store2, Cmac.le8_zero]; rfl

theorem zeroT_frame (m : Mem) (p : Addr) :
    Frame [⟨p, 16⟩] m ((m.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)) :=
  Cmac.frame_store2 _ _ _

/-- The bytes at `p` after writing `xs` there: `xs`, then what was there. -/
theorem bytesAt_writeBytes_prefix (m : Mem) (p : Addr) (xs : List Byte) {n : Nat} (hn : xs.length ≤ n)
    (h : n < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p n = xs ++ bytesAt m (p + BitVec.ofNat 64 xs.length) (n - xs.length) := by
  rw [show n = xs.length + (n - xs.length) by omega, bytesAt_add, bytesAt_writeBytes_self _ _ _ (by omega),
    Nat.add_sub_cancel_left]
  congr 1
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [writeBytes, BitVec.add_assoc, Offset.add_sub_cancel_left, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := xs.length) (by omega), Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  simp [show ¬xs.length + i < xs.length by omega]

/-- Before `flush yo` (or `lens yo`): GHASH has absorbed `x`. -/
structure FlIn (Ctx St W SP : Addr) (yo : Nat) (H : Block) (x : List Byte) (s : State) : Prop where
  env : Env Ctx St W SP s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H

/-- After `flush yo`: GHASH has absorbed `x`, from `m₀`. -/
structure FlOut (Ctx St W SP : Addr) (yo : Nat) (H : Block) (x₀ x : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x
  frame : Frame (tFrame St W SP yo) m₀ s.mem

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

theorem ctx_tFrame : ∀ r ∈ tFrame St W SP yo, (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

/-- `flush yo`. -/
theorem flush_ok {H : Block} {x : List Byte} {s : State} (h : FlIn Ctx St W SP yo H x s)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 (x.length % 16)) :
    WP isa (flush v.callees yo) s (FlOut Ctx St W SP yo H x (x ++ zeros (padLen x.length)) s.mem) := by
  have he := h.env
  have hlt := Nat.mod_lt x.length (show 16 > 0 by decide)
  obtain ⟨s₁, run₁, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbx hbx (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁
  refine WP.ite (decide (x.length % 16 = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : x.length % 16 = 0 := by simpa using ht
    rw [Proof.Gcm.padLen_of_mod h0]
    exact WP.block_nil ⟨he₁, by rw [hm₁]; exact h.hH, fun ha => by rw [hm₁]; simpa [zeros] using ha,
      by rw [hm₁]; exact Frame.refl _ _⟩
  · have h0 : x.length % 16 ≠ 0 := by simpa using hf
    have h13 := he₁.r13; have h14 := he₁.r14; have h15 := he₁.r15
    obtain ⟨s₂, run₂, hm₂, hdi, hsi, hcx, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        ([.mov32 .rax (imm 0), .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax] ++
          ptr .rdi .r15 tO ++ ptr .rsi .r14 32 ++ [.mov .rcx (.reg .rbx)]) s₁ = some s₂ ∧
        s₂.mem = (s.mem.writeW (W + BitVec.ofNat 64 96) (0 : BitVec 64)).writeW
          (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
        s₂.gpr .rdi = W + BitVec.ofNat 64 96 ∧ s₂.gpr .rsi = St + BitVec.ofNat 64 32 ∧
        s₂.gpr .rcx = BitVec.ofNat 64 (x.length % 16) ∧
        (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧
        s₂.wr = s.wr := by
      have w₁ := in_off he₁.perm.w (show 96 + 8 ≤ 2560 by decide) (by decide)
      have w₂ := in_off he₁.perm.w (show 104 + 8 ≤ 2560 by decide) (by decide)
      refine ⟨_, by xrun [h15, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [mem_setReg, add_ofNat_assoc, hm₁]; rfl
      · simp [gpr_setReg, h15]
      · simp [gpr_setReg, h14]
      · simp [gpr_setReg, hg₁, hbx]
      · intro r a b c d; simp [gpr_setReg, a, b, c, d, hg₁]
      · simp [rd_setReg, rd_arithFlags, hrd₁]
      · simp [wr_setReg, wr_arithFlags, hwr₁]
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide) (by decide))
      hrd₂ hwr₂
    have lp : LoopPre s₂ (St + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 96) (x.length % 16) :=
      ⟨hsi, hdi, hcx, by omega, by omega, covers_left (he₂.perm.stC (by omega)), he₂.perm.wC (by omega),
        L.st_w (by omega) (.inr ⟨by decide, by omega⟩)⟩
    refine WP.seq (WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ?_)
    have he₃ : Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
    -- The memory so far.
    have fz : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s₂.mem := by rw [hm₂]; exact zeroT_frame _ _
    have hB₂ : bytesAt s₂.mem (St + BitVec.ofNat 64 32) (x.length % 16) =
        bytesAt s.mem (St + BitVec.ofNat 64 32) (x.length % 16) :=
      bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩))
        (by omega)
    have hlen := length_bytesAt s₂.mem (St + BitVec.ofNat 64 32) (x.length % 16)
    have fc : Frame [⟨W + BitVec.ofNat 64 96, x.length % 16⟩] s₂.mem s₃.mem := by
      rw [hm₃]; exact writeBytes_frame' _ hlen
    have f₃ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s₃.mem :=
      fz.trans (fc.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
    have hT : bytesAt s₃.mem (W + BitVec.ofNat 64 96) 16 =
        bytesAt s.mem (St + BitVec.ofNat 64 32) (x.length % 16) ++ zeros (16 - x.length % 16) := by
      rw [hm₃, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by decide), hlen, hB₂]
      refine congrArg (_ ++ ·) ?_
      have := zeroT_bytes s.mem (W + BitVec.ofNat 64 96)
      rw [← hm₂, show (16 : Nat) = x.length % 16 + (16 - x.length % 16) by omega, bytesAt_add] at this
      have e := congrArg (List.drop (x.length % 16)) this
      rw [List.drop_left' (length_bytesAt _ _ _)] at e
      rw [e, show x.length % 16 + (16 - x.length % 16) = 16 by omega, Spec.Gcm.zeros, List.drop_replicate]
      rfl
    have hY₃ : blockAt s₃.mem (St + BitVec.ofNat 64 yo) = blockAt s.mem (St + BitVec.ofNat 64 yo) :=
      blockAt_frame f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
      rw [blockAt_frame f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide), h.hH]
    refine WP.mono (ghash1_ok v L hyo he₃ .r15 96 (.inr rfl) (P := W + BitVec.ofNat 64 96) (by rw [he₃.r15])
      (by decide) (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (L.w_w (.inl (by decide)) (by decide) (by decide))
      (L.stk_w (by decide)) (covers_left (he₃.perm.wC (by decide)))) fun s₄ g => ?_
    refine ⟨g.env he₃, ?_, ?_, ?_⟩
    · rw [blockAt_frame g.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.ctx_st (by decide) (by omega)
        · exact L.ctx_w (by decide) (by decide)
        · exact (L.stk_ctx (by decide)).symm), hH₃]
    · intro ha
      refine Proof.Gcm.absorb_pad ha h0 (B := bytesAt s₃.mem (W + BitVec.ofNat 64 96) 16) hT ?_
      rw [g.out, hY₃, hH₃]; rfl
    · refine (f₃.sub fun r hr => ?_).trans (gh_tFrame g.frame)
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

omit L hyo in
theorem bswap64_eq : X86_64.bswap64 = byteRev64 := rfl

omit L hyo in
/-- `[8 r]₆₄` into `W + o`. -/
theorem be64Store_ok (s : State) (r : Reg) (_hr : r ≠ .rax) (o : Nat) (ho : o + 8 ≤ 2560) (h15 : s.gpr .r15 = W)
    (hw : Covers [⟨W, 2560⟩] s.wr) :
    ∃ s', runBlock isa (be64Store r o) s = some s' ∧
      s'.mem = s.mem.writeW (W + BitVec.ofNat 64 o) (byteRev64 (BitVec.ofNat 64 (8 * (s.gpr r).toNat))) ∧
      (∀ r', r' ≠ .rax → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w₁ := in_off hw ho (by decide)
  refine ⟨_, by simp only [be64Store]; xrun [h15, w₁], ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, times8_val, bswap64_eq]
  · intro r' hr'; simp [gpr_setReg, hr']
  all_goals rfl

/-- The lengths block of `rbx` and `rbp` bytes, absorbed. -/
theorem lens_ok {H : Block} {s : State} (he : Env Ctx St W SP s)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) :
    WP isa (lens v.callees yo) s fun s' => Env Ctx St W SP s' ∧
      blockAt s'.mem (Ctx + BitVec.ofNat 64 240) = H ∧
      blockAt s'.mem (St + BitVec.ofNat 64 yo) = ghashFrom H (blockAt s.mem (St + BitVec.ofNat 64 yo))
        [Spec.Gcm.ofBytes (lensBlock (s.gpr .rbx).toNat (s.gpr .rbp).toNat)] ∧
      Frame (tFrame St W SP yo) s.mem s'.mem := by
  obtain ⟨s₁, run₁, hm₁, hg₁, hrd₁, hwr₁⟩ := be64Store_ok s .rbx (by decide) tO (by decide) he.r15 he.perm.w
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hrd₁ hwr₁
  obtain ⟨s₂, run₂, hm₂, hg₂, hrd₂, hwr₂⟩ := be64Store_ok s₁ .rbp (by decide) (tO + 8) (by decide) he₁.r15
    he₁.perm.w
  have he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩))
  have hm : s₂.mem = (s.mem.writeW (W + BitVec.ofNat 64 96) (byteRev64 (BitVec.ofNat 64 (8 * (s.gpr .rbx).toNat)))).writeW
      (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (byteRev64 (BitVec.ofNat 64 (8 * (s.gpr .rbp).toNat))) := by
    rw [hm₂, hm₁, hg₁ _ (by decide), add_ofNat_assoc]; rfl
  have fT : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s₂.mem := by rw [hm]; exact Cmac.frame_store2 _ _ _
  have hT : bytesAt s₂.mem (W + BitVec.ofNat 64 96) 16 = lensBlock (s.gpr .rbx).toNat (s.gpr .rbp).toNat := by
    rw [hm, Cmac.bytesAt_store2, Proof.Gcm.le8_byteRev64, Proof.Gcm.le8_byteRev64, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Proof.Gcm.be64_mod, Proof.Gcm.be64_mod]; rfl
  have hY₂ : blockAt s₂.mem (St + BitVec.ofNat 64 yo) = blockAt s.mem (St + BitVec.ofNat 64 yo) :=
    blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  have hH₂ : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide), hH]
  refine WP.mono (ghash1_ok v L hyo he₂ .r15 96 (.inr rfl) (P := W + BitVec.ofNat 64 96) (by rw [he₂.r15])
    (by decide) (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (L.w_w (.inl (by decide)) (by decide) (by decide))
    (L.stk_w (by decide)) (covers_left (he₂.perm.wC (by decide)))) fun s₃ g => ?_
  refine ⟨g.env he₂, ?_, ?_, ?_⟩
  · rw [blockAt_frame g.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.ctx_st (by decide) (by omega)
      · exact L.ctx_w (by decide) (by decide)
      · exact (L.stk_ctx (by decide)).symm), hH₂]
  · have hb : blockAt s₂.mem (W + BitVec.ofNat 64 96) =
        Spec.Gcm.ofBytes (lensBlock (s.gpr .rbx).toNat (s.gpr .rbp).toNat) := by rw [blockAt, hT]
    rw [g.out, hY₂, hH₂, hb]
  · refine (fT.sub fun r hr => ?_).trans (gh_tFrame g.frame)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

end

end VG.Proof.AesGcm.X86_64
