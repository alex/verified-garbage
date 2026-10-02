import VerifiedGarbage.Proof.AesGcm.AArch64.Absorb
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Cmac.Frame

/-!
# AES-GCM on AArch64: padding (`flush`) and the lengths block (`lens`)

Untrusted: everything here is checked by Lean. `padSeg yo src` copies the
`x25` bytes at `x12` (which `src` sets) into `T`, zeroed first, and sets up
the call of `vg_ghash` on it, or on no block if there are none
(`padSeg_ok`); the call absorbs it (`padCall_ok`). `flush yo` pads the
buffered bytes so (`flush_ok`). `lens yo ra rb` stores the lengths block
`[8 ra]₆₄ ‖ [8 rb]₆₄` in `T` and absorbs it (`lensSeg_ok`, `lensCall_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ghash blocks zeros padLen ofBytes)
open VG.Proof.Gcm (Absorbed lensBlock)

/-- The regions `flush` and `lens` write. -/
abbrev tFrame (St W : Addr) (yo : Nat) : List Region :=
  [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩]

/-- The 16 bytes after zeroing. -/
theorem zeroT_bytes (m : Mem) (p : Addr) :
    bytesAt ((m.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)) p 16 = zeros 16 := by
  rw [Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl

/-- Whether there are bytes to pad: the blocks of the call. -/
abbrev padBlocks (o : Nat) : Nat := if o = 0 then 0 else 1

/-- Before the call of a padding: the `o` bytes at `P` (in `m₀`) padded with
zeros in `T`. -/
structure Pad1 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (yo o : Nat) (P : Addr) (m₀ : Mem) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  x25 : s.gpr .x25 = BitVec.ofNat 64 o
  call : GhCall s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) (W + BitVec.ofNat 64 96)
    (W + BitVec.ofNat 64 512) (padBlocks o)
  tb : bytesAt s.mem (W + BitVec.ofNat 64 96) 16 = bytesAt m₀ P o ++ zeros (16 - o)
  frame : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] m₀ s.mem

/-- After a call of `vg_ghash` on `T` (or on nothing), from `m₀`. -/
structure TOut (Ctx St W SP : Addr) (k : Reg → BitVec 64) (yo o : Nat) (Y : Block) (m₀ : Mem)
    (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  x25 : s.gpr .x25 = BitVec.ofNat 64 o
  out : blockAt s.mem (St + BitVec.ofNat 64 yo) = Y
  frame : Frame (tFrame St W yo) m₀ s.mem

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

theorem ctx_tFrame : ∀ r ∈ tFrame St W yo, (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)

/-- Padding the `o` bytes at `P`, which `src` points `x12` at. -/
theorem padSeg_ok {k : Reg → BitVec 64} {src : List Instr} {P : Addr} {o : Nat} {s : State}
    (he : Env Ctx St W SP s) (hk : Kept k s) (h25 : s.gpr .x25 = BitVec.ofNat 64 o) (ho : o < 16)
    (hsrc : ∃ s₁, runBlock isa src s = some s₁ ∧ s₁.gpr .x12 = P ∧ Regs [.x12] s s₁)
    (hP : Covers [⟨P, o⟩] (s.rd ++ s.wr)) (hPW : (⟨P, o⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 96, 16⟩) :
    WP isa (padSeg yo src) s (Pad1 Ctx St W SP k yo o P s.mem) := by
  obtain ⟨s₁, run₁, x12₁, r₁⟩ := hsrc
  have he₁ := he.of_regs r₁
  have w₁ := he₁.perm.wW (show 96 + 8 ≤ 2560 by decide)
  have w₂ := he₁.perm.wW (show 104 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, m₂, x11₂, x13₂, x12₂, r₂⟩ : ∃ s₂, runBlock isa [imm .x9 0, .str .x .x9 .x19 tO,
      .str .x .x9 .x19 (tO + 8), ptr .x11 .x19 tO, mov .x13 .x25] s₁ = some s₂ ∧
      s₂.mem = (s.mem.writeW (W + BitVec.ofNat 64 96) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₂.gpr .x11 = W + BitVec.ofNat 64 96 ∧ s₂.gpr .x13 = BitVec.ofNat 64 o ∧ s₂.gpr .x12 = P ∧
      Others [.x9, .x11, .x13] s₁ s₂ ∧ s₂.sp = s₁.sp ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [he₁.x19, w₁, w₂], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, r₁.mem, add_ofNat_assoc]; rfl
    · simp [gpr_write, he₁.x19]
    · simp [gpr_write, r₁.others .x25 (by decide), h25]
    · simp [gpr_write, x12₁]
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩))
  obtain ⟨og₂, sp₂, rd₂, wr₂⟩ := r₂
  have lp : LoopPre s₂ P (W + BitVec.ofNat 64 96) o := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [rd₂, wr₂, r₁.rd, r₁.wr]; exact hP
    · rw [wr₂, r₁.wr]; exact he.perm.wC (by omega)
    · exact hPW.sub_right (Region.sub_prefix (by omega))
  refine WP.seq (WP.mono (copy_ok s₂ x12₂ x11₂ x13₂ lp) fun s₃ ⟨m₃, g₃, sp₃, rd₃, wr₃⟩ => ?_)
  have gg₃ : ∀ r, r ∉ [Reg.x12] ++ [.x9, .x11, .x13] ++ loopRegs → s₃.gpr r = s.gpr r := fun r hr => by
    rw [g₃ r (fun h' => hr (List.mem_append_right _ h')),
      og₂ r (fun h' => hr (List.mem_append_left _ (List.mem_append_right _ h'))),
      r₁.others r (fun h' => hr (List.mem_append_left _ (List.mem_append_left _ h')))]
  -- The blocks of the call.
  have ev : isa.eval (.zero .x .x25) s₃ = some (decide (o = 0)) :=
    eval_zero (by rw [gg₃ _ (by decide), h25]) (by omega)
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => s₄.gpr .x3 = BitVec.ofNat 64 (padBlocks o) ∧ Regs [.x3] s₃ s₄)
    (WP.ite (decide (o = 0)) ev (fun ht => ?_) (fun hf => ?_)) fun s₄ ⟨x3₄, r₄⟩ => ?_)
  · have h0 : o = 0 := by simpa using ht
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'; exact ⟨by simp [gpr_write, padBlocks, h0], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · have h0 : o ≠ 0 := by simpa using hf
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'; exact ⟨by simp [gpr_write, padBlocks, h0], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  have gg₄ : ∀ r, r ∉ [Reg.x12] ++ [.x9, .x11, .x13] ++ loopRegs ++ [.x3] → s₄.gpr r = s.gpr r := fun r hr => by
    rw [r₄.others r (fun h' => hr (List.mem_append_right _ h')), gg₃ r (fun h' => hr (List.mem_append_left _ h'))]
  obtain ⟨s₅, run₅, x0₅, x1₅, x4₅, x2₅, r₅⟩ : ∃ s₅, runBlock isa (ghArgs yo ++ [ptr .x2 .x19 tO]) s₄ = some s₅ ∧
      s₅.gpr .x0 = Ctx + BitVec.ofNat 64 240 ∧ s₅.gpr .x1 = St + BitVec.ofNat 64 yo ∧
      s₅.gpr .x4 = W + BitVec.ofNat 64 512 ∧ s₅.gpr .x2 = W + BitVec.ofNat 64 96 ∧
      Regs [.x0, .x1, .x4, .x2] s₄ s₅ := by
    have hyo' : yo < 4096 := by omega
    refine ⟨_, by rw [ghArgs_eq]; arun [hyo'], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, gg₄ .x21 (by decide), he.x21]
    · simp [gpr_write, gg₄ .x20 (by decide), he.x20]
    · simp [gpr_write, gg₄ .x19 (by decide), he.x19]
    · simp [gpr_write, gg₄ .x19 (by decide), he.x19]
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have ggA : ∀ r, r ∉ [Reg.x12] ++ [.x9, .x11, .x13] ++ loopRegs ++ [.x3] ++ [.x0, .x1, .x4, .x2] →
      s₅.gpr r = s.gpr r := fun r hr => by
    rw [r₅.others r (fun h' => hr (List.mem_append_right _ h')), gg₄ r (fun h' => hr (List.mem_append_left _ h'))]
  have hm₅ : s₅.mem = writeBytes s₂.mem (W + BitVec.ofNat 64 96) (bytesAt s₂.mem P o) := by
    rw [r₅.mem, r₄.mem, m₃]
  have hsp : s₅.sp = s.sp := by rw [r₅.sp, r₄.sp, sp₃, sp₂, r₁.sp]
  have hrd : s₅.rd = s.rd := by rw [r₅.rd, r₄.rd, rd₃, rd₂, r₁.rd]
  have hwr : s₅.wr = s.wr := by rw [r₅.wr, r₄.wr, wr₃, wr₂, r₁.wr]
  have he₅ : Env Ctx St W SP s₅ := he.keep (fun r hr => ggA r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) hsp hrd hwr
  have fz : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s₂.mem := by rw [m₂]; exact Proof.Cmac.frame_store2 _ _ _
  have hPo : bytesAt s₂.mem P o = bytesAt s.mem P o :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hPW) (by omega)
  have hlen := length_bytesAt s₂.mem P o
  refine ⟨he₅, hk.of_eq fun r hr => ggA r (by
      simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    by rw [ggA _ (by decide), h25], ?_, ?_, ?_⟩
  · have hnb : padBlocks o ≤ 1 := by simp only [padBlocks]; split <;> omega
    refine ghCall_of L hyo he₅ x0₅ x1₅ x2₅ (by rw [r₅.others _ (by decide), x3₄]) x4₅ (by omega)
      (L.st_w (by omega) (.inr ⟨by decide, by omega⟩)) (L.w_w (.inl (by omega)) (by omega) (by decide))
      (covers_left (he₅.perm.wC (by omega)))
  · rw [hm₅, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by decide), hlen, hPo]
    congr 1
    have := zeroT_bytes s.mem (W + BitVec.ofNat 64 96)
    rw [← m₂, show (16 : Nat) = o + (16 - o) by omega, bytesAt_add] at this
    have e := congrArg (List.drop o) this
    rw [List.drop_left' (length_bytesAt _ _ _)] at e
    rw [e, show o + (16 - o) = 16 by omega, Spec.Gcm.zeros, List.drop_replicate]
    rfl
  · rw [hm₅]
    exact fz.trans ((writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)

/-- The call after a padding: `T` absorbed, if there were bytes. -/
theorem padCall_ok (v : GcmImpl) {k : Reg → BitVec 64} {o : Nat} {P : Addr} {m₀ : Mem} {s : State}
    (h : Pad1 Ctx St W SP k yo o P m₀ s) :
    WP isa (ghCall v.callees) s (TOut Ctx St W SP k yo o
      (ghashFrom (blockAt m₀ (Ctx + BitVec.ofNat 64 240)) (blockAt m₀ (St + BitVec.ofNat 64 yo))
        (if o = 0 then [] else [ofBytes (bytesAt m₀ P o ++ zeros (16 - o))])) m₀) := by
  refine WP.mono (gh_call v.gh h.call) fun s' g => ?_
  have hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = blockAt m₀ (Ctx + BitVec.ofNat 64 240) :=
    blockAt_frame h.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  have hY : blockAt s.mem (St + BitVec.ofNat 64 yo) = blockAt m₀ (St + BitVec.ofNat 64 yo) :=
    blockAt_frame h.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  refine ⟨g.env h.env, h.kept.of_saved g.saved, by rw [g.saved _ (by decide) (by decide), h.x25], ?_, ?_⟩
  · rw [g.out, hH, hY]
    by_cases h0 : o = 0
    · simp only [padBlocks, h0, ↓reduceIte, blocksAt_zero]
    · simp only [padBlocks, h0, ↓reduceIte, blocksAt_one, blockAt, h.tb]
  · refine (h.frame.sub fun r hr => ?_).trans (g.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-- `flush yo`: the buffer, of `o = len(x) mod 16` bytes, padded and absorbed. -/
theorem flush_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {x : List Byte} {o : Nat} {s : State}
    (he : Env Ctx St W SP s) (hk : Kept k s) (h25 : s.gpr .x25 = BitVec.ofNat 64 o) (ho : x.length % 16 = o)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) :
    WP isa (flush v.callees yo) s fun s' => TOut Ctx St W SP k yo o (blockAt s'.mem (St + BitVec.ofNat 64 yo))
        s.mem s' ∧ blockAt s'.mem (Ctx + BitVec.ofNat 64 240) = H ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x →
        Absorbed s'.mem (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H (x ++ zeros (padLen x.length))) := by
  have hlt : o < 16 := by rw [← ho]; exact Nat.mod_lt _ (by decide)
  refine WP.seq (WP.mono (padSeg_ok L hyo (P := St + BitVec.ofNat 64 32) he hk h25 hlt
    (by refine ⟨_, by arun [], ?_⟩; exact ⟨by simp [gpr_write, he.x20], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩)
    (covers_left (he.perm.stC (by omega))) (L.st_w (by omega) (.inr ⟨by decide, by decide⟩))) fun s₁ h₁ => ?_)
  refine WP.mono (padCall_ok L hyo v h₁) fun s₂ h₂ => ⟨{ h₂ with out := rfl }, ?_, fun ha => ?_⟩
  · rw [blockAt_frame h₂.frame (ctx_tFrame L hyo), hH]
  · have hB : bytesAt s₂.mem (St + BitVec.ofNat 64 32) o = bytesAt s.mem (St + BitVec.ofNat 64 32) o :=
      bytesAt_frame h₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.st_st (.inr (by omega)) (by omega) (by omega)
        · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
        · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (by omega)
    by_cases h0 : o = 0
    · rw [Proof.Gcm.padLen_of_mod (by omega), Spec.Gcm.zeros, List.replicate_zero, List.append_nil]
      refine ha.congr ?_ (by rw [ho]; exact hB)
      rw [h₂.out]; simp only [h0, ↓reduceIte, Proof.Gcm.ghashFrom_nil]
    · refine Proof.Gcm.absorb_pad ha (by omega) (B := bytesAt s.mem (St + BitVec.ofNat 64 32) o ++ zeros (16 - o))
        (by rw [ho]) ?_
      rw [h₂.out, hH]; simp only [h0, ↓reduceIte]

omit L hyo in
theorem rev64_eq : AArch64.rev64 = byteRev64 := rfl

omit L hyo in
/-- The 8 bytes of `[8 r]₆₄`. -/
theorem le8_lens (x : BitVec 64) : Proof.Cmac.le8 (AArch64.rev64 (x <<< 3)) = Spec.Gcm.be64 (8 * x.toNat) := by
  rw [rev64_eq, Proof.Gcm.le8_byteRev64, lsl3_eq, BitVec.toNat_ofNat, Proof.Gcm.be64_mod]

/-- Before the call of `lens yo ra rb`: the lengths block in `T`. -/
structure Lens1 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (yo o : Nat) (a b : Nat) (m₀ : Mem) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  x25 : s.gpr .x25 = BitVec.ofNat 64 o
  call : GhCall s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) (W + BitVec.ofNat 64 96)
    (W + BitVec.ofNat 64 512) 1
  tb : bytesAt s.mem (W + BitVec.ofNat 64 96) 16 = lensBlock a b
  frame : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] m₀ s.mem

theorem lensSeg_ok {k : Reg → BitVec 64} {o : Nat} {ra rb : Reg} {s : State} (he : Env Ctx St W SP s)
    (hk : Kept k s) (h25 : s.gpr .x25 = BitVec.ofNat 64 o)
    (hrb : rb ≠ .x9) :
    WP isa (.block (lensSeg yo ra rb)) s
      (Lens1 Ctx St W SP k yo o (s.gpr ra).toNat (s.gpr rb).toNat s.mem) := by
  have w₁ := he.perm.wW (show 96 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 104 + 8 ≤ 2560 by decide)
  have hyo' : yo < 4096 := by omega
  obtain ⟨s₁, run₁, m₁, x3₁, x0₁, x1₁, x4₁, x2₁, r₁⟩ : ∃ s₁, runBlock isa (lensSeg yo ra rb) s = some s₁ ∧
      s₁.mem = (s.mem.writeW (W + BitVec.ofNat 64 96) (AArch64.rev64 (s.gpr ra <<< 3))).writeW
        (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (AArch64.rev64 (s.gpr rb <<< 3)) ∧
      s₁.gpr .x3 = BitVec.ofNat 64 1 ∧
      s₁.gpr .x0 = Ctx + BitVec.ofNat 64 240 ∧ s₁.gpr .x1 = St + BitVec.ofNat 64 yo ∧
      s₁.gpr .x4 = W + BitVec.ofNat 64 512 ∧ s₁.gpr .x2 = W + BitVec.ofNat 64 96 ∧
      Others [.x9, .x3, .x0, .x1, .x4, .x2] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by simp only [lensSeg, ghArgs]; arun [he.x19, w₁, w₂, hyo', hrb], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, add_ofNat_assoc]
    · simp [gpr_write]
    · simp [gpr_write, he.x21]
    · simp [gpr_write, he.x20]
    · simp [gpr_write, he.x19]
    · simp [gpr_write, he.x19]
  obtain ⟨og, sp₁, rd₁, wr₁⟩ := r₁
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => og r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  refine ⟨he₁, hk.of_others og, by rw [og _ (by decide), h25], ?_, ?_, ?_⟩
  · exact ghCall_of L hyo he₁ x0₁ x1₁ x2₁ x3₁ x4₁ (by decide)
      (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (L.w_w (.inl (by decide)) (by decide) (by decide))
      (covers_left (he₁.perm.wC (by decide)))
  · rw [m₁, Proof.Cmac.bytesAt_store2, le8_lens, le8_lens]; rfl
  · rw [m₁]; exact Proof.Cmac.frame_store2 _ _ _

/-- The call of `lens`: the lengths block absorbed. -/
theorem lensCall_ok (v : GcmImpl) {k : Reg → BitVec 64} {o a b : Nat} {m₀ : Mem} {s : State}
    (h : Lens1 Ctx St W SP k yo o a b m₀ s) :
    WP isa (ghCall v.callees) s (TOut Ctx St W SP k yo o
      (ghashFrom (blockAt m₀ (Ctx + BitVec.ofNat 64 240)) (blockAt m₀ (St + BitVec.ofNat 64 yo))
        [ofBytes (lensBlock a b)]) m₀) := by
  refine WP.mono (gh_call v.gh h.call) fun s' g => ?_
  have hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = blockAt m₀ (Ctx + BitVec.ofNat 64 240) :=
    blockAt_frame h.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  have hY : blockAt s.mem (St + BitVec.ofNat 64 yo) = blockAt m₀ (St + BitVec.ofNat 64 yo) :=
    blockAt_frame h.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  refine ⟨g.env h.env, h.kept.of_saved g.saved, by rw [g.saved _ (by decide) (by decide), h.x25], ?_, ?_⟩
  · rw [g.out, hH, hY, blocksAt_one,
      show blockAt s.mem (W + BitVec.ofNat 64 96) = ofBytes (lensBlock a b) by rw [blockAt, h.tb]]
  · refine (h.frame.sub fun r hr => ?_).trans (g.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩

end

end VG.Proof.AesGcm.AArch64
