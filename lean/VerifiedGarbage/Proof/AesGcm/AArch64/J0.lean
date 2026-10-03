import VerifiedGarbage.Proof.AesGcm.AArch64.Tag
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Cmac.Dbl32

/-!
# AES-GCM on AArch64: the pre-counter block (`j0`)

Untrusted: everything here is checked by Lean. `j0` writes `J₀` for the
`x24`-byte nonce at `x23` to the state: its bytes and `0x00000001` if it is
12 bytes (`j012_ok`), else GHASH of its whole blocks (`j0Seg_ok`,
`j0Call1_ok`), of its last bytes padded (`padSeg_ok`, `padCall_ok`) and of the
lengths block (`lensSeg_ok`, `lensCall_ok`), `j0hash_ok`; then the first
counter block `inc₃₂(J₀)` and a zero accumulator (`initState_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
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

theorem rev32_eq : AArch64.rev32 = byteRev32 := rfl

theorem le4_one : le4 (BitVec.ofNat 32 0x01000000) = [0, 0, 0, 1] := by decide

/-- A block from the bytes of its four little-endian words. -/
theorem ofBytes_le4 (a b c d : BitVec 32) :
    ofBytes (le4 a ++ le4 b ++ le4 c ++ le4 d) = byteRev32 a ++ byteRev32 b ++ byteRev32 c ++ byteRev32 d := by
  have h := Proof.Cmac.le4_rev4 (byteRev32 a) (byteRev32 b) (byteRev32 c) (byteRev32 d)
  rw [Proof.Cmac.byteRev32_byteRev32, Proof.Cmac.byteRev32_byteRev32, Proof.Cmac.byteRev32_byteRev32,
    Proof.Cmac.byteRev32_byteRev32] at h
  rw [h, Proof.Cmac.ofBytes_toBytes]

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := by simp

/-- `J₀` of a nonce other than 12 bytes, from GHASH of its whole blocks, its
last bytes padded and the lengths block. -/
theorem j0_split (h : Block) (m : Mem) (Np : Addr) {n : Nat} (hn : n ≠ 12) :
    Spec.Gcm.j0 h (bytesAt m Np n) =
      ghashFrom h (ghashFrom h (ghash h (blocks (bytesAt m Np (16 * (n / 16)))))
        (if n % 16 = 0 then [] else
          [ofBytes (bytesAt m (Np + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) ++ zeros (16 - n % 16))]))
        [ofBytes (lensBlock 0 n)] := by
  rw [Proof.Gcm.j0_eq h (by rw [length_bytesAt]; exact hn), length_bytesAt]
  congr 1
  rw [show bytesAt m Np n = bytesAt m Np (16 * (n / 16)) ++ bytesAt m (Np + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)
      by rw [← bytesAt_add]; congr 1; omega, List.append_assoc,
    Proof.Gcm.blocks_append (by rw [length_bytesAt]; omega), ghash, Proof.Gcm.ghashFrom_append]
  by_cases h0 : n % 16 = 0
  · rw [Proof.Gcm.padLen_of_mod h0]
    simp only [h0, ↓reduceIte]
    rw [show bytesAt m (Np + BitVec.ofNat 64 (16 * (n / 16))) 0 ++ zeros 0 = [] from rfl, Proof.Gcm.blocks_nil]
    rfl
  · simp only [h0, ↓reduceIte]
    rw [show padLen n = 16 - n % 16 by simp only [padLen]; omega,
      Proof.Gcm.blocks_single (bs := bytesAt m (Np + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) ++ zeros (16 - n % 16))
        (by rw [List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; omega)]
    rfl

/-- The regions `j0` writes. -/
abbrev j0Frame (St W : Addr) : List Region :=
  [⟨St, 80⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩]

/-- Before `j0`: the `n`-byte nonce at `Np`, its length also in `x26` and 0 in
`x27`. -/
structure J0In (Ctx St W SP : Addr) (k : Reg → BitVec 64) (H : Block) (Np : Addr) (n : Nat) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  x23 : s.gpr .x23 = Np
  x24 : s.gpr .x24 = BitVec.ofNat 64 n
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  x27 : s.gpr .x27 = 0
  data : DataOk St W s Np n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H

/-- Before the first call of `j0hash`: a zero accumulator, and the call on the
whole blocks of the nonce. -/
structure J1 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (H : Block) (Np : Addr) (n : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  x23 : s.gpr .x23 = Np + BitVec.ofNat 64 (16 * (n / 16))
  x25 : s.gpr .x25 = BitVec.ofNat 64 (n % 16)
  data : DataOk St W s Np n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  y0 : blockAt s.mem (St + BitVec.ofNat 64 0) = 0
  call : GhCall s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 0) Np (W + BitVec.ofNat 64 512) (n / 16)
  frame : Frame [⟨St, 16⟩] m₀ s.mem

/-- After the first call: the whole blocks absorbed. -/
structure J2 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (H : Block) (Np : Addr) (n : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  x23 : s.gpr .x23 = Np + BitVec.ofNat 64 (16 * (n / 16))
  x25 : s.gpr .x25 = BitVec.ofNat 64 (n % 16)
  data : DataOk St W s Np n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  y : blockAt s.mem (St + BitVec.ofNat 64 0) = ghash H (blocks (bytesAt m₀ Np (16 * (n / 16))))
  iv : bytesAt s.mem Np n = bytesAt m₀ Np n
  frame : Frame (j0Frame St W) m₀ s.mem

/-- `J₀` written, from `m₀`. -/
structure J0Mid (Ctx St W SP : Addr) (k : Reg → BitVec 64) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem St = Spec.Gcm.j0 H iv
  frame : Frame (j0Frame St W) m₀ s.mem

/-- After `j0`: `J₀`, the accumulator zeroed and the first counter block. -/
structure J0Out (Ctx St W SP : Addr) (k : Reg → BitVec 64) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem St = Spec.Gcm.j0 H iv
  y : blockAt s.mem (St + BitVec.ofNat 64 16) = 0
  cb : blockAt s.mem (St + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  frame : Frame (j0Frame St W) m₀ s.mem

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

theorem ctx_j0Frame : ∀ r ∈ j0Frame St W, (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.cs.sub_left (Lay.ctxSub (by decide))
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)

omit L in
theorem st_j0Frame {m m' : Mem} {d k : Nat} (h : Frame [⟨St + BitVec.ofNat 64 d, k⟩] m m') (hk : d + k ≤ 80) :
    Frame (j0Frame St W) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Lay.stSub hk⟩

omit L in
theorem t_j0Frame {m m' : Mem} (h : Frame (tFrame St W 0) m m') : Frame (j0Frame St W) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- `J₀` of a 12-byte nonce. -/
theorem j012_ok {k : Reg → BitVec 64} {H : Block} {Np : Addr} {s : State} (h : J0In Ctx St W SP k H Np 12 s) :
    WP isa (.block j012) s (J0Mid Ctx St W SP k H (bytesAt s.mem Np 12) s.mem) := by
  have he := h.env
  have hd := h.data
  have r₀ := in_off hd.rd (show 0 + 4 ≤ 12 by decide) (by decide)
  have r₁ := in_off hd.rd (show 4 + 4 ≤ 12 by decide) (by decide)
  have r₂ := in_off hd.rd (show 8 + 4 ≤ 12 by decide) (by decide)
  have w₀ := he.perm.stW (show 0 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 4 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 8 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 12 + 4 ≤ 80 by decide)
  rw [add_ofNat_zero] at r₀ w₀
  obtain ⟨s', run, hm, og, sp, rd, wr⟩ : ∃ s', runBlock isa j012 s = some s' ∧
      s'.mem = store4 s.mem St (s.mem.readW Np 32) (s.mem.readW (Np + BitVec.ofNat 64 4) 32)
        (s.mem.readW (Np + BitVec.ofNat 64 8) 32) (BitVec.ofNat 32 0x01000000) ∧
      Others [.x9, .x10, .x11, .x12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by simp only [j012]; arun [h.x23, he.x20, r₀, r₁, r₂, w₀, w₁, w₂, w₃, add_ofNat_zero], ?_⟩
    refine ⟨?_, by others_tac, rfl, rfl, rfl⟩
    simp only [mem_write, store4, Mem.writeW, Mem.readW, ww32, BitVec.setWidth_eq]
    rfl
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have f : Frame [⟨St + BitVec.ofNat 64 0, 16⟩] s.mem s'.mem := by
    rw [hm, add_ofNat_zero]; exact Proof.Cmac.frame_store4 (m := s.mem) St _ _ _ _
  refine ⟨he.keep (fun r hr => og r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr, h.kept.of_others og, ?_, ?_, st_j0Frame f (by decide)⟩
  · rw [blockAt_frame f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide), h.hH]
  · have hb : bytesAt s.mem Np 12 = bytesAt s.mem Np 4 ++ bytesAt s.mem (Np + BitVec.ofNat 64 4) 4 ++
        bytesAt s.mem (Np + BitVec.ofNat 64 8) 4 := by
      rw [show (12 : Nat) = 4 + 8 from rfl, bytesAt_add, show (8 : Nat) = 4 + 4 from rfl, bytesAt_add,
        add_ofNat_assoc, List.append_assoc]
    rw [Proof.Gcm.j0_12 _ (length_bytesAt _ _ _), blockAt, hm, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW,
      Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, le4_one, hb]

/-- The first counter block, and the accumulator zeroed. -/
theorem initState_ok {k : Reg → BitVec 64} {H : Block} {iv : List Byte} {m₀ : Mem} {s : State}
    (h : J0Mid Ctx St W SP k H iv m₀ s) :
    WP isa (.block initState) s (J0Out Ctx St W SP k H iv m₀) := by
  have he := h.env
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
  rw [add_ofNat_zero] at r₀
  generalize hw : s.mem.readW (St + BitVec.ofNat 64 12) 32 = w
  obtain ⟨s', run, hm, og, sp, rd, wr⟩ : ∃ s', runBlock isa initState s = some s' ∧
      s'.mem = ((store4 s.mem (St + BitVec.ofNat 64 48) (s.mem.readW St 32) (s.mem.readW (St + BitVec.ofNat 64 4) 32)
        (s.mem.readW (St + BitVec.ofNat 64 8) 32) (byteRev32 (byteRev32 w + 1))).writeW (St + BitVec.ofNat 64 16)
          (0 : BitVec 64)).writeW (St + BitVec.ofNat 64 24) (0 : BitVec 64) ∧
      Others [.x9, .x10, .x11, .x12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by simp only [initState]; arun [he.x20, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, z₀, z₁, add_ofNat_zero], ?_⟩
    refine ⟨?_, by others_tac, rfl, rfl, rfl⟩
    simp only [mem_write, store4, Mem.writeW, Mem.readW, ww32, BitVec.setWidth_eq, ← hw, rev32_eq, add_ofNat_assoc]
    rfl
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have f₄ := Proof.Cmac.frame_store4 (m := s.mem) (St + BitVec.ofNat 64 48) (s.mem.readW St 32)
    (s.mem.readW (St + BitVec.ofNat 64 4) 32) (s.mem.readW (St + BitVec.ofNat 64 8) 32) (byteRev32 (byteRev32 w + 1))
  have fz := Proof.Cmac.frame_store2 (m := store4 s.mem (St + BitVec.ofNat 64 48) (s.mem.readW St 32)
    (s.mem.readW (St + BitVec.ofNat 64 4) 32) (s.mem.readW (St + BitVec.ofNat 64 8) 32) (byteRev32 (byteRev32 w + 1)))
    (St + BitVec.ofNat 64 16) 0 0
  rw [add_ofNat_assoc, ← hm] at fz
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
  refine ⟨he.keep (fun r hr => og r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr, h.kept.of_others og,
    ?_, by rw [hJ, h.j0], ?_, ?_, h.frame.trans (st_j0Frame ff (by decide))⟩
  · rw [blockAt_frame ff (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide)), h.hH]
  · rw [blockAt, hm, show St + BitVec.ofNat 64 24 = St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 by
      rw [add_ofNat_assoc], Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; decide
  · rw [blockAt, bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dz) (by decide),
      Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, ← h.j0, blockAt,
      Proof.Cmac.ofBytes_rev4, ← Proof.Cmac.le4_readW s.mem St, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW,
      ofBytes_le4, hw, Proof.Cmac.byteRev32_byteRev32, inc32_words]

/-- The accumulator zeroed and the arguments for the whole blocks of the
nonce. -/
theorem j0Seg_ok {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {s : State}
    (h : J0In Ctx St W SP k H Np n s) :
    WP isa (.block j0Seg) s (J1 Ctx St W SP k H Np n s.mem) := by
  have he := h.env
  have hd := h.data
  have hlt := hd.lt
  have z₀ := he.perm.stW (show 0 + 8 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 8 + 8 ≤ 80 by decide)
  rw [add_ofNat_zero] at z₀
  obtain ⟨s₁, run₁, hm₁, x3₁, x2₁, x0₁, x1₁, x4₁, x23₁, x25₁, og, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa j0Seg s = some s₁ ∧
      s₁.mem = (s.mem.writeW St (0 : BitVec 64)).writeW (St + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₁.gpr .x3 = BitVec.ofNat 64 (n / 16) ∧ s₁.gpr .x2 = Np ∧ s₁.gpr .x0 = Ctx + BitVec.ofNat 64 240 ∧
      s₁.gpr .x1 = St + BitVec.ofNat 64 0 ∧ s₁.gpr .x4 = W + BitVec.ofNat 64 512 ∧
      s₁.gpr .x23 = Np + BitVec.ofNat 64 (16 * (n / 16)) ∧ s₁.gpr .x25 = BitVec.ofNat 64 (n % 16) ∧
      Others [.x9, .x3, .x2, .x0, .x1, .x4, .x23, .x10, .x25] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by simp only [j0Seg, ghArgs]; arun [he.x20, z₀, z₁, add_ofNat_zero], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq]; rfl
    · simp [gpr_write, h.x24, lsr_ofNat _ _ hlt]
    · simp [gpr_write, h.x23]
    · simp [gpr_write, he.x21]
    · simp [gpr_write, he.x20]
    · simp [gpr_write, he.x19]
    · simp [gpr_write, h.x23, h.x24, lsr_ofNat _ _ hlt, lsl4_ofNat]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h.x24, BitVec.setWidth_eq]
      rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15,
        toNat_ofNat_of_lt hlt]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => og r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have fz : Frame [⟨St, 16⟩] s.mem s₁.mem := by rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  have hdw := hd.take (k := 16 * (n / 16)) (by omega)
  refine ⟨he₁, h.kept.of_others og, x23₁, x25₁, hd.of_eq rd₁ wr₁, ?_, ?_, ?_, fz⟩
  · rw [blockAt_frame fz fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using L.ctx_st (a := 240) (n := 16) (d := 0) (k := 16) (by decide) (by decide), h.hH]
  · rw [add_ofNat_zero, blockAt, hm₁, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; decide
  · exact ghCall_of L (yo := 0) (.inl rfl) he₁ x0₁ x1₁ x2₁ x3₁ x4₁ (by have := hdw.lt; omega)
      (by simpa using (hdw.st.sub_right (Lay.stSub (d := 0) (n := 16) (by decide))).symm)
      (hdw.w.sub_right (Lay.wSub (by decide))) (by rw [rd₁, wr₁]; exact hdw.rd)

/-- The whole blocks of the nonce absorbed. -/
theorem j0Call1_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {m₀ : Mem} {s : State}
    (h : J1 Ctx St W SP k H Np n m₀ s) :
    WP isa (ghCall v.callees) s (J2 Ctx St W SP k H Np n m₀) := by
  have hd := h.data
  refine WP.mono (gh_call v.gh h.call) fun s' g => ?_
  have dD : ∀ r ∈ [(⟨St, 16⟩ : Region)], (⟨Np, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simpa using hd.st.sub_right (Lay.stSub (d := 0) (n := 16) (by decide))
  have dD' : ∀ r ∈ [⟨St + BitVec.ofNat 64 0, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩], (⟨Np, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd.st.sub_right (Lay.stSub (by decide))
    · exact hd.w.sub_right (Lay.wSub (by decide))
  have hiv : bytesAt s.mem Np n = bytesAt m₀ Np n := bytesAt_frame h.frame dD (by have := hd.lt; omega)
  refine ⟨g.env h.env, h.kept.of_saved g.saved, by rw [g.saved _ (by decide) (by decide), h.x23],
    by rw [g.saved _ (by decide) (by decide), h.x25], hd.of_eq g.rd g.wr, by rw [hH_gh L (.inl rfl) g, h.hH], ?_,
    by rw [bytesAt_frame g.frame dD' (by have := hd.lt; omega), hiv], ?_⟩
  · rw [g.out, h.y0, h.hH, Proof.Gcm.blocksAt_eq]
    have e := congrArg (List.take (16 * (n / 16))) hiv
    rw [bytesAt_take _ _ (by omega), bytesAt_take _ _ (by omega)] at e
    rw [e]; rfl
  · refine (st_j0Frame (W := W) (d := 0) (k := 16) (by simpa using h.frame) (by decide)).trans
      (g.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- `J₀` of a nonce of any length but 12: GHASH of the nonce padded and of
the lengths block. -/
theorem j0hash_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {s : State}
    (h : J0In Ctx St W SP k H Np n s) (hn : n ≠ 12) :
    WP isa (j0hash v.callees) s (J0Mid Ctx St W SP k H (bytesAt s.mem Np n) s.mem) := by
  have hd := h.data
  have hlt := hd.lt
  have k26 : k .x26 = BitVec.ofNat 64 n := by rw [← h.kept .x26 (by decide), h.x26]
  have k27 : k .x27 = 0 := by rw [← h.kept .x27 (by decide), h.x27]
  refine WP.seq (WP.mono (j0Seg_ok L h) fun s₁ h₁ =>
    WP.seq (WP.mono (j0Call1_ok L v h₁) fun s₂ h₂ => ?_))
  have hdr := h₂.data.drop (k := 16 * (n / 16)) (by omega)
  rw [show n - 16 * (n / 16) = n % 16 by omega] at hdr
  refine WP.seq (WP.mono (padSeg_ok L (yo := 0) (.inl rfl) (P := Np + BitVec.ofNat 64 (16 * (n / 16)))
    h₂.env h₂.kept h₂.x25 (Nat.mod_lt _ (by decide))
    (by refine ⟨_, by arun [], ?_⟩; exact ⟨by simp [gpr_write, h₂.x23], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩)
    hdr.rd (hdr.w.sub_right (Lay.wSub (by decide)))) fun s₃ h₃ =>
    WP.seq (WP.mono (padCall_ok L (.inl rfl) v h₃) fun s₄ h₄ => ?_))
  refine WP.seq (WP.mono (lensSeg_ok L (yo := 0) (.inl rfl) (ra := .x27) (rb := .x26) h₄.env h₄.kept h₄.x25
    (by decide)) fun s₅ h₅ => WP.mono (lensCall_ok L (.inl rfl) v h₅) fun s₆ h₆ => ?_)
  have a₄ : (s₄.gpr .x27).toNat = 0 := by rw [h₄.kept .x27 (by decide), k27]; rfl
  have b₄ : (s₄.gpr .x26).toNat = n := by rw [h₄.kept .x26 (by decide), k26, toNat_ofNat_of_lt hlt]
  have hH₂ : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = H := h₂.hH
  have hH₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame h₄.frame (ctx_tFrame L (.inl rfl)), hH₂]
  have hP : bytesAt s₂.mem (Np + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (Np + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    have e := congrArg (List.drop (16 * (n / 16))) h₂.iv
    rw [bytesAt_drop _ _ (by omega), bytesAt_drop _ _ (by omega), show n - 16 * (n / 16) = n % 16 by omega] at e
    exact e
  refine ⟨h₆.env, h₆.kept, by rw [blockAt_frame h₆.frame (ctx_tFrame L (.inl rfl)), hH₄], ?_, ?_⟩
  · rw [← add_ofNat_zero St, h₆.out, h₄.out, hH₄, hH₂, a₄, b₄, h₂.y, hP, j0_split H s.mem Np hn]
  · exact (h₂.frame.trans (t_j0Frame h₄.frame)).trans (t_j0Frame h₆.frame)

/-- `j0`: the streaming state's `J₀`, accumulator and first counter block. -/
theorem j0_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {s : State}
    (h : J0In Ctx St W SP k H Np n s) :
    WP isa (j0 v.callees) s (J0Out Ctx St W SP k H (bytesAt s.mem Np n) s.mem) := by
  have hlt := h.data.lt
  obtain ⟨s₁, run₁, x9₁, r₁⟩ : ∃ s₁, runBlock isa [.subImm .x .x9 .x24 12] s = some s₁ ∧
      s₁.gpr .x9 = BitVec.ofNat 64 n - BitVec.ofNat 64 12 ∧ Regs [.x9] s s₁ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, h.x24], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  have h₁ : J0In Ctx St W SP k H Np n s₁ :=
    ⟨h.env.of_regs r₁, h.kept.of_others r₁.others, by rw [r₁.others _ (by decide)]; exact h.x23,
      by rw [r₁.others _ (by decide)]; exact h.x24, by rw [r₁.others _ (by decide)]; exact h.x26,
      by rw [r₁.others _ (by decide)]; exact h.x27, h.data.of_eq r₁.rd r₁.wr, by rw [r₁.mem]; exact h.hH⟩
  have ev : isa.eval (.zero .x .x9) s₁ = some (decide (n = 12)) := by
    show some (s₁.read .x .x9 == 0) = _
    rw [State.read, x9₁, BitVec.setWidth_eq, Offset.ofNat_sub_ofNat_beq hlt (by decide)]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  rw [← r₁.mem]
  refine WP.seq (WP.ite (decide (n = 12)) ev (fun ht => ?_) (fun hf => ?_))
  · have h12 : n = 12 := by simpa using ht
    subst h12
    exact WP.mono (j012_ok L h₁) fun _ hm => initState_ok L hm
  · exact WP.mono (j0hash_ok L v h₁ (by simpa using hf)) fun _ hm => initState_ok L hm

end

end VG.Proof.AesGcm.AArch64
