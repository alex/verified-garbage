import VerifiedGarbage.Proof.Scrypt.AArch64.Whole.Steps
import VerifiedGarbage.Proof.Scrypt.AArch64.Whole.Pbkdf2
import VerifiedGarbage.Proof.Scrypt.AArch64.RoMixCT
import VerifiedGarbage.Proof.Scrypt.AArch64.Lit

/-!
# scrypt on AArch64: the calls

What a call of `vg_pbkdf2_hmac_sha256` (`pbk_call`) and of `vg_scrypt_romix`
(`romix_call`) from the frames does, from their arguments (`PbkArgs`,
`RomixArgs`): each keeps `Ctx`, and changes memory only in what it writes and
the stack below the frames. `pbk_pre'` and `romix_pre` are their
preconditions, which the proof of constant time uses too.
-/

namespace VG.Proof.Scrypt.AArch64.Whole

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)
open VG.Spec.Scrypt (bytesAt)
open VG.Proof.Pbkdf2.Md.AArch64 (pbkG)
open VG.Proof.Hmac.Generic.AArch64 (stk)

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

theorem Ctx.ce_sp {t : State} (hc : Ctx L g vv m₀ t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).sp = L.B + BitVec.ofNat 64 16 := by
  rw [State.withRegions_sp, State.callEntry_sp, hc.sp]

theorem sub16 (B : Addr) : B + BitVec.ofNat 64 16 - 16 = B := BitVec.add_sub_cancel _ _

namespace Lay.Ok

variable (hL : L.Ok)
include hL

/-- The password misses every writable buffer. -/
theorem pw_buf {r : Region} (h : InBuf L r) : L.PW.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := h.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [hL.pb.sub_right hs, hL.pv.sub_right hs, hL.pc.sub_right hs, hL.po.sub_right hs]

theorem stk_in {d n : Nat} (h₁ : d + n ≤ 96) {r : Region} (h : InBuf L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  obtain ⟨R, hR, hs⟩ := h.sub
  exact hL.stk_buf h₁ hR hs

/-- The 16 bytes the calls use miss every writable buffer. -/
theorem low_in {r : Region} (h : InBuf L r) : Region.Disjoint ⟨L.B, 16⟩ r := by
  have := hL.stk_in (d := 0) (n := 16) (by omega) h
  simpa using this

theorem scr_in : InBuf L ⟨L.scr, 200 * 8⟩ :=
  .inr (.inr (.inl (within_base _ (by have := hL.slen17; omega))))

end Lay.Ok

/-! ## PBKDF2 -/

section
variable {pbk : Prog isa}

/-- The regions a call of PBKDF2 reads and writes. -/
abbrev pbkRd (L : Lay) (salt : Addr) (sl : BitVec 64) : List Region := [L.PW, ⟨salt, sl.toNat⟩]
abbrev pbkWr (L : Lay) (out : Addr) (ol : BitVec 64) : List Region :=
  [⟨out, ol.toNat⟩, ⟨L.scr, 200 * 8⟩]

/-- What a call of PBKDF2 needs of its salt and its output, beyond being in our buffers. -/
structure PbkRegions (L : Lay) (salt : Addr) (sl : BitVec 64) (out : Addr) (ol : BitVec 64) : Prop where
  sw : ∃ R ∈ L.regions, Within ⟨salt, sl.toNat⟩ R
  ow : InBuf L ⟨out, ol.toNat⟩
  so : Region.Disjoint ⟨salt, sl.toNat⟩ ⟨out, ol.toNat⟩
  sc : Region.Disjoint ⟨salt, sl.toNat⟩ ⟨L.scr, 200 * 8⟩
  oc : Region.Disjoint ⟨out, ol.toNat⟩ ⟨L.scr, 200 * 8⟩
  ks : L.STK.Disjoint ⟨salt, sl.toNat⟩
  ns : salt.toNat + sl.toNat ≤ 2 ^ 64
  no : out.toNat + ol.toNat ≤ 2 ^ 64
  ol : ol.toNat ≤ (2 ^ 32 - 1) * 32

theorem pbk_pre' (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr}
    {ol : BitVec 64} (ha : PbkArgs L salt sl out ol t) (hr : PbkRegions L salt sl out ol) :
    pbkK.pre (t.callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol)) := by
  have hnB := hL.nB
  have t16 : (L.B + BitVec.ofNat 64 16).toNat = L.B.toNat + 16 := toNat_add_ofNat _ (by omega)
  have sw : InBuf L ⟨L.scr, 200 * 8⟩ := hL.scr_in
  simp only [pbkK, pbkG, stk, Spec.Hmac.sha256S, State.withRegions_rd, State.withRegions_wr,
    hc.ce_sp, sub16, t16, gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs), ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7]
  exact ⟨by omega, trivial, trivial, hL.pw_buf hr.ow, hL.pw_buf sw, hr.so, hr.sc, hr.oc,
    by simpa using hL.kp.sub_left (Offset.sub_base L.B (d := 0) (n := 16) (k := 96) (by omega)),
    hr.ks.sub_left (by simpa using Offset.sub_base L.B (d := 0) (n := 16) (k := 96) (by omega)),
    hL.low_in hr.ow, hL.low_in sw, hL.np, hr.ns, hr.no,
    by have := hL.nc; have := hL.slen17; omega, by decide, hr.ol⟩

theorem pbk_sub (hL : L.Ok) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (hr : PbkRegions L salt sl out ol) :
    ∀ r ∈ pbkRd L salt sl ++ pbkWr L out ol, ∃ R ∈ L.regions, Within r R := by
  have hs := hr.sw
  simp only [pbkRd, pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ⟨L.PW, by simp, within_base _ (by omega)⟩
  · obtain ⟨R, hR, hw⟩ := hs
    exact ⟨R, by simpa only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] using hR, hw⟩
  · rcases hr.ow with h | h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  · exact ⟨L.SC, by simp, within_base _ (by have := hL.slen17; omega)⟩

theorem pbk_wsub (hL : L.Ok) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (hr : PbkRegions L salt sl out ol) : ∀ r ∈ pbkWr L out ol, InBuf L r := by
  simp only [pbkWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hr.ow
  · exact hL.scr_in

theorem pbk_call (hv : Verified AArch64.target pbk (Spec.Hmac.sha256I.pbkdf2Contract AArch64.abi 16))
    (hd : pbk.aarch64Depth ≤ 1) (name : String) (hL : L.Ok) {t : State}
    (hc : Ctx L g vv m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (ha : PbkArgs L salt sl out ol t) (hr : PbkRegions L salt sl out ol) :
    WP isa (.call name pbk) t fun t' => Ctx L g vv m₀ t' ∧
      Frame [⟨out, ol.toNat⟩, ⟨L.scr, 200 * 8⟩, ⟨L.B, 16⟩] t.mem t'.mem ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt t.mem L.pw L.pwl.toNat) (bytesAt t.mem salt sl.toNat) 1
        ol.toNat = some (bytesAt t'.mem out ol.toNat) := by
  refine call_ok hL (pbk_correct hv) hd hc (pbk_pre' hL hc ha hr) (pbk_sub hL hr) (pbk_wsub hL hr)
    fun s' hc' hf hpost => ⟨hc', hf, ?_⟩
  have h := hpost
  simp only [pbkK, pbkG, Spec.Hmac.sha256S, State.withRegions_mem, State.callEntry_mem,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), ha.x0, ha.x1, ha.x2, ha.x3,
    ha.x4, ha.x5, ha.x6] at h
  exact h

end

/-! ## ROMix -/

/-- Block `i` of `b`. -/
abbrev blkAt (L : Lay) (i : Nat) : Addr := L.b + BitVec.ofNat 64 (128 * L.r.toNat * i)

/-- The regions a call of ROMix on block `i` writes. -/
abbrev romixWr (L : Lay) (i : Nat) : List Region :=
  [⟨blkAt L i, L.r.toNat * 128⟩, ⟨L.v, L.vlen.toNat * 128⟩, ⟨L.scr, (L.r.toNat + 2) * 128⟩]

theorem blk_le (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + L.r.toNat * 128 ≤ L.blen.toNat * 128 := by
  rw [← hL.len_b, Nat.mul_comm L.r.toNat 128, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

theorem blk_in (hL : L.Ok) {i : Nat} (hi : i < L.pp) : InBuf L ⟨blkAt L i, L.r.toNat * 128⟩ :=
  .inl (within_off _ (blk_le hL hi))

theorem r2 (hL : L.Ok) : (L.r + BitVec.ofNat 64 2).toNat = L.r.toNat + 2 := by
  have := hL.r_lt
  exact toNat_add_ofNat _ (by omega)

theorem romix_pre (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : RomixArgs L (blkAt L i) t) :
    Proof.Scrypt.roMixAArch64.pre (t.callEntry.withRegions [] (romixWr L i)) := by
  have hnB := hL.nB
  have hb := blk_in hL hi
  have hv : InBuf L ⟨L.v, L.vlen.toNat * 128⟩ := .inr (.inl (within_base _ (Nat.le_refl _)))
  have hs : InBuf L ⟨L.scr, (L.r.toNat + 2) * 128⟩ :=
    .inr (.inr (.inl (within_base _ (by have := hL.slen; omega))))
  have tb : (blkAt L i).toNat = L.b.toNat + 128 * L.r.toNat * i := by
    have := blk_le hL hi; have := hL.nb; have := hL.rpos
    exact toNat_add_ofNat _ (by omega)
  have t16 : (L.B + BitVec.ofNat 64 16).toNat = L.B.toNat + 16 := toNat_add_ofNat _ (by omega)
  simp only [Proof.Scrypt.roMixAArch64, State.withRegions_rd, State.withRegions_wr, hc.ce_sp, sub16, t16,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, r2 hL]
  have kb := Within.sub (within_off L.b (blk_le hL hi))
  have ks := Within.sub (within_base L.scr (n := (L.r.toNat + 2) * 128) (k := L.slen.toNat * 128)
    (by have := hL.slen; omega))
  exact ⟨trivial, trivial, hL.bv.sub_left kb, (hL.bc.sub_left kb).sub_right ks, hL.vc.sub_right ks,
    by omega, hL.low_in hb, hL.low_in hv, hL.low_in hs,
    by rw [tb]; have := blk_le hL hi; have := hL.nb; omega, hL.nv,
    by have := hL.nc; have := hL.slen; omega, hL.rpos, hL.vmod, Whole.valid_pow hL.valid, trivial⟩

theorem romix_sub (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    ∀ r ∈ ([] : List Region) ++ romixWr L i, ∃ R ∈ L.regions, Within r R := by
  simp only [romixWr, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.BB, by simp, within_off _ (blk_le hL hi)⟩
  · exact ⟨L.VV, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.SC, by simp, within_base _ (by have := hL.slen; omega)⟩

theorem romix_wsub (hL : L.Ok) {i : Nat} (hi : i < L.pp) : ∀ r ∈ romixWr L i, InBuf L r := by
  simp only [romixWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact blk_in hL hi
  · exact .inr (.inl (within_base _ (Nat.le_refl _)))
  · exact .inr (.inr (.inl (within_base _ (by have := hL.slen; omega))))

theorem roMix_depth : Impl.Scrypt.AArch64.roMix.aarch64Depth ≤ 1 := by lit_decide

theorem romix_call (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : RomixArgs L (blkAt L i) t) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.AArch64.roMix) t fun t' => Ctx L g vv m₀ t' ∧
      Frame (romixWr L i ++ [⟨L.B, 16⟩]) t.mem t'.mem ∧
      bytesAt t'.mem (blkAt L i) (128 * L.r.toNat) =
        Spec.Scrypt.roMix L.r.toNat L.NN (bytesAt t.mem (blkAt L i) (128 * L.r.toNat)) := by
  refine call_ok hL RoMix.roMix_correct roMix_depth hc (romix_pre hL hc hi ha)
    (romix_sub hL hi) (romix_wsub hL hi) fun s' hc' hf hpost => ⟨hc', hf, ?_⟩
  have h := hpost
  simp only [Proof.Scrypt.roMixAArch64, State.withRegions_mem, State.callEntry_mem,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs), ha.x0, ha.x1, ha.x3] at h
  exact h

end

end VG.Proof.Scrypt.AArch64.Whole
