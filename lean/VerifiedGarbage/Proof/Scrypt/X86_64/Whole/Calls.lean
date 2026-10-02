import VerifiedGarbage.Proof.Scrypt.X86_64.Whole.Steps
import VerifiedGarbage.Proof.Scrypt.X86_64.Whole.Pbkdf2
import VerifiedGarbage.Proof.Scrypt.X86_64.RoMixCT

/-!
# scrypt on x86-64: the calls

Untrusted: everything here is checked by Lean. What a call of
`vg_pbkdf2_hmac_sha256` (`pbk_call`) and of `vg_scrypt_romix`
(`romix_call`) from the frame does, from their arguments (`PbkArgs`,
`RomixArgs`): each keeps `Ctx`, and changes memory only in what it writes
and the stack below the frame. `pbk_pre` and `romix_pre` are their
preconditions, which the proof of constant time uses too.
-/

namespace VG.Proof.Scrypt.X86_64.Whole

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)
open VG.Spec.Scrypt (bytesAt)
open VG.Proof.Pbkdf2.Md.X86_64 (pbkG)

/-! ## Calls from the frame -/

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ≠ .rsp) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

/-- Byte `i` of a region the return address of a call misses, on entry to the callee. -/
theorem ce_byte (t : State) {R : Region} (hd : (below (t.gpr .rsp) 8).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.callEntry.mem (R.base + BitVec.ofNat 64 i) = t.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (t.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (by simpa using hd.symm) hR hi

/-- The bytes of a region the return address of a call misses, on entry to the callee. -/
theorem ce_bytesAt (t : State) {p : Addr} {n : Nat} (hd : (below (t.gpr .rsp) 8).Disjoint ⟨p, n⟩)
    (hn : n ≤ 2 ^ 64) : bytesAt t.callEntry.mem p n = bytesAt t.mem p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => ce_byte t (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

section
variable {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

namespace Ctx

variable {t : State} (hc : Ctx L g m₀ t)
include hc

/-- The return address of a call from the frame. -/
theorem ret : below (t.gpr .rsp) 8 = ⟨L.B + BitVec.ofNat 64 24, 8⟩ := by
  rw [hc.rsp]
  show (⟨L.B + BitVec.ofNat 64 32 - BitVec.ofNat 64 8, 8⟩ : Region) = _
  rw [show L.B + BitVec.ofNat 64 32 - BitVec.ofNat 64 8 = L.B + BitVec.ofNat 64 24 from sub8 L.B]

theorem ce_rsp (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rsp = L.B + BitVec.ofNat 64 24 := by
  rw [State.withRegions_gpr, State.callEntry_rsp, hc.rsp, sub8]

/-- A word in the frame above the return address, on entry to the callee. -/
theorem ce_word (hL : L.Ok) (rd wr : List Region) {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 88) :
    (t.callEntry.withRegions rd wr).mem.readW (L.B + BitVec.ofNat 64 d) 64 =
      t.mem.readW (L.B + BitVec.ofNat 64 d) 64 := by
  have := hL.nB
  rw [State.withRegions_mem, State.callEntry_mem, hc.rsp, sub8]
  exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

end Ctx

namespace Lay.Ok

variable (hL : L.Ok)
include hL

/-- The password misses every writable buffer. -/
theorem pw_buf {r : Region} (h : InBuf L r) : L.PW.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := h.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [hL.pb.sub_right hs, hL.pv.sub_right hs, hL.pc.sub_right hs, hL.po.sub_right hs]

theorem stk_pw {d n : Nat} (h₁ : d + n ≤ 88) : Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.PW :=
  hL.kp.sub_left (Offset.sub_base _ h₁)

theorem stk_in {d n : Nat} (h₁ : d + n ≤ 88) {r : Region} (h : InBuf L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  obtain ⟨R, hR, hs⟩ := h.sub
  exact hL.stk_buf h₁ hR hs

theorem scr_in : InBuf L ⟨L.scr, 200 * 8⟩ :=
  .inr (.inr (.inl (within_base _ (by have := hL.slen17; omega))))

end Lay.Ok

/-! ## PBKDF2 -/

section
variable {pbk : Prog isa}

/-- The regions a call of PBKDF2 reads and writes. -/
abbrev pbkRd (L : Lay) (salt : Addr) (sl : BitVec 64) : List Region :=
  [L.PW, ⟨salt, sl.toNat⟩, ⟨L.B + BitVec.ofNat 64 32, 16⟩]
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

theorem pbk_e0 (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr}
    {ol : BitVec 64} (ha : PbkArgs L salt sl out ol t) (rd wr : List Region) :
    stackArg (t.callEntry.withRegions rd wr) 0 = ol := by
  rw [stackArg, stackArgAddr, hc.ce_rsp, add_add, hc.ce_word hL _ _ (by omega) (by omega), ha.a0]

theorem pbk_e1 (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr}
    {ol : BitVec 64} (ha : PbkArgs L salt sl out ol t) (rd wr : List Region) :
    stackArg (t.callEntry.withRegions rd wr) 1 = L.scr := by
  rw [stackArg, stackArgAddr, hc.ce_rsp, add_add, hc.ce_word hL _ _ (by omega) (by omega), ha.a1]

theorem pbk_pre' (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr}
    {ol : BitVec 64} (ha : PbkArgs L salt sl out ol t) (hr : PbkRegions L salt sl out ol) :
    pbkK.pre (t.callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol)) := by
  have hnB := hL.nB
  have e0 := pbk_e0 hL hc ha (pbkRd L salt sl) (pbkWr L out ol)
  have e1 := pbk_e1 hL hc ha (pbkRd L salt sl) (pbkWr L out ol)
  have ea : stackArgAddr (t.callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol)) 0 =
      L.B + BitVec.ofNat 64 32 := by
    rw [stackArgAddr, hc.ce_rsp, add_add]
  have es : L.B + BitVec.ofNat 64 24 - BitVec.ofNat 64 24 = L.B := BitVec.add_sub_cancel _ _
  have t24 : (L.B + BitVec.ofNat 64 24).toNat = L.B.toNat + 24 := toNat_add_ofNat _ (by omega)
  have hs := hr.sw
  simp only [pbkK, pbkG, Spec.Hmac.sha256S, State.withRegions_rd, State.withRegions_wr, e0, e1, ea,
    hc.ce_rsp, es, t24, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), ha.rdi, ha.rsi,
    ha.rdx, ha.rcx, ha.r8, ha.r9]
  have sw : InBuf L ⟨L.scr, 200 * 8⟩ := hL.scr_in
  refine ⟨by omega, by omega, trivial, trivial, hL.pw_buf hr.ow, hL.pw_buf sw, hr.so, hr.sc, hr.oc,
    (hL.stk_in (d := 32) (n := 16) (by omega) hr.ow).symm,
    (hL.stk_in (d := 32) (n := 16) (by omega) sw).symm,
    hL.stk_pw (by omega), hr.ks.sub_left (Offset.sub_base _ (by omega)),
    hL.stk_in (by omega) hr.ow, hL.stk_in (by omega) sw, Offset.disjoint _ (by omega) (by omega) (by omega),
    by simpa using hL.stk_pw (d := 0) (n := 24) (by omega),
    hr.ks.sub_left (by simpa using Offset.sub_base L.B (d := 0) (n := 24) (k := 88) (by omega)),
    by simpa using hL.stk_in (d := 0) (n := 24) (by omega) hr.ow,
    by simpa using hL.stk_in (d := 0) (n := 24) (by omega) sw,
    Offset.base_disjoint _ (by omega) (by omega), hL.np, hr.ns, hr.no,
    by have := hL.nc; have := hL.slen17; omega, by decide, hr.ol⟩

theorem pbk_sub (hL : L.Ok) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (hr : PbkRegions L salt sl out ol) :
    ∀ r ∈ pbkRd L salt sl ++ pbkWr L out ol, ∃ R ∈ L.regions, Within r R := by
  have hnB := hL.nB
  have hs := hr.sw
  simp only [pbkRd, pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl)
  · exact ⟨L.PW, by simp, within_base _ (by omega)⟩
  · obtain ⟨R, hR, hw⟩ := hs
    exact ⟨R, by simpa only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] using hR, hw⟩
  · exact ⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩
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

theorem pbk_call (hv : Verified X86_64.target pbk (Spec.Hmac.sha256I.pbkdf2Contract X86_64.abi 24))
    (hsp : NoSp pbk) (hd : pbk.depth ≤ 3) (name : String) (hL : L.Ok) {t : State}
    (hc : Ctx L g m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (ha : PbkArgs L salt sl out ol t) (hr : PbkRegions L salt sl out ol) :
    WP isa (.call name pbk) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨out, ol.toNat⟩, ⟨L.scr, 200 * 8⟩, ⟨L.B, 32⟩] t.mem t'.mem ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt t.mem L.pw L.pwl.toNat) (bytesAt t.mem salt sl.toNat) 1
        ol.toNat = some (bytesAt t'.mem out ol.toNat) := by
  have hnB := hL.nB
  refine call_ok hL (pbk_correct hv) hsp hd hc (pbk_pre' hL hc ha hr) (pbk_sub hL hr) (pbk_wsub hL hr)
    fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', hf, ?_⟩
  · have h := hpost
    simp only [pbkK, pbkG, Spec.Hmac.sha256S, State.withRegions_mem, hm, pbk_e0 hL hc ha,
      gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), ha.rdi, ha.rsi,
      ha.rdx, ha.rcx, ha.r8, ha.r9, RegUpd.setWidth_setWidth_32] at h
    have e₁ : Spec.Sha256.bytesAt t.callEntry.mem L.pw L.pwl.toNat = bytesAt t.mem L.pw L.pwl.toNat :=
      ce_bytesAt t (by rw [hc.ret]; exact hL.stk_pw (by omega)) (by have := hL.np; omega)
    have e₂ : Spec.Sha256.bytesAt t.callEntry.mem salt sl.toNat = bytesAt t.mem salt sl.toNat :=
      ce_bytesAt t (by rw [hc.ret]; exact hr.ks.sub_left (Offset.sub_base _ (by omega)))
        (by have := hr.ns; omega)
    rw [e₁, e₂] at h
    exact h

end

/-! ## ROMix -/

/-- Block `i` of `b`. -/
abbrev blkAt (L : Lay) (i : Nat) : Addr := L.b + BitVec.ofNat 64 (128 * L.r.toNat * i)

/-- The regions a call of ROMix on block `i` writes. -/
abbrev romixWr (L : Lay) (i : Nat) : List Region :=
  [⟨blkAt L i, L.r.toNat * 128⟩, ⟨L.v, L.vlen.toNat * 128⟩, ⟨L.scr, (L.r.toNat + 2) * 128⟩]

theorem blk_le (hL : L.Ok) {i : Nat} (hi : i < L.pp) : 128 * L.r.toNat * i + L.r.toNat * 128 ≤ L.blen.toNat * 128 := by
  rw [← hL.len_b, Nat.mul_comm L.r.toNat 128, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

theorem blk_in (hL : L.Ok) {i : Nat} (hi : i < L.pp) : InBuf L ⟨blkAt L i, L.r.toNat * 128⟩ :=
  .inl (within_off _ (blk_le hL hi))

theorem r2 (hL : L.Ok) : (L.r + (2 : BitVec 32).signExtend 64).toNat = L.r.toNat + 2 := by
  have := hL.r57
  rw [show (2 : BitVec 32).signExtend 64 = BitVec.ofNat 64 2 from by decide,
    toNat_add_ofNat _ (by omega)]

theorem sub16 (B : Addr) : B + BitVec.ofNat 64 24 - 16 = B + BitVec.ofNat 64 8 := by bv_omega

theorem romix_pre (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : RomixArgs L (blkAt L i) t) :
    Proof.Scrypt.roMixX86_64.pre (t.callEntry.withRegions [] (romixWr L i)) := by
  have hnB := hL.nB
  have hb := blk_in hL hi
  have hv : InBuf L ⟨L.v, L.vlen.toNat * 128⟩ := .inr (.inl (within_base _ (Nat.le_refl _)))
  have hs : InBuf L ⟨L.scr, (L.r.toNat + 2) * 128⟩ :=
    .inr (.inr (.inl (within_base _ (by have := hL.slen; omega))))
  have tb : (blkAt L i).toNat = L.b.toNat + 128 * L.r.toNat * i := by
    have := blk_le hL hi; have := hL.nb; have := hL.rpos
    exact toNat_add_ofNat _ (by omega)
  simp only [Proof.Scrypt.roMixX86_64, State.withRegions_rd, State.withRegions_wr, hc.ce_rsp, sub16,
    gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), ha.rdi, ha.rsi,
    ha.rdx, ha.rcx, ha.r8, ha.r9, r2 hL]
  have kb := Within.sub (within_off L.b (blk_le hL hi))
  have ks := Within.sub (within_base L.scr (n := (L.r.toNat + 2) * 128) (k := L.slen.toNat * 128)
    (by have := hL.slen; omega))
  refine ⟨trivial, trivial, hL.bv.sub_left kb, (hL.bc.sub_left kb).sub_right ks, hL.vc.sub_right ks,
    hL.stk_in (by omega) hb, hL.stk_in (by omega) hv, hL.stk_in (by omega) hs, hL.stk_in (by omega) hb,
    hL.stk_in (by omega) hv, hL.stk_in (by omega) hs,
    by rw [tb]; have := blk_le hL hi; have := hL.nb; omega, hL.nv,
    by have := hL.nc; have := hL.slen; omega, hL.rpos, hL.vmod, Whole.valid_pow hL.valid, trivial⟩

theorem roMix_nosp : NoSp Impl.Scrypt.X86_64.roMix := by
  have : ((instrs Impl.Scrypt.X86_64.roMix).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp this i hi

theorem roMix_depth : Impl.Scrypt.X86_64.roMix.depth ≤ 3 := by lit_decide

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

theorem romix_call (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : RomixArgs L (blkAt L i) t) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.X86_64.roMix) t fun t' => Ctx L g m₀ t' ∧
      Frame (romixWr L i ++ [⟨L.B, 32⟩]) t.mem t'.mem ∧
      bytesAt t'.mem (blkAt L i) (128 * L.r.toNat) =
        Spec.Scrypt.roMix L.r.toNat L.NN (bytesAt t.mem (blkAt L i) (128 * L.r.toNat)) := by
  have hb := blk_in hL hi
  refine call_ok hL RoMix.roMix_correct roMix_nosp roMix_depth hc (romix_pre hL hc hi ha)
    (romix_sub hL hi) (romix_wsub hL hi) fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', hf, ?_⟩
  · have h := hpost
    simp only [Proof.Scrypt.roMixX86_64, State.withRegions_mem, hm,
      gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), ha.rdi, ha.rsi, ha.rcx] at h
    rw [ce_bytesAt t (by rw [hc.ret]; exact hL.stk_in (by omega) (by simpa [Nat.mul_comm] using hb))
      (by have := hL.blen_lt; have := blk_le hL hi; omega)] at h
    exact h

end

end VG.Proof.Scrypt.X86_64.Whole
