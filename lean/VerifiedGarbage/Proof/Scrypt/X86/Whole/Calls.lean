import VerifiedGarbage.Proof.Scrypt.X86.Whole.Steps
import VerifiedGarbage.Proof.Scrypt.X86.Whole.Pbkdf2
import VerifiedGarbage.Proof.Scrypt.X86.RoMixCT

/-!
# scrypt on x86 (32-bit): the calls

What a call of `vg_pbkdf2_hmac_sha256` (`pbk_call`) and of `vg_scrypt_romix`
(`romix_call`) from the frame does, from their arguments in the frame
(`PbkArgs`, `RomixArgs`): each keeps `Ctx`, and changes memory only in what it
writes and the 80 bytes below the frame (`call_ok`). `pbk_pre'` and
`romix_pre` are their preconditions, which the proof of constant time uses
too.
-/

namespace VG.Proof.Scrypt.X86.Whole

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt)
open VG.Proof.Pbkdf2.Whole.X86 (pbkG toNat_setWidth64)

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x h => h₂ x (h₁ x h)

/-- The return address of a call from the frame. -/
theorem e76 (B : BitVec 32) : B + BitVec.ofNat 32 80 - 4 = B + BitVec.ofNat 32 76 := by
  rw [show BitVec.ofNat 32 80 = BitVec.ofNat 32 76 + 4 from rfl, ← BitVec.add_assoc, BitVec.add_sub_cancel]

theorem toNat_B (L : Lay) (hL : L.Ok) {k : Nat} (hk : k < 172) :
    (L.B + BitVec.ofNat 32 k).toNat = L.B.toNat + k := by
  have := hL.nB
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]

section
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

namespace Ctx

variable {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok)
include hc

theorem ce_esp (rd wr : List Region) : (t.callEntry.withRegions rd wr).gpr .esp = L.B + BitVec.ofNat 32 76 := by
  rw [State.withRegions_gpr, State.callEntry_esp, hc.esp, e76]

include hL

theorem ret_at : (t.gpr .esp - 4).setWidth 64 = L.A + BitVec.ofNat 64 76 := by
  rw [hc.esp, e76, addr_B (by have := hL.nB; omega)]

theorem ce_mem (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).mem = t.mem.writeW (L.A + BitVec.ofNat 64 76) (t.unknowns 0) := by
  rw [State.withRegions_mem, State.callEntry_mem, hc.ret_at hL]

/-- A word above the return address, on entry to the callee. -/
theorem ce_word (rd wr : List Region) {d : Nat} (h₁ : 80 ≤ d) (h₂ : d + 4 ≤ 172) :
    (t.callEntry.withRegions rd wr).mem.readW (L.A + BitVec.ofNat 64 d) 32 =
      t.mem.readW (L.A + BitVec.ofNat 64 d) 32 := by
  rw [hc.ce_mem hL]
  exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

theorem ce_argAddr (rd wr : List Region) (i : Nat) (hi : i < 9) :
    argAddr (t.callEntry.withRegions rd wr) i = L.A + BitVec.ofNat 64 (80 + 4 * i) := by
  have := hL.nB
  rw [argAddr, hc.ce_esp, BitVec.add_assoc, BitVec.ofNat_add_ofNat, show 76 + (4 + 4 * i) = 80 + 4 * i by omega,
    addr_B (by omega)]

theorem ce_arg (rd wr : List Region) (i : Nat) (hi : i < 9) :
    arg (t.callEntry.withRegions rd wr) i = t.mem.readW (L.A + BitVec.ofNat 64 (80 + 4 * i)) 32 := by
  rw [arg, hc.ce_argAddr hL rd wr i hi, hc.ce_word hL rd wr (by omega) (by omega)]

/-- The bytes of a region the return address of a call misses, on entry to the callee. -/
theorem ce_bytesAt (rd wr : List Region) {p : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨p, n⟩ ⟨L.A + BitVec.ofNat 64 76, 4⟩) (hn : n ≤ 2 ^ 64) :
    bytesAt (t.callEntry.withRegions rd wr).mem p n = bytesAt t.mem p n := by
  rw [hc.ce_mem hL]
  exact Memory.frame_bytesAt (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
    (Region.contains_self _ _)) (by simpa using hd) hn

theorem ce_bytesAt' (rd wr : List Region) {p : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨p, n⟩ ⟨L.A + BitVec.ofNat 64 76, 4⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt (t.callEntry.withRegions rd wr).mem p n = Spec.Sha256.bytesAt t.mem p n :=
  hc.ce_bytesAt hL rd wr hd hn

end Ctx

theorem covers {t : State} (hc : Ctx L g m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InBuf L r ∨ Within r L.FR) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · obtain ⟨R, hR, hw⟩ := hsub r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.rd, hc.wr]
    simp only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [hc.wr]
    rcases hwsub r hr with (h | h | h | h) | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩

/-- A call of verified code (see `WP.call`), which uses at most 76 bytes of
stack and is given regions within ours to read, and within the writable
buffers or the frame to write: afterwards `Ctx` holds again, memory changed
only within what it writes and the 80 bytes below the frame, and the
callee's postcondition holds. -/
theorem call_ok (hL : L.Ok) {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hst : stackUse c ≤ 76) {t : State} (hc : Ctx L g m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InBuf L r ∨ Within r L.FR)
    {Q : State → Prop}
    (hQ : ∀ s', Ctx L g m₀ s' → Frame (wr ++ [⟨L.A, 80⟩]) t.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .esp → s₂.gpr r = s'.gpr r) ∧
        k.post (t.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) t Q := by
  have hnB := hL.nB
  have hesp : (t.gpr .esp).toNat = L.B.toNat + 80 := by rw [hc.esp, toNat_B L hL (by omega)]
  obtain ⟨hcov, hcovw⟩ := covers hc hsub hwsub
  refine WP.call hv hsp (by omega) hpre hcov hcovw fun s' hrd hwr hcs hf _ hpost => ?_
  have hb : Region.Sub (below (t.gpr .esp) (stackUse c + 4)) ⟨L.A, 80⟩ := by
    show Region.Sub ⟨(t.gpr .esp - BitVec.ofNat 32 (stackUse c + 4)).setWidth 64, _⟩ _
    rw [hc.esp, Offset.sub_ofNat_eq _ (show stackUse c + 4 ≤ 80 by omega), BitVec.add_sub_cancel,
      addr_B (by omega)]
    exact Offset.sub_base _ (by omega)
  have hf' : Frame (wr ++ [⟨L.A, 80⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hb⟩
  have hfs : Region.Sub L.FR L.STK := Offset.sub_base _ (by omega)
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, ?_, fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'),
    hc.kept.frame hf' fun R hR => ?_, hc.frame.trans (Frame.sub hf' fun r hr => ?_)⟩ hf' hpost
  · rw [hcs .esp (by simp [calleeSaved]), hc.esp]
  · rcases List.mem_append.mp hR with hR | hR
    · rcases hwsub R hR with h | h
      · exact hL.args_in (by omega) (by omega) h
      · exact (Offset.disjoint _ (by omega) (by omega) (by omega)).sub_right h.sub
    · simp only [List.mem_singleton] at hR; subst hR
      exact Offset.disjoint_base _ (by omega) (by omega)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hwsub r hr with h | h
      · obtain ⟨R', hR', hs⟩ := h.sub
        rcases hR' with rfl | rfl | rfl | rfl
        · exact ⟨_, by simp, hs⟩
        · exact ⟨_, by simp, hs⟩
        · exact ⟨_, by simp, hs⟩
        · exact ⟨_, by simp, hs⟩
      · exact ⟨L.STK, by simp, sub_trans h.sub hfs⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.STK, by simp, Region.sub_prefix (by omega)⟩

/-- The return address of a call from the frame is in `STK`. -/
theorem ret_stk (L : Lay) : Region.Sub ⟨L.A + BitVec.ofNat 64 76, 4⟩ L.STK := Offset.sub_base _ (by omega)

namespace Lay.Ok

variable (hL : L.Ok)
include hL

theorem scr_in : InBuf L ⟨L.scr.setWidth 64, 200 * 8⟩ :=
  .inr (.inr (.inl (within_base _ (by have := hL.slen17; omega))))

theorem stk_pw {d n : Nat} (h₁ : d + n ≤ 116) : Region.Disjoint ⟨L.A + BitVec.ofNat 64 d, n⟩ L.PW :=
  hL.kp.sub_left (Offset.sub_base _ h₁)

end Lay.Ok

/-! ## PBKDF2 -/

/-- The regions a call of PBKDF2 reads and writes. -/
abbrev pbkRd (L : Lay) (salt sl : BitVec 32) : List Region := [L.PW, ⟨salt.setWidth 64, sl.toNat⟩]
abbrev pbkWr (L : Lay) (out ol : BitVec 32) : List Region :=
  [⟨out.setWidth 64, ol.toNat⟩, ⟨L.scr.setWidth 64, 200 * 8⟩, ⟨L.A + BitVec.ofNat 64 80, 32⟩]

/-- What a call of PBKDF2 needs of its salt and its output, beyond being in our buffers. -/
structure PbkRegions (L : Lay) (salt sl out ol : BitVec 32) : Prop where
  sw : ∃ R ∈ L.regions, Within ⟨salt.setWidth 64, sl.toNat⟩ R
  ow : InBuf L ⟨out.setWidth 64, ol.toNat⟩
  so : Region.Disjoint ⟨salt.setWidth 64, sl.toNat⟩ ⟨out.setWidth 64, ol.toNat⟩
  sc : Region.Disjoint ⟨salt.setWidth 64, sl.toNat⟩ ⟨L.scr.setWidth 64, 200 * 8⟩
  oc : Region.Disjoint ⟨out.setWidth 64, ol.toNat⟩ ⟨L.scr.setWidth 64, 200 * 8⟩
  ks : L.STK.Disjoint ⟨salt.setWidth 64, sl.toNat⟩
  ns : salt.toNat + sl.toNat ≤ 2 ^ 32
  no : out.toNat + ol.toNat ≤ 2 ^ 32
  ol : ol.toNat ≤ (2 ^ 32 - 1) * 32

/-- `A + 76 - 76`. -/
theorem stack76 (L : Lay) : L.A + BitVec.ofNat 64 76 - BitVec.ofNat 64 76 = L.A := BitVec.add_sub_cancel _ _

theorem pbk_pre' (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {salt sl out ol : BitVec 32}
    (ha : PbkArgs L salt sl out ol t.mem) (hr : PbkRegions L salt sl out ol) :
    pbkK.pre (t.callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol)) := by
  have hnB := hL.nB
  have a := hc.ce_arg hL (pbkRd L salt sl) (pbkWr L out ol)
  have ea := hc.ce_argAddr hL (pbkRd L salt sl) (pbkWr L out ol) 0 (by omega)
  have esp := hc.ce_esp (pbkRd L salt sl) (pbkWr L out ol)
  have e76 : (L.B + BitVec.ofNat 32 76).setWidth 64 = L.A + BitVec.ofNat 64 76 := addr_B (by omega)
  have sw := hL.scr_in
  simp only [pbkK, pbkG, Spec.Hmac.sha256S, State.withRegions_rd, State.withRegions_wr, a 0 (by omega),
    a 1 (by omega), a 2 (by omega), a 3 (by omega), a 4 (by omega), a 5 (by omega), a 6 (by omega),
    a 7 (by omega), Nat.reduceMul, Nat.reduceAdd, ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ha.a6, ha.a7, ea,
    esp, e76, stack76, toNat_B L hL (show 76 < 172 by omega)]
  refine ⟨by omega, by omega, trivial, trivial, hL.pw_in hr.ow, hL.pw_in sw, (hL.stk_pw (by omega)).symm,
    hr.so, hr.sc, hr.ks.symm.sub_right (Offset.sub_base _ (by omega)), hr.oc,
    (hL.stk_in (d := 80) (n := 32) (by omega) hr.ow).symm,
    (hL.stk_in (d := 80) (n := 32) (by omega) sw).symm,
    hL.stk_pw (by omega), hr.ks.sub_left (ret_stk L),
    hL.stk_in (by omega) hr.ow, hL.stk_in (by omega) sw, Offset.disjoint _ (by omega) (by omega) (by omega),
    hL.kp.sub_left (Region.sub_prefix (by omega)), hr.ks.sub_left (Region.sub_prefix (by omega)),
    by simpa using hL.stk_in (d := 0) (n := 76) (by omega) hr.ow,
    by simpa using hL.stk_in (d := 0) (n := 76) (by omega) sw,
    Offset.base_disjoint _ (by omega) (by omega), hL.np, hr.ns, hr.no,
    by have := hL.nc; have := hL.slen17; omega, by decide, hr.ol⟩

theorem pbk_sub (hL : L.Ok) {salt sl out ol : BitVec 32} (hr : PbkRegions L salt sl out ol) :
    ∀ r ∈ pbkRd L salt sl ++ pbkWr L out ol, ∃ R ∈ L.regions, Within r R := by
  simp only [pbkRd, pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl)
  · exact ⟨L.PW, by simp, within_base _ (Nat.le_refl _)⟩
  · obtain ⟨R, hR, hw⟩ := hr.sw
    exact ⟨R, by simpa using hR, hw⟩
  · rcases hr.ow with h | h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  · exact ⟨L.SC, by simp, within_base _ (by have := hL.slen17; omega)⟩
  · exact ⟨L.FR, by simp, within_base _ (by omega)⟩

theorem pbk_wsub (hL : L.Ok) {out ol : BitVec 32} (hr : InBuf L ⟨out.setWidth 64, ol.toNat⟩) :
    ∀ r ∈ pbkWr L out ol, InBuf L r ∨ Within r L.FR := by
  simp only [pbkWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inl hr
  · exact .inl hL.scr_in
  · exact .inr (within_base _ (by omega))

theorem pbk_call {pbk : Prog isa}
    (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76))
    (hsp : NoSp pbk) (hst : stackUse pbk ≤ 76) (name : String) (hL : L.Ok) {t : State}
    (hc : Ctx L g m₀ t) {salt sl out ol : BitVec 32}
    (ha : PbkArgs L salt sl out ol t.mem) (hr : PbkRegions L salt sl out ol) :
    WP isa (.call name pbk) t fun t' => Ctx L g m₀ t' ∧
      Frame (pbkWr L out ol ++ [⟨L.A, 80⟩]) t.mem t'.mem ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt t.mem (L.pw.setWidth 64) L.pwl.toNat)
        (bytesAt t.mem (salt.setWidth 64) sl.toNat) 1 ol.toNat =
        some (bytesAt t'.mem (out.setWidth 64) ol.toNat) := by
  have hnB := hL.nB
  refine call_ok hL (pbk_correct hv) hsp hst hc (pbk_pre' hL hc ha hr) (pbk_sub hL hr) (pbk_wsub hL hr.ow)
    fun s' hc' hf ⟨s₂, hm, _, hpost⟩ => ⟨hc', hf, ?_⟩
  have a := hc.ce_arg hL (pbkRd L salt sl) (pbkWr L out ol)
  have h := hpost
  simp only [pbkK, pbkG, Spec.Hmac.sha256S, hm, a 0 (by omega), a 1 (by omega), a 2 (by omega),
    a 3 (by omega), a 4 (by omega), a 5 (by omega), a 6 (by omega), Nat.reduceMul, Nat.reduceAdd, ha.a0,
    ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ha.a6] at h
  rw [hc.ce_bytesAt' hL _ _ (hL.stk_pw (by omega)).symm (by have := hL.np; omega),
    hc.ce_bytesAt' hL _ _ (hr.ks.sub_left (ret_stk L)).symm (by have := hr.ns; omega),
    show (1 : BitVec 32).toNat = 1 from rfl] at h
  exact h

/-! ## ROMix -/

/-- Block `i` of `b`. -/
abbrev blk (L : Lay) (i : Nat) : Addr := L.b.setWidth 64 + BitVec.ofNat 64 (128 * L.r.toNat * i)

/-- Its address, as a word. -/
abbrev cur (L : Lay) (i : Nat) : BitVec 32 := L.b + BitVec.ofNat 32 (128 * L.r.toNat * i)

theorem blk_le (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + L.r.toNat * 128 ≤ L.blen.toNat * 128 := by
  rw [← hL.len_b, Nat.mul_comm L.r.toNat 128, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

theorem cur_eq (hL : L.Ok) {i : Nat} (hi : i < L.pp) : (cur L i).setWidth 64 = blk L i := by
  have := blk_le hL hi; have := hL.nb; have := hL.rpos
  exact addr_B (by omega)

theorem toNat_cur (hL : L.Ok) {i : Nat} (hi : i < L.pp) : (cur L i).toNat = L.b.toNat + 128 * L.r.toNat * i := by
  have := blk_le hL hi; have := hL.nb; have := hL.rpos
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 128 * L.r.toNat * i) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem blk_in (hL : L.Ok) {i : Nat} (hi : i < L.pp) : InBuf L ⟨blk L i, L.r.toNat * 128⟩ :=
  .inl (within_off _ (blk_le hL hi))

/-- The regions a call of ROMix on block `i` reads and writes. -/
abbrev romixRd (L : Lay) : List Region := [⟨L.A + BitVec.ofNat 64 80, 24⟩]
abbrev romixWr (L : Lay) (i : Nat) : List Region :=
  [⟨blk L i, L.r.toNat * 128⟩, ⟨L.v.setWidth 64, L.vlen.toNat * 128⟩,
    ⟨L.scr.setWidth 64, (L.r.toNat + 2) * 128⟩]

theorem r2 (hL : L.Ok) : (L.r + 2).toNat = L.r.toNat + 2 := by
  have := hL.r25
  rw [BitVec.toNat_add, show (2 : BitVec 32).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]

theorem stack36 (L : Lay) : L.A + BitVec.ofNat 64 76 - 36 = L.A + BitVec.ofNat 64 40 := by
  rw [show BitVec.ofNat 64 76 = BitVec.ofNat 64 40 + 36 from rfl, ← BitVec.add_assoc, BitVec.add_sub_cancel]

theorem romix_pre (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : RomixArgs L (cur L i) t.mem) :
    Proof.Scrypt.roMixX86.pre (t.callEntry.withRegions (romixRd L) (romixWr L i)) := by
  have hnB := hL.nB
  have hb := blk_in hL hi
  have hv : InBuf L ⟨L.v.setWidth 64, L.vlen.toNat * 128⟩ := .inr (.inl (within_base _ (Nat.le_refl _)))
  have hs : InBuf L ⟨L.scr.setWidth 64, (L.r.toNat + 2) * 128⟩ :=
    .inr (.inr (.inl (within_base _ (by have := hL.slen; omega))))
  have a := hc.ce_arg hL (romixRd L) (romixWr L i)
  have ea := hc.ce_argAddr hL (romixRd L) (romixWr L i) 0 (by omega)
  have esp := hc.ce_esp (romixRd L) (romixWr L i)
  have e76 : (L.B + BitVec.ofNat 32 76).setWidth 64 = L.A + BitVec.ofNat 64 76 := addr_B (by omega)
  simp only [Proof.Scrypt.roMixX86, State.withRegions_rd, State.withRegions_wr, a 0 (by omega),
    a 1 (by omega), a 2 (by omega), a 3 (by omega), a 4 (by omega), a 5 (by omega), Nat.reduceMul,
    Nat.reduceAdd, ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ea, esp, e76, stack36, r2 hL, cur_eq hL hi,
    toNat_cur hL hi, toNat_B L hL (show 76 < 172 by omega)]
  have kb := Within.sub (within_off (L.b.setWidth 64) (blk_le hL hi))
  have ks := Within.sub (within_base (L.scr.setWidth 64) (n := (L.r.toNat + 2) * 128)
    (k := L.slen.toNat * 128) (by have := hL.slen; omega))
  refine ⟨trivial, trivial, hL.bv.sub_left kb, (hL.bc.sub_left kb).sub_right ks, hL.vc.sub_right ks,
    hL.stk_in (by omega) hb, hL.stk_in (by omega) hv, hL.stk_in (by omega) hs, hL.stk_in (by omega) hb,
    hL.stk_in (by omega) hv, hL.stk_in (by omega) hs, hL.stk_in (by omega) hb, hL.stk_in (by omega) hv,
    hL.stk_in (by omega) hs, by have := blk_le hL hi; have := hL.nb; omega, hL.nv,
    by have := hL.nc; have := hL.slen; omega, by omega, by omega, hL.rpos, hL.vmod,
    Whole.valid_pow hL.valid, trivial⟩

theorem roMix_nosp : NoSp Impl.Scrypt.X86.roMix := NoSp.of_all (by lit_decide)

theorem roMix_stack : stackUse Impl.Scrypt.X86.roMix ≤ 76 := by lit_decide

theorem romix_sub (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    ∀ r ∈ romixRd L ++ romixWr L i, ∃ R ∈ L.regions, Within r R := by
  simp only [romixRd, romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ⟨L.FR, by simp, within_base _ (by omega)⟩
  · exact ⟨L.BB, by simp, within_off _ (blk_le hL hi)⟩
  · exact ⟨L.VV, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.SC, by simp, within_base _ (by have := hL.slen; omega)⟩

theorem romix_wsub (hL : L.Ok) {i : Nat} (hi : i < L.pp) : ∀ r ∈ romixWr L i, InBuf L r ∨ Within r L.FR := by
  simp only [romixWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inl (blk_in hL hi)
  · exact .inl (.inr (.inl (within_base _ (Nat.le_refl _))))
  · exact .inl (.inr (.inr (.inl (within_base _ (by have := hL.slen; omega)))))

theorem romix_call (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : RomixArgs L (cur L i) t.mem) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.X86.roMix) t fun t' => Ctx L g m₀ t' ∧
      Frame (romixWr L i ++ [⟨L.A, 80⟩]) t.mem t'.mem ∧
      bytesAt t'.mem (blk L i) (128 * L.r.toNat) =
        Spec.Scrypt.roMix L.r.toNat L.NN (bytesAt t.mem (blk L i) (128 * L.r.toNat)) := by
  have hb := blk_in hL hi
  refine call_ok hL RoMix.roMix_correct roMix_nosp roMix_stack hc (romix_pre hL hc hi ha)
    (romix_sub hL hi) (romix_wsub hL hi) fun s' hc' hf ⟨s₂, hm, _, hpost⟩ => ⟨hc', hf, ?_⟩
  have a := hc.ce_arg hL (romixRd L) (romixWr L i)
  have h := hpost
  simp only [Proof.Scrypt.roMixX86, hm, a 0 (by omega), a 1 (by omega), a 3 (by omega), Nat.reduceMul,
    Nat.reduceAdd, ha.a0, ha.a1, ha.a3, cur_eq hL hi] at h
  rw [hc.ce_bytesAt hL _ _ (hL.stk_in (by omega) (by simpa [Nat.mul_comm] using hb)).symm
    (by have := hL.blen_lt; have := blk_le hL hi; omega)] at h
  exact h

end

end VG.Proof.Scrypt.X86.Whole
