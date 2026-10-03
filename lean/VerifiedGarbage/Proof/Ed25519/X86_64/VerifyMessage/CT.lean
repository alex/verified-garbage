import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.Args
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Base
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMain
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyVerified
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-! Merged from `Proof.Ed25519.X86_64.VerifyMessage.Body`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.VerifyMessage.Reduce`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.VerifyMessage.Hash`. -/
section
/-! SHA-512 over the three buffers of an Ed25519 verification challenge. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (callWith)
open VG.Impl.Ed25519.X86_64.VerifyMessage
open VG.Proof.Ed25519.X86_64.PublicKey
  (Within within_base within_off gpr_ce rsp_ce sub8 sub88 nosp_init upd_verified upd_nosp upd_depth
   fin_verified fin_nosp fin_depth ce_byte)
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- A read-only input or a portion of one. -/
def Input (L : Lay) (r : Region) : Prop := ∃ R ∈ L.inputs, Within r R

theorem Input.scr {r : Region} (hi : Input L r) (hL : L.Ok) {d n : Nat} (h : d + n ≤ 8192) :
    r.Disjoint ⟨L.scr + BitVec.ofNat 64 d, n⟩ := by
  obtain ⟨R, hR, hs⟩ := hi
  exact (hL.input_scr hR h).sub_left hs.sub

theorem Input.stk {r : Region} (hi : Input L r) (hL : L.Ok) {d n : Nat} (h : d + n ≤ 184) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  obtain ⟨R, hR, hs⟩ := hi
  exact (hL.stk_input hR h).sub_right hs.sub

theorem Ctx.ce_bytes {t : State} (hc : Ctx L g mx m₀ t) (hL : L.Ok)
    {r : Region} (hi : Input L r) (hn : r.len ≤ 2 ^ 64) :
    Spec.Sha512.bytesAt t.callEntry.mem r.base r.len = Spec.Ed25519.bytesAt m₀ r.base r.len := by
  unfold Spec.Sha512.bytesAt Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i h => ?_
  have hn' := List.mem_range.mp h
  rw [ce_byte t (by rw [hc.ret]; exact hi.stk hL (by omega)) hn hn']
  exact Frame.bytes hc.frame (by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · simpa using hi.scr hL (d := 0) (n := 8192) (by omega)
    · have hs := hi.stk hL (d := 0) (n := 184) (by omega)
      simpa using hs.symm) hn hn'

theorem Ctx.ce_repr (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) {iv : Spec.Sha512.HashValue}
    {m : List Byte} (hr : Spec.Sha512.Repr iv t.mem L.scr m) :
    Spec.Sha512.Repr iv t.callEntry.mem L.scr m :=
  Proof.Sha512.Stream.repr_congr (fun i hi => ce_byte t (R := ⟨L.scr, 192⟩)
    (by rw [hc.ret]; simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega))
    (by show (192 : Nat) ≤ 2 ^ 64; decide) hi) hr

abbrev initRd : List Region := []
abbrev initWr (L : Lay) : List Region := [⟨L.scr, 192⟩]

theorem init_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : InitArgs L t) :
    (Proof.Sha512.initX86_64 Spec.Sha512.H0_512).pre (t.callEntry.withRegions initRd (initWr L)) := by
  have hrdi := (gpr_ce t initRd (initWr L) (r := .rdi) (by decide)).trans ha
  refine ⟨rfl, by rw [hrdi]; rfl, ?_⟩
  rw [rsp_ce, hrdi, hc.rsp, sub8]
  simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega)

theorem init_call (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : InitArgs L t) :
    WP isa (.call Spec.Sha512.init512Api.name (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512)) t
      fun t' => Ctx L g mx m₀ t' ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr [] := by
  refine call_ok hL (Proof.Sha512.X86_64.Stream.init_verified _).1 (nosp_init _) (by decide) hc
    (init_pre hL hc ha) ?_ ?_ fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  · rintro r hr
    simp only [initRd, initWr, List.nil_append, List.mem_singleton] at hr
    subst hr
    exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · rintro r hr
    simp only [initWr, List.mem_singleton] at hr
    subst hr
    exact .inr (within_base _ (by omega))
  · have := hpost
    simp only [Proof.Sha512.initX86_64, (gpr_ce t initRd (initWr L) (r := .rdi) (by decide)).trans ha] at this
    rwa [← hm]

theorem init_step (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (callWith initArgs Spec.Sha512.init512Api.name
      (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512)) t
      fun t' => Ctx L g mx m₀ t' ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr [] :=
  WP.seq (WP.mono (initArgs_ok hc) fun _ ⟨hc₁, _, ha⟩ => init_call hL hc₁ ha)

abbrev updWr (L : Lay) : List Region := [⟨L.scr, 192⟩, ⟨L.scr + BitVec.ofNat 64 192, 1376⟩]

theorem upd_regs {t : State} {count : BitVec 64} {p : Addr} {n : BitVec 64}
    (ha : UpdArgs L count p n t) (rd wr : List Region) :
    UpdArgs L count p n (t.callEntry.withRegions rd wr) :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2⟩

theorem upd_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    {count : BitVec 64} {p : Addr} {n : BitVec 64} (ha : UpdArgs L count p n t)
    (hi : Input L ⟨p, n.toNat⟩) :
    Proof.Sha512.updateX86_64.pre (t.callEntry.withRegions [⟨p, n.toNat⟩] (updWr L)) := by
  obtain ⟨hdi, -, hdx, hcx, h8⟩ := upd_regs ha [⟨p, n.toNat⟩] (updWr L)
  simp only [Proof.Sha512.updateX86_64, rsp_ce, hdi, hdx, hcx, h8, hc.rsp, sub8, sub88,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial, Offset.base_disjoint _ (by omega) (by omega),
    by simpa using hi.scr hL (d := 0) (n := 192) (by omega), hi.scr hL (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    by simpa using hi.stk hL (d := 0) (n := 8) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 192) (k := 1376) (by omega) (by omega)⟩

theorem upd_call (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    {prev : List Byte} {count : BitVec 64} {p : Addr} {n : BitVec 64}
    (ha : UpdArgs L count p n t) (hi : Input L ⟨p, n.toNat⟩)
    (hcount : count = BitVec.ofNat 64 prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr prev) :
    WP isa (.call (Spec.Sha512.updateApi.name ++ v.suffix) (Impl.Sha512.X86_64.Stream.update v.callee)) t
      fun t' => Ctx L g mx m₀ t' ∧
        Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr (prev ++ Spec.Ed25519.bytesAt m₀ p n.toNat) := by
  refine call_ok hL (upd_verified v).1 (upd_nosp v) (upd_depth v) hc (upd_pre hL hc ha hi) ?_ ?_
    fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  · intro r hr
    simp only [updWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨R, hR, hsub⟩ := hi
      exact ⟨R, List.mem_append_left _ hR, hsub⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  · intro r hr
    simp only [updWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (within_base _ (by omega))
    · exact .inr (within_off _ (by omega))
  · obtain ⟨hdi, hsi, hdx, hcx, -⟩ := upd_regs ha [⟨p, n.toNat⟩] (updWr L)
    have h := hpost Spec.Sha512.H0_512 prev
      (by rw [State.withRegions_mem, hdi]; exact hc.ce_repr hL hr) (hsi.trans hcount)
    simp only [State.withRegions_mem, hdi, hdx, hcx, hm] at h
    rw [hc.ce_bytes hL hi (Nat.le_of_lt n.isLt)] at h
    exact h


abbrev finWr (L : Lay) : List Region :=
  [⟨L.scr, 192⟩, ⟨L.B + BitVec.ofNat 64 80, 64⟩, ⟨L.scr + BitVec.ofNat 64 192, 1376⟩]

theorem fin_regs {t : State} (ha : FinArgs L t) (rd wr : List Region) :
    FinArgs L (t.callEntry.withRegions rd wr) :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2⟩

theorem fin_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : FinArgs L t) :
    Proof.Sha512.finalizeX86_64.pre (t.callEntry.withRegions [] (finWr L)) := by
  obtain ⟨hdi, -, hdx, hcx⟩ := fin_regs ha [] (finWr L)
  simp only [Proof.Sha512.finalizeX86_64, rsp_ce, hdi, hdx, hcx, hc.rsp, sub8, sub88,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial,
    by simpa using (hL.stk_scr (d := 80) (n := 64) (e := 0) (k := 192) (by omega) (by omega)).symm,
    Offset.base_disjoint _ (by omega) (by omega), hL.stk_scr (by omega) (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    Offset.disjoint _ (by omega) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    Offset.base_disjoint _ (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 192) (k := 1376) (by omega) (by omega)⟩

theorem fin_call (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : FinArgs L t)
    {message : List Byte} (hmess : message.length < 2 ^ 64)
    (hlen : L.len + 64 = BitVec.ofNat 64 message.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr message) :
    WP isa (.call (Spec.Sha512.finalizeApi.name ++ v.suffix) (Impl.Sha512.X86_64.Stream.finalize v.callee)) t
      fun t' => Ctx L g mx m₀ t' ∧ Spec.Sha512.bytesAt t'.mem (L.B + BitVec.ofNat 64 80) 64 =
        Spec.Sha512.sha512 message := by
  refine call_ok hL (fin_verified v).1 (fin_nosp v) (fin_depth v) hc (fin_pre hL hc ha) ?_ ?_
    fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  · intro r hr
    simp only [finWr, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.FR, by simp, 64, by rw [PublicKey.add_add], by show 64 + 64 ≤ 168; decide⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  · intro r hr
    simp only [finWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (within_base _ (by omega))
    · exact .inl ⟨64, by rw [PublicKey.add_add], by show 64 + 64 ≤ 128; decide⟩
    · exact .inr (within_off _ (by omega))
  · obtain ⟨hdi, hsi, hdx, -⟩ := fin_regs ha [] (finWr L)
    have h := hpost Spec.Sha512.H0_512 message
      (by rw [State.withRegions_mem, hdi]; exact hc.ce_repr hL hr) hmess (hsi.trans hlen)
    rw [hdx, hm] at h
    exact h

/-- The bytes hashed, before reduction. -/
def challengeInput (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.bytesAt m L.sig 32 ++ Spec.Ed25519.bytesAt m L.pk 32 ++
    Spec.Ed25519.bytesAt m L.msg L.len.toNat

theorem challengeInput_length : (challengeInput L m₀).length = 64 + L.len.toNat := by
  simp only [challengeInput, List.length_append, PublicKey.bytesAt_length]

theorem hash_ok (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (hlen : 64 + L.len.toNat < 2 ^ 64) :
    WP isa (hash v.callee v.suffix) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha512.bytesAt t'.mem (L.B + BitVec.ofNat 64 80) 64 =
        Spec.Sha512.sha512 (challengeInput L m₀) := by
  have hiR : Input L ⟨L.sig, (32 : BitVec 64).toNat⟩ :=
    ⟨L.SIG, by simp [Lay.inputs], within_base _ (by decide)⟩
  have hiA : Input L ⟨L.pk, (32 : BitVec 64).toNat⟩ :=
    ⟨L.PK, by simp [Lay.inputs], within_base _ (by decide)⟩
  have hiM : Input L L.MSG := ⟨L.MSG, by simp [Lay.inputs], within_base _ (by omega)⟩
  refine WP.seq (WP.mono (init_step hL hc) fun t₁ ⟨hc₁, hr₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (prefixArgs_ok hc₁ fSignature 0 (by decide) (by decide) L.sig hc₁.pSig)
    fun t₂ ⟨hc₂, hm₂, ha₂⟩ => WP.mono (upd_call v hL hc₂ ha₂ hiR rfl (hm₂ ▸ hr₁))
    fun t₃ ⟨hc₃, hr₃⟩ => ?_))
  refine WP.seq (WP.seq (WP.mono (prefixArgs_ok hc₃ fPublicKey 32 (by decide) (by decide) L.pk hc₃.pPk)
    fun t₄ ⟨hc₄, hm₄, ha₄⟩ => WP.mono (upd_call v hL hc₄ ha₄ hiA
      (by simp only [List.nil_append, PublicKey.bytesAt_length]; rfl) (hm₄ ▸ hr₃))
    fun t₅ ⟨hc₅, hr₅⟩ => ?_))
  refine WP.seq (WP.seq (WP.mono (messageArgs_ok hc₅) fun t₆ ⟨hc₆, hm₆, ha₆⟩ =>
    WP.mono (upd_call v hL hc₆ ha₆ hiM
      (by simp only [List.length_append, List.length_nil, PublicKey.bytesAt_length]; rfl) (hm₆ ▸ hr₅))
    fun t₇ ⟨hc₇, hr₇⟩ => ?_))
  refine WP.seq (WP.mono (finalizeArgs_ok hc₇) fun t₈ ⟨hc₈, hm₈, ha₈⟩ => ?_)
  apply fin_call v hL hc₈ ha₈
  · rw [challengeInput_length]; exact hlen
  · rw [challengeInput_length, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm]
    rfl
  · simpa only [List.nil_append] using hm₈ ▸ hr₇

end VG.Proof.Ed25519.X86_64.VerifyMessage
end

/-! Reduce the challenge and place its 64-byte encoding outside scratch. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (scalarReduce stk)
open VG.Impl.Ed25519.X86_64.VerifyMessage
open VG.Proof.Ed25519.X86_64.PublicKey
  (Within within_base within_off gpr_ce rsp_ce sub8 ea_stk add_add sx32)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def ReduceArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.B + BitVec.ofNat 64 16 ∧ t.gpr .rsi = L.B + BitVec.ofNat 64 80 ∧
    t.gpr .rdx = L.scr

theorem reduceArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block reduceArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ ReduceArgs L t' := by
  have h144 := hc.inFr (d := 144) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [reduceArgs, fScratch, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Option.map_some, Option.bind_some,
    reduceCtorEq, ite_false, ite_true, hc.rsp, add_add, Nat.reduceAdd, h144,
    Option.some.injEq, exists_eq_left', hc.pScr, ReduceArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial,
    by rw [show (64 : BitVec 32).signExtend 64 = BitVec.ofNat 64 64 from rfl, add_add], trivial⟩

abbrev reduceRd (L : Lay) : List Region := [⟨L.B + BitVec.ofNat 64 80, 64⟩]
abbrev reduceWr (L : Lay) : List Region := [⟨L.B + BitVec.ofNat 64 16, 32⟩, L.SCR]

theorem reduce_regs {t : State} (ha : ReduceArgs L t) (rd wr : List Region) :
    ReduceArgs L (t.callEntry.withRegions rd wr) :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2⟩

theorem reduce_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : ReduceArgs L t) :
    scalarReduceLocal.pre (t.callEntry.withRegions (reduceRd L) (reduceWr L)) := by
  obtain ⟨hdi, hsi, hdx⟩ := reduce_regs ha (reduceRd L) (reduceWr L)
  simp only [scalarReduceLocal, rsp_ce, hdi, hsi, hdx, hc.rsp, sub8,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial,
    by simpa using hL.stk_scr (d := 80) (n := 64) (e := 0) (k := 8192) (by omega) (by omega),
    Offset.disjoint _ (by omega) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 8192) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 16) (n := 32) (e := 0) (k := 8192) (by omega) (by omega)⟩

theorem reduce_call (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : ReduceArgs L t)
    {digest : List Byte} (hh : Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 64 = digest) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 32 = Spec.Ed25519.scalarReduce digest := by
  refine call_ok hL scalarReduce_ok (Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide))
    (by lit_decide) hc (reduce_pre hL hc ha) ?_ ?_
    fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  · intro r hr
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.FR, by simp, 64, by rw [add_add], by show 64 + 64 ≤ 168; decide⟩
    · exact ⟨L.FR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · intro r hr
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl (within_base _ (by omega))
    · exact .inr (within_base _ (by omega))
  · obtain ⟨hdi, hsi, -⟩ := reduce_regs ha (reduceRd L) (reduceWr L)
    change Spec.Ed25519.bytesAt s₂.mem _ 32 = Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt _ _ 64) at hpost
    rw [hdi, hsi, State.withRegions_mem, hm] at hpost
    have he : Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 80) 64 =
        Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 64 := by
      apply List.map_congr_left
      intro i hi
      exact PublicKey.ce_byte t (R := ⟨L.B + BitVec.ofNat 64 80, 64⟩) (i := i) (by rw [hc.ret]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by decide : 64 ≤ 2 ^ 64) (List.mem_range.mp hi)
    rw [he, hh] at hpost
    exact hpost

/-- Stores in the upper half of the challenge preserve the saved arguments. -/
theorem Ctx.store {t t' : State} (hc : Ctx L g mx m₀ t)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hmx : t'.mxcsr = t.mxcsr)
    (hg : t'.gpr = t.gpr) (hf : Frame [⟨L.B + BitVec.ofNat 64 48, 32⟩] t.mem t'.mem) :
    Ctx L g mx m₀ t' := by
  have keep : ∀ d, 144 ≤ d → d + 8 ≤ 184 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 := by
    intro d h₁ h₂
    exact hf.readW (Region.contains_self _ _) (by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, by rw [hg]; exact hc.rsp,
    fun r hr h => by rw [hg]; exact hc.cs r hr h, by rw [hmx]; exact hc.mx,
    (keep 144 (by omega) (by omega)).trans hc.pScr,
    (keep 152 (by omega) (by omega)).trans hc.pSig,
    (keep 160 (by omega) (by omega)).trans hc.pLen,
    (keep 168 (by omega) (by omega)).trans hc.pMsg,
    (keep 176 (by omega) (by omega)).trans hc.pPk,
    hc.frame.trans (Frame.sub hf ?_)⟩
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨L.STK, by simp, Offset.sub_base _ (by decide)⟩

theorem extend_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block extendChallenge) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 48, 32⟩] t.mem t'.mem ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 48) 64 = 0 ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 56) 64 = 0 ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 64) 64 = 0 ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 72) 64 = 0 := by
  have w0 := hc.inFrW (d := 48) (by omega) (by omega)
  have w1 := hc.inFrW (d := 56) (by omega) (by omega)
  have w2 := hc.inFrW (d := 64) (by omega) (by omega)
  have w3 := hc.inFrW (d := 72) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [extendChallenge, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32,
    State.setReg32, State.store64, BitVec.xor_self, BitVec.setWidth_zero, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags,
    reduceCtorEq, ite_false, ite_true, ea_stk, hc.rsp, add_add, Nat.reduceAdd,
    w0, w1, w2, w3, Option.bind_some, Option.some.injEq, exists_eq_left']
  obtain ⟨hf, h0, h1, h2, h3⟩ := PublicKey.four_ok (L.B + BitVec.ofNat 64 32) t.mem 0 0 0 0
  simp only [add_add, Nat.reduceAdd] at hf h0 h1 h2 h3
  have hz := hc.regs (t' := (arithFlags t (0 : BitVec 32) false false).setReg .rax 0) rfl rfl rfl rfl (by cs_tac)
  exact ⟨hz.store rfl rfl rfl rfl hf, hf, h0, h1, h2, h3⟩

end VG.Proof.Ed25519.X86_64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86_64.VerifyMessage.Equation`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.VerifyMessage.Encoding`. -/
section
/-! The zero-extended scalar is exactly the corrected specification's challenge. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage
open VG
open VG.Spec.Ed25519

theorem reduced_challenge (digest : List Byte) :
    encodeLE 64 (decodeLE digest % L) = scalarReduce digest ++ encodeLE 32 0 := by
  simp only [scalarReduce, Proof.Ed25519.X86_64.encodeLE_eq]
  rw [show (64 : Nat) = 32 + 32 from rfl, Proof.X25519.leBytes_add]
  have hL : L ≤ 256 ^ 32 := by decide
  have hpos : 0 < L := by decide
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) hL)]

theorem zero_words (m : Mem) (p : Addr)
    (h0 : m.readW p 64 = 0) (h1 : m.readW (p + 8) 64 = 0)
    (h2 : m.readW (p + 16) 64 = 0)
    (h3 : m.readW (p + 24) 64 = 0) :
    bytesAt m p 32 = encodeLE 32 0 := by
  rw [Proof.Ed25519.X86_64.encodeLE_eq]
  exact Proof.X25519.bytesAt_leBytes_words64 m p 0
    (by rw [h0]; rfl) (by rw [h1]; rfl) (by rw [h2]; rfl) (by rw [h3]; rfl)

end VG.Proof.Ed25519.X86_64.VerifyMessage
end

/-! Connect the reduced challenge to the verified group equation. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
variable {dbl : VG.Prog VG.X86_64.isa} [VG.Proof.Ed25519.X86_64.EdDouble dbl]
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (verifyEquation)
open VG.Impl.Ed25519.X86_64.VerifyMessage
open VG.Proof.Ed25519.X86_64.PublicKey
  (within_base gpr_ce rsp_ce sub8 ea_stk add_add)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def EqArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.pk ∧ t.gpr .rsi = L.sig ∧ t.gpr .rdx = L.B + BitVec.ofNat 64 16 ∧
    t.gpr .rcx = L.scr

theorem equationArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block equationArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ EqArgs L t' := by
  have h144 := hc.inFr (d := 144) (by omega) (by omega)
  have h152 := hc.inFr (d := 152) (by omega) (by omega)
  have h176 := hc.inFr (d := 176) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [equationArgs, fScratch, fSignature, fPublicKey,
    runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    Option.map_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, h144, h152, h176, Option.some.injEq, exists_eq_left', hc.pScr, hc.pSig, hc.pPk, EqArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, trivial, trivial, trivial⟩

abbrev eqRd (L : Lay) : List Region := [L.PK, L.SIG, ⟨L.B + BitVec.ofNat 64 16, 64⟩]
abbrev eqWr (L : Lay) : List Region := [L.SCR]

theorem eq_regs {t : State} (ha : EqArgs L t) (rd wr : List Region) :
    EqArgs L (t.callEntry.withRegions rd wr) :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2⟩

theorem eq_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : EqArgs L t) :
    verifyLocal.pre (t.callEntry.withRegions (eqRd L) (eqWr L)) := by
  obtain ⟨hdi, hsi, hdx, hcx⟩ := eq_regs ha (eqRd L) (eqWr L)
  simp only [verifyLocal, rsp_ce, hdi, hsi, hdx, hcx, hc.rsp, sub8,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial, hL.sc L.PK (by simp [Lay.inputs]), hL.sc L.SIG (by simp [Lay.inputs]),
    by simpa using hL.stk_scr (d := 16) (n := 64) (e := 0) (k := 8192) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 8192) (by omega) (by omega), hL.nc⟩

/-- What the call of the equation checker `c` needs of its code, beyond its
correctness: it restores MXCSR (`ctlOk`), writes `rsp` only as calls and
returns do, nests no calls, and writes no stack pointer. Decided for each
checker in the registration file. -/
structure EqCode (c : Prog isa) : Prop where
  mx : VG.Proof.Ed25519.X86_64.MxcsrOk c
  noSp : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  depth : c.depth ≤ 1
  spSafe : c.all (fun i => !isa.writesSp i) = true

theorem eq_call (hq : EqCode (VG.Impl.Ed25519.X86_64.verifyEquation fld dbl)) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : EqArgs L t)
    {challenge : List Byte} (hh : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 64 = challenge) :
    WP isa (.call ("vg_ed25519_verify_equation" ++ fs) (verifyEquation fld dbl)) t fun t' => Ctx L g mx m₀ t' ∧
      t'.gpr .rax = Proof.Ed25519.X86_64.signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt m₀ L.pk 32) (Spec.Ed25519.bytesAt m₀ L.sig 64) challenge) := by
  refine call_ok hL (verify_ok hq.mx) (Proof.Pbkdf2.Md.X86_64.nosp_of hq.noSp)
    hq.depth hc (eq_pre hL hc ha) ?_ ?_
    fun s' hc' _ _ ⟨s₂, _, hg, hpost⟩ => ⟨hc', ?_⟩
  · intro r hr
    simp only [eqRd, eqWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨L.PK, by simp [Lay.inputs], within_base _ (by omega)⟩
    · exact ⟨L.SIG, by simp [Lay.inputs], within_base _ (by omega)⟩
    · exact ⟨L.FR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · intro r hr
    simp only [eqWr, List.mem_singleton] at hr
    subst hr
    exact .inr (within_base _ (by omega))
  · obtain ⟨hdi, hsi, hdx, -⟩ := eq_regs ha (eqRd L) (eqWr L)
    change s₂.gpr .rax = Proof.Ed25519.X86_64.signWord (Spec.Ed25519.verifyEquation _ _ _) at hpost
    rw [hg .rax (by decide), hdi, hsi, hdx, State.withRegions_mem] at hpost
    have hpk := hc.ce_bytes hL (r := L.PK)
      ⟨L.PK, by simp [Lay.inputs], within_base _ (by omega)⟩ (by decide : 32 ≤ 2 ^ 64)
    have hsig := hc.ce_bytes hL (r := L.SIG)
      ⟨L.SIG, by simp [Lay.inputs], within_base _ (by omega)⟩ (by decide : 64 ≤ 2 ^ 64)
    have he : Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 16) 64 =
        Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 64 := by
      apply List.map_congr_left
      intro i hi
      exact PublicKey.ce_byte t (R := ⟨L.B + BitVec.ofNat 64 16, 64⟩) (i := i)
        (by rw [hc.ret]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by decide : 64 ≤ 2 ^ 64) (List.mem_range.mp hi)
    change Spec.Ed25519.bytesAt _ L.pk 32 = _ at hpk
    change Spec.Ed25519.bytesAt _ L.sig 64 = _ at hsig
    rw [hpk, hsig, he, hh] at hpost
    exact hpost

end VG.Proof.Ed25519.X86_64.VerifyMessage
end

/-! Correctness of the complete verifier's frame body. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
variable {dbl : VG.Prog VG.X86_64.isa} [VG.Proof.Ed25519.X86_64.EdDouble dbl]
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.VerifyMessage
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem extend_reduced {t : State} (hc : Ctx L g mx m₀ t) {digest : List Byte}
    (hr : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32 = Spec.Ed25519.scalarReduce digest) :
    WP isa (.block extendChallenge) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 64 =
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) := by
  refine WP.mono (extend_ok hc) fun t' ⟨hc', hf, h0, h1, h2, h3⟩ => ⟨hc', ?_⟩
  have hlo : Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 32 =
      Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32 := by
    apply List.map_congr_left
    intro i hi
    exact Frame.bytes (R := ⟨L.B + BitVec.ofNat 64 16, 32⟩) hf (by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide : 32 ≤ 2 ^ 64)
      (List.mem_range.mp hi)
  have hhi := zero_words t'.mem (L.B + BitVec.ofNat 64 48) h0
    (by change t'.mem.readW ((L.B + BitVec.ofNat 64 48) + BitVec.ofNat 64 8) 64 = 0
        rw [PublicKey.add_add]; exact h1)
    (by change t'.mem.readW ((L.B + BitVec.ofNat 64 48) + BitVec.ofNat 64 16) 64 = 0
        rw [PublicKey.add_add]; exact h2)
    (by change t'.mem.readW ((L.B + BitVec.ofNat 64 48) + BitVec.ofNat 64 24) 64 = 0
        rw [PublicKey.add_add]; exact h3)
  have hsplit : Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 64 =
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 32 ++
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 48) 32 := by
    have h := Proof.X25519.bytesAt_add t'.mem (L.B + BitVec.ofNat 64 16) 32 32
    rw [PublicKey.add_add] at h
    exact h
  rw [hsplit, hlo, hr, hhi, reduced_challenge]

theorem challengeInput_eq : challengeInput L m₀ =
    (Spec.Ed25519.bytesAt m₀ L.sig 64).take 32 ++ Spec.Ed25519.bytesAt m₀ L.pk 32 ++
      Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat := by
  have h : (Spec.Ed25519.bytesAt m₀ L.sig 64).take 32 = Spec.Ed25519.bytesAt m₀ L.sig 32 :=
    PublicKey.take_bytesAt m₀ L.sig
  rw [h]
  rfl

theorem body_ok (hq : EqCode (VG.Impl.Ed25519.X86_64.verifyEquation fld dbl)) (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (hlen : 64 + L.len.toNat < 2 ^ 64) :
    WP isa (body fld dbl fs v.callee v.suffix) t fun t' => Ctx L g mx m₀ t' ∧
      t'.gpr .rax = Proof.Ed25519.X86_64.signWord (Spec.Ed25519.verify
        (Spec.Ed25519.bytesAt m₀ L.pk 32) (Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat)
        (Spec.Ed25519.bytesAt m₀ L.sig 64)) := by
  refine WP.seq (WP.mono (hash_ok v hL hc hlen) fun t₁ ⟨hc₁, hh₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (reduceArgs_ok hc₁) fun t₂ ⟨hc₂, hm₂, ha₂⟩ =>
    WP.mono (reduce_call hL hc₂ ha₂ (hm₂ ▸ hh₁)) fun t₃ ⟨hc₃, hr₃⟩ => ?_))
  refine WP.seq (WP.mono (extend_reduced hc₃ hr₃) fun t₄ ⟨hc₄, he₄⟩ => ?_)
  refine WP.seq (WP.mono (equationArgs_ok hc₄) fun t₅ ⟨hc₅, hm₅, ha₅⟩ => ?_)
  have he₅ := hm₅ ▸ he₄
  rw [challengeInput_eq] at he₅
  exact eq_call hq hL hc₅ ha₅ he₅

end VG.Proof.Ed25519.X86_64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86_64.VerifyMessage.CTAccess`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.VerifyMessage.Entry`. -/
section
/-! Entry contract and stack frame of complete Ed25519 verification. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage
open VG VG.X86_64

/-- The disjoint scratch allocation leaves room for the hash's 64-byte prefix. -/
theorem Lay.Ok.message_bound {L : Lay} (h : L.Ok) : 64 + L.len.toNat < 2 ^ 64 := by
  have hd := h.sc L.MSG (by simp [Lay.inputs])
  have nm := h.nm
  have nc := h.nc
  by_cases hz : L.len.toNat = 0
  · omega
  by_cases hp : L.msg ≤ L.scr
  · have hn : ¬ L.MSG.Contains L.scr 1 := fun hx => hd _ hx (by simp [Region.Contains])
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp] at hn
    have hp' : L.msg.toNat ≤ L.scr.toNat := hp
    omega
  · have hp' : L.scr ≤ L.msg := by
      change L.scr.toNat ≤ L.msg.toNat
      change ¬ L.msg.toNat ≤ L.scr.toNat at hp
      omega
    have hn : ¬ L.SCR.Contains L.msg 1 := fun hx => hd _ (by simp [Region.Contains]; omega) hx
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp'] at hn
    have hp'' : L.scr.toNat ≤ L.msg.toNat := hp'
    omega

def verifyMessageLocal : Contract isa where
  pre s := 184 ≤ (s.gpr .rsp).toNat ∧
    s.rd = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, 64⟩] ∧
    s.wr = [⟨s.gpr .r8, 8192⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .r8, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩ ⟨s.gpr .r8, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, 64⟩ ⟨s.gpr .r8, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, 64⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .r8, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 184, 184⟩ ⟨s.gpr .rdi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 184, 184⟩ ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 184, 184⟩ ⟨s.gpr .rcx, 64⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 184, 184⟩ ⟨s.gpr .r8, 8192⟩ ∧
    (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64
  post s t := t.gpr .rax = if Spec.Ed25519.verify
    (Spec.Ed25519.bytesAt s.mem (s.gpr .rdi) 32)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .rcx) 64) then 1 else 0
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧
    s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx ∧
    s.gpr .r8 = t.gpr .r8 ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .rdi) 32 = Spec.Ed25519.bytesAt t.mem (t.gpr .rdi) 32 ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
      Spec.Ed25519.bytesAt t.mem (t.gpr .rsi) (t.gpr .rdx).toNat ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .rcx) 64 = Spec.Ed25519.bytesAt t.mem (t.gpr .rcx) 64

def lay (s : State) : Lay :=
  ⟨s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rcx, s.gpr .r8, s.gpr .rsp - BitVec.ofNat 64 184⟩

theorem lay_ret (s : State) : (lay s).B + BitVec.ofNat 64 184 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem lay_ok {s : State} (h : verifyMessageLocal.pre s) : (lay s).Ok := by
  obtain ⟨-, -, -, pc, mc, sc, rp, rm, rs, rc, kp, km, ks, kc, np, nm, ns, nc⟩ := h
  have e : (lay s).RET = ⟨s.gpr .rsp, 8⟩ := by simp only [Lay.RET, lay_ret]
  refine ⟨?_, ?_, ?_, kc, e ▸ rc, np, nm, ns, nc⟩
  · intro r hr
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact pc
    · exact mc
    · exact sc
  · intro r hr
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact kp
    · exact km
    · exact ks
  · intro r hr
    rw [e]
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact rp
    · exact rm
    · exact rs

def pushRs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8,
    .rax, .rax, .rax, .rax, .rax, .rax, .rax, .rax,
    .rax, .rax, .rax, .rax, .rax, .rax, .rax, .rax]

theorem push_base (sp : Addr) :
    sp - BitVec.ofNat 64 (8 * 21) = sp - BitVec.ofNat 64 184 + BitVec.ofNat 64 16 := by bv_omega

theorem push_slot (sp : Addr) (j : Nat) (hj : j < 5) :
    sp - BitVec.ofNat 64 (8 * (j + 1)) = sp - BitVec.ofNat 64 184 + BitVec.ofNat 64 (176 - 8 * j) := by
  have : 8 * (j + 1) < 2 ^ 64 := by omega
  bv_omega

theorem push_ctx {s : State} (h : verifyMessageLocal.pre s) :
    Ctx (lay s) s.gpr s.mxcsr s.mem (pushed pushRs s) := by
  have hn : 8 * pushRs.length ≤ (s.gpr .rsp).toNat := by show 8 * 21 ≤ _; have := h.1; omega
  obtain ⟨hf, hw⟩ := pushRegs_mem s pushRs (by decide) hn
  have hw' : ∀ j (hj : j < 5), (pushed pushRs s).mem.readW
      ((lay s).B + BitVec.ofNat 64 (176 - 8 * j)) 64 = s.gpr (pushRs[j]'(by show j < 21; omega)) := fun j hj => by
    rw [← hw j (by show j < 21; omega)]; simp only [lay]; rw [push_slot _ j hj]; rfl
  refine ⟨by rw [pushed_rd, h.2.1]; rfl, ?_, ?_, fun r _ hr => pushed_gpr _ _ hr, by rw [pushed_mxcsr],
    hw' 4 (by omega), hw' 3 (by omega), hw' 2 (by omega), hw' 1 (by omega), hw' 0 (by omega), ?_⟩
  · rw [pushed_wr, h.2.2.1]; simp only [show pushRs.length = 21 from rfl, lay]; rw [push_base]
  · rw [pushed_rsp]; simp only [show pushRs.length = 21 from rfl, lay]; rw [push_base]
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨(lay s).STK, by simp, ?_⟩
    simp only [show pushRs.length = 21 from rfl]
    rw [push_base]
    exact Offset.sub_base _ (by omega)

end VG.Proof.Ed25519.X86_64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86_64.VerifyMessage.CTFramework`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.VerifyMessage.Correct`. -/
section
/-! Correctness and ABI preservation of the complete verification operation. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
variable {dbl : VG.Prog VG.X86_64.isa} [VG.Proof.Ed25519.X86_64.EdDouble dbl]
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.VerifyMessage
open VG.Proof.Sha512.X86_64 (Compress)

theorem pop_rsp (B : Addr) :
    B + BitVec.ofNat 64 16 + BitVec.ofNat 64 (8 * 21) = B + BitVec.ofNat 64 184 := by
  rw [PublicKey.add_add]

theorem verifyMessage_ok (hq : EqCode (VG.Impl.Ed25519.X86_64.verifyEquation fld dbl)) (v : Compress) {s : State} (h : verifyMessageLocal.pre s) :
    WP isa (code fld dbl fs v.callee v.suffix) s fun s' => abiPreserved s s' ∧ verifyMessageLocal.post s s' := by
  have hL := lay_ok h
  have hc := push_ctx h
  refine WP.frame (rs := pushRs) (by decide) (by decide) (by decide)
    (by show 8 * 21 ≤ _; have := h.1; omega)
    (WP.mono (body_ok hq v hL hc hL.message_bound)
      fun u ⟨hu, ho⟩ => ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm, ?_, ?_⟩)
  · have hrsp : (popped .r11 pushRs.length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, show pushRs.length = 21 from rfl, pop_rsp, lay_ret]
    refine ⟨fun r hr => ?_, ?_, by rw [popped_mxcsr, hu.mx]⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [popped_gpr _ _ _ hr' (PublicKey.ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [popped_mem]
      refine hu.frame.readW (r := (lay s).RET) ?_ ?_ (by decide)
      · rw [Lay.RET, lay_ret]; exact Region.contains_self _ _
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.rc
        · exact Offset.disjoint_base _ (by omega) (by omega)
  · change (popped .r11 pushRs.length u).gpr .rax = _
    rw [popped_gpr _ _ _ (by decide) (by decide), ho]
    rfl

end VG.Proof.Ed25519.X86_64.VerifyMessage
end

/-! Relating complete verification runs with equal public inputs. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage
open VG VG.X86_64
open VG.Proof.Ed25519.X86_64.PublicKey (Within)

def InputsEq (L : Lay) (m₁ m₂ : Mem) : Prop :=
  Spec.Ed25519.bytesAt m₁ L.pk 32 = Spec.Ed25519.bytesAt m₂ L.pk 32 ∧
  Spec.Ed25519.bytesAt m₁ L.msg L.len.toNat = Spec.Ed25519.bytesAt m₂ L.msg L.len.toNat ∧
  Spec.Ed25519.bytesAt m₁ L.sig 64 = Spec.Ed25519.bytesAt m₂ L.sig 64

abbrev Two.Env := Lay × (Reg → BitVec 64) × (Reg → BitVec 64) × BitVec 32 × BitVec 32 × Mem × Mem

def Two (Φ : Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Two.Env, e.1.Ok ∧ InputsEq e.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2 ∧
    Ctx e.1 e.2.1 e.2.2.2.1 e.2.2.2.2.2.1 a ∧ Ctx e.1 e.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.2 b ∧
    Φ e.1 e.2.2.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2.2.2 b

theorem two_wp {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hct : RelCT isa (Two Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g mx m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ mx₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ mx₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, hi, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem two_block {is : List Instr} {Φ : Lay → Mem → State → Prop}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rsp]) (.block is) hc).isSome = true) :
    RelCT isa (Two Φ) (.block is) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rsp]) (fun _ _ ⟨_, _, _, c₁, c₂, _, _⟩ =>
    Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact c₁.rsp.trans c₂.rsp.symm)) h

theorem two_blk {is : List Instr} {Φ Ψ : Lay → Mem → State → Prop}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rsp]) (.block is) hc).isSome = true)
    (hw : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g mx m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.block is) (Two Ψ) := two_wp (two_block h) hw

structure Access (L : Lay) (rd wr : List Region) : Prop where
  sub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.inputs ++ [L.FR, L.SCR], Within r R
  wsub : ∀ r ∈ wr, Within r L.DATA ∨ Within r L.SCR

theorem covers {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx L g mx m₀ t) {rd wr : List Region} (ha : Access L rd wr) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  constructor <;> apply Covers.of_sub <;> intro r hr
  · obtain ⟨R, hR, hs⟩ := ha.sub r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; exact hR, hs⟩
  · rw [hc.wr]
    rcases ha.wsub r hr with h | h
    · obtain ⟨off, hb, hn⟩ := h
      exact ⟨L.FR, by simp, off, hb, Nat.le_trans hn (by show 128 ≤ 168; decide)⟩
    · exact ⟨L.SCR, by simp, h⟩

theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ : Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, L.Ok → InputsEq L m₁ m₂ →
      Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (ha : ∀ L, Access L (rd L) (wr L)) :
    RelCT isa (Two Φ) (.call n c) fun _ _ => True :=
  RelCT.callEx hv hct fun _ _ ⟨⟨L, _⟩, hL, hi, c₁, c₂, f₁, f₂⟩ =>
    ⟨rd L, wr L, rd L, wr L, hpre _ _ _ _ _ hL c₁ f₁, hpre _ _ _ _ _ hL c₂ f₂,
      hpub _ _ _ _ _ _ _ _ _ hL hi c₁ c₂ f₁ f₂,
      (covers c₁ (ha L)).1, (covers c₁ (ha L)).2, (covers c₂ (ha L)).1, (covers c₂ (ha L)).2,
      c₁.rsp.trans c₂.rsp.symm⟩

theorem two_callP {n : String} {c : Prog isa} {k : Contract isa} {Φ : Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hd : c.depth ≤ 1) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, L.Ok → InputsEq L m₁ m₂ →
      Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (ha : ∀ L, Access L (rd L) (wr L)) :
    RelCT isa (Two Φ) (.call n c) (Two fun _ _ _ => True) :=
  two_wp (two_call hv hct rd wr hpre hpub ha) fun L _ _ _ _ hL hc hf =>
    call_ok hL hv hsp hd hc (hpre _ _ _ _ _ hL hc hf) (ha L).sub (ha L).wsub
      fun _ hc' _ _ _ => ⟨hc', trivial⟩

end VG.Proof.Ed25519.X86_64.VerifyMessage
end

/-! The regions passed to the verifier's subroutines. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage
open VG
open VG.Proof.Ed25519.X86_64.PublicKey (within_base within_off add_add)

theorem init_access (L : Lay) : Access L initRd (initWr L) where
  sub := by
    intro r hr
    simp only [initRd, initWr, List.nil_append, List.mem_singleton] at hr
    subst hr
    exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  wsub := by
    intro r hr
    simp only [initWr, List.mem_singleton] at hr
    subst hr
    exact .inr (within_base _ (by omega))

theorem upd_access (L : Lay) (p : Addr) (n : BitVec 64) (hi : Input L ⟨p, n.toNat⟩) :
    Access L [⟨p, n.toNat⟩] (updWr L) where
  sub := by
    intro r hr
    simp only [updWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨R, hR, hs⟩ := hi
      exact ⟨R, List.mem_append_left _ hR, hs⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  wsub := by
    intro r hr
    simp only [updWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (within_base _ (by omega))
    · exact .inr (within_off _ (by omega))

theorem fin_access (L : Lay) : Access L [] (finWr L) where
  sub := by
    intro r hr
    simp only [finWr, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.FR, by simp, 64, by rw [add_add], by show 64 + 64 ≤ 168; decide⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  wsub := by
    intro r hr
    simp only [finWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (within_base _ (by omega))
    · exact .inl ⟨64, by rw [add_add], by show 64 + 64 ≤ 128; decide⟩
    · exact .inr (within_off _ (by omega))

theorem reduce_access (L : Lay) : Access L (reduceRd L) (reduceWr L) where
  sub := by
    intro r hr
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.FR, by simp, 64, by rw [add_add], by show 64 + 64 ≤ 168; decide⟩
    · exact ⟨L.FR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  wsub := by
    intro r hr
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl (within_base _ (by omega))
    · exact .inr (within_base _ (by omega))

theorem eq_access (L : Lay) : Access L (eqRd L) (eqWr L) where
  sub := by
    intro r hr
    simp only [eqRd, eqWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨L.PK, by simp [Lay.inputs], within_base _ (by omega)⟩
    · exact ⟨L.SIG, by simp [Lay.inputs], within_base _ (by omega)⟩
    · exact ⟨L.FR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  wsub := by
    intro r hr
    simp only [eqWr, List.mem_singleton] at hr
    subst hr
    exact .inr (within_base _ (by omega))

end VG.Proof.Ed25519.X86_64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86_64.VerifyMessage.CTHash`. -/
section
/-! SHA-512's trace depends only on the input pointers and length. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.VerifyMessage
open VG.Proof.Ed25519.X86_64.PublicKey
  (gpr_ce rsp_ce nosp_init upd_verified upd_nosp upd_depth fin_verified fin_nosp fin_depth within_base)
open VG.Proof.Sha512.X86_64 (Compress)

theorem init_ct : RelCT isa (Two fun _ _ _ => True)
    (Impl.Ed25519.X86_64.callWith initArgs Spec.Sha512.init512Api.name
      (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512)) (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block initArgs) (Two fun L _ => InitArgs L) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (initArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := two_callP (n := Spec.Sha512.init512Api.name) (Φ := fun L _ => InitArgs L)
    (Proof.Sha512.X86_64.Stream.init_verified _).1 (Proof.Sha512.X86_64.Stream.init_verified _).2.1
    (nosp_init _) (by decide) (fun _ => initRd) initWr (fun _ _ _ _ _ hL hc ha => init_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ _ _ _ a₁ a₂ =>
      ((gpr_ce t₁ initRd (initWr L) (by decide)).trans a₁).trans
        ((gpr_ce t₂ initRd (initWr L) (by decide)).trans a₂).symm) init_access
  exact b.seq c

theorem upd_ct (v : Compress) (count : Lay → BitVec 64) (p : Lay → Addr) (n : Lay → BitVec 64)
    (hi : ∀ L, Input L ⟨p L, (n L).toNat⟩) :
    RelCT isa (Two fun L _ => UpdArgs L (count L) (p L) (n L))
      (.call (Spec.Sha512.updateApi.name ++ v.suffix) (Impl.Sha512.X86_64.Stream.update v.callee))
      (Two fun _ _ _ => True) := by
  exact two_callP (upd_verified v).1 (upd_verified v).2.1 (upd_nosp v) (upd_depth v)
    (fun L => [⟨p L, (n L).toNat⟩]) updWr
    (fun L _ _ _ _ hL hc ha => upd_pre hL hc ha (hi L))
    (fun L t₁ t₂ _ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁', r₁⟩ := upd_regs a₁ [⟨p L, (n L).toNat⟩] (updWr L)
      obtain ⟨d₂, s₂, x₂, c₂', r₂⟩ := upd_regs a₂ [⟨p L, (n L).toNat⟩] (updWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        r₁.trans r₂.symm, by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp]⟩)
    (fun L => upd_access L (p L) (n L) (hi L))

theorem finalize_ct (v : Compress) : RelCT isa (Two fun _ _ _ => True)
    (Impl.Ed25519.X86_64.callWith finalizeArgs (Spec.Sha512.finalizeApi.name ++ v.suffix)
      (Impl.Sha512.X86_64.Stream.finalize v.callee)) (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block finalizeArgs) (Two fun L _ => FinArgs L) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (finalizeArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := two_callP (n := Spec.Sha512.finalizeApi.name ++ v.suffix) (Φ := fun L _ => FinArgs L)
    (fin_verified v).1 (fin_verified v).2.1 (fin_nosp v) (fin_depth v) (fun _ => []) finWr
    (fun _ _ _ _ _ hL hc ha => fin_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁'⟩ := fin_regs a₁ [] (finWr L)
      obtain ⟨d₂, s₂, x₂, c₂'⟩ := fin_regs a₂ [] (finWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp]⟩) fin_access
  exact b.seq c

theorem hash_ct (v : Compress) : RelCT isa (Two fun _ _ _ => True)
    (hash v.callee v.suffix) (Two fun _ _ _ => True) := by
  have r : RelCT isa (Two fun _ _ _ => True) (.block (prefixArgs fSignature 0))
      (Two fun L _ => UpdArgs L 0 L.sig 32) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (prefixArgs_ok hc fSignature 0 (by decide) (by decide) _ hc.pSig)
        fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have a : RelCT isa (Two fun _ _ _ => True) (.block (prefixArgs fPublicKey 32))
      (Two fun L _ => UpdArgs L 32 L.pk 32) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (prefixArgs_ok hc fPublicKey 32 (by decide) (by decide) _ hc.pPk)
        fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have m : RelCT isa (Two fun _ _ _ => True) (.block messageArgs)
      (Two fun L _ => UpdArgs L 64 L.msg L.len) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (messageArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  exact init_ct.seq ((r.seq (upd_ct v (fun _ => 0) Lay.sig (fun _ => 32)
    (fun L => ⟨L.SIG, by simp [Lay.inputs], within_base _ (by decide)⟩))).seq
    ((a.seq (upd_ct v (fun _ => 32) Lay.pk (fun _ => 32)
      (fun L => ⟨L.PK, by simp [Lay.inputs], within_base _ (by decide)⟩))).seq
    ((m.seq (upd_ct v (fun _ => 64) Lay.msg Lay.len
      (fun L => ⟨L.MSG, by simp [Lay.inputs], within_base _ (by omega)⟩))).seq (finalize_ct v))))

end VG.Proof.Ed25519.X86_64.VerifyMessage
end

/-! The complete verifier leaks only its explicitly public inputs. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
variable {dbl : VG.Prog VG.X86_64.isa} [VG.Proof.Ed25519.X86_64.EdDouble dbl]
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (scalarReduce verifyEquation callWith)
open VG.Impl.Ed25519.X86_64.VerifyMessage
open VG.Proof.Ed25519.X86_64.PublicKey (gpr_ce rsp_ce within_base)
open VG.Proof.Sha512.X86_64 (Compress)

def Challenge (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.encodeLE 64
    (Spec.Ed25519.decodeLE (Spec.Sha512.sha512 (challengeInput L m)) % Spec.Ed25519.L)

def ChallengeReady (L : Lay) (m : Mem) (s : State) : Prop :=
  Spec.Ed25519.bytesAt s.mem (L.B + BitVec.ofNat 64 16) 64 = Challenge L m

theorem InputsEq.challenge {L : Lay} {m₁ m₂ : Mem} (hi : InputsEq L m₁ m₂) :
    Challenge L m₁ = Challenge L m₂ := by
  unfold Challenge
  rw [challengeInput_eq, challengeInput_eq, hi.1, hi.2.1, hi.2.2]

def prepare (v : Compress) : Prog isa :=
  .seq (hash v.callee v.suffix)
    (.seq (callWith reduceArgs "vg_ed25519_scalar_reduce" scalarReduce) (.block extendChallenge))

theorem prepare_ok (v : Compress) {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}
    (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (prepare v) t fun t' => Ctx L g mx m₀ t' ∧ ChallengeReady L m₀ t' := by
  refine WP.seq (WP.mono (hash_ok v hL hc hL.message_bound) fun t₁ ⟨hc₁, hh₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (reduceArgs_ok hc₁) fun t₂ ⟨hc₂, hm₂, ha₂⟩ =>
    WP.mono (reduce_call hL hc₂ ha₂ (hm₂ ▸ hh₁)) fun t₃ ⟨hc₃, hr₃⟩ => ?_))
  exact extend_reduced hc₃ hr₃

theorem reduce_ct : RelCT isa (Two fun _ _ _ => True)
    (callWith reduceArgs "vg_ed25519_scalar_reduce" scalarReduce) (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block reduceArgs) (Two fun L _ => ReduceArgs L) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (reduceArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := two_callP (n := "vg_ed25519_scalar_reduce") (Φ := fun L _ => ReduceArgs L)
    scalarReduce_ok scalarReduce_ct (Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide)) (by lit_decide)
    reduceRd reduceWr (fun _ _ _ _ _ hL hc ha => reduce_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁⟩ := reduce_regs a₁ (reduceRd L) (reduceWr L)
      obtain ⟨d₂, s₂, x₂⟩ := reduce_regs a₂ (reduceRd L) (reduceWr L)
      exact ⟨by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp], d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm⟩)
    reduce_access
  exact b.seq c

theorem prepare_ct (v : Compress) : RelCT isa (Two fun _ _ _ => True) (prepare v) (Two ChallengeReady) :=
  two_wp ((hash_ct v).seq (reduce_ct.seq (two_block (by taint_decide))))
    (fun _ _ _ _ _ hL hc _ => prepare_ok v hL hc)

def EquationReady (L : Lay) (m : Mem) (s : State) : Prop := EqArgs L s ∧ ChallengeReady L m s

theorem equationArgs_ct : RelCT isa (Two ChallengeReady) (.block equationArgs) (Two EquationReady) :=
  two_blk (by taint_decide) fun _ _ _ _ _ _ hc hh =>
    WP.mono (equationArgs_ok hc) fun _ ⟨hc', hm, ha⟩ => ⟨hc', ha, by unfold ChallengeReady at hh ⊢; rw [hm]; exact hh⟩

theorem ce_challenge {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx L g mx m₀ t) (hr : ChallengeReady L m₀ t) :
    Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 16) 64 = Challenge L m₀ := by
  rw [← hr]
  apply List.map_congr_left
  intro i hi
  exact PublicKey.ce_byte t (R := ⟨L.B + BitVec.ofNat 64 16, 64⟩) (i := i)
    (by rw [hc.ret]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
    (by decide : 64 ≤ 2 ^ 64) (List.mem_range.mp hi)

theorem equation_ct (hq : EqCode (VG.Impl.Ed25519.X86_64.verifyEquation fld dbl)) : RelCT isa (Two EquationReady)
    (.call ("vg_ed25519_verify_equation" ++ fs) (verifyEquation fld dbl)) fun _ _ => True := by
  refine two_call (verify_ok hq.mx) verify_ct eqRd eqWr
    (fun _ _ _ _ _ hL hc ha => eq_pre hL hc ha.1) ?_ eq_access
  intro L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂ hL hi c₁ c₂ a₁ a₂
  obtain ⟨d₁, s₁, x₁, r₁⟩ := eq_regs a₁.1 (eqRd L) (eqWr L)
  obtain ⟨d₂, s₂, x₂, r₂⟩ := eq_regs a₂.1 (eqRd L) (eqWr L)
  refine ⟨by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp], d₁.trans d₂.symm,
    s₁.trans s₂.symm, x₁.trans x₂.symm, r₁.trans r₂.symm, ?_, ?_, ?_⟩
  · rw [d₁, d₂, State.withRegions_mem, State.withRegions_mem]
    have h₁ := c₁.ce_bytes hL (r := L.PK)
      ⟨L.PK, by simp [Lay.inputs], within_base _ (by omega)⟩ (by decide : 32 ≤ 2 ^ 64)
    have h₂ := c₂.ce_bytes hL (r := L.PK)
      ⟨L.PK, by simp [Lay.inputs], within_base _ (by omega)⟩ (by decide : 32 ≤ 2 ^ 64)
    exact h₁.trans (hi.1.trans h₂.symm)
  · rw [s₁, s₂, State.withRegions_mem, State.withRegions_mem]
    have h₁ := c₁.ce_bytes hL (r := L.SIG)
      ⟨L.SIG, by simp [Lay.inputs], within_base _ (by omega)⟩ (by decide : 64 ≤ 2 ^ 64)
    have h₂ := c₂.ce_bytes hL (r := L.SIG)
      ⟨L.SIG, by simp [Lay.inputs], within_base _ (by omega)⟩ (by decide : 64 ≤ 2 ^ 64)
    exact h₁.trans (hi.2.2.trans h₂.symm)
  · rw [x₁, x₂, State.withRegions_mem, State.withRegions_mem, ce_challenge c₁ a₁.2,
      ce_challenge c₂ a₂.2, hi.challenge]

theorem body_ct (hq : EqCode (VG.Impl.Ed25519.X86_64.verifyEquation fld dbl)) (v : Compress) : RelCT isa (Two fun _ _ _ => True)
    (body fld dbl fs v.callee v.suffix) fun _ _ => True := by
  have h := (prepare_ct v).seq (equationArgs_ct.seq (equation_ct (fs := fs) hq))
  have reassoc : ∀ {s t s'}, Exec isa (body fld dbl fs v.callee v.suffix) s t s' →
      Exec isa (.seq (prepare v) (callWith equationArgs ("vg_ed25519_verify_equation" ++ fs) (verifyEquation fld dbl))) s t s' := by
    intro s t s' he
    cases he with
    | seq hh hr =>
      cases hr with
      | seq hr he =>
        cases he with
        | seq hx he =>
          simpa only [prepare, List.append_assoc] using Exec.seq (Exec.seq hh (Exec.seq hr hx)) he
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp he₁ he₂
  exact h _ _ _ _ _ _ hp (reassoc he₁) (reassoc he₂)

theorem verifyMessage_ct (hq : EqCode (VG.Impl.Ed25519.X86_64.verifyEquation fld dbl)) (v : Compress) :
    ConstantTime isa verifyMessageLocal.pre verifyMessageLocal.pub (code fld dbl fs v.callee v.suffix) := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => h.2.2.1)
    (RelCT.mono (body_ct hq v) ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hsp, hdi, hsi, hdx, hcx, h8, hp, hm, hs⟩, rfl, rfl⟩
  have e : lay s₂ = lay s₁ := by simp only [lay, hsp, hdi, hsi, hdx, hcx, h8]
  have hi : InputsEq (lay s₁) s₁.mem s₂.mem := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [lay, hdi] using hp
    · simpa only [lay, hsi, hdx] using hm
    · simpa only [lay, hcx] using hs
  exact ⟨⟨lay s₁, s₁.gpr, s₂.gpr, s₁.mxcsr, s₂.mxcsr, s₁.mem, s₂.mem⟩, lay_ok h₁,
    hi, push_ctx h₁, e ▸ push_ctx h₂, trivial, trivial⟩

end VG.Proof.Ed25519.X86_64.VerifyMessage
