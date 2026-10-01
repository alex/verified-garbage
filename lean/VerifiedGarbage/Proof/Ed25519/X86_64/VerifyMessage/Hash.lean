import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.Args

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
