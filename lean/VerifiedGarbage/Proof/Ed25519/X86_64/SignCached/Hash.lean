import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Args

/-! Modular SHA-512 calls used by the complete signer. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (callWith)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey
  (Within within_base within_off gpr_ce rsp_ce sub8 sub88 nosp_init upd_verified upd_nosp upd_depth
   fin_verified fin_nosp fin_depth ce_byte)
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- A hash input can be a caller buffer or a saved value in the frame. -/
structure Input (L : Lay) (r : Region) : Prop where
  cover : ∃ R ∈ L.inputs ++ [L.FR, L.OUT, L.SCR], Within r R
  scratch : r.Disjoint L.SCR
  below : (⟨L.B, 16⟩ : Region).Disjoint r

theorem Input.scr {r : Region} (hi : Input L r) {d n : Nat} (h : d + n ≤ 8192) :
    r.Disjoint ⟨L.scr + BitVec.ofNat 64 d, n⟩ :=
  hi.scratch.sub_right (Offset.sub_base _ h)

theorem Input.stk {r : Region} (hi : Input L r) {d n : Nat} (h : d + n ≤ 16) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r :=
  hi.below.sub_left (Offset.sub_base _ h)

theorem Ctx.ce_bytes {t : State} (hc : Ctx L g mx m₀ t)
    {r : Region} (hi : Input L r) (hn : r.len ≤ 2 ^ 64) :
    Spec.Sha512.bytesAt t.callEntry.mem r.base r.len = Spec.Ed25519.bytesAt t.mem r.base r.len := by
  unfold Spec.Sha512.bytesAt Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i h => ?_
  exact ce_byte t (by rw [hc.ret]; exact hi.stk (by omega)) hn (List.mem_range.mp h)

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
      fun t' => Ctx L g mx m₀ t' ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr [] ∧ Frame (initWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine call_ok hL (Proof.Sha512.X86_64.Stream.init_verified _).1 (nosp_init _) (by decide) hc
    (init_pre hL hc ha) ?_ ?_ fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_, hf⟩
  · rintro r hr
    simp only [initRd, initWr, List.nil_append, List.mem_singleton] at hr
    subst hr
    exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · rintro r hr
    simp only [initWr, List.mem_singleton] at hr
    subst hr
    exact .inr (.inr (within_base _ (by omega)))
  · have := hpost
    simp only [Proof.Sha512.initX86_64, (gpr_ce t initRd (initWr L) (r := .rdi) (by decide)).trans ha] at this
    rwa [← hm]

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
    by simpa using hi.scr (d := 0) (n := 192) (by omega), hi.scr (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    by simpa using hi.stk (d := 0) (n := 8) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 192) (k := 1376) (by omega) (by omega)⟩

theorem upd_call (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    {prev : List Byte} {count : BitVec 64} {p : Addr} {n : BitVec 64}
    (ha : UpdArgs L count p n t) (hi : Input L ⟨p, n.toNat⟩)
    (hcount : count = BitVec.ofNat 64 prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr prev) :
    WP isa (.call (Spec.Sha512.updateApi.name ++ v.suffix) (Impl.Sha512.X86_64.Stream.update v.callee)) t
      fun t' => Ctx L g mx m₀ t' ∧
        Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr (prev ++ Spec.Ed25519.bytesAt t.mem p n.toNat) ∧
        Frame (updWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine call_ok hL (upd_verified v).1 (upd_nosp v) (upd_depth v) hc (upd_pre hL hc ha hi) ?_ ?_
    fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_, hf⟩
  · intro r hr
    simp only [updWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hi.cover
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  · intro r hr
    simp only [updWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inr (within_base _ (by omega)))
    · exact .inr (.inr (within_off _ (by omega)))
  · obtain ⟨hdi, hsi, hdx, hcx, -⟩ := upd_regs ha [⟨p, n.toNat⟩] (updWr L)
    have h := hpost Spec.Sha512.H0_512 prev
      (by rw [State.withRegions_mem, hdi]; exact hc.ce_repr hL hr) (hsi.trans hcount)
    simp only [State.withRegions_mem, hdi, hdx, hcx, hm] at h
    rw [hc.ce_bytes hi (Nat.le_of_lt n.isLt)] at h
    exact h


abbrev finWr (L : Lay) : List Region :=
  [⟨L.scr, 192⟩, ⟨L.B + BitVec.ofNat 64 144, 64⟩, ⟨L.scr + BitVec.ofNat 64 192, 1376⟩]

theorem fin_regs {t : State} {count : BitVec 64} (ha : FinArgs L count t) (rd wr : List Region) :
    FinArgs L count (t.callEntry.withRegions rd wr) :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2⟩

theorem fin_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) {count : BitVec 64} (ha : FinArgs L count t) :
    Proof.Sha512.finalizeX86_64.pre (t.callEntry.withRegions [] (finWr L)) := by
  obtain ⟨hdi, -, hdx, hcx⟩ := fin_regs ha [] (finWr L)
  simp only [Proof.Sha512.finalizeX86_64, rsp_ce, hdi, hdx, hcx, hc.rsp, sub8, sub88,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial,
    by simpa using (hL.stk_scr (d := 144) (n := 64) (e := 0) (k := 192) (by omega) (by omega)).symm,
    Offset.base_disjoint _ (by omega) (by omega), hL.stk_scr (by omega) (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    Offset.disjoint _ (by omega) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    Offset.base_disjoint _ (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 192) (k := 1376) (by omega) (by omega)⟩

theorem fin_call (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) {count : BitVec 64} (ha : FinArgs L count t)
    {message : List Byte} (hmess : message.length < 2 ^ 64)
    (hlen : count = BitVec.ofNat 64 message.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr message) :
    WP isa (.call (Spec.Sha512.finalizeApi.name ++ v.suffix) (Impl.Sha512.X86_64.Stream.finalize v.callee)) t
      fun t' => Ctx L g mx m₀ t' ∧ Spec.Sha512.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) 64 =
        Spec.Sha512.sha512 message ∧ Frame (finWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine call_ok hL (fin_verified v).1 (fin_nosp v) (fin_depth v) hc (fin_pre hL hc ha) ?_ ?_
    fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_, hf⟩
  · intro r hr
    simp only [finWr, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.FR, by simp, 128, by rw [PublicKey.add_add], by show 128 + 64 ≤ 248; decide⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  · intro r hr
    simp only [finWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inr (within_base _ (by omega)))
    · exact .inl ⟨128, by rw [PublicKey.add_add], by show 128 + 64 ≤ 192; decide⟩
    · exact .inr (.inr (within_off _ (by omega)))
  · obtain ⟨hdi, hsi, hdx, -⟩ := fin_regs ha [] (finWr L)
    have h := hpost Spec.Sha512.H0_512 message
      (by rw [State.withRegions_mem, hdi]; exact hc.ce_repr hL hr) hmess (hsi.trans hlen)
    rw [hdx, hm] at h
    exact h

end VG.Proof.Ed25519.X86_64.SignCached
