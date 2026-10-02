import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Prep
import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Contract
import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Verified

/-!
# Streaming RC2-CBC on AArch64: the update functions

Untrusted: everything here is checked by Lean. With no complete block, the
data is appended to the pending bytes (`short_ok`); otherwise, inside the
frame saving `x30`, the copies (`prep_ok`) are followed by the call of the
verified CBC function (`call_ok`). `update_post_short` and
`update_post_long` (`Proof/Rc2/Stream.lean`) turn the memory each leaves
into the contract's postcondition.
-/

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64
open VG.Impl.Rc2.AArch64.Stream (copy short prep longMain cbcCall update)
open VG.Proof.MdStream.AArch64 (Upd wp_add toNat_ofNat_lt eval_zero ofNat_beq_zero)
open VG.WriteBytes (writeBytes)

/-! ## The CBC call -/

theorem cbc_correct' (d : Spec.Rc2.Direction) (s : State) (hs : (Cbc.contract d).pre s) :
    ∃ t s', Exec isa (Impl.Rc2.AArch64.Cbc.cbc d) s t s' ∧ abiPreserved s s' ∧
      (Cbc.contract d).post s s' := by
  cases d
  · exact Cbc.encrypt_correct s hs
  · exact Cbc.decrypt_correct s hs

theorem cbcCall_eq (d : Spec.Rc2.Direction) : cbcCall d =
    .call (match d with | .encrypt => "vg_rc2_cbc_encrypt" | .decrypt => "vg_rc2_cbc_decrypt")
      (Impl.Rc2.AArch64.Cbc.cbc d) := by cases d <;> rfl

theorem cbc_noFrames (d : Spec.Rc2.Direction) : (Impl.Rc2.AArch64.Cbc.cbc d).noFrames = true := by
  cases d
  · change Impl.Rc2.AArch64.Cbc.encrypt.noFrames = true; lit_decide
  · change Impl.Rc2.AArch64.Cbc.decrypt.noFrames = true; lit_decide

/-- The CBC function on the `n` blocks at `op`, with the schedule at `c` and the
chaining value at `c + 128`, with the update's regions. -/
theorem call_ok (d : Spec.Rc2.Direction) {s : State} {c dp op b : Addr} {len ol n : Nat}
    (h0 : s.gpr .x0 = c) (h1 : s.gpr .x1 = c + BitVec.ofNat 64 128) (h2 : s.gpr .x2 = op)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 n) (h4 : s.gpr .x4 = b) (hn : 8 * n = ol) (hol : ol < 2 ^ 64)
    (hrd : s.rd = [⟨dp, len⟩]) (hwr : s.wr = [⟨c, 144⟩, ⟨op, ol⟩, ⟨b, 576⟩])
    (co : Region.Disjoint ⟨c, 144⟩ ⟨op, ol⟩) (cb : Region.Disjoint ⟨c, 144⟩ ⟨b, 576⟩)
    (ob : Region.Disjoint ⟨op, ol⟩ ⟨b, 576⟩) (fo : op.toNat + ol ≤ 2 ^ 64)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨c + BitVec.ofNat 64 128, 8⟩, ⟨op, 8 * n⟩, ⟨b, 512⟩] s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      Spec.Rc2.blocksAt s'.mem op n = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem c) d
        (Spec.Rc2.blockAt s.mem (c + BitVec.ofNat 64 128)) (Spec.Rc2.blocksAt s.mem op n)).1 →
      Spec.Rc2.blockAt s'.mem (c + BitVec.ofNat 64 128) = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem c) d
        (Spec.Rc2.blockAt s.mem (c + BitVec.ofNat 64 128)) (Spec.Rc2.blocksAt s.mem op n)).2 →
      Q s') :
    WP isa (cbcCall d) s Q := by
  have e0 : s.callEntry.gpr .x0 = c := (State.callEntry_gpr _ (by decide)).trans h0
  have e1 : s.callEntry.gpr .x1 = c + BitVec.ofNat 64 128 := (State.callEntry_gpr _ (by decide)).trans h1
  have e2 : s.callEntry.gpr .x2 = op := (State.callEntry_gpr _ (by decide)).trans h2
  have e3 : s.callEntry.gpr .x3 = BitVec.ofNat 64 n := (State.callEntry_gpr _ (by decide)).trans h3
  have e4 : s.callEntry.gpr .x4 = b := (State.callEntry_gpr _ (by decide)).trans h4
  have hn' : (BitVec.ofNat 64 n).toNat = n := toNat_ofNat_lt (by omega)
  have ivS : Region.Sub ⟨c + BitVec.ofNat 64 128, 8⟩ ⟨c, 144⟩ := Offset.sub_base _ (by omega)
  have keyS : Region.Sub ⟨c, 128⟩ ⟨c, 144⟩ := Region.sub_prefix (by omega)
  have outS : Region.Sub ⟨op, 8 * n⟩ ⟨op, ol⟩ := Region.sub_prefix (by omega)
  have bufS : Region.Sub ⟨b, 512⟩ ⟨b, 576⟩ := Region.sub_prefix (by omega)
  have zero : ∀ x : Addr, x = x + BitVec.ofNat 64 0 := fun x => by simp
  rw [cbcCall_eq]
  refine WP.call (k := Cbc.contract d) (cbc_correct' d) (rd := [⟨c, 128⟩])
    (wr := [⟨c + BitVec.ofNat 64 128, 8⟩, ⟨op, 8 * n⟩, ⟨b, 512⟩]) ?_ ?_ ?_ ?_ (cbc_noFrames d)
  · simp only [Cbc.contract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, e0, e1, e2,
      e3, e4, hn']
    exact ⟨trivial, trivial, Offset.base_disjoint _ (Nat.le_refl _) (by omega),
      (co.sub_left keyS).sub_right outS, (cb.sub_left keyS).sub_right bufS,
      (co.sub_left ivS).sub_right outS, (cb.sub_left ivS).sub_right bufS,
      (ob.sub_left outS).sub_right bufS, by omega⟩
  · rw [hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨c, 144⟩, by simp, 0, zero c, by dsimp only; omega⟩
    · exact ⟨⟨c, 144⟩, by simp, 128, rfl, by dsimp only; omega⟩
    · exact ⟨⟨op, ol⟩, by simp, 0, zero op, by dsimp only; omega⟩
    · exact ⟨⟨b, 576⟩, by simp, 0, zero b, by dsimp only; omega⟩
  · rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨c, 144⟩, by simp, 128, rfl, by dsimp only; omega⟩
    · exact ⟨⟨op, ol⟩, by simp, 0, zero op, by dsimp only; omega⟩
    · exact ⟨⟨b, 576⟩, by simp, 0, zero b, by dsimp only; omega⟩
  · intro s' hr hw hsp hf hcs _ hpost
    simp only [Cbc.contract, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, e0, e1, e2,
      e3, hn'] at hpost
    exact hQ s' hr hw hsp hf hcs hpost.1 hpost.2

/-! ## The postcondition -/

/-- The update's postcondition, for the arguments of `Lay`. -/
def UPost (d : Spec.Rc2.Direction) (σ : State) (c dp op : Addr) (p len ol : Nat) (s' : State) : Prop :=
  Spec.Rc2.contextAt s'.mem c d ((p + len) % 8) =
      (Spec.Rc2.update (Spec.Rc2.contextAt σ.mem c d p) (Spec.Rc2.bytesAt σ.mem dp len)).1 ∧
    Spec.Rc2.bytesAt s'.mem op ol =
      (Spec.Rc2.update (Spec.Rc2.contextAt σ.mem c d p) (Spec.Rc2.bytesAt σ.mem dp len)).2

/-! ## No complete block -/

theorem short_ok (d : Spec.Rc2.Direction) {σ : State} {c dp op b : Addr} {p len ol : Nat}
    (h : Lay σ c dp op b p len ol) (hol : ol = 0) :
    WP isa short σ fun s' => (∀ r ∈ preserved, s'.gpr r = σ.gpr r) ∧ s'.sp = σ.sp ∧
      UPost d σ c dp op p len ol s' := by
  have p8 := h.p8
  have olq := h.olq
  have hpl : p + len < 8 := by omega
  unfold short
  refine WP.seq (wp_add fun s₁ u₁ => WP.block_nil ?_)
  refine copy_ok (A := dp) (B := c + BitVec.ofNat 64 (136 + p)) (k := len) (by decide) (by decide)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by rw [u₁.other _ (by decide), h.x2]; simp)
    (by rw [u₁.gpr, h.x0, h.x1, Offset.add_add, Nat.add_comm])
    (by rw [u₁.other _ (by decide), h.x3]) h.lenlt
    (fun i hi => by
      rw [u₁.rd, u₁.wr, h.rd]
      exact inR (R := ⟨dp, len⟩) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    (fun i hi => by
      rw [u₁.wr, h.wr, Offset.add_add]
      exact inR (R := ⟨c, 144⟩) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    (h.cd.sub_left (Offset.sub_base _ (by omega))).symm fun s' cp => ?_
  have hm : s'.mem = writeBytes σ.mem (c + BitVec.ofNat 64 (136 + p)) (Spec.Rc2.bytesAt σ.mem dp len) := by
    rw [cp.mem, u₁.mem]
  have hf := frame_writeBytes σ.mem (c + BitVec.ofNat 64 (136 + p)) dp len
  rw [← hm] at hf
  refine ⟨fun r hr => ?_, by rw [cp.sp, u₁.sp], ?_⟩
  · have hne : ∀ r ∈ preserved, r ≠ .x9 ∧ r ≠ .x2 ∧ r ≠ .x8 ∧ r ≠ .x3 := by decide
    obtain ⟨h1, h2, h3, h4⟩ := hne r hr
    rw [cp.other r h1 h2 h3 h4, u₁.other r h3]
  obtain ⟨r1, r2⟩ := update_post_short (d := d) (out := op) hpl
    (scheduleAt_frame hf c (by simpa using Offset.base_disjoint c (by omega) (by omega)))
    (blockAt_frame hf (c + 128) (by simpa using Offset.disjoint c (d := 128) (by omega) (by omega) (by omega)))
    (by
      rw [bytesAt_add, Proof.Rc2.bytesAt_frame hf _ _ (by omega)
        (by simpa using Offset.disjoint c (d := 136) (n := p) (by omega) (by omega) (by omega)),
        show (136 : Addr) = BitVec.ofNat 64 136 from rfl, Offset.add_add, hm,
        bytesAt_writeBytes' _ _ _ _ (by omega)])
  refine ⟨r1, ?_⟩
  rw [olq]; exact r2

/-! ## Complete blocks -/

theorem prep_keeps : prep.allInstrs (fun i => preserved.all fun r => dstOf i != some r) = true := by
  decide +kernel

/-- `update` with complete blocks, without its frame. -/
theorem long_ok (d : Spec.Rc2.Direction) {σ : State} {c dp op b : Addr} {p len ol : Nat}
    (h : Lay σ c dp op b p len ol) (hol : ol ≠ 0) :
    WP isa (longMain d) σ fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = σ.gpr r) ∧
      UPost d σ c dp op p len ol s' := by
  have p8 := h.p8
  have olq := h.olq
  have hl := h.lenlt
  have hpo : p ≤ ol := by omega
  unfold longMain
  refine WP.seq (WP.mono (WP.gprs (rs := preserved) (prep_ok h hol) prep_keeps (by decide +kernel)) fun s₁ ⟨hc, hk⟩ => ?_)
  refine call_ok d hc.x0 hc.x1 hc.x2 hc.x3 hc.x4 (n := (p + len) / 8) (by omega) h.ollt
    (hc.rd.trans h.rd) (hc.wr.trans h.wr) h.co h.cb h.ob h.fo
    fun s' hrd hwr hsp hf hcs hout hiv => ⟨fun r hr h30 => (hcs r hr h30).trans (hk r hr), ?_⟩
  have hctx : ∀ {e n : Nat}, e + n ≤ 144 → Region.Sub ⟨c + BitVec.ofNat 64 e, n⟩ ⟨c, 144⟩ :=
    fun he => Offset.sub_base _ he
  have co' : ∀ {e n : Nat}, e + n ≤ 144 → Region.Disjoint ⟨c + BitVec.ofNat 64 e, n⟩ ⟨op, ol⟩ :=
    fun he => h.co.sub_left (hctx he)
  have cb' : ∀ {e n : Nat}, e + n ≤ 144 → Region.Disjoint ⟨c + BitVec.ofNat 64 e, n⟩ ⟨b, 512⟩ :=
    fun he => (h.cb.sub_left (hctx he)).sub_right (Region.sub_prefix (by omega))
  have co0 : Region.Disjoint ⟨c, 128⟩ ⟨op, ol⟩ := h.co.sub_left (Region.sub_prefix (by omega))
  have cb0 : Region.Disjoint ⟨c, 128⟩ ⟨b, 512⟩ :=
    (h.cb.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega))
  have outS : Region.Sub ⟨op, 8 * ((p + len) / 8)⟩ ⟨op, ol⟩ := Region.sub_prefix (by omega)
  have hr : len + p - ol = (p + len) % 8 := by omega
  have pend := hc.pend
  rw [hr, show ol - p = (p + len) / 8 * 8 - p by omega] at pend
  obtain ⟨r1, r2⟩ := update_post_long (d := d) (m₁ := s₁.mem) (out := op) (p := p) (len := len)
    (by omega) (by omega) (by rw [← olq]; exact hc.out)
    (scheduleAt_frame hc.frame c (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact co0.sub_right (Region.sub_prefix (Nat.le_refl _))
      · exact Offset.base_disjoint c (k := 128) (e := 136) (n := 8) (by omega) (by omega)))
    (blockAt_frame hc.frame (c + 128) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact co' (e := 128) (by omega)
      · exact Offset.disjoint c (d := 128) (n := 8) (e := 136) (k := 8) (by omega) (by omega) (by omega)))
    (by
      rw [Proof.Rc2.bytesAt_frame hf _ _ (by omega) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl | rfl)
        · exact Offset.disjoint c (d := 136) (n := (p + len) % 8) (e := 128) (k := 8) (by omega) (by omega)
            (by omega)
        · exact (co' (e := 136) (n := (p + len) % 8) (by omega)).sub_right outS
        · exact cb' (e := 136) (n := (p + len) % 8) (by omega))]
      exact pend)
    (scheduleAt_frame hf c (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact Offset.base_disjoint c (k := 128) (e := 128) (n := 8) (by omega) (by omega)
      · exact co0.sub_right outS
      · exact cb0))
    hout hiv
  refine ⟨r1, ?_⟩
  rw [olq]; exact r2

/-! ## The whole update -/

theorem longMain_noFrames (d : Spec.Rc2.Direction) : (longMain d).noFrames = true := by
  cases d <;> decide +kernel

theorem update_correct (d : Spec.Rc2.Direction) (s₀ : State) (hs : (updateContract d).pre s₀) :
    WP isa (update d) s₀ fun s' => GprAbi s₀ s' ∧ (updateContract d).post s₀ s' := by
  obtain ⟨sp16, hrd, hwr, cd, co, cb, dout, db, ob, kc, kd, ko, kb, -, -, fo, -, p8, olq⟩ := hs
  have h : Lay s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x4) (s₀.gpr .x6) (s₀.gpr .x1).toNat
      (s₀.gpr .x3).toNat (s₀.gpr .x5).toNat :=
    ⟨rfl, ofNat_toNat' _, rfl, ofNat_toNat' _, rfl, ofNat_toNat' _, rfl, hrd, hwr, cd, co, cb, dout, db,
      ob, fo, (s₀.gpr .x3).isLt, (s₀.gpr .x5).isLt, p8, olq⟩
  unfold update
  refine WP.ite (decide ((s₀.gpr .x5).toNat = 0))
    (by show VG.AArch64.eval (.zero .x .x5) s₀ = _
        have e := ofNat_beq_zero (s₀.gpr .x5).isLt
        rw [← h.x5] at e
        rw [VG.Proof.MdStream.AArch64.eval_zero, e]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.mono (short_ok d h hb) fun s' ⟨hk, hsp, hp⟩ => ⟨⟨hk, hsp⟩, hp⟩
  simp only [decide_eq_false_iff_not] at hb
  have hσ : Lay (inner s₀) (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x4) (s₀.gpr .x6) (s₀.gpr .x1).toNat
      (s₀.gpr .x3).toNat (s₀.gpr .x5).toNat :=
    ⟨h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, h.x6, h.rd, h.wr, cd, co, cb, dout, db, ob, fo, h.lenlt,
      h.ollt, p8, olq⟩
  refine WP.frameReg sp16 (fun R hR => ?_) (WP.mono (long_ok d hσ hb) fun s₂ ⟨hk, hpost⟩ => ?_)
    (by rw [fdepth_of_noFrames (longMain_noFrames d)]; decide)
  · rw [hwr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact kc
    · exact ko
    · exact kb
  refine ⟨⟨fun r hr => ?_, rfl⟩, ?_⟩
  · by_cases h30 : r = .x30
    · subst h30; simp [State.write]
    · simp only [State.write, h30, ite_false]
      exact hk r hr h30
  · have hf := frame_push s₀
    have hctx : ∀ {e n : Nat}, e + n ≤ 144 →
        ∀ r ∈ [(⟨s₀.sp - 16, 16⟩ : Region)], Region.Disjoint ⟨s₀.gpr .x0 + BitVec.ofNat 64 e, n⟩ r := by
      intro e n he r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact (kc.sub_right (Offset.sub_base _ he)).symm
    have e₁ : Spec.Rc2.contextAt (inner s₀).mem (s₀.gpr .x0) d (s₀.gpr .x1).toNat =
        Spec.Rc2.contextAt s₀.mem (s₀.gpr .x0) d (s₀.gpr .x1).toNat := by
      unfold Spec.Rc2.contextAt
      rw [inner_mem, scheduleAt_frame hf _ (by simpa using hctx (e := 0) (n := 128) (by omega)),
        blockAt_frame hf (s₀.gpr .x0 + 128) (hctx (e := 128) (by omega)),
        Proof.Rc2.bytesAt_frame hf (s₀.gpr .x0 + 136) _ (by omega) (hctx (e := 136) (by omega))]
    have e₂ : Spec.Rc2.bytesAt (inner s₀).mem (s₀.gpr .x2) (s₀.gpr .x3).toNat =
        Spec.Rc2.bytesAt s₀.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat := by
      rw [inner_mem]
      exact Proof.Rc2.bytesAt_frame hf _ _ (by omega) (by simpa using kd.symm)
    have hp : UPost d (inner s₀) (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x4) (s₀.gpr .x1).toNat
      (s₀.gpr .x3).toNat (s₀.gpr .x5).toNat s₂ := hpost
    unfold UPost at hp
    rw [e₁, e₂] at hp
    exact hp

end VG.Proof.Rc2.AArch64.Stream
