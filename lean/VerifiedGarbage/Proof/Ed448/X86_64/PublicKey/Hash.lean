import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Layout
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.Stream

/-!
# Ed448 public-key derivation on x86-64: the hash of the seed

From the state after the frame's push: the Keccak state at `scratch` zeroed
(`zero_ok`), then the calls of `vg_keccak_absorb`, `vg_keccak_pad` and
`vg_keccak_squeeze` (rate 136, SHAKE's suffix), with their working space at
`scratch + 256`, leave `SHAKE256(seed, 114)` at `scratch + 1024`
(`hash_ok`).
-/

namespace VG.Proof.Ed448.X86_64.PublicKey

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Spec.Sha3 (stateAt)

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem sub88 (B : Addr) : B + BitVec.ofNat 64 8 - 8 = B := by bv_omega

/-- Code that writes only caller-saved registers and within `scratch`. -/
theorem Ctx.scrw (hL : L.Ok) {t t' : State} (hc : Ctx L g mx m₀ t) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    {rs : List Region} (hrs : ∀ r ∈ rs, Within r L.SCR) (hf : Frame rs t.mem t'.mem) :
    Ctx L g mx m₀ t' := by
  have keep : ∀ d, 80 ≤ d → d + 8 ≤ 104 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _)
      (fun r hr => (hL.kc.sub_left (Offset.sub_base _ (by omega))).sub_right (hrs r hr).sub) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    (keep 80 (by omega) (by omega)).trans hc.pScr, (keep 88 (by omega) (by omega)).trans hc.pSeed,
    (keep 96 (by omega) (by omega)).trans hc.pOut,
    hc.frame.trans (Frame.sub hf fun r hr => ⟨L.SCR, by simp, (hrs r hr).sub⟩)⟩

/-- The Keccak state at `scratch`, on entry to a call from the frame. -/
theorem Ctx.ce_state (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    stateAt t.callEntry.mem L.scr = stateAt t.mem L.scr :=
  Proof.Sha3.stateAt_congr fun _ hi => ce_byte t (R := ⟨L.scr, 200⟩)
    (by rw [hc.ret]; simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 200) (by omega) (by omega))
    (by show (200 : Nat) ≤ 2 ^ 64; decide) hi

/-- The seed on entry to a call from the frame. -/
theorem Ctx.ce_seed (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    Spec.Sha3.bytesAt t.callEntry.mem L.seed 57 = Spec.Sha3.bytesAt m₀ L.seed 57 := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [ce_byte t (R := L.SEED) (by rw [hc.ret]; exact hL.stk_SEED (by omega))
    (by show (57 : Nat) ≤ 2 ^ 64; decide) hi]
  exact hc.seed hL hi

/-! ## Zeroing the state -/

theorem zeroHead_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkZeroHead) t fun t' =>
      Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = L.scr ∧ t'.gpr .rax = 0 := by
  have h80 := hc.inFr (d := 80) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkZeroHead, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, State.load64,
    State.setReg32, ea_stk, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    Option.map_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add, Nat.reduceAdd, h80,
    Option.some.injEq, exists_eq_left', hc.pScr]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, rfl⟩

theorem zstore_ok {t : State} (hc : Ctx L g mx m₀ t) (hdi : t.gpr .rdi = L.scr) {k : Nat} (hk : k < 25) :
    WP isa (.block [Instr.store { base := .rdi, disp := ((8 * k : Nat) : Int) } .rax]) t fun t' =>
      t'.mem = t.mem.writeW (L.scr + BitVec.ofNat 64 (8 * k)) (t.gpr .rax) ∧ t'.gpr = t.gpr ∧
        t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.mxcsr = t.mxcsr := by
  have w := hc.inScrW (o := 8 * k) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_base, hdi, w, ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- The stores of `pkZeroStores`, the first `n`. -/
abbrev zstores (n : Nat) : List Instr :=
  (List.range n).map fun k => .store { base := .rdi, disp := ((8 * k : Nat) : Int) } .rax

theorem zstores_ok (hL : L.Ok) : ∀ n ≤ 25, ∀ t : State, Ctx L g mx m₀ t → t.gpr .rdi = L.scr →
    t.gpr .rax = 0 → WP isa (.block (zstores n)) t fun t' =>
      Ctx L g mx m₀ t' ∧ t'.gpr .rdi = L.scr ∧ t'.gpr .rax = 0 ∧ Frame [⟨L.scr, 200⟩] t.mem t'.mem ∧
        ∀ j < n, t'.mem.readW (L.scr + BitVec.ofNat 64 (8 * j)) 64 = 0
  | 0, _, _, hc, h1, h2 => WP.block_nil ⟨hc, h1, h2, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn, t, hc, h1, h2 => by
    rw [zstores, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (zstores_ok hL n (by omega) t hc h1 h2) fun u ⟨hu, u1, u2, uf, uz⟩ => ?_
    refine WP.mono (zstore_ok hu u1 (k := n) (by omega)) fun v ⟨vm, vg, vrd, vwr, vmx⟩ => ?_
    have hf1 : Frame [⟨L.scr, 200⟩] u.mem v.mem := by
      rw [vm]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega) (by omega))
    refine ⟨hu.scrw hL vrd vwr vmx (fun r _ => by rw [vg])
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact within_base _ (by omega)) hf1,
      by rw [vg]; exact u1, by rw [vg]; exact u2, uf.trans hf1, fun j hj => ?_⟩
    rw [vm, u2]
    by_cases hjk : j = n
    · subst hjk; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), uz j (by omega)]

theorem zero_state {m : Mem} {p : Addr} (h : ∀ j < 25, m.readW (p + BitVec.ofNat 64 (8 * j)) 64 = 0) :
    stateAt m p = Spec.Sha3.zero := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Sha3.stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
  exact h i hi

theorem zero_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa pkZeroState t fun t' => Ctx L g mx m₀ t' ∧ stateAt t'.mem L.scr = Spec.Sha3.zero := by
  refine WP.seq (WP.mono (zeroHead_ok hc) fun u ⟨hu, _, u1, u2⟩ => ?_)
  exact WP.mono (zstores_ok hL 25 (by omega) u hu u1 u2) fun v ⟨hv, _, _, _, hz⟩ => ⟨hv, zero_state hz⟩

/-! ## The sponge functions -/

theorem absorb_nosp : NoSp Impl.Sha3.X86_64.Stream.absorb := by
  have : ((instrs Impl.Sha3.X86_64.Stream.absorb).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem pad_nosp : NoSp Impl.Sha3.X86_64.Stream.pad := by
  have : ((instrs Impl.Sha3.X86_64.Stream.pad).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem squeeze_nosp : NoSp Impl.Sha3.X86_64.Stream.squeeze := by
  have : ((instrs Impl.Sha3.X86_64.Stream.squeeze).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem absorb_depth : Impl.Sha3.X86_64.Stream.absorb.depth ≤ 1 := by decide +kernel
theorem pad_depth : Impl.Sha3.X86_64.Stream.pad.depth ≤ 1 := by decide +kernel
theorem squeeze_depth : Impl.Sha3.X86_64.Stream.squeeze.depth ≤ 1 := by decide +kernel

/-! ## `absorb` -/

/-- What the call of `absorb` needs of the registers. -/
def AbsArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.scr ∧ t.gpr .rsi = BitVec.ofNat 64 136 ∧ t.gpr .rdx = BitVec.ofNat 64 0 ∧
    t.gpr .rcx = L.seed ∧ t.gpr .r8 = BitVec.ofNat 64 57 ∧ t.gpr .r9 = L.scr + BitVec.ofNat 64 256

theorem absArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkAbsorbArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ AbsArgs L t' := by
  have h80 := hc.inFr (d := 80) (by omega) (by omega)
  have h88 := hc.inFr (d := 88) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkAbsorbArgs, scrPtr, keccakScratch, fScratch, fSeed, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.load64,
    State.setReg32, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, h80, h88, Option.some.injEq, exists_eq_left', hc.pScr, hc.pSeed, AbsArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, by decide, by decide, trivial, by decide,
    by rw [sx32 (by omega)]⟩

abbrev absRd (L : Lay) : List Region := [L.SEED]
abbrev absWr (L : Lay) : List Region := [⟨L.scr, 200⟩, ⟨L.scr + BitVec.ofNat 64 256, 640⟩]

theorem abs_regs {t : State} (ha : AbsArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.scr ∧
      (t.callEntry.withRegions rd wr).gpr .rsi = BitVec.ofNat 64 136 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = BitVec.ofNat 64 0 ∧
      (t.callEntry.withRegions rd wr).gpr .rcx = L.seed ∧
      (t.callEntry.withRegions rd wr).gpr .r8 = BitVec.ofNat 64 57 ∧
      (t.callEntry.withRegions rd wr).gpr .r9 = L.scr + BitVec.ofNat 64 256 :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2.2⟩

theorem abs_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : AbsArgs L t) :
    Proof.Sha3.absorbX86_64.pre (t.callEntry.withRegions (absRd L) (absWr L)) := by
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := abs_regs ha (absRd L) (absWr L)
  simp only [Proof.Sha3.absorbX86_64, rsp_ce, hdi, hsi, hdx, hcx, h8, h9, hc.rsp, sub8, sub88,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨by first | trivial | rfl, by first | trivial | rfl, Offset.base_disjoint _ (by omega) (by omega),
    by simpa using hL.seed_scr (e := 0) (k := 200) (by omega), hL.seed_scr (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 200) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 200) (by omega) (by omega),
    by simpa using hL.stk_SEED (d := 0) (n := 8) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 256) (k := 640) (by omega) (by omega),
    by decide, by decide⟩

theorem abs_sub : ∀ r ∈ absRd L ++ absWr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], Within r R := by
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.SEED, by simp, within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩

theorem abs_wsub : ∀ r ∈ absWr L, Within r L.OUT ∨ Within r L.SCR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inr (within_base _ (by omega))
  · exact .inr (within_off _ (by omega))

theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) :
    Spec.Sha3.Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

theorem abs_call (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : AbsArgs L t)
    (hz : stateAt t.mem L.scr = Spec.Sha3.zero) :
    WP isa (.call "vg_keccak_absorb" Impl.Sha3.X86_64.Stream.absorb) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha3.Repr t'.mem L.scr 136 (Spec.Sha3.bytesAt m₀ L.seed 57) := by
  refine call_ok hL Proof.Sha3.X86_64.Stream.Absorb.absorb_correct absorb_nosp absorb_depth hc
    (abs_pre hL hc ha) abs_sub abs_wsub fun s' hc' _ _ ⟨s₂, hm, _, hpost, _⟩ => ⟨hc', ?_⟩
  obtain ⟨hdi, hsi, hdx, hcx, h8, -⟩ := abs_regs ha (absRd L) (absWr L)
  simp only [State.withRegions_mem, hdi, hsi, hdx, hcx, h8, hm, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod] at hpost
  have h := hpost [] (repr_nil (by rw [hc.ce_state hL, hz])) rfl
  rwa [List.nil_append, hc.ce_seed hL] at h

theorem abs_step (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (hz : stateAt t.mem L.scr = Spec.Sha3.zero) :
    WP isa (callWith pkAbsorbArgs "vg_keccak_absorb" Impl.Sha3.X86_64.Stream.absorb) t fun t' =>
      Ctx L g mx m₀ t' ∧ Spec.Sha3.Repr t'.mem L.scr 136 (Spec.Sha3.bytesAt m₀ L.seed 57) :=
  WP.seq (WP.mono (absArgs_ok hc) fun _ ⟨hc₁, hm₁, ha⟩ => abs_call hL hc₁ ha (hm₁ ▸ hz))

/-! ## `pad` -/

/-- What the call of `pad` needs of the registers. -/
def PadArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.scr ∧ t.gpr .rsi = BitVec.ofNat 64 136 ∧ t.gpr .rdx = BitVec.ofNat 64 57 ∧
    t.gpr .rcx = BitVec.ofNat 64 0x1f ∧ t.gpr .r8 = L.scr + BitVec.ofNat 64 256

theorem padArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkPadArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ PadArgs L t' := by
  have h80 := hc.inFr (d := 80) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkPadArgs, scrPtr, keccakScratch, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.load64,
    State.setReg32, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, h80, Option.some.injEq, exists_eq_left', hc.pScr, PadArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, by decide, by decide, by decide,
    by rw [sx32 (by omega)]⟩

abbrev padRd : List Region := []
abbrev padWr (L : Lay) : List Region := [⟨L.scr, 200⟩, ⟨L.scr + BitVec.ofNat 64 256, 640⟩]

theorem pad_regs {t : State} (ha : PadArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.scr ∧
      (t.callEntry.withRegions rd wr).gpr .rsi = BitVec.ofNat 64 136 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = BitVec.ofNat 64 57 ∧
      (t.callEntry.withRegions rd wr).gpr .rcx = BitVec.ofNat 64 0x1f ∧
      (t.callEntry.withRegions rd wr).gpr .r8 = L.scr + BitVec.ofNat 64 256 :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2⟩

theorem pad_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : PadArgs L t) :
    Proof.Sha3.padX86_64.pre (t.callEntry.withRegions padRd (padWr L)) := by
  obtain ⟨hdi, hsi, hdx, -, h8⟩ := pad_regs ha padRd (padWr L)
  simp only [Proof.Sha3.padX86_64, rsp_ce, hdi, hsi, hdx, h8, hc.rsp, sub8, sub88,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨by first | trivial | rfl, by first | trivial | rfl, Offset.base_disjoint _ (by omega) (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 200) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 200) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 256) (k := 640) (by omega) (by omega),
    by decide, by decide⟩

theorem pad_sub : ∀ r ∈ padRd ++ padWr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], Within r R := by
  simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩

theorem pad_wsub : ∀ r ∈ padWr L, Within r L.OUT ∨ Within r L.SCR := abs_wsub

theorem pad_call (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : PadArgs L t) {msg : List Byte}
    (hr : Spec.Sha3.Repr t.mem L.scr 136 msg) (hl : msg.length = 57) :
    WP isa (.call "vg_keccak_pad" Impl.Sha3.X86_64.Stream.pad) t fun t' => Ctx L g mx m₀ t' ∧
      stateAt t'.mem L.scr = Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) := by
  refine call_ok hL Proof.Sha3.X86_64.Stream.Pad.pad_correct pad_nosp pad_depth hc
    (pad_pre hL hc ha) pad_sub pad_wsub fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  obtain ⟨hdi, hsi, hdx, hcx, -⟩ := pad_regs ha padRd (padWr L)
  simp only [Proof.Sha3.padX86_64, State.withRegions_mem, hdi, hsi, hdx, hcx, hm, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod] at hpost
  have hr' : Spec.Sha3.Repr t.callEntry.mem L.scr 136 msg := by unfold Spec.Sha3.Repr; rw [hc.ce_state hL]; exact hr
  rw [hpost msg hr' (by rw [hl])]
  rfl

theorem pad_step (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) {msg : List Byte}
    (hr : Spec.Sha3.Repr t.mem L.scr 136 msg) (hl : msg.length = 57) :
    WP isa (callWith pkPadArgs "vg_keccak_pad" Impl.Sha3.X86_64.Stream.pad) t fun t' =>
      Ctx L g mx m₀ t' ∧
        stateAt t'.mem L.scr = Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) :=
  WP.seq (WP.mono (padArgs_ok hc) fun _ ⟨hc₁, hm₁, ha⟩ => pad_call hL hc₁ ha (hm₁ ▸ hr) hl)

/-! ## `squeeze` -/

/-- What the call of `squeeze` needs of the registers. -/
def SqzArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.scr ∧ t.gpr .rsi = BitVec.ofNat 64 136 ∧ t.gpr .rdx = BitVec.ofNat 64 0 ∧
    t.gpr .rcx = L.scr + BitVec.ofNat 64 1024 ∧ t.gpr .r8 = BitVec.ofNat 64 114 ∧
    t.gpr .r9 = L.scr + BitVec.ofNat 64 256

theorem sqzArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkSqueezeArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ SqzArgs L t' := by
  have h80 := hc.inFr (d := 80) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkSqueezeArgs, scrPtr, keccakScratch, hashAt, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32,
    State.load64, State.setReg32, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp,
    add_add, Nat.reduceAdd, h80, Option.some.injEq, exists_eq_left', hc.pScr, SqzArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, by decide, by decide, by rw [sx32 (by omega)],
    by decide, by rw [sx32 (by omega)]⟩

abbrev sqzRd : List Region := []
abbrev sqzWr (L : Lay) : List Region :=
  [⟨L.scr, 200⟩, ⟨L.scr + BitVec.ofNat 64 1024, 114⟩, ⟨L.scr + BitVec.ofNat 64 256, 640⟩]

theorem sqz_regs {t : State} (ha : SqzArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.scr ∧
      (t.callEntry.withRegions rd wr).gpr .rsi = BitVec.ofNat 64 136 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = BitVec.ofNat 64 0 ∧
      (t.callEntry.withRegions rd wr).gpr .rcx = L.scr + BitVec.ofNat 64 1024 ∧
      (t.callEntry.withRegions rd wr).gpr .r8 = BitVec.ofNat 64 114 ∧
      (t.callEntry.withRegions rd wr).gpr .r9 = L.scr + BitVec.ofNat 64 256 :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2.2⟩

theorem sqz_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : SqzArgs L t) :
    Proof.Sha3.squeezeX86_64.pre (t.callEntry.withRegions sqzRd (sqzWr L)) := by
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := sqz_regs ha sqzRd (sqzWr L)
  simp only [Proof.Sha3.squeezeX86_64, rsp_ce, hdi, hsi, hdx, hcx, h8, h9, hc.rsp, sub8, sub88,
    State.withRegions_rd, State.withRegions_wr, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact ⟨by first | trivial | rfl, by first | trivial | rfl, Offset.base_disjoint _ (by omega) (by omega),
    Offset.base_disjoint _ (by omega) (by omega), Offset.disjoint _ (by omega) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 200) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 200) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 1024) (k := 114) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 256) (k := 640) (by omega) (by omega),
    by decide, by decide⟩

theorem sqz_sub : ∀ r ∈ sqzRd ++ sqzWr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], Within r R := by
  simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩

theorem sqz_wsub : ∀ r ∈ sqzWr L, Within r L.OUT ∨ Within r L.SCR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inr (within_base _ (by omega))
  · exact .inr (within_off _ (by omega))
  · exact .inr (within_off _ (by omega))

theorem sqz_call (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : SqzArgs L t) :
    WP isa (.call "vg_keccak_squeeze" Impl.Sha3.X86_64.Stream.squeeze) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha3.bytesAt t'.mem (L.scr + BitVec.ofNat 64 1024) 114 =
        Spec.Sha3.squeezeFrom 136 (stateAt t.mem L.scr) 0 114 := by
  refine call_ok hL Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct squeeze_nosp squeeze_depth hc
    (sqz_pre hL hc ha) sqz_sub sqz_wsub fun s' hc' _ _ ⟨s₂, hm, _, hpost, _⟩ => ⟨hc', ?_⟩
  obtain ⟨hdi, hsi, hdx, hcx, h8, -⟩ := sqz_regs ha sqzRd (sqzWr L)
  simp only [State.withRegions_mem, hdi, hsi, hdx, hcx, h8, hm, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod] at hpost
  rw [hpost, hc.ce_state hL]

theorem sqz_step (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (callWith pkSqueezeArgs "vg_keccak_squeeze" Impl.Sha3.X86_64.Stream.squeeze) t fun t' =>
      Ctx L g mx m₀ t' ∧ Spec.Sha3.bytesAt t'.mem (L.scr + BitVec.ofNat 64 1024) 114 =
        Spec.Sha3.squeezeFrom 136 (stateAt t.mem L.scr) 0 114 :=
  WP.seq (WP.mono (sqzArgs_ok hc) fun _ ⟨hc₁, hm₁, ha⟩ => by rw [← hm₁]; exact sqz_call hL hc₁ ha)

/-! ## The hash -/

theorem squeezeFrom_zero (rate : Nat) (S : Spec.Sha3.State) (d : Nat) :
    Spec.Sha3.squeezeFrom rate S 0 d = Spec.Sha3.squeeze rate S d := by
  simp only [Spec.Sha3.squeezeFrom, Spec.Sha3.squeeze, Nat.zero_add, List.drop_zero]

theorem shake256_eq (m : List Byte) (d : Nat) :
    Spec.Sha3.shake256 m d =
      Spec.Sha3.squeezeFrom 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix m)) 0 d := by
  rw [squeezeFrom_zero]; rfl

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha3.bytesAt m p n).length = n := by
  simp [Spec.Sha3.bytesAt]

/-- `SHAKE256(seed, 114)` at `scratch + 1024`. -/
theorem hash_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa pkHash t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha3.bytesAt t'.mem (L.scr + BitVec.ofNat 64 1024) 114 =
        Spec.Sha3.shake256 (Spec.Sha3.bytesAt m₀ L.seed 57) 114 := by
  refine WP.seq (WP.mono (zero_ok hL hc) fun t₁ ⟨hc₁, hz₁⟩ => ?_)
  refine WP.seq (WP.mono (abs_step hL hc₁ hz₁) fun t₂ ⟨hc₂, hr₂⟩ => ?_)
  refine WP.seq (WP.mono (pad_step hL hc₂ hr₂ (bytesAt_length _ _ _)) fun t₃ ⟨hc₃, hs₃⟩ => ?_)
  refine WP.mono (sqz_step hL hc₃) fun t₄ ⟨hc₄, hb₄⟩ => ⟨hc₄, ?_⟩
  rw [hb₄, hs₃, shake256_eq]

end VG.Proof.Ed448.X86_64.PublicKey
