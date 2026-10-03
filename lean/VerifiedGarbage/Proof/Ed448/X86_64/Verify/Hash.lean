import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Args
import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Hash
import VerifiedGarbage.Proof.X25519.Bytes

/-!
# Ed448 verification on x86-64: the hash

Between the frame's push and pop (`Ctx`): the first ten bytes of
`dom4(0, context)` written to the frame (`hdr_ok`), the Keccak state at
`scratch` zeroed (`zeroSt_ok`), and the calls of `vg_keccak_absorb`,
`vg_keccak_pad` and `vg_keccak_squeeze` on it, with their working space at
`scratch + 256` (`kabs_ok`, `kpad_ok`, `ksqz_ok`); then `hash`, which leaves
`SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)` in the frame (`hash_ok`).
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Verify
open VG.Proof.MlKem.X86_64 (Keep WP.keep AbsorbArgs PadArgs SqueezeArgs absorb_pre pad_pre squeeze_pre absorb_nosp
  pad_nosp squeeze_nosp absorb_depth pad_depth squeeze_depth callEntry_repr callEntry_bytesAt callEntry_stateAt
  ofNat_toNat')
open VG.Spec.Sha3 (bytesAt stateAt absorb pad squeezeFrom Repr)

/-! ## Regions -/

theorem x0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero _

theorem H_eq (L : Lay) : L.H = L.B + BitVec.ofNat 64 32 := add_add _ _ _

theorem K_eq (L : Lay) : L.K = L.B + BitVec.ofNat 64 152 := add_add _ _ _

section
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- The 16 bytes below `rsp` that a call from the frame uses. -/
theorem k16 {t : State} (hc : Ctx L g mx m₀ t) {r : Region} (h : Region.Disjoint ⟨L.B, 16⟩ r) :
    (below (t.gpr .rsp) 16).Disjoint r := by
  rw [hc.rsp]; exact h.sub_left (below_call_sub L.B (Nat.le_refl _))

theorem st_ks (L : Lay) : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.KS, 640⟩ := by
  have := Offset.disjoint L.scr (d := 0) (n := 200) (e := 256) (k := 640) (by omega) (by omega) (by omega)
  simpa only [x0] using this

theorem st_h (hL : L.Ok) : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.H, 114⟩ := by
  have := hL.stk_x (d := 32) (n := 114) (e := 0) (k := 200) (by omega) (by omega)
  rw [H_eq]; simpa only [x0] using this.symm

theorem h_ks (hL : L.Ok) : Region.Disjoint ⟨L.H, 114⟩ ⟨L.KS, 640⟩ := by
  rw [H_eq]; exact hL.stk_x (by omega) (by omega)

/-- The 16 bytes below the frame, apart from `scratch`. -/
theorem k_x (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ := by
  have := hL.stk_x (d := 0) (n := 16) (by omega) h₂
  simpa only [x0] using this

theorem k_st (hL : L.Ok) : Region.Disjoint ⟨L.B, 16⟩ ⟨L.ST, 200⟩ := by
  have := k_x hL (e := 0) (k := 200) (by omega); simpa only [x0] using this

theorem k_ks (hL : L.Ok) : Region.Disjoint ⟨L.B, 16⟩ ⟨L.KS, 640⟩ := k_x hL (by omega)

theorem k_h : Region.Disjoint ⟨L.B, 16⟩ ⟨L.H, 114⟩ := by
  rw [H_eq]; exact Offset.base_disjoint _ (by omega) (by omega)

/-- The 16 bytes below the frame, apart from a buffer apart from the stack. -/
theorem k_r (hL : L.Ok) {r : Region} (hr : L.STK.Disjoint r) : Region.Disjoint ⟨L.B, 16⟩ r := by
  have := hL.stk_r hr (d := 0) (n := 16) (by omega); simpa only [x0] using this

theorem w_st : Within ⟨L.ST, 200⟩ L.SCR := within_base _ (by omega)
theorem w_ks : Within ⟨L.KS, 640⟩ L.SCR := within_off _ (by omega)
theorem w_h : Within ⟨L.H, 114⟩ L.DAT := within_off _ (by omega)

/-- The first 57 bytes of the signature, `R`. -/
abbrev R57 (L : Lay) : Region := ⟨L.sig, 57⟩

theorem r57_sub : Region.Sub (R57 L) L.SIG := (within_base _ (by omega)).sub

/-! ## The header of `dom4` -/

/-- `"SigEd448" ‖ 0 ‖ ctx_len`, the first ten bytes of `dom4(0, context)`. -/
abbrev hdrBytes (L : Lay) : List Byte :=
  "SigEd448".toList.map (fun c => BitVec.ofNat 8 c.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 L.ctxLen.toNat]

/-- `rax` doubled `n` times. -/
theorem dbl_ok : ∀ (n : Nat) (s : State),
    WP isa (.block (List.replicate n (.alu .add .rax (.reg .rax)))) s fun s' =>
      (s'.gpr .rax = s.gpr .rax * BitVec.ofNat 64 (2 ^ n) ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr) ∧
        Keep [.rax] s s'
  | 0, s => WP.block_nil ⟨⟨by simp, rfl, rfl⟩, Keep.refl _ _⟩
  | n + 1, s => by
    rw [List.replicate_succ', WP.block_append_iff]
    refine WP.mono (dbl_ok n s) fun s1 ⟨⟨h1, hm1, hx1⟩, k1⟩ => ?_
    refine WP.mono (WP.keep [.rax] (Q := fun s2 => s2.gpr .rax = s1.gpr .rax + s1.gpr .rax ∧
        s2.mem = s1.mem ∧ s2.mxcsr = s1.mxcsr)
      (by xrun [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]) (by decide))
      fun s2 ⟨⟨h2, hm2, hx2⟩, k2⟩ =>
        ⟨⟨?_, hm2.trans hm1, hx2.trans hx1⟩, (k1.trans k2).mono fun r hr => by simpa using hr⟩
    rw [h2, h1, ← BitVec.mul_add, BitVec.ofNat_add_ofNat, Nat.pow_succ, Nat.mul_two]

/-- The bytes of the two words of the header. -/
theorem hdr_bytes (m : Mem) (p : Addr) (c : BitVec 64) (hc : c.toNat < 256) :
    bytesAt ((m.writeW p (BitVec.ofNat 64 sigEd448)).writeW (p + BitVec.ofNat 64 8)
      (c * BitVec.ofNat 64 (2 ^ 8))) p 10 =
      "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 c.toNat] := by
  generalize hM : (m.writeW p (BitVec.ofNat 64 sigEd448)).writeW (p + BitVec.ofNat 64 8)
    (c * BitVec.ofNat 64 (2 ^ 8)) = M
  have h0 : M.readW p 64 = BitVec.ofNat 64 sigEd448 := by
    rw [← hM, Mem.readW_writeW_sep (Offset.sep_base p (n := 8) (e := 8) (k := 8) (by omega) (by omega))
      (by decide), Mem.readW_writeW_self64]
  have h1 : M.readW (p + BitVec.ofNat 64 8) 64 = c * BitVec.ofNat 64 (2 ^ 8) := by
    rw [← hM, Mem.readW_writeW_self64]
  have hw : (c * BitVec.ofNat 64 (2 ^ 8)).toNat = c.toNat * 256 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  have e10 : bytesAt M p 10 = bytesAt M p 8 ++ (bytesAt M (p + BitVec.ofNat 64 8) 8).take 2 := by
    have a := Proof.X25519.bytesAt_add M p 8 2
    have b := Proof.X25519.bytesAt_add M (p + BitVec.ofNat 64 8) 2 6
    have l := Proof.X25519.length_bytesAt M (p + BitVec.ofNat 64 8) 2
    change Spec.X25519.bytesAt M p 10 = Spec.X25519.bytesAt M p 8 ++
      (Spec.X25519.bytesAt M (p + BitVec.ofNat 64 8) 8).take 2
    rw [a, show (8 : Nat) = 2 + 6 from rfl, b, List.take_left' l]
  have b8 : ∀ q, bytesAt M q 8 = Proof.X25519.leBytes 8 (M.readW q 64).toNat :=
    fun q => Proof.X25519.bytesAt_leBytes_64 M q
  rw [e10, b8, b8, h0, h1, hw, show Proof.X25519.leBytes 8 (BitVec.ofNat 64 sigEd448).toNat =
    "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) by decide]
  refine congrArg (List.append _) ?_
  simp only [Proof.X25519.leBytes_succ, List.take_succ_cons, List.take_zero]
  have e1 : BitVec.ofNat 8 (c.toNat * 256) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, show (0 : BitVec 8).toNat = 0 from rfl]; omega
  have e2 : c.toNat * 256 / 256 = c.toNat := by omega
  rw [e1, e2]
  rfl

theorem hdr_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block hdr) t fun t' => Ctx L g mx m₀ t' ∧ bytesAt t'.mem L.SP 10 = hdrBytes L := by
  have w0 : InRegions t.wr L.SP 8 := by simpa only [x0] using hc.inFrW (d := 0) (n := 8) (by omega)
  have r216 := hc.inFr (d := 216) (by omega)
  have e : (t.mem.writeW L.SP (BitVec.ofNat 64 sigEd448)).readW (L.SP + BitVec.ofNat 64 216) 64 = L.ctxLen := by
    rw [Mem.readW_writeW_sep (fun x h₁ h₂ =>
      Offset.sep_base L.SP (n := 8) (e := 216) (k := 8) (by omega) (by omega) x h₂ h₁) (by decide)]
    exact hc.pCtxLen
  rw [hdr, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = t.mem.writeW L.SP (BitVec.ofNat 64 sigEd448) ∧
      s1.gpr .rax = L.ctxLen ∧ s1.mxcsr = t.mxcsr)
    (by xrun [ea_stk, fHdr, fCtxLen, hc.rsp, w0, r216, e, RegUpd.mxcsr_setReg]) (by decide))
    fun t1 ⟨⟨hm1, ha1, hx1⟩, k1⟩ => ?_
  refine WP.mono (dbl_ok 8 t1) fun t2 ⟨⟨ha2, hm2, hx2⟩, k2⟩ => ?_
  have hsp2 : t2.gpr .rsp = L.SP := by rw [k2.gpr (by decide), k1.gpr (by decide), hc.rsp]
  have w8 : InRegions t2.wr (L.SP + BitVec.ofNat 64 8) 8 := by
    rw [k2.2.2, k1.2.2]; exact hc.inFrW (by omega)
  refine WP.mono (Q := fun t3 : State => t3.mem = t2.mem.writeW (L.SP + BitVec.ofNat 64 8) (t2.gpr .rax) ∧
      t3.gpr = t2.gpr ∧ t3.rd = t2.rd ∧ t3.wr = t2.wr ∧ t3.mxcsr = t2.mxcsr) ?_
    fun t3 ⟨hm3, hg3, hrd3, hwr3, hx3⟩ => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_stk, fHdr, Nat.reduceAdd, hsp2,
      w8, ite_true, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩
  have hm : t3.mem = (t.mem.writeW L.SP (BitVec.ofNat 64 sigEd448)).writeW (L.SP + BitVec.ofNat 64 8)
      (L.ctxLen * BitVec.ofNat 64 (2 ^ 8)) := by
    rw [hm3, ha2, ha1, hm2, hm1]
  have hf : Frame ([⟨L.SP, 16⟩] ++ [⟨L.B, 16⟩]) t.mem t3.mem := by
    rw [hm]
    have c0 : (⟨L.SP, 16⟩ : Region).Contains L.SP 8 := by
      simpa only [x0] using Offset.contains_base L.SP (d := 0) (n := 8) (k := 16) (by omega) (by omega)
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ c0).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by omega) (by omega))
  refine ⟨hc.of_frame hL (hrd3.trans (k2.2.1.trans k1.2.1)) (hwr3.trans (k2.2.2.trans k1.2.2))
    (fun r hr => by
      rw [hg3, k2.gpr (by simp only [List.mem_singleton]; exact ne_cs hr (by decide)),
        k1.gpr (by simp only [List.mem_singleton]; exact ne_cs hr (by decide))])
    (by rw [hx3, hx2, hx1]) hf (fun r hr => ?_), ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact .inr (within_base _ (by omega))
  · rw [hm]; exact hdr_bytes _ _ _ hL.ctxLt

/-! ## Zeroing the state -/

/-- The first `n` stores of `zeroSt`. -/
abbrev zstores (n : Nat) : List Instr :=
  (List.range n).map fun k => .store { base := .rdi, disp := ((8 * k : Nat) : Int) } .rax

theorem zstore_ok {scr : Addr} {s : State} (hdi : s.gpr .rdi = scr) {k : Nat}
    (hw : InRegions s.wr (scr + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block [Instr.store { base := .rdi, disp := ((8 * k : Nat) : Int) } .rax]) s fun s' =>
      s'.mem = s.mem.writeW (scr + BitVec.ofNat 64 (8 * k)) (s.gpr .rax) ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_base, hdi, hw, ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem zstores_ok {scr : Addr} : ∀ n ≤ 25, ∀ s : State, s.gpr .rdi = scr → s.gpr .rax = 0 →
    (∀ j < 25, InRegions s.wr (scr + BitVec.ofNat 64 (8 * j)) 8) →
    WP isa (.block (zstores n)) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mxcsr = s.mxcsr ∧ Frame [⟨scr, 200⟩] s.mem s'.mem ∧
      ∀ j < n, s'.mem.readW (scr + BitVec.ofNat 64 (8 * j)) 64 = 0
  | 0, _, _, _, _, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn, s, h1, h2, hw => by
    rw [zstores, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (zstores_ok n (by omega) s h1 h2 hw) fun u ⟨ug, urd, uwr, umx, uf, uz⟩ => ?_
    refine WP.mono (zstore_ok (scr := scr) (k := n) (by rw [ug]; exact h1) (by rw [uwr]; exact hw n (by omega)))
      fun v ⟨vm, vg, vrd, vwr, vmx⟩ => ?_
    have hf1 : Frame [⟨scr, 200⟩] u.mem v.mem := by
      rw [vm]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    refine ⟨vg.trans ug, vrd.trans urd, vwr.trans uwr, vmx.trans umx, uf.trans hf1, fun j hj => ?_⟩
    rw [vm, ug, h2]
    by_cases hjk : j = n
    · subst hjk; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), uz j (by omega)]

theorem zero_state {m : Mem} {p : Addr} (h : ∀ j < 25, m.readW (p + BitVec.ofNat 64 (8 * j)) 64 = 0) :
    stateAt m p = Spec.Sha3.zero := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Sha3.stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
  exact h i hi

theorem zeroSt_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa zeroSt t fun t' => Ctx L g mx m₀ t' ∧ Frame [⟨L.ST, 200⟩] t.mem t'.mem ∧
      stateAt t'.mem L.ST = Spec.Sha3.zero := by
  refine WP.seq ?_
  show WP isa (.block (aSt.mov .rdi ++ [.mov32 .rax (.imm 0)])) t _
  rw [WP.block_append_iff]
  refine WP.mono (Arg.mov_ok .rdi aSt (by decide) (by decide) t hc.frOk) fun t1 ⟨⟨h1, hm1, hx1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = t1.mem ∧ s1.gpr .rax = 0 ∧ s1.mxcsr = t1.mxcsr)
    (by xrun [RegUpd.mxcsr_setReg]) (by decide)) fun t2 ⟨⟨hm2, hax, hx2⟩, k2⟩ => ?_
  have hdi : t2.gpr .rdi = L.scr := (k2.gpr (by decide)).trans (h1.trans hc.aSt)
  have hw2 : t2.wr = L.FR :: L.wr := k2.2.2.trans (k1.2.2.trans hc.wr)
  refine WP.mono (zstores_ok 25 (Nat.le_refl _) t2 hdi hax fun j hj => ?_)
    fun t3 ⟨g3, rd3, wr3, mx3, hf, hz⟩ => ?_
  · rw [hw2, hL.wr]
    exact ⟨L.SCR, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [hm2, hm1] at hf
    have hcs : ∀ r ∈ calleeSaved, t3.gpr r = t.gpr r := fun r hr => by
      rw [g3, k2.gpr (by simp only [List.mem_singleton]; exact ne_cs hr (by decide)),
        k1.gpr (by simp only [List.mem_singleton]; exact ne_cs hr (by decide))]
    have hf' : Frame ([⟨L.ST, 200⟩] ++ [⟨L.B, 16⟩]) t.mem t3.mem :=
      hf.mono fun r hr => by simp at hr ⊢; exact .inl hr
    exact ⟨hc.of_frame hL (rd3.trans (k2.2.1.trans k1.2.1)) (wr3.trans (k2.2.2.trans k1.2.2)) hcs
      (by rw [mx3, hx2, hx1]) hf' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inl w_st), hf, zero_state hz⟩

/-! ## Absorbing -/

/-- The arguments of a call of `vg_keccak_absorb`. -/
abbrev absArgs (src len pos : Arg) : List Arg := [aSt, .imm 136, pos, src, len, aKs]

theorem kabs_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    {src len pos : Arg} (hok : (absArgs src len pos).all Arg.ok = true)
    {dp : Addr} {n q : Nat} (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 64 n)
    (hq : pos.val t = BitVec.ofNat 64 q) (hql : q < 136) (hnl : n < 2 ^ 64)
    (hin : ∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨dp, n⟩ R)
    (dS : Region.Disjoint ⟨dp, n⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨dp, n⟩ ⟨L.KS, 640⟩)
    (kD : Region.Disjoint ⟨L.B, 16⟩ ⟨dp, n⟩) :
    WP isa (kabs src len pos) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        Repr t'.mem L.ST 136 (msg ++ bytesAt t.mem dp n)) ∧ (t'.gpr .rax).toNat = (q + n) % 136 := by
  refine WP.seq (WP.mono (setArgs_ok _ hok t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hA
  rw [hc.aSt] at e1
  rw [hc.aKs] at e6
  rw [hdp] at e4
  rw [hn] at e5
  rw [hq] at e3
  have ha : AbsorbArgs t1 L.ST dp L.KS 136 q n :=
    ⟨e1, e2, e3, e4, e5, e6, by decide, hql, hnl, st_ks L, dS, dK, k16 hc1 (k_st hL), k16 hc1 kD,
      k16 hc1 (k_ks hL)⟩
  refine call_ok hL Proof.Sha3.X86_64.Stream.Absorb.absorb_correct absorb_nosp (by rw [absorb_depth])
    hc1 (absorb_pre ha) (by simpa using hin) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inl w_st, .inl w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, hg₂, hpost, hrax⟩ => ?_
  have hn' := ofNat_toNat' hnl
  have hq' := ofNat_toNat' (show q < 2 ^ 64 by omega)
  simp only [State.withRegions_mem, gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.r8 ≠ .rsp),
    e1, e2, e3, e4, e5, hm₂, hn', hq'] at hpost hrax
  refine ⟨hc', by rw [← hm]; simpa using hf, fun msg hmsg hp => ?_, by rw [← hg₂ _ (by decide)]; exact hrax⟩
  have := hpost msg ((callEntry_repr t1 ha.k_st).mpr (hm ▸ hmsg)) hp
  rwa [callEntry_bytesAt t1 hnl ha.k_d, hm] at this

/-! ## Padding -/

/-- The arguments of a call of `vg_keccak_pad`. -/
abbrev padArgs (pos : Arg) : List Arg := [aSt, .imm 136, pos, .imm 0x1f, aKs]

theorem kpad_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    {pos : Arg} (hok : (padArgs pos).all Arg.ok = true) {q : Nat}
    (hq : pos.val t = BitVec.ofNat 64 q) (hql : q < 136) :
    WP isa (kpad pos) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        stateAt t'.mem L.ST = absorb 136 (pad 136 Spec.Sha3.shakeSuffix msg)) := by
  refine WP.seq (WP.mono (setArgs_ok _ hok t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  rw [hc.aSt] at e1
  rw [hc.aKs] at e5
  rw [hq] at e3
  have ha : PadArgs t1 L.ST L.KS 136 q :=
    ⟨e1, e2, e3, e5, by decide, hql, st_ks L, k16 hc1 (k_st hL), k16 hc1 (k_ks hL)⟩
  refine call_ok hL Proof.Sha3.X86_64.Stream.Pad.pad_correct pad_nosp (by rw [pad_depth])
    hc1 (pad_pre ha) (by simp) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inl w_st, .inl w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost⟩ => ?_
  have hq' := ofNat_toNat' (show q < 2 ^ 64 by omega)
  simp only [Proof.Sha3.padX86_64, State.withRegions_mem, gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), e1, e2, e3, e4, hm₂, hq'] at hpost
  refine ⟨hc', by rw [← hm]; simpa using hf, fun msg hmsg hp => ?_⟩
  have := hpost msg ((callEntry_repr t1 ha.k_st).mpr (hm ▸ hmsg)) hp
  rw [this]
  rfl

/-! ## Squeezing -/

/-- The arguments of a call of `vg_keccak_squeeze`. -/
abbrev sqzArgs : List Arg := [aSt, .imm 136, .imm 0, .sp fH, .imm 114, aKs]

theorem ksqz_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa ksqz t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.H, 114⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] t.mem t'.mem ∧
      bytesAt t'.mem L.H 114 = squeezeFrom 136 (stateAt t.mem L.ST) 0 114 := by
  refine WP.seq (WP.mono (setArgs_ok sqzArgs (by decide) t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hA
  rw [hc.aSt] at e1
  rw [hc.aKs] at e6
  rw [hc.sp] at e4
  change t1.gpr .rcx = L.H at e4
  have ha : SqueezeArgs t1 L.ST L.H L.KS 136 0 114 :=
    ⟨e1, e2, e3, e4, e5, e6, by decide, by decide, by decide, st_h hL, st_ks L, h_ks hL, k16 hc1 (k_st hL),
      k16 hc1 k_h, k16 hc1 (k_ks hL)⟩
  refine call_ok hL Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct squeeze_nosp
    (by rw [squeeze_depth]) hc1 (squeeze_pre ha) (by simp) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [.inl w_st, .inr w_h, .inl w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost, _⟩ => ?_
  simp only [State.withRegions_mem, gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.r8 ≠ .rsp),
    e1, e2, e3, e4, e5, hm₂, Arg.val, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hpost
  refine ⟨hc', by rw [← hm]; simpa using hf, ?_⟩
  rw [hpost, callEntry_stateAt t1 ha.k_st, hm]

/-! ## The hash -/

theorem ofNat_toNat_self (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem ofNat_toNat_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  subst h; exact (ofNat_toNat_self x).symm

/-- `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)` in the frame, with the first ten
bytes of `dom4` as the frame holds them. -/
theorem hash_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa hash t fun t' => Ctx L g mx m₀ t' ∧
      bytesAt t'.mem L.H 114 = Spec.Sha3.shake256 (bytesAt t.mem L.SP 10 ++
        bytesAt m₀ L.ctx L.ctxLen.toNat ++ bytesAt m₀ L.sig 57 ++ bytesAt m₀ L.pk 57 ++
        bytesAt m₀ L.msg L.len.toNat) 114 := by
  have hctx := hL.ctxLt
  have hS : Region.Disjoint ⟨L.SP, 10⟩ ⟨L.ST, 200⟩ := by
    have := hL.stk_x (d := 16) (n := 10) (e := 0) (k := 200) (by omega) (by omega)
    simpa only [x0] using this
  have hK : Region.Disjoint ⟨L.SP, 10⟩ ⟨L.KS, 640⟩ := hL.stk_x (d := 16) (n := 10) (by omega) (by omega)
  have kH : Region.Disjoint ⟨L.B, 16⟩ ⟨L.SP, 10⟩ := Offset.base_disjoint _ (by omega) (by omega)
  -- Zero the state.
  refine WP.seq (WP.mono (zeroSt_ok hL hc) fun t1 ⟨hc1, hf1, hz⟩ => ?_)
  have eh : bytesAt t1.mem L.SP 10 = bytesAt t.mem L.SP 10 :=
    bytesAt_congr fun i hi => hf1.bytes (R := ⟨L.SP, 10⟩) (by simpa using hS) (show (10 : Nat) ≤ 2 ^ 64 by decide) hi
  have hR1 : Repr t1.mem L.ST 136 [] := PublicKey.repr_nil hz
  -- The header of `dom4`, in the frame.
  refine WP.seq (WP.mono (kabs_ok hL hc1 (by decide) (dp := L.SP) (n := 10) (q := 0)
    (by rw [hc1.sp]; exact x0 _) rfl rfl (by decide) (by decide) ⟨L.FR, by simp, within_base _ (by omega)⟩
    hS hK kH) fun t2 ⟨hc2, _, hR2, hx2⟩ => ?_)
  have hR2 := hR2 [] hR1 rfl
  -- The context.
  refine WP.seq (WP.mono (kabs_ok hL hc2 (by decide) (dp := L.ctx) (n := L.ctxLen.toNat)
    (by rw [hc2.slot]; exact hc2.pCtx) (by rw [hc2.slot]; exact hc2.pCtxLen.trans (ofNat_toNat_self _).symm)
    (ofNat_toNat_eq hx2) (by omega) (by omega) ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩
    (by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by omega); simpa only [x0] using this.symm)
    (hL.x_r hL.xCtx (e := 256) (k := 640) (by omega)).symm (k_r hL hL.kCtx))
    fun t3 ⟨hc3, _, hR3, hx3⟩ => ?_)
  have hR3 := hR3 _ hR2 (by simp only [List.length_append, List.length_nil, bytesAt_length] <;> omega)
  rw [hc2.bytesAt_eq hL.xCtx hL.kCtx (by have := hL.nCtx; omega)] at hR3
  -- `R`.
  have xR := hL.xSig.sub_right r57_sub
  have kR := hL.kSig.sub_right r57_sub
  refine WP.seq (WP.mono (kabs_ok hL hc3 (by decide) (dp := L.sig) (n := 57)
    (by rw [hc3.slot]; exact hc3.pSig) rfl (ofNat_toNat_eq hx3) (Nat.mod_lt _ (by decide)) (by decide)
    ⟨L.SIG, List.mem_append_left _ hL.inSig, within_base _ (by omega)⟩
    (by have := hL.x_r xR (e := 0) (k := 200) (by omega); simpa only [x0] using this.symm)
    (hL.x_r xR (e := 256) (k := 640) (by omega)).symm (k_r hL kR))
    fun t4 ⟨hc4, _, hR4, hx4⟩ => ?_)
  have hR4 := hR4 _ hR3 (by simp only [List.length_append, List.length_nil, bytesAt_length] <;> omega)
  rw [hc3.bytesAt_eq xR kR (by decide)] at hR4
  -- `A`.
  refine WP.seq (WP.mono (kabs_ok hL hc4 (by decide) (dp := L.pk) (n := 57)
    (by rw [hc4.slot]; exact hc4.pPk) rfl (ofNat_toNat_eq hx4) (Nat.mod_lt _ (by decide)) (by decide)
    ⟨L.PK, List.mem_append_left _ hL.inPk, within_self _⟩
    (by have := hL.x_r hL.xPk (e := 0) (k := 200) (by omega); simpa only [x0] using this.symm)
    (hL.x_r hL.xPk (e := 256) (k := 640) (by omega)).symm (k_r hL hL.kPk))
    fun t5 ⟨hc5, _, hR5, hx5⟩ => ?_)
  have hR5 := hR5 _ hR4 (by simp only [List.length_append, List.length_nil, bytesAt_length] <;> omega)
  rw [hc4.bytesAt_eq hL.xPk hL.kPk (by decide)] at hR5
  -- The message.
  refine WP.seq (WP.mono (kabs_ok hL hc5 (by decide) (dp := L.msg) (n := L.len.toNat)
    (by rw [hc5.slot]; exact hc5.pMsg) (by rw [hc5.slot]; exact hc5.pLen.trans (ofNat_toNat_self _).symm)
    (ofNat_toNat_eq hx5) (Nat.mod_lt _ (by decide)) L.len.isLt
    ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩
    (by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by omega); simpa only [x0] using this.symm)
    (hL.x_r hL.xMsg (e := 256) (k := 640) (by omega)).symm (k_r hL hL.kMsg))
    fun t6 ⟨hc6, _, hR6, hx6⟩ => ?_)
  have hR6 := hR6 _ hR5 (by simp only [List.length_append, List.length_nil, bytesAt_length] <;> omega)
  rw [hc5.bytesAt_eq hL.xMsg hL.kMsg (by have := hL.nMsg; omega)] at hR6
  -- Pad and squeeze.
  refine WP.seq (WP.mono (kpad_ok hL hc6 (by decide) (ofNat_toNat_eq hx6) (Nat.mod_lt _ (by decide)))
    fun t7 ⟨hc7, _, hS7⟩ => ?_)
  have hS7 := hS7 _ hR6 (by simp only [List.length_append, List.length_nil, bytesAt_length] <;> omega)
  refine WP.mono (ksqz_ok hL hc7) fun t8 ⟨hc8, _, hm8⟩ => ⟨hc8, ?_⟩
  rw [hm8, hS7, PublicKey.shake256_eq, List.nil_append, eh]

end

end VG.Proof.Ed448.X86_64.Verify
