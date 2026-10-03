import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Calls
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Pre

/-!
# Ed448 verification on x86-64: correctness

The frame's body leaves the result of the equation on the hash of the
signature's `R`, the public key and the message, with the context's `dom4`
prefix, in `rax` (`body_ok`); the frame's push gives `Ctx` (`entry_ctx`).
From a state satisfying `verifyContract X86_64.abi 272`, `verify` returns 0
if the context is longer than 255 bytes and otherwise that result, which is
`Spec.Ed448.verify`'s (`verify_wp`).
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Verify
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Spec.Sha3 (bytesAt)

/-! ## The frame's body -/

section
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- `R`, the first half of the signature. -/
theorem take_bytesAt (m : Mem) (p : Addr) : (bytesAt m p 114).take 57 = bytesAt m p 57 := by
  have a := Proof.X25519.bytesAt_add m p 57 57
  have l := Proof.X25519.length_bytesAt m p 57
  change (Spec.X25519.bytesAt m p (57 + 57)).take 57 = Spec.X25519.bytesAt m p 57
  rw [a, List.take_left' l]

theorem ed_bytesAt : Spec.Ed448.bytesAt = bytesAt := rfl

/-- The challenge of the signature in `m₀`. -/
abbrev chal (L : Lay) (m₀ : Mem) : List Byte :=
  Spec.Ed448.scalarReduce (Spec.Ed448.hash (bytesAt m₀ L.ctx L.ctxLen.toNat)
    (bytesAt m₀ L.sig 57 ++ bytesAt m₀ L.pk 57 ++ bytesAt m₀ L.msg L.len.toNat))

theorem body_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa body t fun t' => Ctx L g mx m₀ t' ∧
      t'.gpr .rax = if Spec.Ed448.verifyEquation (bytesAt m₀ L.pk 57) (bytesAt m₀ L.sig 114) (chal L m₀)
        then 1 else 0 := by
  refine WP.seq (WP.mono (hdr_ok hL hc) fun t1 ⟨hc1, hh⟩ => ?_)
  refine WP.seq (WP.mono (hash_ok hL hc1) fun t2 ⟨hc2, hH⟩ => ?_)
  refine WP.seq (WP.mono (reduce_ok hL hc2) fun t3 ⟨hc3, hK⟩ => ?_)
  refine WP.mono (equation_ok hL hc3) fun t4 ⟨hc4, hr⟩ => ⟨hc4, ?_⟩
  have ek : bytesAt t3.mem L.K 57 = chal L m₀ := by
    change Spec.Ed448.bytesAt t3.mem L.K 57 = _
    rw [hK, hH, hh]
    refine congrArg Spec.Ed448.scalarReduce ?_
    simp only [Spec.Ed448.hash, Spec.Ed448.dom4, bytesAt_length, List.append_assoc, List.cons_append,
      List.nil_append]
  rw [hr, ek]

end

/-! ## The frame -/

/-- The registers pushed, at their slots. -/
theorem push_slot (B : Addr) (j : Nat) (hj : j < 32) :
    B + BitVec.ofNat 64 272 - BitVec.ofNat 64 (8 * (j + 1)) =
      B + BitVec.ofNat 64 16 + BitVec.ofNat 64 (248 - 8 * j) := by
  rw [add_add, Offset.sub_ofNat_eq _ (a := 8 * (j + 1)) (b := 272) (by omega), BitVec.add_sub_cancel]
  congr 2; omega

theorem push_base (B : Addr) : B + BitVec.ofNat 64 272 - BitVec.ofNat 64 (8 * 32) = B + BitVec.ofNat 64 16 := by
  have := push_slot B 31 (by omega); simpa using this

theorem regs_length : regs.length = 32 := rfl

/-- After the push of the registers holding `scratch`, `sig`, `len`, `msg`,
`ctx_len`, `ctx`, `pk` and 0: `Ctx`. -/
theorem entry_ctx {L : Lay} (hL : L.Ok) {s : State} (hsp : s.gpr .rsp = L.B + BitVec.ofNat 64 272)
    (hrd : s.rd = L.rd) (hwr : s.wr = L.wr) (h11 : s.gpr .r11 = L.scr) (h9 : s.gpr .r9 = L.sig)
    (h8 : s.gpr .r8 = L.len) (hcx : s.gpr .rcx = L.msg) (hdx : s.gpr .rdx = L.ctxLen)
    (hsi : s.gpr .rsi = L.ctx) (hdi : s.gpr .rdi = L.pk) :
    Ctx L s.gpr s.mxcsr s.mem (pushed regs s) := by
  have hn : 8 * regs.length ≤ (s.gpr .rsp).toNat := by
    rw [hsp, regs_length, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := hL.nB
    rw [Nat.mod_eq_of_lt (a := 272) (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  obtain ⟨hf, hw⟩ := pushRegs_mem s regs (by decide) hn
  have slot : ∀ j (hj : j < 32), (pushed regs s).mem.readW (L.SP + BitVec.ofNat 64 (248 - 8 * j)) 64 =
      s.gpr (regs[j]'(by rw [regs_length]; omega)) := fun j hj => by
    rw [← hw j (by rw [regs_length]; omega), hsp, push_slot _ j hj]; rfl
  have base : s.gpr .rsp - BitVec.ofNat 64 (8 * regs.length) = L.SP := by
    rw [hsp, regs_length]; exact push_base L.B
  refine ⟨by simp [hrd], by rw [pushed_wr, base, hwr]; rfl, by rw [pushed_rsp, base], fun r _ hr' => pushed_gpr _ _ hr',
    by simp, (slot 6 (by omega)).trans hdi, (slot 5 (by omega)).trans hsi, (slot 4 (by omega)).trans hdx,
    (slot 3 (by omega)).trans hcx, (slot 2 (by omega)).trans h8, (slot 1 (by omega)).trans h9,
    (slot 0 (by omega)).trans h11, ?_⟩
  show Frame [L.SCR, L.STK] s.mem (pushRegs s regs).mem
  refine Frame.sub hf fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨L.STK, by simp, ?_⟩
  rw [base, regs_length]
  exact Offset.sub_base _ (by omega)

/-! ## Before the frame -/

theorem wp_ite_t {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some true) (h : WP isa th s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteT hc e, q⟩

theorem wp_ite_f {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some false) (h : WP isa el s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteF hc e, q⟩

/-- `cmp rdx, 256`. -/
theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm 256)]) s fun s1 => s1.gpr = s.gpr ∧ s1.mem = s.mem ∧
      s1.rd = s.rd ∧ s1.wr = s.wr ∧ s1.mxcsr = s.mxcsr ∧
      isa.eval .b s1 = some (decide ((s.gpr .rdx).toNat < 256)) := by
  xrun [show BitVec.signExtend 64 (256 : BitVec 32) = 256 by decide]
  exact ⟨rfl, rfl⟩

theorem stackArgAddr0 (s : State) : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := rfl

/-- `scratch` to `r11`, 0 to `rax`. -/
theorem verifyMov_ok {s s1 : State} (h : VPre s) (hg : s1.gpr = s.gpr) (hm : s1.mem = s.mem)
    (hrd : s1.rd = s.rd) :
    WP isa (.block [.mov .r11 (.mem (stk 8)), .mov32 .rax (.imm 0)]) s1 fun s2 =>
      (s2.gpr .r11 = stackArg s 0 ∧ s2.gpr .rax = 0 ∧ s2.mem = s.mem ∧ s2.mxcsr = s1.mxcsr) ∧
        Keep [.r11, .rax] s1 s2 := by
  have h8 : InRegions (s1.rd ++ s1.wr) (s1.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    refine ⟨vArgs s, by simp [hrd, h.rd], ?_⟩
    rw [hg, ← stackArgAddr0]
    exact Region.contains_self _ _
  refine WP.keep _ ?_ (by decide)
  xrun [ea_stk, h8, RegUpd.mxcsr_setReg]
  rw [hm, hg]
  exact ⟨rfl, rfl⟩

theorem sw_ite (b : Bool) :
    BitVec.setWidth 32 (if b = true then (1 : BitVec 64) else 0) = if b = true then 1 else 0 := by
  cases b <;> rfl

theorem cs_r11 : ∀ r ∈ calleeSaved, r ≠ .r11 := by decide
theorem cs_tmp : ∀ r ∈ calleeSaved, r ∉ [Reg.r11, .rax] := by decide

/-! ## The function -/

theorem verify_wp {s : State} (hpre : (Spec.Ed448.verifyContract X86_64.abi 272).pre s) :
    WP isa verify s fun s' => abiPreserved s s' ∧ (Spec.Ed448.verifyContract X86_64.abi 272).post s s' := by
  have h := vPre_of hpre
  unfold verify
  refine WP.seq (WP.mono (cmp_ok s) fun s1 ⟨hg1, hm1, hrd1, hwr1, hx1, hc1⟩ => ?_)
  by_cases h8 : (s.gpr .rdx).toNat < 256
  · rw [decide_eq_true h8] at hc1
    refine wp_ite_t hc1 (WP.seq (WP.mono (verifyMov_ok h hg1 hm1 hrd1) fun s2 ⟨⟨h11, hax, hm2, hx2⟩, k2⟩ => ?_))
    have hL := vlay_ok h h8
    have hg2 : ∀ r, r ∉ [Reg.r11, .rax] → s2.gpr r = s.gpr r := fun r hr => (k2.gpr hr).trans (by rw [hg1])
    have hsp2 : s2.gpr .rsp = (vlay s).B + BitVec.ofNat 64 272 := by
      rw [hg2 _ (by decide), vlay_B]
    have hn : 8 * regs.length ≤ (s2.gpr .rsp).toNat := by
      rw [hg2 _ (by decide), regs_length]; have := h.sp; omega
    refine WP.frame (by decide) (by decide) (by decide) hn ?_
    have hc := entry_ctx hL hsp2 (k2.2.1.trans hrd1) (k2.2.2.trans hwr1) h11 (hg2 _ (by decide))
      (hg2 _ (by decide)) (hg2 _ (by decide)) (hg2 _ (by decide)) (hg2 _ (by decide)) (hg2 _ (by decide))
    refine WP.mono (body_ok hL hc) fun s' ⟨hc', hr⟩ => ⟨by rw [hc'.rsp, hc.rsp], by rw [hc'.wr, hc.wr], ?_, ?_⟩
    · -- The calling convention.
      refine ⟨fun r hr => ?_, ?_, ?_⟩
      · by_cases hr' : r = .rsp
        · subst hr'
          rw [popped_rsp, hc'.rsp, Lay.SP, add_add, regs_length, vlay_B]
        · rw [popped_gpr _ _ _ hr' (cs_r11 r hr), hc'.cs r hr hr', hg2 r (cs_tmp r hr)]
      · have eR : vRet s = ⟨(vlay s).B + BitVec.ofNat 64 272, 8⟩ := by rw [vlay_B]
        rw [popped_mem, hc'.frame.readW (r := vRet s) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact h.retScr
            · rw [eR]; exact Offset.disjoint_base _ (by omega) (by have := hL.nB; omega)) (by decide), hm2]
      · rw [popped_mxcsr, hc'.mx, hx2, hx1]
    · sig_post [Spec.Ed448.verifyContract, Spec.Ed448.verifySig, Spec.Ed448.scratchWords, X86_64.abi,
        X86_64.argRegs, List.range, List.range.loop]
      rw [hr]
      simp only [ed_bytesAt, Spec.Ed448.verify, bytesAt_length, take_bytesAt, vlay, chal, ← hm2,
        decide_eq_true (show (s.gpr .rdx).toNat ≤ 255 by omega), Bool.true_and]
      exact sw_ite _
  · rw [decide_eq_false h8] at hc1
    refine wp_ite_f hc1 ?_
    xrun
    refine ⟨⟨fun r hr => ?_, by rw [RegUpd.mem_setReg, hm1], by rw [RegUpd.mxcsr_setReg, hx1]⟩, ?_⟩
    · rw [RegUpd.gpr_setReg_of_ne _ _ (fun e => by subst e; revert hr; decide), hg1]
    · sig_post [Spec.Ed448.verifyContract, Spec.Ed448.verifySig, Spec.Ed448.scratchWords, X86_64.abi,
        X86_64.argRegs, List.range, List.range.loop]
      simp only [ed_bytesAt, Spec.Ed448.verify, bytesAt_length,
        decide_eq_false (show ¬ (s.gpr .rdx).toNat ≤ 255 by omega), Bool.false_and]
      rfl

end VG.Proof.Ed448.X86_64.Verify
