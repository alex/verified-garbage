import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCall

/-!
# ML-DSA on ARMv7, `sign_message`: correctness

Untrusted: everything here is checked by Lean. From a state satisfying
`signMessageContract p Arm.abi 36`, `signMessage n c p` returns 2 if the
context string is longer than 255 bytes; otherwise it computes `μ` of the
formatted message and calls the signing function on `μ` `c`, which gives
the signature of `ML-DSA.Sign_internal` on the formatted message
(`signMessage_wp`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem wp_ite_t {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some true) (h : WP isa th s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteT hc e, q⟩

theorem wp_ite_f {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some false) (h : WP isa el s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteF hc e, q⟩

theorem lsr8_zero (x : BitVec 32) : (x >>> 8 - 0#32 == 0#32) = decide (x.toNat < 256) := by
  rw [BitVec.sub_zero]
  by_cases h : x.toNat < 256
  · rw [decide_eq_true h, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_zero]; omega
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
    simp only [BitVec.toNat_zero] at this; omega

/-- `r12 ← ctx_len >> 8`, compared with 0, and the branch on it. -/
theorem chk_ok {s : State} (hin : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 0)) 4) :
    WP isa (.block [.ldrSp .r12 0, .mov .r12 (.shifted .r12 .lsr 8), .cmp .r12 (.imm 0)]) s fun s1 =>
      Only [.r12] s s1 ∧ isa.eval .ne s1 = some (decide ¬ (stackArg s 0).toNat < 256) := by
  refine wp_ldrSp (by decide) hin fun s1 o1 e1 => wp_movLsr (by decide) (by decide) fun s2 o2 e2 =>
    wp_cmpImm (by decide) fun s3 o3 e3 => wp_nil ⟨(o1.trans o2).trans (o3.mono fun r h => by simp at h), ?_⟩
  show some (!s3.z) = _
  rw [e3, e2, e1, show (0 : BitVec 32) = 0#32 from rfl, lsr8_zero]
  simp only [decide_not]
  rfl

/-- The words on the stack of a state satisfying `SPre` are readable. -/
theorem SPre.args {p : Params} {s : State} (h : SPre p s) {o : Nat} (ho : o + 4 ≤ 16) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 o)) 4 := by
  refine ⟨rArgs s 16, by simp [h.rd], ?_⟩
  simp only [rArgs, stackArgAddr0]
  rw [addr_add (by have := h.spA; omega)]
  exact Offset.contains_base _ ho (by omega)

theorem stackArg_eq (s : State) (j : Nat) :
    s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * j))) 32 = stackArg s j := rfl

theorem Ctx.slotOffV {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx L g m₀ t) (hL : L.Ok) (o : Nat) : (Arg.slotOff fKey o).val t = L.key + BitVec.ofNat 32 o := by
  have := hc.slotV hL (f := fKey) (j := 0) rfl (by omega)
  simp only [Arg.val] at this ⊢
  rw [this]; rfl

theorem signMessage_wp {p : Params} {n : String} {c : Prog isa}
    (hS : SignFn p c) (hp : p ∈ params) {s : State} (hpre : (signMessageContract p Arm.abi 36).pre s) :
    WP isa (signMessage n c p) s fun s' =>
      abiPreserved s s' ∧ (signMessageContract p Arm.abi 36).post s s' := by
  have h := sPre_of hpre
  unfold signMessage top
  refine WP.seq (WP.mono (chk_ok (h.args (by omega))) fun s1 ⟨o1, hc1⟩ => ?_)
  by_cases h8 : (stackArg s 0).toNat < 256
  · rw [decide_eq_false (by simpa using h8)] at hc1
    have hL := slay_ok hp h h8
    have hs1 : ∀ o, o + 4 ≤ 16 → s1.mem.readW (State.addr (s1.sp + BitVec.ofNat 32 o)) 32 =
        s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 o)) 32 := fun _ _ => by rw [o1.mem, o1.sp]
    refine wp_ite_f hc1 (WP.seq (WP.mono (enter_ok hL rfl (nA := 16) (by decide) (Nat.le_refl _) (o1.sp)
      (by rw [o1.rd]; rfl) (by rw [o1.wr]; rfl) (o1.get .r0) (o1.get .r1) (o1.get .r2) (o1.get .r3)
      (fun o ho => by rw [o1.rd, o1.wr, o1.sp]; exact h.args ho) (by rw [o1.sp]; exact h.spA)
      (by rw [o1.sp, ← stackArgAddr0]; exact h.scrArgs) (by omega)
      (by rw [hs1 12 (by omega)]; exact stackArg_eq s 3) (by decide) (fun j hj => by
        have hj4 : j < 4 := hj
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
        · exact (hs1 0 (by decide)).trans (stackArg_eq s 0)
        · exact (hs1 4 (by decide)).trans (stackArg_eq s 1)
        · exact (hs1 8 (by decide)).trans (stackArg_eq s 2)
        · exact (hs1 12 (by decide)).trans (stackArg_eq s 3))) fun t hc => ?_))
    have hsk := (skLen_ge hp).1
    have ekey : State.addr ((slay p s).key + BitVec.ofNat 32 64) = State.addr (slay p s).key + BitVec.ofNat 64 64 :=
      addr_add (by have := h.nSk; simp only [slay]; omega)
    have wtr : Within ⟨State.addr ((slay p s).key + BitVec.ofNat 32 64), 64⟩ (slay p s).KEY := by
      rw [ekey]; exact within_off _ (show 64 + 64 ≤ p.skLen by omega)
    have hfit : ((slay p s).key + BitVec.ofNat 32 64).toNat + 64 ≤ 2 ^ 32 := by
      have := h.nSk
      simp only [slay]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 64) (by decide), Nat.mod_eq_of_lt (by omega)]
      omega
    have hst : Region.Sub ⟨(slay p s).ST, 200⟩ (slay p s).SC := by
      have := hL.sub_sc (e := 0) (k := 200) (by omega)
      simpa only [x0] using this
    refine WP.seq (WP.seq (WP.mono (muHash_ok hL hc (tr := .slotOff fKey 64) (by decide) rfl
      (fun t' hc' => hc'.slotOffV hL 64) hfit ⟨_, List.mem_append_left _ hL.inKey, wtr⟩
      ((hL.xKey.symm.sub_left wtr.sub).sub_right hst)
      ((hL.xKey.symm.sub_left wtr.sub).sub_right (hL.sub_sc (by omega : 200 + 640 ≤ 1024)))
      (hL.kKey.sub_right wtr.sub)) fun t₁ ⟨hc₁, hμ⟩ => ?_))
    refine WP.mono (signCall_ok hS hp h h8 hc₁) fun s' ⟨hf, hq⟩ => ?_
    refine WP.mono (leave_ok hL hf) fun s'' ⟨hcs, hsp, hm, hx0, _, _⟩ => ?_
    refine ⟨⟨fun r hr => by rw [hcs r hr]; exact o1.get r (fun e => by
        simp only [List.mem_singleton] at e; subst e; revert hr; decide), by rw [hsp]; rfl⟩, ?_⟩
    sig_post [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
    simp only [signInternal, messageRep, skTr]
    have hm₀ : s1.mem = s.mem := o1.mem
    have ek : bytesAt t₁.mem (State.addr (s.gpr .r0)) p.skLen = bytesAt s.mem (State.addr (s.gpr .r0)) p.skLen :=
      (hc₁.bytesAt_eq (p := State.addr (slay p s).key) (n := p.skLen) hL.xKey hL.kKey (by have := h.nSk; omega)).trans
        (by rw [hm₀]; rfl)
    have er : bytesAt t₁.mem (State.addr (stackArg s 1)) 32 = bytesAt s.mem (State.addr (stackArg s 1)) 32 :=
      (hc₁.bytesAt_eq (p := State.addr (slay p s).rnd) (n := 32) h.rndScr.symm h.stkRnd (by decide)).trans
        (by rw [hm₀]; rfl)
    have etr : bytesAt t.mem (State.addr ((slay p s).key + BitVec.ofNat 32 64)) 64 =
        ((bytesAt s.mem (State.addr (s.gpr .r0)) p.skLen).drop 64).take 64 := by
      rw [hc.bytesAt_eq (hL.xKey.sub_right wtr.sub) (hL.kKey.sub_right wtr.sub) (by decide), hm₀, ekey,
        Proof.MlKem.bytesAt_slice _ _ (by omega)]
      rfl
    rw [ek, er, hμ, etr, hm₀] at hq
    rw [Proof.MlKem.Arm.setWidth_append32, hx0, hm]
    simp only [hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc] at hq ⊢
    exact hq
  · rw [decide_eq_true (by simpa using h8)] at hc1
    refine wp_ite_t hc1 (wp_movImm (by decide) fun s2 o2 e2 => wp_nil ⟨⟨fun r hr => ?_, by rw [o2.sp, o1.sp]⟩, ?_⟩)
    · have h0 : r ∉ [Reg.r0] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      have h12 : r ∉ [Reg.r12] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      rw [o2.gpr r h0, o1.gpr r h12]
    · sig_post [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega), Proof.MlKem.Arm.setWidth_append32, e2]

end VG.Proof.MlDsa.Arm.Message
