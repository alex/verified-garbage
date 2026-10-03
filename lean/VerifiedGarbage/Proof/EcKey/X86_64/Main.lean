import VerifiedGarbage.Proof.Ecdsa.X86_64.Finish
import VerifiedGarbage.Impl.EcKey.X86_64
import VerifiedGarbage.Proof.Ecdsa.X86_64.Middle
import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-!
# Elliptic curve public keys on x86-64: the result, and the whole function

## The result

`finish` writes `04 ‖ x ‖ y` big-endian to `out`, or zeros, by the flag's
mask, returns the flag's low bit, and restores the callee-saved registers
(`finish_ok`): the leading byte (`lead_ok`), then the two coordinates as
the signature's `finish` writes `r ‖ s`.
-/

namespace VG.Proof.EcKey.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

theorem ea_r14 (s : State) : s.ea { base := .r14 } = s.gpr .r14 := by
  show s.gpr .r14 + BitVec.ofInt 64 0 = _
  exact BitVec.add_zero _

theorem writeW8_self (m : Mem) (a : Addr) (v : Byte) : m.writeW a v a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero]
  apply BitVec.eq_of_toNat_eq
  simp

theorem writeW8_outside (m : Mem) (a : Addr) (v : Byte) : Outside a 0 1 m (m.writeW a v) := by
  intro x hx
  have : ¬ (x - a).toNat < 1 := by simp only [ofs] at hx; omega
  simp only [Mem.writeW, Mem.write, Nat.reduceDiv, this, ite_false]

theorem mask4 (b : Bool) :
    (((4 : BitVec 32).setWidth 64 &&& (if b then BitVec.allOnes 64 else 0)).setWidth 8 : Byte) =
      if b then 4 else 0 := by
  cases b <;> decide

/-- `04` (or `0`) to `out`, by the mask in `rcx`. -/
theorem lead_ok {s : State} {out : Addr} (hr14 : s.gpr .r14 = out) (hw : InRegions s.wr out 1) (b : Bool)
    (hc : s.gpr .rcx = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block ([.mov32 .rax (.imm 4), .alu .and .rax (.reg .rcx),
      .store8 { base := .r14, disp := 0 } .rax] : List Instr)) s fun s' =>
      s'.mem out = (if b then 4 else 0) ∧ Outside out 0 1 s.mem s'.mem ∧ KeepRegs [.rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.setReg32,
    State.store8, ea_r14, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, reduceCtorEq,
    ite_true, ite_false, hr14, hw, hc, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [writeW8_self, mask4], writeW8_outside _ _ _, fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem finish_eq (c : Cfg) : Impl.EcKey.X86_64.Cfg.finish c =
    ([.mov .rcx (.mem (sc (c.sl FLAG)))] : List Instr) ++
    (([.mov32 .rax (.imm 4), .alu .and .rax (.reg .rcx), .store8 { base := .r14, disp := 0 } .rax] :
      List Instr) ++
    (storeBE c.n .r14 1 (c.sl X) ++ (storeBE c.n .r14 (1 + 8 * c.n) (c.sl Impl.EcKey.X86_64.Y) ++
    (([.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] : List Instr) ++
    Spill.restoreCode .rdi Cfg.saved)))) := by
  simp only [Impl.EcKey.X86_64.Cfg.finish, List.append_assoc]; rfl

/-- The result, the return value and the callee-saved registers. -/
theorem pkFinish_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {out : Addr}
    (hr14 : s.gpr .r14 = out) (hw : (⟨out, 1 + 16 * c.n⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 1 + 16 * c.n⟩ ⟨base, size⟩)
    {g : Reg → BitVec 64} (hsv : Spill.Saved s.mem base g Cfg.saved) (b : Bool)
    (hf : word s.mem base (c.sl FLAG) = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block (Impl.EcKey.X86_64.Cfg.finish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out (1 + 16 * c.n) =
        (if b then 4 :: (toBytes (8 * c.n) (sv c base s X) ++ toBytes (8 * c.n) (sv c base s Impl.EcKey.X86_64.Y))
          else List.replicate (1 + 16 * c.n) 0) ∧
      (s'.gpr .rax).setWidth 32 = (if b then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧
      (∀ r, r ∉ [.rax, .rcx, .rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) := by
  have h7 := hc.n7
  have hn0 := hc.n0
  have hn := hs.nowrap
  have hX := sl_le c h7 (i := X) (by decide)
  have hY := sl_le c h7 (i := Impl.EcKey.X86_64.Y) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have h1 : ∀ e, out + BitVec.ofNat 64 1 + BitVec.ofNat 64 e = out + BitVec.ofNat 64 (1 + e) := fun e => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have h8 : ∀ e, out + BitVec.ofNat 64 (1 + 8 * c.n) + BitVec.ofNat 64 e =
      out + BitVec.ofNat 64 (1 + 8 * c.n + e) := fun e => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hdsc : ∀ {a d : Nat}, a + 8 * c.n ≤ size → d + 8 * c.n ≤ 1 + 16 * c.n →
      Region.Disjoint ⟨off base a, 8 * c.n⟩ ⟨out + BitVec.ofNat 64 d, 8 * c.n⟩ := fun ha hd' =>
    (hd.symm.sub_left (Offset.sub_base base ha)).sub_right (Offset.sub_base out hd')
  have hscd : ∀ {d k : Nat}, d + k ≤ 1 + 16 * c.n →
      Region.Disjoint ⟨base, size⟩ ⟨out + BitVec.ofNat 64 d, k⟩ := fun hd' =>
    hd.symm.sub_right (Offset.sub_base out hd')
  have hout : out + BitVec.ofNat 64 0 = out := BitVec.add_zero out
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (movRcx_mem_ok hs (d := c.sl FLAG) (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have hr14₁ : s₁.gpr .r14 = out := by rw [k₁.1 _ (by decide), hr14]
  rw [WP.block_append_iff]
  have hc0 : (⟨out, 1 + 16 * c.n⟩ : Region).Contains out 1 := by
    have := Offset.contains_base out (d := 0) (n := 1) (k := 1 + 16 * c.n) (by omega) (by omega)
    rwa [hout] at this
  refine WP.mono (lead_ok hr14₁ ⟨_, by rw [k₁.2.2.2]; exact hw, hc0⟩ b (by rw [e₁, hf]))
    fun s₂ ⟨e₂, O₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have U₂ := O₂.unch_far (by have := hscd (d := 0) (k := 1) (by omega); rwa [hout] at this)
  have hr14₂ : s₂.gpr .r14 = out := by rw [k₂.gpr _ (by decide), hr14₁]
  have hrcx₂ : s₂.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₂.gpr _ (by decide), e₁, hf]
  have x₂ : wordsVal s₂.mem base (c.sl X) c.n = sv c base s X := by
    rw [U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hm₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeBE_ok hs₂ (dst := .r14) (d := 1) (a := c.sl X) (by decide) b
    hrcx₂ hX (fun e he => ⟨_, by rw [k₂.wr, k₁.2.2.2]; exact hw, by
      rw [hr14₂, h1]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hr14₂]; exact hdsc hX (by omega))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hr14₂] at e₃ O₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have U₃ := O₃.unch_far (hscd (d := 1) (by omega))
  have hr14₃ : s₃.gpr .r14 = out := by rw [k₃.gpr _ (by decide), hr14₂]
  have hrcx₃ : s₃.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₃.gpr _ (by decide), hrcx₂]
  have y₃ : wordsVal s₃.mem base (c.sl Impl.EcKey.X86_64.Y) c.n = sv c base s Impl.EcKey.X86_64.Y := by
    rw [U₃.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega),
      U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hm₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeBE_ok hs₃ (dst := .r14) (d := 1 + 8 * c.n) (a := c.sl Impl.EcKey.X86_64.Y) (by decide) b
    hrcx₃ hY (fun e he => ⟨_, by rw [k₃.wr, k₂.wr, k₁.2.2.2]; exact hw, by
      rw [hr14₃, h8]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hr14₃]; exact hdsc hY (by omega))) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [hr14₃] at e₄ O₄
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have U₄ := O₄.unch_far (hscd (d := 1 + 8 * c.n) (by omega))
  have hrcx₄ : s₄.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₄.gpr _ (by decide), hrcx₃]
  have lead : Spec.Ecdsa.bytesAt s₄.mem out 1 = [if b then 4 else 0] := by
    rw [bytesAt_keep O₄ (Offset.base_disjoint out (by omega) (by omega)) (by omega) (by omega),
      bytesAt_keep O₃ (Offset.base_disjoint out (by omega) (by omega)) (by omega) (by omega)]
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, hout, e₂]
  have first : Spec.Ecdsa.bytesAt s₄.mem (out + BitVec.ofNat 64 1) (8 * c.n) =
      if b then toBytes (8 * c.n) (sv c base s X) else List.replicate (8 * c.n) 0 := by
    rw [bytesAt_keep O₄ (Offset.disjoint out (by omega) (by omega) (by omega)) (by omega) (by omega), e₃, x₂]
  rw [WP.block_append_iff]
  refine WP.mono (raxBit_ok s₄) fun s₅ ⟨e₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  have hsv₅ : Spill.Saved s₅.mem base g Cfg.saved := by
    rw [k₅.2.1]
    have h48 : ∀ w ∈ [(size, 2 ^ 64)], 48 ≤ w.1 := fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw; decide
    exact Saved.unch (Saved.unch (Saved.unch (hm₁ ▸ hsv) h48 U₂) h48 U₃) h48 U₄
  refine WP.mono (Spill.restore_ok .rdi Cfg.saved g s₅ (by decide) (fun p hp => ?_)
    (by rw [hs₅.rdi]; exact hsv₅)) fun s₆ ⟨g₆, r₆, m₆, _, _⟩ => ?_
  · have := saved_lt p hp
    rw [hs₅.rdi]; exact ⟨_, List.mem_append_right _ hs₅.wr, hs₅.contains (by have : size = 8192 := rfl; omega) (by decide)⟩
  refine ⟨?_, ?_, g₆, fun r hr => ?_⟩
  · rw [m₆, k₅.2.1, bytesAt_add, show 16 * c.n = 8 * c.n + 8 * c.n by omega, bytesAt_add, lead, first,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, e₄, y₃]
    cases b
    · simp only [Bool.false_eq_true, ite_false, List.replicate_add]; rfl
    · simp only [ite_true]; rfl
  · have hra : Reg.rax ∉ Cfg.saved.map Prod.fst := by decide
    rw [r₆ _ hra, e₅, hrcx₄, mask_bit]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [r₆ r (by simp [Cfg.saved, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2]),
      k₅.1 r (by simp [hr.1]), k₄.gpr r (by simp [hr.1]), k₃.gpr r (by simp [hr.1]),
      k₂.gpr r (by simp [hr.1]), k₁.1 r (by simp [hr.2.1])]

end VG.Proof.EcKey.X86_64

/-!
## `x`, `y`, the checks and the result

`middle` computes `x = X Z^(p-2)` and `y = Y Z^(p-2)` from `X`, `Y` and the
power in `ACC`, each left Montgomery's form by a multiplication by 1
(`pkOps_ok`), then ands the masks of `d ∈ [1, n-1]` and `Z ≠ 0` into the
flag and writes the result (`middle_ok`).
-/

namespace VG.Proof.EcKey.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Impl.EcKey.X86_64 (YM Y)

variable {c : Cfg}

theorem middle_eq (c : Cfg) : Impl.EcKey.X86_64.Cfg.middle c =
    .seq (.block (mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC)))
    (.seq (.block (mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE)))
    (.seq (.block (mul c.MP' (c.sl YM) (c.sl RY) (c.sl ACC)))
    (.seq (.block (mul c.MP' (c.sl Y) (c.sl YM) (c.sl ONE)))
    (.block (c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ Impl.EcKey.X86_64.Cfg.finish c))))) := rfl

/-- What `middle`'s field operations leave. -/
structure OpsPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r
  wr : s'.wr = s.wr
  unch : Unch base ([XM, X, YM, Y, TMP].map fun i => (c.sl i, 8 * c.n)) s.mem s'.mem
  x_lt : sv c base s' X < c.C.p
  x : (sv c base s' X : ZMod c.C.p) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
  y_lt : sv c base s' Y < c.C.p
  y : (sv c base s' Y : ZMod c.C.p) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s RY) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)

/-- The four field operations of `middle`. -/
theorem pkOps_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hMP : ModOk c.MP' size c.C.p s.mem base) (hacc : sv c base s ACC < c.C.p) (hone : sv c base s ONE = 1)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', OpsPost c base s s' → WP isa rest s' Q) :
    WP isa (.seq (.block (mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC)))
      (.seq (.block (mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE)))
      (.seq (.block (mul c.MP' (c.sl YM) (c.sl RY) (c.sl ACC)))
      (.seq (.block (mul c.MP' (c.sl Y) (c.sl YM) (c.sl ONE))) rest)))) s Q := by
  have h7 := hc.n7
  have hn := hs.nowrap
  have hpR := coprime_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  -- `XM = X · ACC`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs hMP (o := XM) (a := RX) (b := ACC) (by decide)
    (by decide) (by decide) hacc) fun s₁ ⟨k₁, _, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have kP₁ := hMP.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have v₁ : ∀ {i}, i < 45 → i ≠ XM → i ≠ TMP → sv c base s₁ i = sv c base s i := fun hi h₁ h₂ =>
    sv_keep (MP'_n c) rfl h7 hn k₁ hi h₁ h₂
  -- `X = XM · 1`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs₁ kP₁ (o := X) (a := XM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [v₁ (by decide) (by decide) (by decide), hone]; omega))
    fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have kP₂ := kP₁.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ X → i ≠ TMP → sv c base s₂ i = sv c base s i := fun hi h₁ h₂ h₃ =>
    (sv_keep (MP'_n c) rfl h7 hn k₂ hi h₂ h₃).trans (v₁ hi h₁ h₃)
  have x₂ : (sv c base s₂ X : ZMod c.C.p) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) := by
    rw [toM_one_mul hpR (by rw [e₂, v₁ (i := ONE) (by decide) (by decide) (by decide), hone]),
      toM_mul hpR e₁]
  -- `YM = Y · ACC`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs₂ kP₂ (o := YM) (a := RY) (b := ACC) (by decide)
    (by decide) (by decide) (by rw [v₂ (by decide) (by decide) (by decide) (by decide)]; exact hacc))
    fun s₃ ⟨k₃, _, e₃⟩ => ?_)
  have hs₃ := k₃.scr hs₂
  have kP₃ := kP₂.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₃ (by decide) (by decide)
  have v₃ : ∀ {i}, i < 45 → i ≠ XM → i ≠ X → i ≠ YM → i ≠ TMP → sv c base s₃ i = sv c base s i :=
    fun hi h₁ h₂ h₃ h₄ => (sv_keep (MP'_n c) rfl h7 hn k₃ hi h₃ h₄).trans (v₂ hi h₁ h₂ h₄)
  -- `Y = YM · 1`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs₃ kP₃ (o := Y) (a := YM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [v₃ (by decide) (by decide) (by decide) (by decide) (by decide), hone]; omega))
    fun s₄ ⟨k₄, lt₄, e₄⟩ => h s₄ ?_)
  have X₄ : sv c base s₄ X = sv c base s₂ X := by
    rw [sv_keep (MP'_n c) rfl h7 hn k₄ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide)]
  have e₃' : sv c base s₃ YM * 2 ^ (64 * c.n) % c.C.p = sv c base s RY * sv c base s ACC % c.C.p := by
    rw [e₃, v₂ (i := RY) (by decide) (by decide) (by decide) (by decide),
      v₂ (i := ACC) (by decide) (by decide) (by decide) (by decide)]
  refine ⟨k₄.scr hs₃, fun r hr => ?_, by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr], ?_,
    by rw [X₄]; exact lt₂, by rw [X₄]; exact x₂, lt₄, ?_⟩
  · rw [k₄.gpr r hr, k₃.gpr r hr, k₂.gpr r hr, k₁.gpr r hr]
  · exact (((unch_slots (MP'_n c) rfl k₁.unch (l := [XM, X, YM, Y, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₂.unch (l := [XM, X, YM, Y, TMP]) (by simp) (by simp))).trans
      ((unch_slots (MP'_n c) rfl k₃.unch (l := [XM, X, YM, Y, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₄.unch (l := [XM, X, YM, Y, TMP]) (by simp) (by simp)))).mono
      fun w hw => by
        simp only [List.mem_append, or_self] at hw
        exact hw
  · rw [toM_one_mul hpR (by rw [e₄, v₃ (i := ONE) (by decide) (by decide) (by decide) (by decide) (by decide),
      hone]), toM_mul hpR e₃']

/-- Whether the public key is a point the result encodes: `d` in `[1, n-1]`
and `Z ≠ 0`. -/
abbrev ok (c : Cfg) (base : Addr) (s : State) : Bool :=
  decide ((0 < sv c base s D ∧ sv c base s D < c.C.n) ∧ sv c base s RZ ≠ 0)

/-- `x`, `y`, the checks and the result. -/
theorem middle_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hacc : sv c base s ACC < c.C.p)
    (hflag : word s.mem base (c.sl FLAG) = BitVec.allOnes 64) {out : Addr}
    (hr14 : s.gpr .r14 = out) (hw : (⟨out, 1 + 16 * c.n⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 1 + 16 * c.n⟩ ⟨base, size⟩) :
    WP isa (Impl.EcKey.X86_64.Cfg.middle c) s fun s' => ∃ xv yv, xv < c.C.p ∧
      (xv : ZMod c.C.p) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      yv < c.C.p ∧ (yv : ZMod c.C.p) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RY) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      Spec.Ecdsa.bytesAt s'.mem out (1 + 16 * c.n) =
        (if ok c base s then 4 :: (toBytes (8 * c.n) xv ++ toBytes (8 * c.n) yv)
          else List.replicate (1 + 16 * c.n) 0) ∧
      (s'.gpr .rax).setWidth 32 = (if ok c base s then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) := by
  have h0 := hc.n0
  have h7 := hc.n7
  have hn := hs.nowrap
  have hf : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  rw [middle_eq]
  refine pkOps_ok hc hs (modP_of hc F.mp) hacc F.one fun s₄ Op => ?_
  have F₄ := F.unch h7 hn (fixedOk_slW (l := [XM, X, YM, Y, TMP]) (by decide)) Op.unch
  have e₄ : ∀ {i}, i < 45 → i ∉ [XM, X, YM, Y, TMP] → sv c base s₄ i = sv c base s i := fun hi hl =>
    sv_unch Op.unch h7 hn hi (apart_slW hl)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (checkRange_ok c Op.scr h0 (sl_le c h7 (i := D) (by decide)) (sl_le c h7 (i := MN) (by decide))
    hf) fun s₅ ⟨f₅, k₅, O₅⟩ => ?_
  have hs₅ := Op.scr.of_keepRegs k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c hs₅ h0 (sl_le c h7 (i := RZ) (by decide)) hf) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  have F₆ := (F₄.unch h7 hn fixedOk_flag O₅.unch).unch h7 hn fixedOk_flag O₆.unch
  have e₆ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₆ i = sv c base s₄ i := fun hi hif =>
    (sv_flag O₆ h0 h7 hn hi hif).trans (sv_flag O₅ h0 h7 hn hi hif)
  have hflag₆ : word s₆.mem base (c.sl FLAG) = if ok c base s then BitVec.allOnes 64 else 0 := by
    have hMN : wordsVal s₄.mem base (c.sl MN) c.n = c.C.n := F₄.mn
    have z₄ : wordsVal s₄.mem base (c.sl RZ) c.n = sv c base s RZ := e₄ (by decide) (by decide)
    have d₄ : wordsVal s₄.mem base (c.sl D) c.n = sv c base s D := e₄ (by decide) (by decide)
    rw [f₆, f₅, flag_unch Op.unch h7 h0 hn (by decide), hflag, sv_flag O₅ h0 h7 hn (i := RZ) (by decide)
      (by decide), hMN, z₄, d₄, BitVec.allOnes_and, mask_and]
    simp only [mask, decide_eq_true_eq]
  have hr14₆ : s₆.gpr .r14 = out := by
    rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), Op.gpr _ (r14_not_clob hc.n4), hr14]
  have hw₆ : (⟨out, 1 + 16 * c.n⟩ : Region) ∈ s₆.wr := by rw [k₆.wr, k₅.wr, Op.wr]; exact hw
  refine WP.mono (pkFinish_ok hc hs₆ hr14₆ hw₆ hd F₆.saved _ hflag₆) fun s' ⟨bytes, rax, saved, _⟩ =>
    ⟨_, _, Op.x_lt, Op.x, Op.y_lt, Op.y, ?_, rax, saved⟩
  rw [bytes, e₆ (i := X) (by decide) (by decide), e₆ (i := Y) (by decide) (by decide)]

end VG.Proof.EcKey.X86_64

/-!
## The whole function

`publicKey_ok`: `Cfg.publicKey` computes the specification's public key of
`d`, for any curve the ECDSA proof supports (`CfgOk`), and restores the
callee-saved registers.

After `args`, the code up to `Z^(p-2)` is the signature's, with `k`, `d`
and the hash all `d`; its proof (`stage₁`, `stage₂`) is for the signature's
arguments, whose regions are within the public key's: so it runs on the
state with the signature's regions, and `Exec.widen` gives the same run
with the public key's. `middle_ok` and `publicKey_eq` do the rest.
-/

namespace VG.Proof.EcKey.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

variable {c : Cfg}

/-- The arguments: `out = rdi` (`1 + 16 n` bytes), `d = rsi` (`8 n` bytes)
and `scratch = rdx`, readable and writable as the contract says and apart
from each other as it says. -/
structure PkPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rsi, 8 * c.n⟩]
  wr : s.wr = [⟨s.gpr .rdi, 1 + 16 * c.n⟩, ⟨s.gpr .rdx, size⟩]
  out_sc : Region.Disjoint ⟨s.gpr .rdi, 1 + 16 * c.n⟩ ⟨s.gpr .rdx, size⟩
  out_d : Region.Disjoint ⟨s.gpr .rdi, 1 + 16 * c.n⟩ ⟨s.gpr .rsi, 8 * c.n⟩
  d_sc : Region.Disjoint ⟨s.gpr .rsi, 8 * c.n⟩ ⟨s.gpr .rdx, size⟩
  out_fit : (s.gpr .rdi).toNat + (1 + 16 * c.n) ≤ 2 ^ 64
  sc_fit : (s.gpr .rdx).toNat + size ≤ 2 ^ 64

/-- The private key. -/
abbrev dk (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rsi) (8 * c.n))

/-- The result the contract asks for: the specification's public key of `d`,
`04 ‖ x ‖ y`, and `1`, or zeros and `0`. -/
def PkPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.EcKey.publicKey c.C (dk c s₀) with
  | some (.affine x y) => (s'.gpr .rax).setWidth 32 = 1 ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .rdi) (1 + 16 * c.n) = Spec.EcKey.encodePoint (.affine x y)
  | _ => (s'.gpr .rax).setWidth 32 = 0 ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .rdi) (1 + 16 * c.n) = List.replicate (1 + 16 * c.n) 0

theorem args_ok (s : State) :
    WP isa (.block Impl.EcKey.X86_64.Cfg.args) s fun s' =>
      s'.gpr .r8 = s.gpr .rdx ∧ s'.gpr .rcx = s.gpr .rsi ∧ s'.gpr .rdx = s.gpr .rsi ∧
        Keeps [.r8, .rcx, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [Impl.EcKey.X86_64.Cfg.args, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, RegUpd.gpr_setReg, ite_true, reduceCtorEq, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]

/-- `vg_ec_<curve>_public_key` computes the specification's public key and
restores the callee-saved registers. -/
theorem publicKey_ok (hc : CfgOk c) {s₀ : State} (hp : PkPre c s₀) :
    WP isa (Impl.EcKey.X86_64.Cfg.publicKey c) s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ PkPost c s₀ s' := by
  have h0 := hc.n0
  have : Fact c.C.p.Prime := ⟨hc.good.prime⟩
  have hpR := coprime_pow_two hc.p_odd (64 * c.n)
  refine WP.seq (WP.mono (args_ok s₀) fun s₁ ⟨r8₁, rcx₁, rdx₁, k₁⟩ => ?_)
  have rsi₁ : s₁.gpr .rsi = s₀.gpr .rsi := k₁.1 _ (by decide)
  have rdi₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.1 _ (by decide)
  -- The signature's regions, `k`, `d` and the hash all at `d`.
  obtain ⟨sN, hsN⟩ : ∃ sN, sN = s₁.withRegions
      [⟨s₀.gpr .rsi, 8 * c.n⟩, ⟨s₀.gpr .rsi, 8 * c.n⟩, ⟨s₀.gpr .rsi, 8 * c.n⟩]
      [⟨s₀.gpr .rdi, 16 * c.n⟩, ⟨s₀.gpr .rdx, size⟩] := ⟨_, rfl⟩
  have g : ∀ r, sN.gpr r = s₁.gpr r := fun r => by rw [hsN]; rfl
  have mN : sN.mem = s₀.mem := by rw [hsN]; exact k₁.2.1
  have hsub : Region.Sub ⟨s₀.gpr .rdi, 16 * c.n⟩ ⟨s₀.gpr .rdi, 1 + 16 * c.n⟩ := Region.sub_prefix (by omega)
  have hpN : Pre c sN := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [g, rsi₁, rdi₁, rdx₁, rcx₁, r8₁]
    · rw [hsN]; rfl
    · rw [hsN]; rfl
    · exact hp.out_sc.sub_left hsub
    · exact hp.out_d.sub_left hsub
    · exact hp.out_d.sub_left hsub
    · exact hp.out_d.sub_left hsub
    · exact hp.d_sc
    · exact hp.d_sc
    · exact hp.d_sc
    · have := hp.out_fit; omega
    · exact hp.sc_fit
  have hb : sN.gpr .r8 = s₀.gpr .rdx := by rw [g, r8₁]
  obtain ⟨t, s₂N, ex, S₂⟩ := stage₁ hc (hpN.setup hc.n7) (rest := .seq (ladder c.ladderCfg) (.seq (pow c.powP) (.block [])))
    (Q := St₂ c sN (sN.gpr .r8)) fun _ S₁ => stage₂ hc S₁ fun _ S₂ => WP.block_nil S₂
  rw [hb] at S₂
  -- The same run, with the public key's regions.
  have hrd₁ : s₁.rd = [⟨s₀.gpr .rsi, 8 * c.n⟩] := by rw [k₁.2.2.1, hp.rd]
  have hwr₁ : s₁.wr = [⟨s₀.gpr .rdi, 1 + 16 * c.n⟩, ⟨s₀.gpr .rdx, size⟩] := by rw [k₁.2.2.2, hp.wr]
  have ex' := Exec.widen ex (rd := s₁.rd) (wr := s₁.wr)
    (by
      rw [hsN, State.withRegions_rd, State.withRegions_wr, hrd₁, hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩
      · exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩
      · exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩
      · exact ⟨⟨s₀.gpr .rdi, 1 + 16 * c.n⟩, by simp, 0, (BitVec.add_zero _).symm,
          by show 0 + 16 * c.n ≤ 1 + 16 * c.n; omega⟩
      · exact ⟨⟨s₀.gpr .rdx, size⟩, by simp, 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩)
    (by
      rw [hsN, State.withRegions_wr, hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨s₀.gpr .rdi, 1 + 16 * c.n⟩, List.mem_cons_self .., 0, (BitVec.add_zero _).symm,
          by show 0 + 16 * c.n ≤ 1 + 16 * c.n; omega⟩
      · exact ⟨⟨s₀.gpr .rdx, size⟩, by simp, 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩)
  rw [hsN, State.withRegions_withRegions, State.withRegions_self] at ex'
  obtain ⟨s₂, hs₂⟩ : ∃ s₂, s₂ = s₂N.withRegions s₁.rd s₁.wr := ⟨_, rfl⟩
  rw [← hs₂] at ex'
  have g₂ : s₂.gpr = s₂N.gpr := by rw [hs₂]; rfl
  have m₂ : s₂.mem = s₂N.mem := by rw [hs₂]; rfl
  have w₂ : s₂.wr = s₁.wr := by rw [hs₂]; rfl
  have sv₂ : ∀ i, sv c (s₀.gpr .rdx) s₂ i = sv c (s₀.gpr .rdx) s₂N i := fun i => by rw [sv, sv, m₂]
  have hs₂' : Scr s₂ (s₀.gpr .rdx) size :=
    ⟨by rw [g₂]; exact S₂.scr.rdi, by rw [w₂, hwr₁]; simp, S₂.scr.nowrap⟩
  have F₂ : Fixed c (s₀.gpr .rdx) sN.gpr s₂.mem := m₂ ▸ S₂.fixed
  obtain ⟨t', s', exm, xv, yv, hxl, hx, hyl, hy, bytes, rax, saved⟩ :=
    middle_ok hc hs₂' F₂ (by rw [sv₂]; exact S₂.acc_lt) (by rw [m₂]; exact S₂.flag)
      (by rw [g₂, S₂.r14, g, rdi₁]) (by rw [w₂, hwr₁]; simp) hp.out_sc
  refine ⟨_, _, .seq ex' exm, fun r hr => ?_, ?_⟩
  · have hsv : ∀ r ∈ Cfg.saved.map Prod.fst, r ∉ [Reg.r8, .rcx, .rdx] := by decide
    rw [saved r hr, g, k₁.1 r (hsv r hr)]
  -- The specification.
  have hk : kv c sN = dk c s₀ := by simp only [kv, dk, mN, g, rcx₁]
  have hD : sv c (s₀.gpr .rdx) s₂ D = dk c s₀ := by rw [sv₂, S₂.d]; simp only [dv, dk, mN, g, rsi₁]
  have hR := S₂.rep
  rw [hk] at hR
  have hZ : ∀ {i}, tmv c.C c.n (s₀.gpr .rdx) s₂N (c.sl i) = toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rdx) s₂ i) :=
    fun {i} => by rw [sv₂]
  have acc := S₂.acc
  rw [← sv₂, hZ] at acc
  rw [hZ, hZ, hZ] at hR
  have hxX : (xv : ZMod c.C.p) = toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rdx) s₂ RX) *
      toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rdx) s₂ RZ) ^ (c.C.p - 2) := by rw [hx, acc]
  have hyY : (yv : ZMod c.C.p) = toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rdx) s₂ RY) *
      toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rdx) s₂ RZ) ^ (c.C.p - 2) := by rw [hy, acc]
  have hz := toM_eq_zero_iff hpR (x := sv c (s₀.gpr .rdx) s₂ RZ) (by rw [sv₂]; exact S₂.rz_lt)
  unfold PkPost
  rw [publicKey_eq hR hxl hxX hyl hyY]
  by_cases hd : 1 ≤ dk c s₀ ∧ dk c s₀ < c.C.n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]
    by_cases h0 : sv c (s₀.gpr .rdx) s₂ RZ = 0
    · have hok : ok c (s₀.gpr .rdx) s₂ = false := decide_eq_false (by rw [hD]; omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (hz.mpr h0))]
      exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩
    · have hok : ok c (s₀.gpr .rdx) s₂ = true := decide_eq_true (by rw [hD]; omega)
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => h0 (hz.mp h)))]
      refine ⟨by rw [rax, hok]; rfl, ?_⟩
      rw [bytes, hok]
      show _ = 4 :: (toBytes c.C.len xv ++ toBytes c.C.len yv)
      rw [hc.len]; rfl
  · have hok : ok c (s₀.gpr .rdx) s₂ = false := decide_eq_false (by rw [hD]; omega)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
    exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩

end VG.Proof.EcKey.X86_64
