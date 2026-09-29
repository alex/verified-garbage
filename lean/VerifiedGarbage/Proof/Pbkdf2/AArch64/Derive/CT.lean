import VerifiedGarbage.Proof.Pbkdf2.AArch64.Derive.Correct
import VerifiedGarbage.Proof.Framework.AArch64.RelCT

/-!
# PBKDF2-HMAC-SHA-256 on AArch64: constant time

Untrusted: everything here is checked by Lean.

As on x86-64 (`VG.Proof.Pbkdf2.X86_64.Derive`), we relate two runs from entry
states that agree on the public arguments (`RelCT`): at every point,
correctness determines the registers the code uses as addresses, and the
callees' arguments, from the public arguments alone, so they agree in both
runs; between the calls, the taint analysis proves each block constant time
from that; the calls are constant time by the callees' own proofs; the
branches and loops test values correctness determines; and the frame saving
`x30` leaks the stack pointer, which is public (`RelCT.frameReg`).
-/

namespace VG.Proof.Pbkdf2.AArch64Derive

open VG VG.AArch64 VG.Impl.Pbkdf2.AArch64
open VG.Spec.Sha256 (bytesAt Repr)
open VG.Proof.Sha256.AArch64.Stream (eval_zero eval_nonzero)

/-- The public arguments are the same. -/
structure PubEq (a b : State) : Prop where
  pw : pw a = pw b
  x1 : a.gpr .x1 = b.gpr .x1
  sa : sa a = sa b
  x3 : a.gpr .x3 = b.gpr .x3
  x4 : (a.gpr .x4).setWidth 32 = (b.gpr .x4).setWidth 32
  op : op a = op b
  x6 : a.gpr .x6 = b.gpr .x6
  sc : sc a = sc b
  sp : a.sp = b.sp

theorem pubEq_of {a b : State} (h : Proof.Pbkdf2.pbkdf2Sha256AArch64.pub a b) : PubEq a b :=
  let ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩

section
variable {a b : State} (hq : PubEq a b)
include hq

theorem PubEq.pl : pl a = pl b := congrArg BitVec.toNat hq.x1
theorem PubEq.sl : sl a = sl b := congrArg BitVec.toNat hq.x3
theorem PubEq.cc : cc a = cc b := congrArg BitVec.toNat hq.x4
theorem PubEq.ol : ol a = ol b := congrArg BitVec.toNat hq.x6
theorem PubEq.kp : AArch64Derive.kp a = AArch64Derive.kp b := by
  unfold AArch64Derive.kp; rw [hq.pl, hq.pw, hq.sc]
theorem PubEq.kn : AArch64Derive.kn a = AArch64Derive.kn b := by
  unfold AArch64Derive.kn; rw [hq.pl, hq.x1]

end

theorem zero_eq {s₁ s₂ : State} {r : Reg} (h : s₁.gpr r = s₂.gpr r) :
    isa.eval (.zero .x r) s₁ = isa.eval (.zero .x r) s₂ := by
  have e₁ := eval_zero s₁ r
  have e₂ := eval_zero s₂ r
  rw [h] at e₁
  exact e₁.trans e₂.symm

/-- Each run, from its own entry state. -/
def Both (A : State → State → Prop) (a b : State) (s₁ s₂ : State) : Prop := A a s₁ ∧ A b s₂

/-- What a callee's contract needs of the state it is called from, given regions of its own. -/
def Site (k : Contract isa) (s : State) : Prop :=
  ∃ rd wr : List Region, k.pre (s.callEntry.withRegions rd wr) ∧ Covers (rd ++ wr) (s.rd ++ s.wr) ∧
    Covers wr s.wr

theorem agree_of {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp) (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    AArch64.Taint.Agree (AArch64.Taint.ofRegs rs) s₁ s₂ :=
  ⟨hsp, fun r hr => h r (AArch64.Taint.mem_ofRegs.mp hr)⟩

section
variable {a b : State} (ha : Pre a) (hb : Pre b)

include ha hb in
/-- A piece of code constant time, and correct in each run. -/
theorem lift {A B : State → State → Prop} {c : Prog isa} (hct : RelCT isa (Both A a b) c fun _ _ => True)
    (hw : ∀ {s₀ s : State}, Pre s₀ → A s₀ s → WP isa c s (B s₀)) : RelCT isa (Both A a b) c (Both B a b) :=
  (hct.wp fun _ _ h => ⟨hw ha h.1, hw hb h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- Code the taint analysis proves constant time from registers that agree. -/
theorem blk {A : State → State → Prop} {c : Prog isa} (rs : List Reg) {hc : VG.Taint.Hint AArch64.Taint.T}
    (ht : (taint.check (AArch64.Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ {s₁ s₂ : State}, A a s₁ → A b s₂ → s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    RelCT isa (Both A a b) c fun _ _ => True :=
  RelCT.taint (A := taint) (AArch64.Taint.ofRegs rs) (fun _ _ h => agree_of (hag h.1 h.2).1 (hag h.1 h.2).2) ht

include ha hb in
/-- A call of verified code. -/
theorem call_rel {k : Contract isa} {c : Prog isa} {nm : String} (hvk : Verified AArch64.target c k)
    {A : State → State → Prop} (site : ∀ {s₀ s : State}, Pre s₀ → A s₀ s → Site k s)
    (hpub : ∀ {s₁ s₂ : State}, A a s₁ → A b s₂ → ∀ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂)) :
    RelCT isa (Both A a b) (.call nm c) fun _ _ => True :=
  RelCT.callEx hvk.1 hvk.2.1 fun _ _ h =>
    let ⟨rd₁, wr₁, p₁, c₁, w₁⟩ := site ha h.1
    let ⟨rd₂, wr₂, p₂, c₂, w₂⟩ := site hb h.2
    ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub h.1 h.2 _ _ _ _, c₁, w₁, c₂, w₂⟩

end

/-! ## Registers that agree -/

section
variable {a b : State} (hq : PubEq a b) {s₁ s₂ : State}
include hq

theorem Base.eq (h₁ : Base a s₁) (h₂ : Base b s₂) : s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.x19], s₁.gpr r = s₂.gpr r :=
  ⟨by rw [h₁.sp, h₂.sp, hq.sp], fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.x19, h₂.x19, hq.sc]⟩

theorem Core.eq {k : Nat} (h₁ : Core a k s₁) (h₂ : Core b k s₂) :
    s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.x19, .x21, .x24], s₁.gpr r = s₂.gpr r := by
  refine ⟨by rw [h₁.regs.base.sp, h₂.regs.base.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.regs.base.x19, h₂.regs.base.x19, hq.sc]
  · rw [h₁.regs.x21, h₂.regs.x21, hq.ol]
  · rw [h₁.regs.x24, h₂.regs.x24, hq.op]

end

/-! ## The calls -/

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem hk2_site {s : State} (h : HK1 s₀ s) : Site Proof.Sha256.initAArch64 s :=
  ⟨_, _, sinit_pre h.2, by rw [h.1.base.rd, h.1.base.wr, hp.rd, hp.wr]; cov, by rw [h.1.base.wr, hp.wr]; cov⟩

theorem hk4_site {s : State} (h : HK3 s₀ s) : Site Proof.Sha256.updateAArch64 s := by
  obtain ⟨⟨k, -⟩, h0, -, h2, h3, h4⟩ := h
  exact ⟨_, _, update_pre k.base.sp hp.sp16 h0 h2 (congrArg BitVec.toNat h3) h4 (by dj) (by dj) (by dj)
    (by dj) (by dj) (by dj), by rw [k.base.rd, k.base.wr, hp.rd, hp.wr]; cov, by rw [k.base.wr, hp.wr]; cov⟩

theorem hk6_site {s : State} (h : HK5 s₀ s) : Site Proof.Sha256.finalizeAArch64 s := by
  obtain ⟨⟨k, -⟩, h0, -, h2, h3⟩ := h
  exact ⟨_, _, sfin_pre k.base.sp hp.sp16 h0 h2 h3 (by dj) (by dj) (by dj) (by dj) (by dj) (by dj),
    by rw [k.base.rd, k.base.wr, hp.rd, hp.wr]; cov, by rw [k.base.wr, hp.wr]; cov⟩

theorem ks2_site {s : State} (h : KS1 s₀ s) : Site Proof.Hmac.initSha256AArch64 s := by
  obtain ⟨⟨k, -⟩, h0, h1, h2, h3, h4⟩ := h
  have cK : ∀ R : Region, R = sR s₀ 0 96 ∨ R = sR s₀ 96 96 ∨ R = sR s₀ 528 160 →
      Region.Disjoint ⟨kp s₀, (kn s₀).toNat⟩ R := by
    rintro R (rfl | rfl | rfl) <;> rcases key_reg s₀ with ⟨e, -⟩ | e <;> rw [e] <;> dj
  refine ⟨_, _, hinit_pre k.base.sp hp.sp16 h0 h1 h2 (congrArg BitVec.toNat h3) h4 (kn_le s₀) (by dj) (by dj)
    (by dj) (cK _ (.inl rfl)) (cK _ (.inr (.inl rfl))) (cK _ (.inr (.inr rfl))) (by dj) (by dj)
    (by rcases key_reg s₀ with ⟨e, -⟩ | e <;> rw [e] <;> dj) (by dj), ?_, by rw [k.base.wr, hp.wr]; cov⟩
  rw [k.base.rd, k.base.wr, hp.rd, hp.wr]
  rcases key_reg s₀ with ⟨e, -⟩ | e <;> rw [e] <;> cov

theorem ks4_site {s : State} (h : KS3 s₀ s) : Site Proof.Sha256.updateAArch64 s := by
  obtain ⟨⟨k, -⟩, -, h0, -, h2, h3, h4⟩ := h
  exact ⟨_, _, update_pre k.base.sp hp.sp16 h0 h2 (congrArg BitVec.toNat h3) h4 (by dj) (by dj) (by dj)
    (by dj) (by dj) (by dj), by rw [k.base.rd, k.base.wr, hp.rd, hp.wr]; cov, by rw [k.base.wr, hp.wr]; cov⟩

theorem bu2_site {k : Nat} {s : State} (h : BU1 s₀ k s) : Site Proof.Sha256.updateAArch64 s := by
  obtain ⟨c, -, -, h0, -, h2, h3, h4⟩ := h
  exact ⟨_, _, update_pre c.regs.base.sp hp.sp16 h0 h2 (n := 4) (by rw [h3]; rfl) h4 (by dj) (by dj) (by dj)
    (by dj) (by dj) (by dj), by rw [c.regs.base.rd, c.regs.base.wr, hp.rd, hp.wr]; cov,
    by rw [c.regs.base.wr, hp.wr]; cov⟩

theorem bu4_site {k : Nat} {s : State} (h : BU3 s₀ k s) : Site Proof.Hmac.finalizeSha256AArch64 s := by
  obtain ⟨⟨c, -⟩, h0, h1, -, h3⟩ := h
  exact ⟨_, _, hfin_pre c.regs.base.sp hp.sp32 h0 h1 h3 (by dj) (by dj) (by dj) (by dj) (by dj) (by dj),
    by rw [c.regs.base.rd, c.regs.base.wr, hp.rd, hp.wr]; cov, by rw [c.regs.base.wr, hp.wr]; cov⟩

theorem bt2_site {k : Nat} {s : State} (h : BT1 s₀ k s) : Site Proof.Pbkdf2.iterateSha256AArch64 s := by
  obtain ⟨c, -, -, h0, h1, -, h3, h4⟩ := h
  exact ⟨_, _, iter_pre h0 h1 h3 h4 (by dj) (by dj) (by dj) (by dj) (by dj),
    by rw [c.regs.base.rd, c.regs.base.wr, hp.rd, hp.wr]; cov, by rw [c.regs.base.wr, hp.wr]; cov⟩

end

/-! ## What the callees are told agrees -/

section
variable {a b : State} (hq : PubEq a b) {s₁ s₂ : State} (rd₁ wr₁ rd₂ wr₂ : List Region)
include hq

theorem hk2_pub (h₁ : HK1 a s₁) (h₂ : HK1 b s₂) :
    Proof.Sha256.initAArch64.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) := by
  simp only [Proof.Sha256.initAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, ce0]
  exact ⟨by rw [h₁.2, h₂.2, hq.sc], by rw [h₁.1.base.sp, h₂.1.base.sp, hq.sp]⟩

theorem hk4_pub (h₁ : HK3 a s₁) (h₂ : HK3 b s₂) :
    Proof.Sha256.updateAArch64.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) := by
  obtain ⟨⟨k₁, -⟩, x0, x1, x2, x3, x4⟩ := h₁
  obtain ⟨⟨k₂, -⟩, y0, y1, y2, y3, y4⟩ := h₂
  simp only [Proof.Sha256.updateAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    ce0, ce1, ce2, ce3, ce4]
  exact ⟨by rw [x0, y0, hq.sc], by rw [x1, y1], by rw [x2, y2, hq.pw], by rw [x3, y3, hq.x1],
    by rw [x4, y4, hq.sc], by rw [k₁.base.sp, k₂.base.sp, hq.sp]⟩

theorem hk6_pub (h₁ : HK5 a s₁) (h₂ : HK5 b s₂) :
    Proof.Sha256.finalizeAArch64.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) := by
  obtain ⟨⟨k₁, -⟩, x0, x1, x2, x3⟩ := h₁
  obtain ⟨⟨k₂, -⟩, y0, y1, y2, y3⟩ := h₂
  simp only [Proof.Sha256.finalizeAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    ce0, ce1, ce2, ce3]
  exact ⟨by rw [x0, y0, hq.sc], by rw [x1, y1, hq.x1], by rw [x2, y2, hq.sc], by rw [x3, y3, hq.sc],
    by rw [k₁.base.sp, k₂.base.sp, hq.sp]⟩

theorem ks2_pub (h₁ : KS1 a s₁) (h₂ : KS1 b s₂) :
    Proof.Hmac.initSha256AArch64.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) := by
  obtain ⟨⟨k₁, -⟩, x0, x1, x2, x3, x4⟩ := h₁
  obtain ⟨⟨k₂, -⟩, y0, y1, y2, y3, y4⟩ := h₂
  simp only [Proof.Hmac.initSha256AArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    ce0, ce1, ce2, ce3, ce4]
  exact ⟨by rw [x0, y0, hq.sc], by rw [x1, y1, hq.sc], by rw [x2, y2, hq.kp], by rw [x3, y3, hq.kn],
    by rw [x4, y4, hq.sc], by rw [k₁.base.sp, k₂.base.sp, hq.sp]⟩

theorem ks4_pub (h₁ : KS3 a s₁) (h₂ : KS3 b s₂) :
    Proof.Sha256.updateAArch64.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) := by
  obtain ⟨⟨k₁, -⟩, -, x0, x1, x2, x3, x4⟩ := h₁
  obtain ⟨⟨k₂, -⟩, -, y0, y1, y2, y3, y4⟩ := h₂
  simp only [Proof.Sha256.updateAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    ce0, ce1, ce2, ce3, ce4]
  exact ⟨by rw [x0, y0, hq.sc], by rw [x1, y1], by rw [x2, y2, hq.sa], by rw [x3, y3, hq.x3],
    by rw [x4, y4, hq.sc], by rw [k₁.base.sp, k₂.base.sp, hq.sp]⟩

theorem bu2_pub {k : Nat} (h₁ : BU1 a k s₁) (h₂ : BU1 b k s₂) :
    Proof.Sha256.updateAArch64.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) := by
  obtain ⟨c₁, -, -, x0, x1, x2, x3, x4⟩ := h₁
  obtain ⟨c₂, -, -, y0, y1, y2, y3, y4⟩ := h₂
  simp only [Proof.Sha256.updateAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    ce0, ce1, ce2, ce3, ce4]
  exact ⟨by rw [x0, y0, hq.sc], by rw [x1, y1, hq.sl], by rw [x2, y2, hq.sc], by rw [x3, y3],
    by rw [x4, y4, hq.sc], by rw [c₁.regs.base.sp, c₂.regs.base.sp, hq.sp]⟩

theorem bu4_pub {k : Nat} (h₁ : BU3 a k s₁) (h₂ : BU3 b k s₂) :
    Proof.Hmac.finalizeSha256AArch64.pub (s₁.callEntry.withRegions rd₁ wr₁)
      (s₂.callEntry.withRegions rd₂ wr₂) := by
  obtain ⟨⟨c₁, -⟩, x0, x1, x2, x3⟩ := h₁
  obtain ⟨⟨c₂, -⟩, y0, y1, y2, y3⟩ := h₂
  simp only [Proof.Hmac.finalizeSha256AArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    ce0, ce1, ce2, ce3]
  exact ⟨by rw [x0, y0, hq.sc], by rw [x1, y1, hq.sc], by rw [x2, y2, hq.sl], by rw [x3, y3, hq.sc],
    by rw [c₁.regs.base.sp, c₂.regs.base.sp, hq.sp]⟩

theorem bt2_pub {k : Nat} (h₁ : BT1 a k s₁) (h₂ : BT1 b k s₂) :
    Proof.Pbkdf2.iterateSha256AArch64.pub (s₁.callEntry.withRegions rd₁ wr₁)
      (s₂.callEntry.withRegions rd₂ wr₂) := by
  obtain ⟨c₁, -, -, x0, x1, x2, x3, x4⟩ := h₁
  obtain ⟨c₂, -, -, y0, y1, y2, y3, y4⟩ := h₂
  simp only [Proof.Pbkdf2.iterateSha256AArch64, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, ce0, ce1, ce2, ce3, ce4]
  exact ⟨by rw [x0, y0, hq.sc], by rw [x1, y1, hq.sc], BitVec.eq_of_toNat_eq (by rw [x2, y2, hq.cc]),
    by rw [x3, y3, hq.sc], by rw [x4, y4, hq.sc], by rw [c₁.regs.base.sp, c₂.regs.base.sp, hq.sp]⟩

end

/-! ## The pieces -/

section
variable {a b : State} (ha : Pre a) (hb : Pre b) (hq : PubEq a b)
include ha hb hq

theorem prologue_rel :
    RelCT isa (fun s₁ s₂ => s₁ = ini a ∧ s₂ = ini b) (.block dPrologue) (Both AtP a b) := by
  have ct : RelCT isa (fun s₁ s₂ => s₁ = ini a ∧ s₂ = ini b) (.block dPrologue) fun _ _ => True :=
    RelCT.taint (A := taint) (AArch64.Taint.ofRegs [.x7]) (fun _ _ ⟨e, e'⟩ => by
      subst e e'
      exact agree_of (by show a.sp - 16 = b.sp - 16; rw [hq.sp]) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hq.sc) (by taint_decide)
  exact (ct.wp (F₁ := AtP a) (F₂ := AtP b) fun _ _ ⟨e, e'⟩ => by
    rw [e, e']; exact ⟨prologue_ok ha, prologue_ok hb⟩).mono (fun _ _ h => h) fun _ _ h => h.2

theorem hashKey_rel : RelCT isa (Both Kp0 a b) hashKey fun _ _ => True := by
  unfold hashKey
  refine RelCT.seq (lift ha hb (blk [.x19] (by taint_decide) fun h₁ h₂ => Base.eq hq h₁.base h₂.base)
    fun _ h => hk1_ok h) ?_
  refine RelCT.seq (lift ha hb (call_rel ha hb Proof.Sha256.AArch64.Stream.init_verified
    (fun hp h => hk2_site hp h) fun h₁ h₂ _ _ _ _ => hk2_pub hq _ _ _ _ h₁ h₂) fun hp h => hk2_ok hp h) ?_
  refine RelCT.seq (lift ha hb (blk [.x19] (by taint_decide) fun h₁ h₂ => Base.eq hq h₁.1.base h₂.1.base)
    fun _ h => hk3_ok h) ?_
  refine RelCT.seq (lift ha hb (call_rel ha hb Proof.Sha256.AArch64.Stream.Update.update_verified
    (fun hp h => hk4_site hp h) fun h₁ h₂ _ _ _ _ => hk4_pub hq _ _ _ _ h₁ h₂) fun hp h => hk4_ok hp h) ?_
  refine RelCT.seq (lift ha hb (blk [.x19] (by taint_decide) fun h₁ h₂ => Base.eq hq h₁.1.base h₂.1.base)
    fun _ h => hk5_ok h) ?_
  refine RelCT.seq (lift ha hb (call_rel ha hb Proof.Sha256.AArch64.Stream.Finalize.finalize_verified
    (fun hp h => hk6_site hp h) fun h₁ h₂ _ _ _ _ => hk6_pub hq _ _ _ _ h₁ h₂) fun hp h => hk6_ok hp h) ?_
  exact blk [.x19] (by taint_decide) fun h₁ h₂ => Base.eq hq h₁.1.base h₂.1.base

theorem key_rel : RelCT isa (Both AtP a b) keyPrep fun _ _ => True := by
  unfold keyPrep
  refine RelCT.ite (fun s₁ s₂ h => zero_eq (by rw [h.1.x21, h.2.x21, hq.x1]))
    (RelCT.taint (A := taint) (AArch64.Taint.ofRegs []) (fun _ _ h => agree_of
      (by rw [h.1.1.base.sp, h.1.2.base.sp, hq.sp]) (by simp)) (by taint_decide)) ?_
  refine (RelCT.seq (R := Both KT a b) (lift (A := Kp0) (B := KT) ha hb (blk [] (by taint_decide) fun h₁ h₂ =>
      ⟨(Base.eq hq h₁.base h₂.base).1, by simp⟩) fun _ h => kt_ok h) ?_).mono
    (fun _ _ h => ⟨⟨h.1.1.base, h.1.1.x20, h.1.1.x21, h.1.1.x22, h.1.1.x23, h.1.1.x24⟩,
      ⟨h.1.2.base, h.1.2.x20, h.1.2.x21, h.1.2.x22, h.1.2.x23, h.1.2.x24⟩⟩) fun _ _ h => h
  refine RelCT.ite (fun s₁ s₂ h => zero_eq (by rw [h.1.2, h.2.2, hq.x1]))
    (RelCT.taint (A := taint) (AArch64.Taint.ofRegs []) (fun _ _ h => agree_of
      (by rw [h.1.1.1.base.sp, h.1.2.1.base.sp, hq.sp]) (by simp)) (by taint_decide)) ?_
  exact (hashKey_rel ha hb hq).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h

theorem keySalt_rel : RelCT isa (Both AtK a b) keySalt (Both KS4 a b) := by
  unfold keySalt
  refine RelCT.seq (lift ha hb (blk [.x19] (by taint_decide) fun h₁ h₂ =>
    Base.eq hq h₁.regs.base h₂.regs.base) fun _ h => ks1_ok h) ?_
  refine RelCT.seq (lift ha hb (call_rel ha hb Proof.Hmac.AArch64.Init.init_verified (fun hp h => ks2_site hp h)
    fun h₁ h₂ _ _ _ _ => ks2_pub hq _ _ _ _ h₁ h₂) fun hp h => ks2_ok hp h) ?_
  refine RelCT.seq (lift ha hb (blk [.x19] (by taint_decide) fun h₁ h₂ => Base.eq hq h₁.1.base h₂.1.base)
    fun hp h => ks3_ok hp h) ?_
  exact lift ha hb (call_rel ha hb Proof.Sha256.AArch64.Stream.Update.update_verified
    (fun hp h => ks4_site hp h) fun h₁ h₂ _ _ _ _ => ks4_pub hq _ _ _ _ h₁ h₂) fun hp h => ks4_ok hp h

theorem body_rel (k : Nat) :
    RelCT isa (Both (fun s₀ s => Core s₀ k s) a b) block (Both (fun s₀ s => Next s₀ k s) a b) := by
  unfold block blockU blockT
  refine RelCT.seq (R := Both (fun s₀ s => AtU s₀ k s) a b) ?_
    (RelCT.seq (R := Both (fun s₀ s => AtT s₀ k s) a b) ?_ ?_)
  · refine RelCT.seq (lift ha hb (blk [.x19] (by taint_decide) fun h₁ h₂ =>
      Base.eq hq h₁.regs.base h₂.regs.base) fun hp h => bu1_ok hp h) ?_
    refine RelCT.seq (lift ha hb (call_rel ha hb Proof.Sha256.AArch64.Stream.Update.update_verified
      (fun hp h => bu2_site hp h) fun h₁ h₂ _ _ _ _ => bu2_pub hq _ _ _ _ h₁ h₂) fun hp h => bu2_ok hp h) ?_
    refine RelCT.seq (lift ha hb (blk [.x19] (by taint_decide) fun h₁ h₂ =>
      Base.eq hq h₁.1.regs.base h₂.1.regs.base) fun _ h => bu3_ok h) ?_
    exact lift ha hb (call_rel ha hb Proof.Hmac.AArch64.Finalize.finalize_verified
      (fun hp h => bu4_site hp h) fun h₁ h₂ _ _ _ _ => bu4_pub hq _ _ _ _ h₁ h₂) fun hp h => bu4_ok hp h
  · refine RelCT.seq (lift ha hb (blk [.x19] (by taint_decide) fun h₁ h₂ =>
      Base.eq hq h₁.1.regs.base h₂.1.regs.base) fun hp h => bt1_ok hp h) ?_
    exact lift ha hb (call_rel ha hb Proof.Pbkdf2.AArch64.iterate_verified
      (fun hp h => bt2_site hp h) fun h₁ h₂ _ _ _ _ => bt2_pub hq _ _ _ _ h₁ h₂) fun hp h => bt2_ok hp h
  · exact lift ha hb (blk [.x19, .x21, .x24] (by taint_decide) fun h₁ h₂ => Core.eq hq h₁.1 h₂.1)
      fun hp h => blockOut_ok hp h

theorem blocks_rel :
    RelCT isa (Both Setup a b) (.ite (.zero .x .x21) (.block []) (.loop block (.nonzero .x .x21)))
      fun _ _ => True := by
  refine RelCT.ite (fun s₁ s₂ h => zero_eq (by rw [h.1.x21, h.2.x21, hq.x6]))
    (RelCT.taint (A := taint) (AArch64.Taint.ofRegs []) (fun _ _ h => agree_of
      (by rw [h.1.1.base.sp, h.1.2.base.sp, hq.sp]) (by simp)) (by taint_decide)) ?_
  have lp := RelCT.loop (M := isa) (body := block) (c := .nonzero .x .x21) (Q := fun _ _ => True)
    (fun n s₁ s₂ => ∃ k, n = ol a - 32 * k ∧ Core a k s₁ ∧ Core b k s₂) (fun n => by
      refine RelCT.exists_ fun k => ?_
      intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hn, h₁, h₂⟩ e₁ e₂
      obtain ⟨ht, n₁, n₂⟩ := body_rel ha hb hq k _ _ _ _ _ _ ⟨h₁, h₂⟩ e₁ e₂
      have eL : L a k = L b k := by simp only [L, hq.ol]
      have eW : W a k = W b k := by simp only [W, L, hq.ol]
      have z₁ := n₁.cond
      have z₂ : isa.eval (.nonzero .x .x21) s₂' = some (!decide (L a k - W a k = 0)) := by
        rw [n₂.cond, eL, eW]
      refine ⟨ht, z₁.trans z₂.symm, fun _ => trivial, fun hc => ?_⟩
      have hl : L a k - W a k ≠ 0 := fun h0 => by rw [z₁, h0] at hc; simp at hc
      have := h₁.lt
      exact ⟨ol a - 32 * (k + 1), by omega, k + 1, rfl, n₁.next hl, n₂.next (by rwa [← eL, ← eW])⟩) (ol a)
  refine lp.mono (fun s₁ s₂ h => ?_) fun _ _ h => h
  have hz : AArch64.eval (.zero .x .x21) s₁ = some false := h.2
  rw [eval_zero, h.1.1.x21] at hz
  have h0 : 0 < ol a := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [show a.gpr .x6 = 0 from BitVec.eq_of_toNat_eq h0] at hz; simp at hz
  exact ⟨0, by simp, h.1.1.core h0, h.1.2.core (by rw [← hq.ol]; exact h0)⟩

theorem main_rel : RelCT isa (fun s₁ s₂ => s₁ = ini a ∧ s₂ = ini b) deriveMain fun _ _ => True := by
  unfold deriveMain
  refine RelCT.seq (prologue_rel ha hb hq) ?_
  refine RelCT.seq (lift ha hb (key_rel ha hb hq) fun hp h => key_ok hp h) ?_
  refine RelCT.seq (keySalt_rel ha hb hq) ?_
  refine RelCT.seq (lift ha hb (blk [.x19] (by taint_decide) fun h₁ h₂ =>
    Base.eq hq h₁.1.1.base h₂.1.1.base) fun hp h => setup_ok hp h) ?_
  refine RelCT.seq (lift ha hb (blocks_rel ha hb hq) fun hp h => blocks_ok hp h) ?_
  exact blk [.x19] (by taint_decide) fun h₁ h₂ => Base.eq hq h₁.1 h₂.1

theorem derive_rel : RelCT isa (fun s₁ s₂ => s₁ = a ∧ s₂ = b) derive fun _ _ => True := by
  unfold derive
  refine RelCT.frameReg ((main_rel ha hb hq).mono (fun s₁ s₂ h => ?_) fun _ _ h => h) fun s₁ s₂ h => ?_
  · obtain ⟨a', b', ⟨e, e'⟩, e₁, e₂⟩ := h
    subst e e'
    exact ⟨e₁, e₂⟩
  · obtain ⟨e, e'⟩ := h
    subst e e'
    obtain ⟨t₁, s₁', x₁, -⟩ := correctMain ha
    obtain ⟨t₂, s₂', x₂, -⟩ := correctMain hb
    exact ⟨hq.sp, ⟨t₁, s₁', x₁⟩, t₂, s₂', x₂⟩

end

theorem constantTime :
    ConstantTime isa Proof.Pbkdf2.pbkdf2Sha256AArch64.pre Proof.Pbkdf2.pbkdf2Sha256AArch64.pub derive :=
  fun _ _ _ _ _ _ h₁ h₂ hpub e₁ e₂ =>
    (derive_rel (pre_of h₁) (pre_of h₂) (pubEq_of hpub) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Verified -/

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | .x4 => 1 | .x5 => 0x3000 | .x7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 2048⟩]

theorem sat_pre : Proof.Pbkdf2.pbkdf2Sha256AArch64.pre sat := by
  simp only [Proof.Pbkdf2.pbkdf2Sha256AArch64]
  repeat' apply And.intro
  all_goals first
    | rfl
    | decide
    | (intro a h₁ h₂; simp only [Region.Contains, sat] at h₁ h₂; bv_omega)

theorem verified : Verified AArch64.target derive Proof.Pbkdf2.pbkdf2Sha256AArch64 := by
  refine ⟨fun s hs => ?_, constantTime, sat, sat_pre⟩
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
  exact ⟨t, s', he, h⟩

end VG.Proof.Pbkdf2.AArch64Derive
