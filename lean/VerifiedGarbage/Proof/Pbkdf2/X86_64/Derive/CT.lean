import VerifiedGarbage.Proof.Pbkdf2.X86_64.Derive.Correct
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-!
# PBKDF2-HMAC-SHA-256 on x86-64: constant time

Untrusted: everything here is checked by Lean.

This holds for any compression function `f` (`Vf`), so it is proven once for
every implementation. As for the iteration (`IterateCT.lean`), we relate two
runs from entry states that agree on the public arguments (`RelCT`): at
every point, correctness determines the registers the code uses as
addresses, and the callees' arguments, from the public arguments alone, so
they agree in both runs; between the calls, the taint analysis proves each
block constant time from that; the calls are constant time by the callees'
own proofs; and the branches and loops test values correctness determines.
-/

namespace VG.Proof.Pbkdf2.X86_64.Derive

open VG VG.X86_64 VG.Impl.Pbkdf2.X86_64
open VG.Impl.Sha256.X86_64 (at_)
open VG.Spec.Sha256 (bytesAt Repr)
open VG.Proof.Sha256.X86_64 (ea_at ofInt_natCast)
open VG.Proof.Sha256.X86_64.Stream (wp_movm)
open VG.Impl.Sha256.X86_64.Stream (Callee)

/-- The public arguments are the same. -/
structure PubEq (a b : State) : Prop where
  pw : pw a = pw b
  rsi : a.gpr .rsi = b.gpr .rsi
  sa : sa a = sa b
  rcx : a.gpr .rcx = b.gpr .rcx
  r8 : (a.gpr .r8).setWidth 32 = (b.gpr .r8).setWidth 32
  op : op a = op b
  arg : stackArg a 0 = stackArg b 0
  sc : sc a = sc b
  rsp : a.gpr .rsp = b.gpr .rsp

theorem pubEq_of {a b : State} (h : Proof.Pbkdf2.pbkdf2Sha256X86_64.pub a b) : PubEq a b :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2⟩

section
variable {a b : State} (hq : PubEq a b)
include hq

theorem PubEq.pl : pl a = pl b := congrArg BitVec.toNat hq.rsi
theorem PubEq.sl : sl a = sl b := congrArg BitVec.toNat hq.rcx
theorem PubEq.cc : cc a = cc b := congrArg BitVec.toNat hq.r8
theorem PubEq.ol : ol a = ol b := congrArg BitVec.toNat hq.arg
theorem PubEq.kp : Derive.kp a = Derive.kp b := by unfold Derive.kp; rw [hq.pl, hq.pw, hq.sc]
theorem PubEq.kn : Derive.kn a = Derive.kn b := by unfold Derive.kn; rw [hq.pl, hq.rsi]

end

/-- Each run, from its own entry state. -/
def Both (A : State → State → Prop) (a b : State) (s₁ s₂ : State) : Prop := A a s₁ ∧ A b s₂

/-- What a callee's contract needs of the state it is called from, given regions of its own. -/
def Site (k : Contract isa) (s : State) : Prop :=
  ∃ rd wr : List Region, k.pre (s.callEntry.withRegions rd wr) ∧ Covers (rd ++ wr) (s.rd ++ s.wr) ∧
    Covers wr s.wr

theorem ce_eq {s₁ s₂ : State} (hsp : s₁.gpr .rsp = s₂.gpr .rsp) {r : Reg} (h : s₁.gpr r = s₂.gpr r)
    (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (s₁.callEntry.withRegions rd₁ wr₁).gpr r = (s₂.callEntry.withRegions rd₂ wr₂).gpr r := by
  by_cases hr : r = .rsp
  · subst hr; simp only [State.withRegions_gpr, State.callEntry_rsp, hsp]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ hr, h]

section
variable {a b : State} (ha : Pre a) (hb : Pre b)

include ha hb in
/-- A piece of code constant time, and correct in each run. -/
theorem lift {A B : State → State → Prop} {c : Prog isa} (hct : RelCT isa (Both A a b) c fun _ _ => True)
    (hw : ∀ {s₀ s : State}, Pre s₀ → A s₀ s → WP isa c s (B s₀)) : RelCT isa (Both A a b) c (Both B a b) :=
  (hct.wp fun _ _ h => ⟨hw ha h.1, hw hb h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- Code the taint analysis proves constant time from registers that agree. -/
theorem blk {A : State → State → Prop} {c : Prog isa} (rs : List Reg) {hc : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ {s₁ s₂ : State}, A a s₁ → A b s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    RelCT isa (Both A a b) c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun _ _ h => Taint.agree_ofRegs (hag h.1 h.2)) ht

include ha hb in
/-- A call of verified code. -/
theorem call_rel {k : Contract isa} {c : Prog isa} {nm : String} (hvk : Verified X86_64.target c k)
    {A : State → State → Prop} (site : ∀ {s₀ s : State}, Pre s₀ → A s₀ s → Site k s)
    (hpub : ∀ {s₁ s₂ : State}, A a s₁ → A b s₂ → ∀ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂))
    (hsp : ∀ {s₁ s₂ : State}, A a s₁ → A b s₂ → s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa (Both A a b) (.call nm c) fun _ _ => True :=
  RelCT.callEx hvk.1 hvk.2.1 fun _ _ h =>
    let ⟨rd₁, wr₁, p₁, c₁, w₁⟩ := site ha h.1
    let ⟨rd₂, wr₂, p₂, c₂, w₂⟩ := site hb h.2
    ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub h.1 h.2 _ _ _ _, c₁, w₁, c₂, w₂, hsp h.1 h.2⟩

end

/-! ## Registers that agree -/

section
variable {a b : State} (hq : PubEq a b) {s₁ s₂ : State}
include hq

theorem Base.eq (h₁ : Base a s₁) (h₂ : Base b s₂) : ∀ r ∈ [Reg.rbx, .rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.rbx, h₂.rbx, hq.sc]
  · rw [h₁.rsp, h₂.rsp, hq.rsp]

theorem Core.eq {k : Nat} (h₁ : Core a k s₁) (h₂ : Core b k s₂) :
    ∀ r ∈ [Reg.rbx, .rbp, .r13, .rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.regs.base.rbx, h₂.regs.base.rbx, hq.sc]
  · rw [h₁.regs.rbp, h₂.regs.rbp, hq.op]
  · rw [h₁.regs.r13, h₂.regs.r13, hq.ol]
  · rw [h₁.regs.base.rsp, h₂.regs.base.rsp, hq.rsp]

end

/-! ## The calls -/

section
variable {s₀ : State} (hp : Pre s₀) {f : Callee} (hv : Vf f)
include hp

theorem hk2_site {s : State} (h : HK1 s₀ s) : Site Proof.Sha256.initX86_64 s := by
  have hsp := h.1.base.rsp
  exact ⟨_, _, sinit_pre h.2 (by rw [hsp]; dj), by rw [h.1.base.rd, h.1.base.wr, hp.rd, hp.wr]; cov,
    by rw [h.1.base.wr, hp.wr]; cov⟩

theorem hk4_site {s : State} (h : HK3 s₀ s) : Site Proof.Sha256.updateX86_64 s := by
  obtain ⟨⟨k, -⟩, h1, -, h3, h4, h5⟩ := h
  have hsp := k.base.rsp
  exact ⟨_, _, update_pre h1 h3 (congrArg BitVec.toNat h4) h5 (by dj) (by dj) (by dj) (by rw [hsp]; dj)
    (by rw [hsp]; dj) (by rw [hsp]; dj), by rw [k.base.rd, k.base.wr, hp.rd, hp.wr]; cov,
    by rw [k.base.wr, hp.wr]; cov⟩

theorem hk6_site {s : State} (h : HK5 s₀ s) : Site Proof.Sha256.finalizeX86_64 s := by
  obtain ⟨⟨k, -⟩, h1, -, h3, h4⟩ := h
  have hsp := k.base.rsp
  exact ⟨_, _, sfin_pre h1 h3 h4 (by dj) (by dj) (by dj) (by rw [hsp]; dj) (by rw [hsp]; dj) (by rw [hsp]; dj),
    by rw [k.base.rd, k.base.wr, hp.rd, hp.wr]; cov, by rw [k.base.wr, hp.wr]; cov⟩

theorem ks2_site {s : State} (h : KS1 s₀ s) : Site Proof.Hmac.initSha256X86_64 s := by
  obtain ⟨⟨k, -⟩, h1, h2, h3, h4, h5⟩ := h
  have hsp := k.base.rsp
  have hn : (kn s₀).toNat ≤ 64 := by
    unfold kn; split
    · exact Nat.le_of_lt_succ ‹_›
    · decide
  have cK : ∀ R : Region, R = sR s₀ 0 96 ∨ R = sR s₀ 96 96 ∨ R = sR s₀ 512 160 →
      Region.Disjoint ⟨kp s₀, (kn s₀).toNat⟩ R := by
    rintro R (rfl | rfl | rfl) <;> rcases key_reg s₀ with ⟨e, -⟩ | e <;> rw [e] <;> dj
  refine ⟨_, _, hinit_pre h1 h2 h3 (congrArg BitVec.toNat h4) h5 hn (by dj) (by dj) (by dj)
    (cK _ (.inl rfl)) (cK _ (.inr (.inl rfl))) (cK _ (.inr (.inr rfl))) (by rw [hsp]; dj) (by rw [hsp]; dj)
    (by rw [hsp]; rcases key_reg s₀ with ⟨e, -⟩ | e <;> rw [e] <;> dj) (by rw [hsp]; dj), ?_,
    by rw [k.base.wr, hp.wr]; cov⟩
  rw [k.base.rd, k.base.wr, hp.rd, hp.wr]
  rcases key_reg s₀ with ⟨e, -⟩ | e <;> rw [e] <;> cov

theorem ks4_site {s : State} (h : KS3 s₀ s) : Site Proof.Sha256.updateX86_64 s := by
  obtain ⟨⟨k, -⟩, -, h1, -, h3, h4, h5⟩ := h
  have hsp := k.base.rsp
  exact ⟨_, _, update_pre h1 h3 (congrArg BitVec.toNat h4) h5 (by dj) (by dj) (by dj) (by rw [hsp]; dj)
    (by rw [hsp]; dj) (by rw [hsp]; dj), by rw [k.base.rd, k.base.wr, hp.rd, hp.wr]; cov,
    by rw [k.base.wr, hp.wr]; cov⟩

theorem bu2_site {k : Nat} {s : State} (h : BU1 s₀ k s) : Site Proof.Sha256.updateX86_64 s := by
  obtain ⟨c, -, -, h1, -, h3, h4, h5⟩ := h
  have hsp := c.regs.base.rsp
  exact ⟨_, _, update_pre h1 h3 (n := 4) (by rw [h4]; rfl) h5 (by dj) (by dj) (by dj) (by rw [hsp]; dj)
    (by rw [hsp]; dj) (by rw [hsp]; dj), by rw [c.regs.base.rd, c.regs.base.wr, hp.rd, hp.wr]; cov,
    by rw [c.regs.base.wr, hp.wr]; cov⟩

theorem bu4_site {k : Nat} {s : State} (h : BU3 s₀ k s) : Site Proof.Hmac.finalizeSha256X86_64 s := by
  obtain ⟨⟨c, -⟩, h1, h2, -, h4⟩ := h
  have hsp := c.regs.base.rsp
  exact ⟨_, _, hfin_pre h1 h2 h4 (by dj) (by dj) (by dj) (by rw [hsp]; dj) (by rw [hsp]; dj) (by rw [hsp]; dj),
    by rw [c.regs.base.rd, c.regs.base.wr, hp.rd, hp.wr]; cov, by rw [c.regs.base.wr, hp.wr]; cov⟩

theorem bt2_site {k : Nat} {s : State} (h : BT1 s₀ k s) : Site Proof.Pbkdf2.iterateSha256X86_64 s := by
  obtain ⟨c, -, -, h1, h2, -, h4, h5⟩ := h
  have hsp := c.regs.base.rsp
  exact ⟨_, _, iter_pre h1 h2 h4 h5 (by dj) (by dj) (by dj) (by dj) (by dj) (by rw [hsp]; dj) (by rw [hsp]; dj)
    (by rw [hsp]; dj) (by rw [hsp]; dj), by rw [c.regs.base.rd, c.regs.base.wr, hp.rd, hp.wr]; cov,
    by rw [c.regs.base.wr, hp.wr]; cov⟩

end

/-! ## What the callees are told agrees -/

section
variable {a b : State} (hq : PubEq a b) {s₁ s₂ : State} (rd₁ wr₁ rd₂ wr₂ : List Region)
include hq

theorem hk2_pub (h₁ : HK1 a s₁) (h₂ : HK1 b s₂) :
    Proof.Sha256.initX86_64.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) := by
  have sp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [h₁.1.base.rsp, h₂.1.base.rsp, hq.rsp]
  exact ce_eq sp (by rw [h₁.2, h₂.2, hq.sc]) _ _ _ _

theorem hk4_pub (h₁ : HK3 a s₁) (h₂ : HK3 b s₂) :
    Proof.Sha256.updateX86_64.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) := by
  obtain ⟨⟨k₁, -⟩, x1, x2, x3, x4, x5⟩ := h₁
  obtain ⟨⟨k₂, -⟩, y1, y2, y3, y4, y5⟩ := h₂
  have sp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [k₁.base.rsp, k₂.base.rsp, hq.rsp]
  simp only [Proof.Sha256.updateX86_64]
  exact ⟨ce_eq sp (by rw [x1, y1, hq.sc]) _ _ _ _, ce_eq sp (by rw [x2, y2]) _ _ _ _,
    ce_eq sp (by rw [x3, y3, hq.pw]) _ _ _ _, ce_eq sp (by rw [x4, y4, hq.rsi]) _ _ _ _,
    ce_eq sp (by rw [x5, y5, hq.sc]) _ _ _ _, ce_eq sp sp _ _ _ _⟩

theorem hk6_pub (h₁ : HK5 a s₁) (h₂ : HK5 b s₂) :
    Proof.Sha256.finalizeX86_64.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) := by
  obtain ⟨⟨k₁, -⟩, x1, x2, x3, x4⟩ := h₁
  obtain ⟨⟨k₂, -⟩, y1, y2, y3, y4⟩ := h₂
  have sp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [k₁.base.rsp, k₂.base.rsp, hq.rsp]
  simp only [Proof.Sha256.finalizeX86_64]
  exact ⟨ce_eq sp (by rw [x1, y1, hq.sc]) _ _ _ _, ce_eq sp (by rw [x2, y2, hq.rsi]) _ _ _ _,
    ce_eq sp (by rw [x3, y3, hq.sc]) _ _ _ _, ce_eq sp (by rw [x4, y4, hq.sc]) _ _ _ _, ce_eq sp sp _ _ _ _⟩

theorem ks2_pub (h₁ : KS1 a s₁) (h₂ : KS1 b s₂) :
    Proof.Hmac.initSha256X86_64.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) := by
  obtain ⟨⟨k₁, -⟩, x1, x2, x3, x4, x5⟩ := h₁
  obtain ⟨⟨k₂, -⟩, y1, y2, y3, y4, y5⟩ := h₂
  have sp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [k₁.base.rsp, k₂.base.rsp, hq.rsp]
  simp only [Proof.Hmac.initSha256X86_64]
  exact ⟨ce_eq sp (by rw [x1, y1, hq.sc]) _ _ _ _, ce_eq sp (by rw [x2, y2, hq.sc]) _ _ _ _,
    ce_eq sp (by rw [x3, y3, hq.kp]) _ _ _ _, ce_eq sp (by rw [x4, y4, hq.kn]) _ _ _ _,
    ce_eq sp (by rw [x5, y5, hq.sc]) _ _ _ _, ce_eq sp sp _ _ _ _⟩

theorem ks4_pub (h₁ : KS3 a s₁) (h₂ : KS3 b s₂) :
    Proof.Sha256.updateX86_64.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) := by
  obtain ⟨⟨k₁, -⟩, -, x1, x2, x3, x4, x5⟩ := h₁
  obtain ⟨⟨k₂, -⟩, -, y1, y2, y3, y4, y5⟩ := h₂
  have sp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [k₁.base.rsp, k₂.base.rsp, hq.rsp]
  simp only [Proof.Sha256.updateX86_64]
  exact ⟨ce_eq sp (by rw [x1, y1, hq.sc]) _ _ _ _, ce_eq sp (by rw [x2, y2]) _ _ _ _,
    ce_eq sp (by rw [x3, y3, hq.sa]) _ _ _ _, ce_eq sp (by rw [x4, y4, hq.rcx]) _ _ _ _,
    ce_eq sp (by rw [x5, y5, hq.sc]) _ _ _ _, ce_eq sp sp _ _ _ _⟩

theorem bu2_pub {k : Nat} (h₁ : BU1 a k s₁) (h₂ : BU1 b k s₂) :
    Proof.Sha256.updateX86_64.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) := by
  obtain ⟨c₁, -, -, x1, x2, x3, x4, x5⟩ := h₁
  obtain ⟨c₂, -, -, y1, y2, y3, y4, y5⟩ := h₂
  have sp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [c₁.regs.base.rsp, c₂.regs.base.rsp, hq.rsp]
  simp only [Proof.Sha256.updateX86_64]
  exact ⟨ce_eq sp (by rw [x1, y1, hq.sc]) _ _ _ _, ce_eq sp (by rw [x2, y2, hq.sl]) _ _ _ _,
    ce_eq sp (by rw [x3, y3, hq.sc]) _ _ _ _, ce_eq sp (by rw [x4, y4]) _ _ _ _,
    ce_eq sp (by rw [x5, y5, hq.sc]) _ _ _ _, ce_eq sp sp _ _ _ _⟩

theorem bu4_pub {k : Nat} (h₁ : BU3 a k s₁) (h₂ : BU3 b k s₂) :
    Proof.Hmac.finalizeSha256X86_64.pub (s₁.callEntry.withRegions rd₁ wr₁)
      (s₂.callEntry.withRegions rd₂ wr₂) := by
  obtain ⟨⟨c₁, -⟩, x1, x2, x3, x4⟩ := h₁
  obtain ⟨⟨c₂, -⟩, y1, y2, y3, y4⟩ := h₂
  have sp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [c₁.regs.base.rsp, c₂.regs.base.rsp, hq.rsp]
  simp only [Proof.Hmac.finalizeSha256X86_64]
  exact ⟨ce_eq sp (by rw [x1, y1, hq.sc]) _ _ _ _, ce_eq sp (by rw [x2, y2, hq.sc]) _ _ _ _,
    ce_eq sp (by rw [x3, y3, hq.sl]) _ _ _ _, ce_eq sp (by rw [x4, y4, hq.sc]) _ _ _ _, ce_eq sp sp _ _ _ _⟩

theorem bt2_pub {k : Nat} (h₁ : BT1 a k s₁) (h₂ : BT1 b k s₂) :
    Proof.Pbkdf2.iterateSha256X86_64.pub (s₁.callEntry.withRegions rd₁ wr₁)
      (s₂.callEntry.withRegions rd₂ wr₂) := by
  obtain ⟨c₁, -, -, x1, x2, x3, x4, x5⟩ := h₁
  obtain ⟨c₂, -, -, y1, y2, y3, y4, y5⟩ := h₂
  have sp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [c₁.regs.base.rsp, c₂.regs.base.rsp, hq.rsp]
  simp only [Proof.Pbkdf2.iterateSha256X86_64]
  refine ⟨ce_eq sp (by rw [x1, y1, hq.sc]) _ _ _ _, ce_eq sp (by rw [x2, y2, hq.sc]) _ _ _ _, ?_,
    ce_eq sp (by rw [x4, y4, hq.sc]) _ _ _ _, ce_eq sp (by rw [x5, y5, hq.sc]) _ _ _ _, ce_eq sp sp _ _ _ _⟩
  simp only [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp)]
  exact BitVec.eq_of_toNat_eq (by rw [x3, y3, hq.cc])

end

/-! ## The pieces -/

theorem pro1_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block [.mov .rax (.mem (at_ .rsp 16))]) s₀ fun (s : State) => s.gpr .rax = sc s₀ ∧ s.gpr .rsp = s₀.gpr .rsp := by
  refine wp_movm (a := stackArgAddr s₀ 1) (by rw [ea_at, ofInt_natCast]; rfl) ?_ fun s₁ u₁ =>
    WP.block_nil ⟨u₁.gpr, u₁.other _ (by decide)⟩
  refine ⟨argR s₀, by simp [hp.rd], ?_⟩
  simp only [Region.Contains, stackArgAddr]
  rw [show s₀.gpr .rsp + BitVec.ofNat 64 (8 * (1 + 1)) - (s₀.gpr .rsp + BitVec.ofNat 64 (8 * (0 + 1))) = 8 by
    bv_omega]
  decide

section
variable {a b : State} (ha : Pre a) (hb : Pre b) (hq : PubEq a b) {f : Callee} (hv : Vf f)
include ha hb hq

theorem prologue_rel :
    RelCT isa (fun s₁ s₂ => s₁ = a ∧ s₂ = b) (.block dPrologue) (Both AtP a b) := by
  have p1 : RelCT isa (fun s₁ s₂ => s₁ = a ∧ s₂ = b) (.block [.mov .rax (.mem (at_ .rsp 16))])
      fun s₁ s₂ => ∀ r ∈ [Reg.rax, .rsp], s₁.gpr r = s₂.gpr r :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rsp]) (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [e, e']; exact hq.rsp) (by taint_decide)).wp
      (F₁ := fun (s : State) => s.gpr .rax = sc a ∧ s.gpr .rsp = a.gpr .rsp)
      (F₂ := fun (s : State) => s.gpr .rax = sc b ∧ s.gpr .rsp = b.gpr .rsp)
      fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact ⟨pro1_ok ha, pro1_ok hb⟩).mono (fun _ _ h => h) fun _ _ h => by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h.2.1.1, h.2.2.1, hq.sc]
        · rw [h.2.1.2, h.2.2.2, hq.rsp]
  have ct : RelCT isa (fun s₁ s₂ => s₁ = a ∧ s₂ = b) (.block dPrologue) fun _ _ => True := by
    unfold dPrologue
    rw [List.append_assoc]
    exact RelCT.block_append p1
      (RelCT.taint (A := taint) (Taint.ofRegs [.rax, .rsp]) (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide))
  exact (ct.wp (F₁ := AtP a) (F₂ := AtP b) fun _ _ ⟨e, e'⟩ => by
    rw [e, e']; exact ⟨prologue_ok ha, prologue_ok hb⟩).mono (fun _ _ h => h) fun _ _ h => h.2

include hv in
theorem hashKey_rel (sfx : String) : RelCT isa (Both Kp0 a b) (hashKey f sfx) fun _ _ => True := by
  unfold hashKey
  refine RelCT.seq (lift ha hb (blk [.rbx, .rsp] (by taint_decide) fun h₁ h₂ => Base.eq hq h₁.base h₂.base)
    fun _ h => hk1_ok h) ?_
  refine RelCT.seq (lift ha hb (call_rel ha hb Proof.Sha256.X86_64.Stream.init_verified
    (fun hp h => hk2_site hp h) (fun h₁ h₂ _ _ _ _ => hk2_pub hq _ _ _ _ h₁ h₂)
    fun h₁ h₂ => Base.eq hq h₁.1.base h₂.1.base _ (by simp)) fun hp h => hk2_ok hp h) ?_
  refine RelCT.seq (lift ha hb (blk [.rbx, .rsp] (by taint_decide) fun h₁ h₂ => Base.eq hq h₁.1.base h₂.1.base)
    fun _ h => hk3_ok h) ?_
  refine RelCT.seq (lift ha hb (call_rel ha hb hv.update_v (fun hp h => hk4_site hp h)
    (fun h₁ h₂ _ _ _ _ => hk4_pub hq _ _ _ _ h₁ h₂) fun h₁ h₂ => Base.eq hq h₁.1.1.base h₂.1.1.base _ (by simp))
    fun hp h => hk4_ok hp hv h) ?_
  refine RelCT.seq (lift ha hb (blk [.rbx, .rsp] (by taint_decide) fun h₁ h₂ => Base.eq hq h₁.1.base h₂.1.base)
    fun _ h => hk5_ok h) ?_
  refine RelCT.seq (lift ha hb (call_rel ha hb hv.sfin_v (fun hp h => hk6_site hp h)
    (fun h₁ h₂ _ _ _ _ => hk6_pub hq _ _ _ _ h₁ h₂) fun h₁ h₂ => Base.eq hq h₁.1.1.base h₂.1.1.base _ (by simp))
    fun hp h => hk6_ok hp hv h) ?_
  exact blk [.rbx, .rsp] (by taint_decide) fun h₁ h₂ => Base.eq hq h₁.1.base h₂.1.base

include hv in
theorem key_rel (sfx : String) :
    RelCT isa (Both AtP a b) (.ite .b (.block []) (hashKey f sfx)) fun _ _ => True :=
  RelCT.ite (fun s₁ s₂ h => by show s₁.cf = s₂.cf; rw [h.1.cf, h.2.cf, hq.pl])
    (RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide))
    ((hashKey_rel ha hb hq hv sfx).mono (fun _ _ h => ⟨⟨h.1.1.base, h.1.1.r12, h.1.1.r13, h.1.1.r14, h.1.1.r15,
      h.1.1.rbp⟩, ⟨h.1.2.base, h.1.2.r12, h.1.2.r13, h.1.2.r14, h.1.2.r15, h.1.2.rbp⟩⟩) fun _ _ h => h)

include hv in
theorem keySalt_rel (sfx : String) : RelCT isa (Both AtK a b) (keySalt f sfx) (Both KS4 a b) := by
  unfold keySalt
  refine RelCT.seq (lift ha hb (blk [.rbx, .rsp] (by taint_decide) fun h₁ h₂ =>
    Base.eq hq h₁.regs.base h₂.regs.base) fun _ h => ks1_ok h) ?_
  refine RelCT.seq (lift ha hb (call_rel ha hb hv.hinit_v (fun hp h => ks2_site hp h)
    (fun h₁ h₂ _ _ _ _ => ks2_pub hq _ _ _ _ h₁ h₂) fun h₁ h₂ => Base.eq hq h₁.1.regs.base h₂.1.regs.base _ (by simp))
    fun hp h => ks2_ok hp hv h) ?_
  refine RelCT.seq (lift ha hb (blk [.rbx, .rsp] (by taint_decide) fun h₁ h₂ => Base.eq hq h₁.1.base h₂.1.base)
    fun hp h => ks3_ok hp h) ?_
  exact lift ha hb (call_rel ha hb hv.update_v (fun hp h => ks4_site hp h)
    (fun h₁ h₂ _ _ _ _ => ks4_pub hq _ _ _ _ h₁ h₂) fun h₁ h₂ => Base.eq hq h₁.1.1.base h₂.1.1.base _ (by simp))
    fun hp h => ks4_ok hp hv h

include hv in
theorem body_rel (sfx : String) (k : Nat) :
    RelCT isa (Both (fun s₀ s => Core s₀ k s) a b) (block f sfx) (Both (fun s₀ s => Next s₀ k s) a b) := by
  unfold block blockU blockT
  refine RelCT.seq (R := Both (fun s₀ s => AtU s₀ k s) a b) ?_
    (RelCT.seq (R := Both (fun s₀ s => AtT s₀ k s) a b) ?_ ?_)
  · refine RelCT.seq (lift ha hb (blk [.rbx, .rsp] (by taint_decide) fun h₁ h₂ =>
      Base.eq hq h₁.regs.base h₂.regs.base) fun hp h => bu1_ok hp h) ?_
    refine RelCT.seq (lift ha hb (call_rel ha hb hv.update_v (fun hp h => bu2_site hp h)
      (fun h₁ h₂ _ _ _ _ => bu2_pub hq _ _ _ _ h₁ h₂) fun h₁ h₂ => Base.eq hq h₁.1.regs.base h₂.1.regs.base _ (by simp))
      fun hp h => bu2_ok hp hv h) ?_
    refine RelCT.seq (lift ha hb (blk [.rbx, .rsp] (by taint_decide) fun h₁ h₂ =>
      Base.eq hq h₁.1.regs.base h₂.1.regs.base) fun _ h => bu3_ok h) ?_
    exact lift ha hb (call_rel ha hb (hv.hfin_v _) (fun hp h => bu4_site hp h)
      (fun h₁ h₂ _ _ _ _ => bu4_pub hq _ _ _ _ h₁ h₂) fun h₁ h₂ => Base.eq hq h₁.1.1.regs.base h₂.1.1.regs.base _ (by simp))
      fun hp h => bu4_ok hp hv h
  · refine RelCT.seq (lift ha hb (blk [.rbx, .rsp] (by taint_decide) fun h₁ h₂ =>
      Base.eq hq h₁.1.regs.base h₂.1.regs.base) fun hp h => bt1_ok hp h) ?_
    exact lift ha hb (call_rel ha hb hv.iter_v (fun hp h => bt2_site hp h)
      (fun h₁ h₂ _ _ _ _ => bt2_pub hq _ _ _ _ h₁ h₂) fun h₁ h₂ => Base.eq hq h₁.1.regs.base h₂.1.regs.base _ (by simp))
      fun hp h => bt2_ok hp hv h
  · exact lift ha hb (blk [.rbx, .rbp, .r13, .rsp] (by taint_decide) fun h₁ h₂ => Core.eq hq h₁.1 h₂.1)
      fun hp h => blockOut_ok hp h

include hv in
theorem blocks_rel (sfx : String) :
    RelCT isa (Both Setup a b) (.ite .e (.block []) (.loop (block f sfx) .ne)) fun _ _ => True := by
  refine RelCT.ite (fun s₁ s₂ h => by show s₁.zf = s₂.zf; rw [h.1.zf, h.2.zf, hq.ol])
    (RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)) ?_
  have lp := RelCT.loop (M := isa) (body := block f sfx) (c := .ne) (Q := fun _ _ => True)
    (fun n s₁ s₂ => ∃ k, n = ol a - 32 * k ∧ Core a k s₁ ∧ Core b k s₂) (fun n => by
      refine RelCT.exists_ fun k => ?_
      intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hn, h₁, h₂⟩ e₁ e₂
      obtain ⟨ht, n₁, n₂⟩ := body_rel ha hb hq hv sfx k _ _ _ _ _ _ ⟨h₁, h₂⟩ e₁ e₂
      have eL : L a k = L b k := by simp only [L, hq.ol]
      have eW : W a k = W b k := by simp only [W, L, hq.ol]
      have z₁ : isa.eval .ne s₁' = some (!decide (L a k - W a k = 0)) := by
        show s₁'.zf.map (!·) = _; rw [n₁.zf]; rfl
      have z₂ : isa.eval .ne s₂' = some (!decide (L a k - W a k = 0)) := by
        show s₂'.zf.map (!·) = _; rw [n₂.zf, eL, eW]; rfl
      refine ⟨ht, z₁.trans z₂.symm, fun _ => trivial, fun hc => ?_⟩
      have hl : L a k - W a k ≠ 0 := fun h0 => by rw [z₁, h0] at hc; simp at hc
      have := h₁.lt
      exact ⟨ol a - 32 * (k + 1), by omega, k + 1, rfl, n₁.next hl, n₂.next (by rwa [← eL, ← eW])⟩) (ol a)
  refine lp.mono (fun s₁ s₂ h => ?_) fun _ _ h => h
  have hz : s₁.zf = some false := h.2
  rw [h.1.1.zf] at hz
  have h0 : 0 < ol a := by simp at hz; omega
  exact ⟨0, by simp, h.1.1.core h0, h.1.2.core (by rw [← hq.ol]; exact h0)⟩

include hv in
theorem derive_rel (sfx : String) :
    RelCT isa (fun s₁ s₂ => s₁ = a ∧ s₂ = b) (derive f sfx) fun _ _ => True := by
  unfold derive
  refine RelCT.seq (prologue_rel ha hb hq) ?_
  refine RelCT.seq (lift ha hb (key_rel ha hb hq hv sfx) fun hp h => key_ok hp hv sfx h) ?_
  refine RelCT.seq (keySalt_rel ha hb hq hv sfx) ?_
  refine RelCT.seq (lift ha hb (blk [.rbx, .rsp] (by taint_decide) fun h₁ h₂ =>
    Base.eq hq h₁.1.1.base h₂.1.1.base) fun hp h => setup_ok hp h) ?_
  refine RelCT.seq (lift ha hb (blocks_rel ha hb hq hv sfx) fun hp h => blocks_ok hp hv sfx h) ?_
  exact blk [.rbx, .rsp] (by taint_decide) fun h₁ h₂ => Base.eq hq h₁.1 h₂.1

end

theorem constantTime {f : Callee} (hv : Vf f) (sfx : String) :
    ConstantTime isa Proof.Pbkdf2.pbkdf2Sha256X86_64.pre Proof.Pbkdf2.pbkdf2Sha256X86_64.pub (derive f sfx) :=
  fun _ _ _ _ _ _ h₁ h₂ hpub e₁ e₂ =>
    (derive_rel (pre_of h₁) (pre_of h₂) (pubEq_of hpub) hv sfx _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Verified -/

theorem derive_hm {f : Callee} (hv : Vf f) (sfx : String) :
    (derive f sfx).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [derive, hashKey, keySalt, block, blockU, blockT, blockOut, byteLoop, Code.allInstrs, hv.update_hm,
    hv.sfin_hm, hv.hinit_hm, hv.hfin_hm, hv.iter_hm, Bool.and_true, Bool.true_and]
  decide +kernel

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .r8 => 1 | .r9 => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩, ⟨0x8008, 16⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 2048⟩]

theorem sat_arg0 : stackArg sat 0 = 0 := by decide
theorem sat_arg1 : stackArg sat 1 = 0x4000 := by decide

theorem sat_pre : Proof.Pbkdf2.pbkdf2Sha256X86_64.pre sat := by
  simp only [Proof.Pbkdf2.pbkdf2Sha256X86_64, sat_arg0, sat_arg1]
  repeat' apply And.intro
  all_goals first
    | rfl
    | decide
    | (intro a h₁ h₂; simp only [Region.Contains, sat, stackArgAddr] at h₁ h₂; bv_omega)

/-- `derive f` is verified for any compression function `f` that `Vf` allows. -/
theorem verified_of {f : Callee} (hv : Vf f) (sfx : String) :
    Verified X86_64.target (derive f sfx) Proof.Pbkdf2.pbkdf2Sha256X86_64 := by
  refine ⟨fun s hs => ?_, constantTime hv sfx, sat, sat_pre⟩
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs) hv sfx
  exact ⟨t, s', he, abiPreserved_of_exec (derive_hm hv sfx) he h.1, h.2⟩

end VG.Proof.Pbkdf2.X86_64.Derive
