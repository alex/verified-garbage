import VerifiedGarbage.Proof.Scrypt.AArch64.RoMixFun
import VerifiedGarbage.Proof.Scrypt.AArch64.BlockMixVerified
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import Mathlib.Tactic.DefEqTransformations

/-!
# scryptROMix on AArch64: verified

Untrusted: everything here is checked by Lean. `BlockMixSpec` of the
verified `vg_scrypt_blockmix`, from its `Verified` proof by `WP.callF`; then
constant time, up to the indices `j`, as on x86-64 (`X86_64/RoMixCT.lean`):
we relate two runs (`RelCT`). Correctness determines our registers from the
public arguments, so they agree between the calls, where the taint analysis
proves each piece constant time; the calls are constant time by
scryptBlockMix's own proof. In step 3, the address of `V[j]` depends on `j`,
which the contract declares public: the two runs compute the same `j`, since
both compute their indices in order (`Inv3.js`) and agree on the whole list.
-/

namespace VG.Proof.Scrypt.AArch64.RoMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blockMix)
open VG.Proof.Md5.AArch64.Stream (Upd wp_mov wp_addImm wp_lsr eval_nonzero)
open VG.Proof.Scrypt.AArch64.BlockMix (covers_of_in covers_pair)
open VG.Proof.Scrypt.X86_64.BlockMix (InRegions.right)

/-! ## The call of `vg_scrypt_blockmix` -/

theorem blockMix_fdepth : Impl.Scrypt.AArch64.blockMix.fdepth = 1 := by decide +kernel

theorem bm_pre {s : State} {src dst scr : Addr} {r : Nat} (h0 : s.gpr .x0 = src)
    (h1 : s.gpr .x1 = BitVec.ofNat 64 r) (h2 : s.gpr .x2 = dst) (h3 : s.gpr .x3 = BitVec.ofNat 64 r)
    (h4 : s.gpr .x4 = scr) (hr : 0 < r) (hlt : 128 * r < 2 ^ 64)
    (hds : Region.Disjoint ⟨dst, 128 * r⟩ ⟨scr, 128⟩) (hsd : Region.Disjoint ⟨src, 128 * r⟩ ⟨dst, 128 * r⟩)
    (hss : Region.Disjoint ⟨src, 128 * r⟩ ⟨scr, 128⟩) (hsp : 16 ≤ s.sp.toNat)
    (bsrc : (below s.sp 16).Disjoint ⟨src, 128 * r⟩) (bdst : (below s.sp 16).Disjoint ⟨dst, 128 * r⟩)
    (bscr : (below s.sp 16).Disjoint ⟨scr, 128⟩)
    (nsrc : src.toNat + 128 * r ≤ 2 ^ 64) (ndst : dst.toNat + 128 * r ≤ 2 ^ 64)
    (nscr : scr.toNat + 128 ≤ 2 ^ 64)
    (isrc : InRegions (s.rd ++ s.wr) src (128 * r)) (idst : InRegions s.wr dst (128 * r))
    (iscr : InRegions s.wr scr 128) :
    Proof.Scrypt.blockMixAArch64.pre
      (s.callEntry.withRegions [⟨src, 128 * r⟩] [⟨dst, 128 * r⟩, ⟨scr, 128⟩]) ∧
    Covers ([⟨src, 128 * r⟩] ++ [⟨dst, 128 * r⟩, ⟨scr, 128⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨dst, 128 * r⟩, ⟨scr, 128⟩] s.wr := by
  have tr : (BitVec.ofNat 64 r).toNat = r := toNat_ofNat_lt (by omega)
  have c128 : r * 128 = 128 * r := Nat.mul_comm _ _
  have cw := covers_pair (covers_of_in idst) (covers_of_in iscr)
  refine ⟨?_, ?_, cw⟩
  · simp only [Proof.Scrypt.blockMixAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h2, h3, h4, tr, c128]
    exact ⟨trivial, trivial, hds, hsd, hss, hsp, bsrc, bdst, bscr, nsrc, ndst, nscr, trivial, hr⟩
  · have h1 := covers_of_in isrc
    intro a n h
    simp only [List.cons_append, List.nil_append] at h
    obtain ⟨R, hR, hc⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact h1 a n ⟨_, List.mem_singleton_self _, hc⟩
    · obtain ⟨R', hR', hc'⟩ := cw a n ⟨_, by simp, hc⟩
      exact ⟨R', List.mem_append_right _ hR', hc'⟩
    · obtain ⟨R', hR', hc'⟩ := cw a n ⟨_, by simp, hc⟩
      exact ⟨R', List.mem_append_right _ hR', hc'⟩

theorem blockMixSpec : BlockMixSpec Impl.Scrypt.AArch64.blockMix := by
  intro s src dst scr r h0 h1 h2 h3 h4 hr hlt hds hsd hss hsp bsrc bdst bscr nsrc ndst nscr
    isrc idst iscr Q hQ
  have tr : (BitVec.ofNat 64 r).toNat = r := toNat_ofNat_lt (by omega)
  obtain ⟨p, c₁, c₂⟩ := bm_pre h0 h1 h2 h3 h4 hr hlt hds hsd hss hsp bsrc bdst bscr nsrc ndst nscr
    isrc idst iscr
  refine WP.callF (k := Proof.Scrypt.blockMixAArch64) BlockMix.blockMix_verified.1 p c₁ c₂ ?_
    (by rw [blockMix_fdepth]; decide)
  intro s₂ hrd hwr hsp' hf hcs hpost
  simp only [Proof.Scrypt.blockMixAArch64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2, tr] at hpost
  rw [blockMix_fdepth] at hf
  exact hQ s₂ hrd hwr hsp' hcs hf hpost

/-! ## What each run knows -/

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  x0 : s₀.gpr .x0 = s₀'.gpr .x0
  x1 : s₀.gpr .x1 = s₀'.gpr .x1
  x2 : s₀.gpr .x2 = s₀'.gpr .x2
  x3 : s₀.gpr .x3 = s₀'.gpr .x3
  x4 : s₀.gpr .x4 = s₀'.gpr .x4
  sp : s₀.sp = s₀'.sp

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.rr : rr s₀ = rr s₀' := by simp only [RoMix.rr, hq.x1]
theorem PubEq.NN : NN s₀ = NN s₀' := by simp only [RoMix.NN, RoMix.vl, RoMix.rr, hq.x1, hq.x3]
theorem PubEq.vAt (i : Nat) : vAt s₀ i = vAt s₀' i := by
  simp only [RoMix.vAt, RoMix.vP, RoMix.rr, hq.x1, hq.x2]
theorem PubEq.tP : tP s₀ = tP s₀' := by simp only [RoMix.tP, RoMix.sc, hq.x4]

end

/-- The registers the loops keep, with `x24 = bp` and `x23 = q`. -/
structure KR (s₀ : State) (bp q : Addr) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = bP s₀
  x20 : s.gpr .x20 = vP s₀
  x21 : s.gpr .x21 = sc s₀
  x22 : s.gpr .x22 = BitVec.ofNat 64 (128 * rr s₀)
  x23 : s.gpr .x23 = q
  x24 : s.gpr .x24 = bp

/-- The registers `KR` fixes. -/
abbrev kRegs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24]

theorem kRegs_ne : ∀ r ∈ kRegs, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x9 := by
  decide

theorem kRegs_pres : ∀ r ∈ kRegs, r ∈ preserved ∧ r ≠ .x30 ∧ r ∉ linkRegs := by decide

theorem KR.keep {s₀ : State} {bp q : Addr} {s s' : State} (h : KR s₀ bp q s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hk : ∀ r ∈ kRegs, s'.gpr r = s.gpr r) : KR s₀ bp q s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hk _ (by decide)).trans h.x19,
    (hk _ (by decide)).trans h.x20, (hk _ (by decide)).trans h.x21, (hk _ (by decide)).trans h.x22,
    (hk _ (by decide)).trans h.x23, (hk _ (by decide)).trans h.x24⟩

/-- Whether an instruction writes none of `kRegs`. -/
def kFree (i : Instr) : Bool := kRegs.all fun r => dstOf i != some r

/-- `KR` survives code that writes none of its registers. -/
theorem KR.exec {c : Prog isa} (hc : c.allInstrs kFree = true) {s₀ : State} {bp q : Addr}
    {s s' : State} {t : List Leak} (he : Exec isa c s t s') (h : KR s₀ bp q s) : KR s₀ bp q s' := by
  obtain ⟨rd, wr, sp⟩ := Exec.rdwr he
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  refine h.keep rd wr sp fun r hr => Exec.gpr (fun i hi => ?_) he (.inr (kRegs_pres r hr).2.2)
  have := hc i hi
  simp only [kFree, List.all_eq_true, bne_iff_ne, ne_eq] at this
  exact this r hr

theorem Inv2.kr {s₀ : State} {i : Nat} {s : State} (h : Inv2 s₀ i s) :
    KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.sp, h.x19, h.x20, h.x21, h.x22, h.x23, h.x24⟩

theorem Inv3.kr {s₀ : State} {i : Nat} {s : State} (h : Inv3 s₀ i s) :
    KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) (BitVec.ofNat 64 (NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.sp, h.x19, h.x20, h.x21, h.x22, h.x23, h.x24⟩

theorem agree_of {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs rs) s₁ s₂ :=
  ⟨hsp, fun r hr => h r (VG.AArch64.Taint.mem_ofRegs.mp hr)⟩

/-- The registers `KR` fixes, and the stack pointer, agree in two runs. -/
theorem agree_K {s₀ s₀' : State} (hq : PubEq s₀ s₀') {bp q bp' q' : Addr} {s s' : State}
    (h : KR s₀ bp q s) (h' : KR s₀' bp' q' s') (hbp : bp = bp') (hq' : q = q') {extra : List Reg}
    (hx : ∀ r ∈ extra, s.gpr r = s'.gpr r) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs (extra ++ kRegs)) s s' := by
  refine agree_of (by rw [h.sp, h'.sp, hq.sp]) fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact hx r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19, bP, bP, hq.x0]
  · rw [h.x20, h'.x20, vP, vP, hq.x2]
  · rw [h.x21, h'.x21, sc, sc, hq.x4]
  · rw [h.x22, h'.x22, hq.rr]
  · rw [h.x23, h'.x23, hq']
  · rw [h.x24, h'.x24, hbp]

/-- The arguments of a call of `vg_scrypt_blockmix` from `A` into `b`. -/
structure Args (s₀ : State) (A : Addr) (s : State) : Prop where
  x0 : s.gpr .x0 = A
  x1 : s.gpr .x1 = BitVec.ofNat 64 (rr s₀)
  x2 : s.gpr .x2 = bP s₀
  x3 : s.gpr .x3 = BitVec.ofNat 64 (rr s₀)
  x4 : s.gpr .x4 = sc s₀

/-- A block that may be the source of such a call. -/
structure SrcOK (s₀ : State) (A : Addr) : Prop where
  b : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩
  w : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨sc s₀, 128⟩
  stk : (stkR s₀).Disjoint ⟨A, 128 * rr s₀⟩
  nw : A.toNat + 128 * rr s₀ ≤ 2 ^ 64
  inr : InRegions (s₀.rd ++ s₀.wr) A (128 * rr s₀)

theorem srcOK_v {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < NN s₀) : SrcOK s₀ (vAt s₀ i) :=
  ⟨(vAt_b hp hi).sub_right b_sub', (vAt_s hp hi).sub_right w_sub, (vAt_stk hp hi).symm,
    vAt_nw hp hi, InRegions.right (vAt_in hp hi)⟩

theorem srcOK_t {s₀ : State} (hp : Pre s₀) : SrcOK s₀ (tP s₀) :=
  ⟨t_b hp, t_w hp, hp.stk_s.sub_right (t_sub hp), t_nw hp, InRegions.right (t_in hp)⟩

theorem call_pre {s₀ : State} (hp : Pre s₀) {A : Addr} (hA : SrcOK s₀ A) {bp q : Addr} {s : State}
    (h : KR s₀ bp q s) (ha : Args s₀ A s) :
    Proof.Scrypt.blockMixAArch64.pre (s.callEntry.withRegions [⟨A, 128 * rr s₀⟩]
      [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩]) ∧
    Covers ([⟨A, 128 * rr s₀⟩] ++ [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩] s.wr := by
  have lt := r_lt hp
  exact bm_pre ha.x0 ha.x1 ha.x2 ha.x3 ha.x4 hp.pos lt
    ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hA.b hA.w
    (by rw [h.sp]; exact hp.sp16) (by rw [h.sp]; exact hA.stk)
    (by rw [h.sp]; exact hp.stk_b.sub_right (b_sub' (s₀ := s₀)))
    (by rw [h.sp]; exact hp.stk_s.sub_right (w_sub (s₀ := s₀))) hA.nw (by have := hp.b_nw; omega)
    (by have := hp.s_nw; omega) (by rw [h.rd, h.wr]; exact hA.inr) (by rw [h.wr]; exact b_in hp)
    (by rw [h.wr]; exact w_in hp)

theorem call_wp {s₀ : State} (hp : Pre s₀) {A : Addr} (hA : SrcOK s₀ A) {bp q : Addr} {s : State}
    (h : KR s₀ bp q s) (ha : Args s₀ A s) :
    WP isa (.call "vg_scrypt_blockmix" Impl.Scrypt.AArch64.blockMix) s (KR s₀ bp q) := by
  have lt := r_lt hp
  exact blockMixSpec s A (bP s₀) (sc s₀) (rr s₀) ha.x0 ha.x1 ha.x2 ha.x3 ha.x4 hp.pos lt
    ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hA.b hA.w
    (by rw [h.sp]; exact hp.sp16) (by rw [h.sp]; exact hA.stk)
    (by rw [h.sp]; exact hp.stk_b.sub_right (b_sub' (s₀ := s₀)))
    (by rw [h.sp]; exact hp.stk_s.sub_right (w_sub (s₀ := s₀))) hA.nw (by have := hp.b_nw; omega)
    (by have := hp.s_nw; omega) (by rw [h.rd, h.wr]; exact hA.inr) (by rw [h.wr]; exact b_in hp)
    (by rw [h.wr]; exact w_in hp) _ fun _ rd wr sp cs _ _ =>
      h.keep rd wr sp fun r hr => cs r (kRegs_pres r hr).1 (kRegs_pres r hr).2.1

theorem call_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀') {A A' : Addr}
    (hA : SrcOK s₀ A) (hA' : SrcOK s₀' A') (hAA : A = A') {bp q bp' q' : Addr} :
    RelCT isa (fun s s' => (KR s₀ bp q s ∧ Args s₀ A s) ∧ (KR s₀' bp' q' s' ∧ Args s₀' A' s'))
      (.call "vg_scrypt_blockmix" Impl.Scrypt.AArch64.blockMix)
      fun s s' => KR s₀ bp q s ∧ KR s₀' bp' q' s' := by
  subst hAA
  have eb : bP s₀' = bP s₀ := hq.x0.symm
  have es : sc s₀' = sc s₀ := hq.x4.symm
  have er : rr s₀' = rr s₀ := hq.rr.symm
  have call := RelCT.call (n := "vg_scrypt_blockmix") (P := fun s s' =>
      (KR s₀ bp q s ∧ Args s₀ A s) ∧ (KR s₀' bp' q' s' ∧ Args s₀' A s'))
    BlockMix.blockMix_verified.1 BlockMix.blockMix_verified.2.1 [⟨A, 128 * rr s₀⟩]
    [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩] fun s s' ⟨⟨h, ha⟩, ⟨h', ha'⟩⟩ => by
      obtain ⟨p₁, c₁, w₁⟩ := call_pre hp hA h ha
      obtain ⟨p₂, c₂, w₂⟩ := call_pre hp' hA' h' ha'
      rw [eb, es, er] at p₂ c₂ w₂
      refine ⟨p₁, p₂, ?_, c₁, w₁, c₂, w₂⟩
      simp only [Proof.Scrypt.blockMixAArch64, State.withRegions_gpr, State.withRegions_sp,
        State.callEntry_sp, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), ha.x0, ha.x1, ha.x2, ha.x3, ha.x4,
        ha'.x0, ha'.x1, ha'.x2, ha'.x3, ha'.x4, eb, es, er, h.sp, h'.sp, hq.sp]
      exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  exact (call.wp fun s s' h => ⟨call_wp hp hA h.1.1 h.1.2, call_wp hp' hA' h.2.1 h.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## Relating pieces of code -/

/-- Code that writes none of `kRegs` keeps `KR` in both runs. -/
theorem RelCT.keepK {P : State → State → Prop} {c : Prog isa} (h : RelCT isa P c fun _ _ => True)
    (hc : c.allInstrs kFree = true) {s₀ s₀' : State} {bp q bp' q' : Addr}
    (hk : ∀ s s', P s s' → KR s₀ bp q s ∧ KR s₀' bp' q' s') :
    RelCT isa P c fun s s' => KR s₀ bp q s ∧ KR s₀' bp' q' s' :=
  fun _ _ _ _ _ _ hp e e' =>
    ⟨(h _ _ _ _ _ _ hp e e').1, KR.exec hc e (hk _ _ hp).1, KR.exec hc e' (hk _ _ hp).2⟩

theorem RelCT.assoc {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq (.seq a b) c) Q) : RelCT isa P (.seq a (.seq b c)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ bc₁ =>
    cases bc₁ with
    | seq b₁ c₁ =>
      cases e₂ with
      | seq a₂ bc₂ =>
        cases bc₂ with
        | seq b₂ c₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ b₁) c₁) (.seq (.seq a₂ b₂) c₂)
          simp only [List.append_assoc] at ht
          exact ⟨ht, hq⟩

theorem RelCT.exists' {α : Type} {P : α → State → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ a, RelCT isa (P a) c Q) :
    RelCT isa (fun s s' => ∃ a, P a s s') c Q :=
  fun _ _ _ _ _ _ ⟨a, hp⟩ e e' => h a _ _ _ _ _ _ hp e e'

/-! ## Setting up the calls -/

theorem tail_wp {s₀ : State} (hp : Pre s₀) {bp q A : Addr} {s : State} (h : KR s₀ bp q s)
    (hA : s.gpr .x0 = A) :
    WP isa (.block bmTail) s fun s' => KR s₀ bp q s' ∧ Args s₀ A s' := by
  have lt := r_lt hp
  refine wp_lsr (by decide) fun a ua => wp_mov fun b ub => wp_mov fun d ud => wp_mov fun e ue =>
    WP.block_nil ⟨?_, ?_⟩
  · exact h.keep (by rw [ue.rd, ud.rd, ub.rd, ua.rd]) (by rw [ue.wr, ud.wr, ub.wr, ua.wr])
      (by rw [ue.sp, ud.sp, ub.sp, ua.sp]) fun r hr => by
        obtain ⟨-, h1, h2, h3, h4, -⟩ := kRegs_ne r hr
        rw [ue.other _ h4, ud.other _ h3, ub.other _ h2, ua.other _ h1]
  have h1 : a.gpr .x1 = BitVec.ofNat 64 (rr s₀) := by
    rw [ua.gpr, h.x22, shr_ofNat _ lt]; congr 1; omega
  exact ⟨by rw [ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), hA],
    by rw [ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide), h1],
    by rw [ue.other _ (by decide), ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h.x19],
    by rw [ue.other _ (by decide), ud.gpr, ub.other _ (by decide), h1],
    by rw [ue.gpr, ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.x21]⟩

theorem x2_wp {s₀ : State} (hp : Pre s₀) {bp q : Addr} {s : State} (h : KR s₀ bp q s) :
    WP isa (.block ([mov .x0 .x24] ++ bmTail)) s fun s' => KR s₀ bp q s' ∧ Args s₀ bp s' :=
  wp_mov fun a ua => tail_wp hp
    (h.keep ua.rd ua.wr ua.sp fun r hr => ua.other r (kRegs_ne r hr).1) (by rw [ua.gpr, h.x24])

theorem x3_wp {s₀ : State} (hp : Pre s₀) {bp q : Addr} {s : State} (h : KR s₀ bp q s) :
    WP isa (.block ([.addImm .x .x0 .x21 192] ++ bmTail)) s
      fun s' => KR s₀ bp q s' ∧ Args s₀ (tP s₀) s' :=
  wp_addImm (by decide) fun a ua => tail_wp hp
    (h.keep ua.rd ua.wr ua.sp fun r hr => ua.other r (kRegs_ne r hr).1) (by rw [ua.gpr, h.x21])

/-! ## Step 2, in two runs -/

theorem eval_x23 (s : State) : isa.eval (.nonzero .x .x23) s = some (s.gpr .x23 != 0) :=
  eval_nonzero s .x23

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body2_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv2 s₀ i s ∧ Inv2 s₀' i s') (step2 Impl.Scrypt.AArch64.blockMix)
      fun s s' => (Inv2 s₀ (i + 1) s ∧ (s.gpr .x23 != 0) = decide (i + 1 ≠ NN s₀)) ∧
        (Inv2 s₀' (i + 1) s' ∧ (s'.gpr .x23 != 0) = decide (i + 1 ≠ NN s₀')) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have ev : vAt s₀ i = vAt s₀' i := hq.vAt i
  have e15 : BitVec.ofNat 64 (NN s₀ - i) = BitVec.ofNat 64 (NN s₀' - i) := by rw [hq.NN]
  let K (t₀ t : State) : Prop := KR t₀ (vAt t₀ i) (BitVec.ofNat 64 (NN t₀ - i)) t
  have ac : RelCT isa (fun s s' => Inv2 s₀ i s ∧ Inv2 s₀' i s')
      (.seq (.block [mov .x9 .x19, mov .x10 .x24, .lsr .x .x11 .x22 3]) copyLoop)
      fun s s' => K s₀ s ∧ K s₀' s' :=
    RelCT.keepK (RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.kr h.2.kr ev e15 (by simp)) (by taint_decide))
      (by decide +kernel) fun _ _ h => ⟨h.1.kr, h.2.kr⟩
  have x : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block ([mov .x0 .x24] ++ bmTail)) fun s s' =>
        (K s₀ s ∧ Args s₀ (vAt s₀ i) s) ∧ (K s₀' s' ∧ Args s₀' (vAt s₀' i) s') :=
    ((RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 ev e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨x2_wp hp h.1, x2_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cl := call_rel hp hp' hq (srcOK_v hp hi) (srcOK_v hp' hi') ev
    (bp := vAt s₀ i) (q := BitVec.ofNat 64 (NN s₀ - i)) (bp' := vAt s₀' i)
    (q' := BitVec.ofNat 64 (NN s₀' - i))
  have e : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block [.add .x .x24 .x24 .x22, .subImm .x .x23 .x23 1]) fun _ _ => True :=
    RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 ev e15 (by simp)) (by taint_decide)
  have body := RelCT.assoc (ac.seq ((x.seq cl).seq e))
  rw [← blockMixTo_eq] at body
  exact (body.wp fun _ _ h => ⟨step2_ok blockMixSpec hp hi h.1, step2_ok blockMixSpec hp' hi' h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem loop2_rel :
    RelCT isa (fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s')
      (.loop (step2 Impl.Scrypt.AArch64.blockMix) (.nonzero .x .x23))
      fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step2 Impl.Scrypt.AArch64.blockMix)
    (c := .nonzero .x .x23) (Q := fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv2 s₀ i s ∧ Inv2 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body2_rel hp hp' hq hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_x23, eval_x23, z, z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

end

/-! ## Step 3 -/

theorem j_wp {s₀ : State} (hp : Pre s₀) {q : Addr} {s : State}
    (h : KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) q s) {j : Nat} (hj : jOf s₀ s.mem = j) :
    WP isa (.block jBlock) s fun s' =>
      KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) q s' ∧ s'.gpr .x9 = BitVec.ofNat 64 j :=
  WP.mono (j_ok hp h.x19 h.x22 h.x24 h.rd h.wr) fun _ u =>
    ⟨h.keep u.rd u.wr u.sp fun r hr => u.other r (kRegs_ne r hr).2.2.2.2.2, by rw [u.gpr, hj]⟩

/-- The next index, from the ones still to come. -/
theorem drop_js {s₀ : State} {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s) :
    ∃ rest, (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop i = jOf s₀ s.mem :: rest := by
  have e : NN s₀ - i = NN s₀ - (i + 1) + 1 := by omega
  have hs := h.js
  rw [e, mixLoop_succ_snd] at hs
  exact ⟨_, hs.symm⟩

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body3_rel_j {i : Nat} (hi : i < NN s₀) (j : Nat) :
    RelCT isa (fun s s' => (Inv3 s₀ i s ∧ jOf s₀ s.mem = j) ∧ (Inv3 s₀' i s' ∧ jOf s₀' s'.mem = j))
      (step3 Impl.Scrypt.AArch64.blockMix)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ (s.gpr .x23 != 0) = decide (i + 1 ≠ NN s₀)) ∧
        (Inv3 s₀' (i + 1) s' ∧ (s'.gpr .x23 != 0) = decide (i + 1 ≠ NN s₀')) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have e1 : BitVec.ofNat 64 (NN s₀ - 1) = BitVec.ofNat 64 (NN s₀' - 1) := by rw [hq.NN]
  have e15 : BitVec.ofNat 64 (NN s₀ - i) = BitVec.ofNat 64 (NN s₀' - i) := by rw [hq.NN]
  -- The registers `KR` fixes, in step 3's iteration `i`.
  let K (t₀ t : State) : Prop :=
    KR t₀ (BitVec.ofNat 64 (NN t₀ - 1)) (BitVec.ofNat 64 (NN t₀ - i)) t
  have jb : RelCT isa (fun s s' => (Inv3 s₀ i s ∧ jOf s₀ s.mem = j) ∧
        (Inv3 s₀' i s' ∧ jOf s₀' s'.mem = j)) (.block jBlock) fun s s' =>
        (K s₀ s ∧ s.gpr .x9 = BitVec.ofNat 64 j) ∧ (K s₀' s' ∧ s'.gpr .x9 = BitVec.ofNat 64 j) :=
    ((RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.1.kr h.2.1.kr e1 e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨j_wp hp h.1.1.kr h.1.2, j_wp hp' h.2.1.kr h.2.2⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have mx : RelCT isa (fun s s' => (K s₀ s ∧ s.gpr .x9 = BitVec.ofNat 64 j) ∧
        (K s₀' s' ∧ s'.gpr .x9 = BitVec.ofNat 64 j))
      (.seq (.block [.madd .x .x10 .x9 .x22 .x20, mov .x9 .x19, .addImm .x .x11 .x21 192,
        .lsr .x .x12 .x22 3]) xorLoop) fun s s' => K s₀ s ∧ K s₀' s' :=
    RelCT.keepK (RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs ([.x9] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.1 h.2.1 e1 e15 fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]) (by taint_decide))
      (by decide +kernel) fun _ _ h => ⟨h.1.1, h.2.1⟩
  have x : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block ([.addImm .x .x0 .x21 192] ++ bmTail)) fun s s' =>
        (K s₀ s ∧ Args s₀ (tP s₀) s) ∧ (K s₀' s' ∧ Args s₀' (tP s₀') s') :=
    ((RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨x3_wp hp h.1, x3_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cl := call_rel hp hp' hq (srcOK_t hp) (srcOK_t hp') hq.tP
    (bp := BitVec.ofNat 64 (NN s₀ - 1)) (q := BitVec.ofNat 64 (NN s₀ - i))
    (bp' := BitVec.ofNat 64 (NN s₀' - 1)) (q' := BitVec.ofNat 64 (NN s₀' - i))
  have e : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s') (.block [.subImm .x .x23 .x23 1])
      fun _ _ => True :=
    RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)
  have body := jb.seq (RelCT.assoc (mx.seq ((x.seq cl).seq e)))
  rw [← blockMixTo_eq] at body
  exact (body.wp fun _ _ h => ⟨step3_ok blockMixSpec hp hi h.1.1,
    step3_ok blockMixSpec hp' hi' h.2.1⟩).mono (fun _ _ h => h) fun _ _ h => h.2

variable (hL : Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀) =
  Spec.Scrypt.roMixIndices (rr s₀') (NN s₀') (B s₀'))
include hL

theorem body3_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv3 s₀ i s ∧ Inv3 s₀' i s') (step3 Impl.Scrypt.AArch64.blockMix)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ (s.gpr .x23 != 0) = decide (i + 1 ≠ NN s₀)) ∧
        (Inv3 s₀' (i + 1) s' ∧ (s'.gpr .x23 != 0) = decide (i + 1 ≠ NN s₀')) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  refine (RelCT.exists' fun (j : Nat) => body3_rel_j hp hp' hq hi j).mono
    (fun s s' ⟨h, h'⟩ => ?_) fun _ _ h => h
  obtain ⟨r, hr⟩ := drop_js hi h
  obtain ⟨r', hr'⟩ := drop_js hi' h'
  rw [← hL, hr] at hr'
  have e := (List.cons.inj hr').1
  exact ⟨jOf s₀ s.mem, ⟨h, rfl⟩, ⟨h', e.symm⟩⟩

theorem loop3_rel :
    RelCT isa (fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s')
      (.loop (step3 Impl.Scrypt.AArch64.blockMix) (.nonzero .x .x23))
      fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step3 Impl.Scrypt.AArch64.blockMix)
    (c := .nonzero .x .x23) (Q := fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv3 s₀ i s ∧ Inv3 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body3_rel hp hp' hq hL hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_x23, eval_x23, z, z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

theorem roMix_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') Impl.Scrypt.AArch64.roMix fun _ _ => True := by
  show RelCT isa _ (roMixWith Impl.Scrypt.AArch64.blockMix) _
  unfold roMixWith
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block rmPrologue)
      fun s s' => P1 s₀ s ∧ P1 s₀' s' :=
    ((RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => by
        rw [e, e']
        refine agree_of hq.sp fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.x0
        · exact hq.x1
        · exact hq.x2
        · exact hq.x3
        · exact hq.x4) (c := .block rmPrologue) (by taint_decide)).wp
      (F₁ := P1 s₀) (F₂ := P1 s₀') fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have nl : RelCT isa (fun s s' => P1 s₀ s ∧ P1 s₀' s') nLoop fun s s' => N1 s₀ s ∧ N1 s₀' s' :=
    ((RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs [.x9, .x10, .x11])
      (fun _ _ ⟨h, h'⟩ => agree_of (by rw [h.sp, h'.sp, hq.sp]) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.x9, h'.x9, hq.rr]
        · rw [h.x10, h'.x10]
        · rw [h.x11, h'.x11, RoMix.vl, RoMix.vl, hq.x3]) (c := nLoop) (by taint_decide)).wp
      fun _ _ h => ⟨nloop_ok hp h.1, nloop_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have st : RelCT isa (fun s s' => N1 s₀ s ∧ N1 s₀' s') (.block rmSetup)
      fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs [.x10, .x20, .x21])
      (fun _ _ ⟨h, h'⟩ => agree_of (by rw [h.sp, h'.sp, hq.sp]) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.x10, h'.x10, hq.NN]
        · rw [h.x20, h'.x20, vP, vP, hq.x2]
        · rw [h.x21, h'.x21, sc, sc, hq.x4]) (c := .block rmSetup) (by taint_decide)).wp
      fun _ _ h => ⟨setup2_ok hp h.1, setup2_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have md : RelCT isa (fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s') (.block rmMid)
      fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs [.x21])
      (fun _ _ ⟨h, h'⟩ => agree_of (by rw [h.sp, h'.sp, hq.sp]) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.x21, h'.x21, sc, sc, hq.x4]) (c := .block rmMid) (by taint_decide)).wp
      fun _ _ h => ⟨mid_ok hp h.1, mid_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have epi : RelCT isa (fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s') (.block rmEpilogue)
      fun _ _ => True :=
    RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs [.x21])
      (fun _ _ h => agree_of (by rw [h.1.sp, h.2.sp, hq.sp]) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.1.x21, h.2.x21, sc, sc, hq.x4]) (by taint_decide)
  exact pro.seq (nl.seq (st.seq ((loop2_rel hp hp' hq).seq
    (md.seq ((loop3_rel hp hp' hq hL).seq epi)))))

end

/-! ## Verified -/

theorem pubEq_of {s₁ s₂ : State} (h : Proof.Scrypt.roMixAArch64.pub s₁ s₂) : PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- No instruction of ROMix, or of the functions it calls, writes `x25`–`x29`. -/
theorem others_kept :
    (instrs Impl.Scrypt.AArch64.roMix).all
      (fun i => [Reg.x25, .x26, .x27, .x28, .x29].all fun r => dstOf i != some r) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem preserved_cases :
    ∀ r ∈ preserved, r ∈ rmSaved.map Prod.fst ∨ r ∈ [Reg.x25, .x26, .x27, .x28, .x29] := by
  decide

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1 | .x2 => 0x2000 | .x3 => 1 | .x4 => 0x3000 | .x5 => 3 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩, ⟨0x2000, 128⟩, ⟨0x3000, 384⟩]

theorem roMix_verified :
    Verified AArch64.target Impl.Scrypt.AArch64.roMix Proof.Scrypt.roMixAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, hk, hsp, hpost⟩ := correct blockMixSpec (pre_of hs)
    refine ⟨t, s', he, ⟨fun r hr => ?_, hsp⟩, hpost⟩
    rcases preserved_cases r hr with h | h
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
      exact hk p hp
    · have hc := others_kept
      rw [List.all_eq_true] at hc
      refine Exec.gpr (fun i hi => ?_) he (.inr (by revert h; revert r; decide))
      have := hc i hi
      simp only [List.all_eq_true, bne_iff_ne, ne_eq] at this
      exact this r h
  · intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
    exact (roMix_rel (pre_of h₁) (pre_of h₂) (pubEq_of hpub) hpub.2.2.2.2.2.2.2
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_, by decide, ?_, ?_, ?_, by decide, by decide, by decide,
      by decide, by decide, ⟨0, rfl⟩, rfl⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, satState] at h₁ h₂
      bv_omega

end VG.Proof.Scrypt.AArch64.RoMix
