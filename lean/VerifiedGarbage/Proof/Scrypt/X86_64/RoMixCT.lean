import VerifiedGarbage.Proof.Scrypt.X86_64.RoMixFun
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import Mathlib.Tactic.DefEqTransformations

/-!
# scryptROMix on x86-64: constant time, up to the indices `j`

Untrusted: everything here is checked by Lean.

As for scryptBlockMix (`BlockMixCT.lean`), we relate two runs (`RelCT`):
correctness determines our registers from the public arguments, so they
agree between the calls, where the taint analysis proves each block
constant time; the calls are constant time by scryptBlockMix's own proof.
In step 3, the address of `V[j]` and the branches of the multiplication
depend on `j`, which the contract declares public: the two runs compute the
same `j`, since both compute their indices in order (`Inv3.js`) and agree on
the whole list.
-/

namespace VG.Proof.Scrypt.X86_64.RoMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blockMix)
open VG.Proof.Sha1.X86_64.Stream (wp_mov wp_addi wp_add wp_subi)

/-! ## What each run knows -/

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.rr : rr s₀ = rr s₀' := by simp only [RoMix.rr, hq.rsi]
theorem PubEq.NN : NN s₀ = NN s₀' := by simp only [RoMix.NN, RoMix.vl, RoMix.rr, hq.rsi, hq.rcx]
theorem PubEq.vAt (i : Nat) : vAt s₀ i = vAt s₀' i := by
  simp only [RoMix.vAt, RoMix.vP, RoMix.rr, hq.rsi, hq.rdx]
theorem PubEq.tP : tP s₀ = tP s₀' := by simp only [RoMix.tP, RoMix.sc, hq.r8]

end

/-- The registers the loops keep, with `rbp = bp` and `r15 = q`. -/
structure KR (s₀ : State) (bp q : Addr) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bP s₀
  rbp : s.gpr .rbp = bp
  r12 : s.gpr .r12 = vP s₀
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)
  r15 : s.gpr .r15 = q

theorem KR.keep {s₀ : State} {bp q : Addr} {s s' : State} (h : KR s₀ bp q s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hk : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) :
    KR s₀ bp q s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hk _ (by simp [calleeSaved])).trans h.rsp,
    (hk _ (by simp [calleeSaved])).trans h.rbx, (hk _ (by simp [calleeSaved])).trans h.rbp,
    (hk _ (by simp [calleeSaved])).trans h.r12, (hk _ (by simp [calleeSaved])).trans h.r13,
    (hk _ (by simp [calleeSaved])).trans h.r14, (hk _ (by simp [calleeSaved])).trans h.r15⟩

/-- `KR` survives instructions that write none of its registers. -/
theorem KR.upd {s₀ : State} {bp q : Addr} {s s' : State} (h : KR s₀ bp q s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r) :
    KR s₀ bp q s' :=
  h.keep hrd hwr fun r hr => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := cs_ne hr
    exact hk r h1 h2 h3 h4 h5 h6

theorem Inv2.kr {s₀ : State} {i : Nat} {s : State} (h : Inv2 s₀ i s) :
    KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.rsp, h.rbx, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

theorem Inv3.kr {s₀ : State} {i : Nat} {s : State} (h : Inv3 s₀ i s) :
    KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) (BitVec.ofNat 64 (NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.rsp, h.rbx, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

/-- The registers `KR` fixes agree in two runs. -/
theorem KR.agree {s₀ s₀' : State} (hq : PubEq s₀ s₀') {bp q bp' q' : Addr} {s s' : State}
    (h : KR s₀ bp q s) (h' : KR s₀' bp' q' s') (hbp : bp = bp') (hq' : q = q') :
    ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, bP, bP, hq.rdi]
  · rw [h.rbp, h'.rbp, hbp]
  · rw [h.r12, h'.r12, vP, vP, hq.rdx]
  · rw [h.r13, h'.r13, sc, sc, hq.r8]
  · rw [h.r14, h'.r14, hq.rr]
  · rw [h.r15, h'.r15, hq']
  · rw [h.rsp, h'.rsp, hq.rsp]

/-- The arguments of a call of `vg_scrypt_blockmix` from `A` into `b`. -/
structure Args (s₀ : State) (A : Addr) (s : State) : Prop where
  rdi : s.gpr .rdi = A
  rsi : s.gpr .rsi = BitVec.ofNat 64 (rr s₀)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (rr s₀)
  rdx : s.gpr .rdx = bP s₀
  r8 : s.gpr .r8 = sc s₀

/-- A block that may be the source of such a call. -/
structure SrcOK (s₀ : State) (A : Addr) : Prop where
  b : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩
  w : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨sc s₀, 128⟩
  stk : (stkR s₀).Disjoint ⟨A, 128 * rr s₀⟩
  nw : A.toNat + 128 * rr s₀ ≤ 2 ^ 64
  inr : InRegions (s₀.rd ++ s₀.wr) A (128 * rr s₀)

theorem srcOK_v {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < NN s₀) : SrcOK s₀ (vAt s₀ i) :=
  ⟨(vAt_b hp hi).sub_right b_sub', (vAt_s hp hi).sub_right w_sub, (vAt_stk hp hi).symm,
    vAt_nw hp hi, BlockMix.InRegions.right (vAt_in hp hi)⟩

theorem srcOK_t {s₀ : State} (hp : Pre s₀) : SrcOK s₀ (tP s₀) :=
  ⟨t_b hp, t_w hp, hp.stk_s.sub_right (t_sub hp), t_nw hp, BlockMix.InRegions.right (t_in hp)⟩

/-! ## The call -/

theorem call_pre {s₀ : State} (hp : Pre s₀) {A : Addr} (hA : SrcOK s₀ A) {bp q : Addr} {s : State}
    (h : KR s₀ bp q s) (ha : Args s₀ A s) :
    Proof.Scrypt.blockMixX86_64.pre (s.callEntry.withRegions [⟨A, 128 * rr s₀⟩]
      [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩]) ∧
    Covers ([⟨A, 128 * rr s₀⟩] ++ [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩] s.wr := by
  have lt := r_lt hp
  exact bm_pre ha.rdi ha.rsi ha.rdx ha.rcx ha.r8 hp.pos lt
    ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hA.b hA.w
    (by rw [h.rsp]; exact hA.stk) (by rw [h.rsp]; exact hp.stk_b.sub_right (b_sub' (s₀ := s₀)))
    (by rw [h.rsp]; exact hp.stk_s.sub_right (w_sub (s₀ := s₀))) hA.nw (by have := hp.b_nw; omega)
    (by have := hp.s_nw; omega) (by rw [h.rd, h.wr]; exact hA.inr) (by rw [h.wr]; exact b_in hp)
    (by rw [h.wr]; exact w_in hp)

theorem call_wp {s₀ : State} (hp : Pre s₀) {A : Addr} (hA : SrcOK s₀ A) {bp q : Addr} {s : State}
    (h : KR s₀ bp q s) (ha : Args s₀ A s) :
    WP isa (.call "vg_scrypt_blockmix" Impl.Scrypt.X86_64.blockMix) s (KR s₀ bp q) := by
  have lt := r_lt hp
  exact blockMixSpec s A (bP s₀) (sc s₀) (rr s₀) ha.rdi ha.rsi ha.rdx ha.rcx ha.r8 hp.pos lt
    ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hA.b hA.w
    (by rw [h.rsp]; exact hA.stk) (by rw [h.rsp]; exact hp.stk_b.sub_right (b_sub' (s₀ := s₀)))
    (by rw [h.rsp]; exact hp.stk_s.sub_right (w_sub (s₀ := s₀))) hA.nw (by have := hp.b_nw; omega)
    (by have := hp.s_nw; omega) (by rw [h.rd, h.wr]; exact hA.inr) (by rw [h.wr]; exact b_in hp)
    (by rw [h.wr]; exact w_in hp) _ fun _ rd wr cs _ _ => h.keep rd wr cs

theorem call_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀') {A A' : Addr}
    (hA : SrcOK s₀ A) (hA' : SrcOK s₀' A') (hAA : A = A') {bp q bp' q' : Addr} :
    RelCT isa (fun s s' => (KR s₀ bp q s ∧ Args s₀ A s) ∧ (KR s₀' bp' q' s' ∧ Args s₀' A' s'))
      (.call "vg_scrypt_blockmix" Impl.Scrypt.X86_64.blockMix)
      fun s s' => KR s₀ bp q s ∧ KR s₀' bp' q' s' := by
  subst hAA
  have eb : bP s₀' = bP s₀ := hq.rdi.symm
  have es : sc s₀' = sc s₀ := hq.r8.symm
  have er : rr s₀' = rr s₀ := hq.rr.symm
  have call := RelCT.call (n := "vg_scrypt_blockmix") (P := fun s s' =>
      (KR s₀ bp q s ∧ Args s₀ A s) ∧ (KR s₀' bp' q' s' ∧ Args s₀' A s'))
    BlockMix.blockMix_verified.1 BlockMix.blockMix_verified.2.1 [⟨A, 128 * rr s₀⟩]
    [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩] fun s s' ⟨⟨h, ha⟩, ⟨h', ha'⟩⟩ => by
      obtain ⟨p₁, c₁, w₁⟩ := call_pre hp hA h ha
      obtain ⟨p₂, c₂, w₂⟩ := call_pre hp' hA' h' ha'
      rw [eb, es, er] at p₂ c₂ w₂
      refine ⟨p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [h.rsp, h'.rsp, hq.rsp]⟩
      simp only [Proof.Scrypt.blockMixX86_64, State.withRegions_gpr, State.callEntry_rsp,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), ha.rdi, ha.rsi, ha.rdx, ha.rcx, ha.r8,
        ha'.rdi, ha'.rsi, ha'.rdx, ha'.rcx, ha'.r8, eb, es, er, h.rsp, h'.rsp, hq.rsp]
      exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  exact (call.wp fun s s' h => ⟨call_wp hp hA h.1.1 h.1.2, call_wp hp' hA' h.2.1 h.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## What each piece does to the registers -/

/-- The registers `KR` fixes. -/
abbrev kRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]

theorem agree_K {s₀ s₀' : State} (hq : PubEq s₀ s₀') {bp q bp' q' : Addr} {s s' : State}
    (h : KR s₀ bp q s) (h' : KR s₀' bp' q' s') (hbp : bp = bp') (hq' : q = q') {extra : List Reg}
    (hx : ∀ r ∈ extra, s.gpr r = s'.gpr r) :
    X86_64.Taint.Agree (Taint.ofRegs (extra ++ kRegs)) s s' :=
  Taint.agree_ofRegs fun r hr => (List.mem_append.mp hr).elim (hx r) (KR.agree hq h h' hbp hq' r)

theorem a2_wp {s₀ : State} (hp : Pre s₀) {bp q : Addr} {s : State} (h : KR s₀ bp q s) :
    WP isa (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rcx (.reg .r14),
      .shift .shr .rcx 3]) s fun s' => KR s₀ bp q s' ∧ s'.gpr .rdi = bP s₀ ∧ s'.gpr .rsi = bp ∧
        s'.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀) := by
  have lt := r_lt hp
  refine wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun d ud _ _ =>
    wp_shr (by decide) (by decide) fun e ue _ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · exact h.upd (by rw [ue.rd, ud.rd, ub.rd, ua.rd]) (by rw [ue.wr, ud.wr, ub.wr, ua.wr])
      fun r _ h2 h3 h4 _ _ => by rw [ue.other _ h4, ud.other _ h4, ub.other _ h3, ua.other _ h2]
  · rw [ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide), ua.gpr, h.rbx]
  · rw [ue.other _ (by decide), ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h.rbp]
  · rw [ue.gpr, ud.gpr, ub.other _ (by decide), ua.other _ (by decide), h.r14, shr_ofNat _ lt]
    congr 1; omega

theorem copy_wp {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < NN s₀) {q : Addr} {s : State}
    (h : KR s₀ (vAt s₀ i) q s) (hdi : s.gpr .rdi = bP s₀) (hsi : s.gpr .rsi = vAt s₀ i)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀)) :
    WP isa copyLoop s (KR s₀ (vAt s₀ i) q) := by
  have lt := r_lt hp
  have e8 : 8 * (16 * rr s₀) = 128 * rr s₀ := by omega
  refine WP.mono (copyLoop_ok (src := bP s₀) (dst := vAt s₀ i) (n := 16 * rr s₀)
    (by have := hp.pos; omega) (by omega) hdi hsi hcx
    (fun k hk => by rw [h.rd, h.wr]; exact b_word hp hk)
    (fun k hk => by rw [h.wr]; exact v_word hp hi hk)
    (by rw [e8]; exact (vAt_b hp hi).symm.sub_left b_sub')) fun t ⟨rd, wr, g, _⟩ =>
    h.upd rd wr fun r h1 h2 h3 h4 _ _ => g r h1 h2 h3 h4

theorem tail_wp {s₀ : State} (hp : Pre s₀) {bp q A : Addr} {s : State} (h : KR s₀ bp q s)
    (hA : s.gpr .rdi = A) :
    WP isa (.block bmTail) s fun s' => KR s₀ bp q s' ∧ Args s₀ A s' := by
  have lt := r_lt hp
  refine wp_mov fun a ua _ _ => wp_shr (by decide) (by decide) fun b ub _ =>
    wp_mov fun d ud _ _ => wp_mov fun e ue _ _ => wp_mov fun f uf _ _ => WP.block_nil ⟨?_, ?_⟩
  · exact h.upd (by rw [uf.rd, ue.rd, ud.rd, ub.rd, ua.rd]) (by rw [uf.wr, ue.wr, ud.wr, ub.wr, ua.wr])
      fun r _ _ h3 h4 h5 h6 => by
        rw [uf.other _ h6, ue.other _ h5, ud.other _ h4, ub.other _ h3, ua.other _ h3]
  have hsi : b.gpr .rsi = BitVec.ofNat 64 (rr s₀) := by
    rw [ub.gpr, ua.gpr, h.r14, shr_ofNat _ lt]; congr 1; omega
  exact ⟨by rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), hA],
    by rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), hsi],
    by rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, hsi],
    by rw [uf.other _ (by decide), ue.gpr, ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.rbx],
    by rw [uf.gpr, ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.r13]⟩

theorem x2_wp {s₀ : State} (hp : Pre s₀) {bp q : Addr} {s : State} (h : KR s₀ bp q s) :
    WP isa (.block ([.mov .rdi (.reg .rbp)] ++ bmTail)) s fun s' => KR s₀ bp q s' ∧ Args s₀ bp s' :=
  wp_mov fun a ua _ _ => tail_wp hp (h.upd ua.rd ua.wr fun r _ h2 _ _ _ _ => ua.other r h2)
    (by rw [ua.gpr, h.rbp])

theorem x3_wp {s₀ : State} (hp : Pre s₀) {bp q : Addr} {s : State} (h : KR s₀ bp q s) :
    WP isa (.block ([.mov .rdi (.reg .r13), .alu .add .rdi (.imm 192)] ++ bmTail)) s
      fun s' => KR s₀ bp q s' ∧ Args s₀ (tP s₀) s' :=
  wp_mov fun a ua _ _ => wp_addi fun b ub => tail_wp hp
    (h.upd (by rw [ub.rd, ua.rd]) (by rw [ub.wr, ua.wr]) fun r _ h2 _ _ _ _ => by
      rw [ub.other r h2, ua.other r h2])
    (by rw [ub.gpr, ua.gpr, h.r13, sx192])

/-! ## Step 2, in two runs -/

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body2_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv2 s₀ i s ∧ Inv2 s₀' i s') (step2 Impl.Scrypt.X86_64.blockMix)
      fun s s' => (Inv2 s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = NN s₀))) ∧
        (Inv2 s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀'))) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have ev : vAt s₀ i = vAt s₀' i := hq.vAt i
  have e15 : BitVec.ofNat 64 (NN s₀ - i) = BitVec.ofNat 64 (NN s₀' - i) := by rw [hq.NN]
  have a : RelCT isa (fun s s' => Inv2 s₀ i s ∧ Inv2 s₀' i s')
      (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rcx (.reg .r14),
        .shift .shr .rcx 3]) fun s s' =>
        (KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s ∧ s.gpr .rdi = bP s₀ ∧
          s.gpr .rsi = vAt s₀ i ∧ s.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀)) ∧
        (KR s₀' (vAt s₀' i) (BitVec.ofNat 64 (NN s₀' - i)) s' ∧ s'.gpr .rdi = bP s₀' ∧
          s'.gpr .rsi = vAt s₀' i ∧ s'.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀')) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.kr h.2.kr ev e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨a2_wp hp h.1.kr, a2_wp hp' h.2.kr⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have c : RelCT isa (fun s s' =>
        (KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s ∧ s.gpr .rdi = bP s₀ ∧
          s.gpr .rsi = vAt s₀ i ∧ s.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀)) ∧
        (KR s₀' (vAt s₀' i) (BitVec.ofNat 64 (NN s₀' - i)) s' ∧ s'.gpr .rdi = bP s₀' ∧
          s'.gpr .rsi = vAt s₀' i ∧ s'.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀')))
      copyLoop fun s s' => KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s ∧
        KR s₀' (vAt s₀' i) (BitVec.ofNat 64 (NN s₀' - i)) s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rdi, .rsi, .rcx] ++ kRegs))
      (fun _ _ ⟨⟨h, d, si, cx⟩, ⟨h', d', si', cx'⟩⟩ => agree_K hq h h' ev e15 fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [d, d', bP, bP, hq.rdi]
        · rw [si, si', ev]
        · rw [cx, cx', hq.rr]) (by taint_decide)).wp
      fun _ _ ⟨⟨h, d, si, cx⟩, ⟨h', d', si', cx'⟩⟩ =>
        ⟨copy_wp hp hi h d si cx, copy_wp hp' hi' h' d' si' cx'⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have x : RelCT isa (fun s s' => KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s ∧
        KR s₀' (vAt s₀' i) (BitVec.ofNat 64 (NN s₀' - i)) s')
      (.block ([.mov .rdi (.reg .rbp)] ++ bmTail)) fun s s' =>
        (KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s ∧ Args s₀ (vAt s₀ i) s) ∧
        (KR s₀' (vAt s₀' i) (BitVec.ofNat 64 (NN s₀' - i)) s' ∧ Args s₀' (vAt s₀' i) s') :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 ev e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨x2_wp hp h.1, x2_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cl := call_rel hp hp' hq (srcOK_v hp hi) (srcOK_v hp' hi') ev
    (bp := vAt s₀ i) (q := BitVec.ofNat 64 (NN s₀ - i)) (bp' := vAt s₀' i)
    (q' := BitVec.ofNat 64 (NN s₀' - i))
  have e : RelCT isa (fun s s' => KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s ∧
        KR s₀' (vAt s₀' i) (BitVec.ofNat 64 (NN s₀' - i)) s')
      (.block [.alu .add .rbp (.reg .r14), .alu .sub .r15 (.imm 1)]) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 ev e15 (by simp)) (by taint_decide)
  have body := a.seq (c.seq ((x.seq cl).seq e))
  rw [← blockMixTo_eq] at body
  exact (body.wp fun _ _ h => ⟨step2_ok blockMixSpec hp hi h.1, step2_ok blockMixSpec hp' hi' h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem loop2_rel :
    RelCT isa (fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s') (.loop (step2 Impl.Scrypt.X86_64.blockMix) .ne)
      fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step2 Impl.Scrypt.X86_64.blockMix) (c := .ne)
    (Q := fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv2 s₀ i s ∧ Inv2 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body2_rel hp hp' hq hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      have ev : ∀ x : State, isa.eval .ne x = x.zf.map (!·) := fun _ => rfl
      beta_reduce
      rw [ev, ev, z, z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

end

/-! ## Step 3: what each piece does to the registers -/

theorem j_wp {s₀ : State} (hp : Pre s₀) {q : Addr} {s : State}
    (h : KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) q s) {j : Nat} (hj : jOf s₀ s.mem = j) :
    WP isa (.block jBlock) s fun s' =>
      KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) q s' ∧ s'.gpr .rax = BitVec.ofNat 64 j := by
  have lt := r_lt hp
  have := hp.pos
  unfold jBlock
  refine Proof.Sha1.X86_64.Stream.wp_movm (a := bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64))
    (ea_j hp s h.rbx h.r14)
    (by rw [h.rd, h.wr, hp.rd, hp.wr]
        exact BlockMix.InRegions.of_mem (R := bR s₀) (by simp)
          (BlockMix.contains_off (by omega) (by omega)))
    fun a ua => wp_and fun b ub => WP.block_nil ⟨?_, ?_⟩
  · exact h.upd (by rw [ub.rd, ua.rd]) (by rw [ub.wr, ua.wr]) fun r h1 _ _ _ _ _ => by
      rw [ub.other _ h1, ua.other _ h1]
  · rw [ub.gpr, ua.gpr, ua.other .rbp (by decide), h.rbp, jOf_eq hp, hj]

theorem m1_wp {bp q : Addr} {s₀ : State} {s : State} (h : KR s₀ bp q s) {j : Nat}
    (hax : s.gpr .rax = BitVec.ofNat 64 j) :
    WP isa (.block [.mov .rdx (.reg .r12), .mov .rcx (.reg .r14)]) s fun s' =>
      KR s₀ bp q s' ∧ s'.gpr .rax = BitVec.ofNat 64 j ∧ s'.gpr .rdx = vP s₀ ∧
        s'.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀) :=
  wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => WP.block_nil
    ⟨h.upd (by rw [ub.rd, ua.rd]) (by rw [ub.wr, ua.wr]) fun r _ _ _ h4 h5 _ => by
      rw [ub.other _ h4, ua.other _ h5],
    by rw [ub.other _ (by decide), ua.other _ (by decide), hax],
    by rw [ub.other _ (by decide), ua.gpr, h.r12], by rw [ub.gpr, ua.other _ (by decide), h.r14]⟩

theorem mul_wp {bp q : Addr} {s₀ : State} {s : State} (h : KR s₀ bp q s) {j : Nat} (hj : j < 2 ^ 64)
    (hax : s.gpr .rax = BitVec.ofNat 64 j) (hdx : s.gpr .rdx = vP s₀)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀)) :
    WP isa mulLoop s fun s' => KR s₀ bp q s' ∧ s'.gpr .rdx = vAt s₀ j :=
  WP.mono (mulLoop_ok hj hax hdx hcx) fun _ ⟨rd, wr, _, g, dx⟩ =>
    ⟨h.upd rd wr fun r h1 _ _ h4 h5 _ => g r h1 h5 h4, by rw [dx, Nat.mul_comm]⟩

theorem m2_wp {bp q : Addr} {s₀ : State} {s : State} (h : KR s₀ bp q s) (hp : Pre s₀) {j : Nat}
    (hdx : s.gpr .rdx = vAt s₀ j) :
    WP isa (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rdx), .mov .r8 (.reg .r13),
      .alu .add .r8 (.imm 192), .mov .rcx (.reg .r14), .shift .shr .rcx 3]) s fun s' =>
      KR s₀ bp q s' ∧ s'.gpr .rdi = bP s₀ ∧ s'.gpr .rsi = vAt s₀ j ∧ s'.gpr .r8 = tP s₀ ∧
        s'.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀) := by
  have lt := r_lt hp
  refine wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun d ud _ _ => wp_addi fun e ue =>
    wp_mov fun f uf _ _ => wp_shr (by decide) (by decide) fun g ug _ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h.upd (by rw [ug.rd, uf.rd, ue.rd, ud.rd, ub.rd, ua.rd])
      (by rw [ug.wr, uf.wr, ue.wr, ud.wr, ub.wr, ua.wr]) fun r _ h2 h3 h4 _ h6 => by
        rw [ug.other _ h4, uf.other _ h4, ue.other _ h6, ud.other _ h6, ub.other _ h3, ua.other _ h2]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), ub.other _ (by decide), ua.gpr, h.rbx]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), ub.gpr, ua.other _ (by decide), hdx]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.gpr, ud.gpr, ub.other _ (by decide),
      ua.other _ (by decide), h.r13, sx192]
  · rw [ug.gpr, uf.gpr, ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.r14, shr_ofNat _ lt]
    congr 1; omega

theorem xor_wp {bp q : Addr} {s₀ : State} {s : State} (h : KR s₀ bp q s) (hp : Pre s₀) {j : Nat}
    (hj : j < NN s₀) (hdi : s.gpr .rdi = bP s₀) (hsi : s.gpr .rsi = vAt s₀ j)
    (hr8 : s.gpr .r8 = tP s₀) (hcx : s.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀)) :
    WP isa xorLoop s (KR s₀ bp q) := by
  have lt := r_lt hp
  have e8 : 8 * (16 * rr s₀) = 128 * rr s₀ := by omega
  refine WP.mono (xorLoop_ok (x := bP s₀) (y := vAt s₀ j) (d := tP s₀) (n := 16 * rr s₀)
    (by have := hp.pos; omega) (by omega) hdi hsi hr8 hcx
    (fun k hk => by rw [h.rd, h.wr]; exact b_word hp hk)
    (fun k hk => by rw [h.rd, h.wr]; exact BlockMix.InRegions.right (v_word hp hj hk))
    (fun k hk => by rw [h.wr]; exact t_word hp hk)
    (by rw [e8]; exact t_b hp) (by rw [e8]; exact (vAt_s hp hj).symm.sub_left (t_sub hp)))
    fun _ ⟨rd, wr, g, _⟩ => h.upd rd wr fun r h1 h2 h3 h4 _ h6 => g r h1 h2 h3 h6 h4

/-- The next index, from the ones still to come. -/
theorem drop_js {s₀ : State} {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s) :
    ∃ rest, (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop i = jOf s₀ s.mem :: rest := by
  have e : NN s₀ - i = NN s₀ - (i + 1) + 1 := by omega
  have hs := h.js
  rw [e, mixLoop_succ_snd] at hs
  exact ⟨_, hs.symm⟩

theorem RelCT.exists' {α : Type} {P : α → State → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ a, RelCT isa (P a) c Q) :
    RelCT isa (fun s s' => ∃ a, P a s s') c Q :=
  fun _ _ _ _ _ _ ⟨a, hp⟩ e e' => h a _ _ _ _ _ _ hp e e'

/-! ## Step 3, in two runs -/

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body3_rel_j {i : Nat} (hi : i < NN s₀) (j : Nat) (hj : j < NN s₀) :
    RelCT isa (fun s s' => (Inv3 s₀ i s ∧ jOf s₀ s.mem = j) ∧ (Inv3 s₀' i s' ∧ jOf s₀' s'.mem = j))
      (step3 Impl.Scrypt.X86_64.blockMix)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = NN s₀))) ∧
        (Inv3 s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀'))) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have hj' : j < NN s₀' := hq.NN ▸ hj
  have vlt := v_lt hp
  have hjl : j < 2 ^ 64 := by
    have : NN s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_left _ (by have := hp.pos; omega)
    omega
  have e1 : BitVec.ofNat 64 (NN s₀ - 1) = BitVec.ofNat 64 (NN s₀' - 1) := by rw [hq.NN]
  have e15 : BitVec.ofNat 64 (NN s₀ - i) = BitVec.ofNat 64 (NN s₀' - i) := by rw [hq.NN]
  -- The registers `KR` fixes, in step 3's iteration `i`.
  let K (t₀ t : State) : Prop := KR t₀ (BitVec.ofNat 64 (NN t₀ - 1)) (BitVec.ofNat 64 (NN t₀ - i)) t
  have jb : RelCT isa (fun s s' => (Inv3 s₀ i s ∧ jOf s₀ s.mem = j) ∧
        (Inv3 s₀' i s' ∧ jOf s₀' s'.mem = j)) (.block jBlock) fun s s' =>
        (K s₀ s ∧ s.gpr .rax = BitVec.ofNat 64 j) ∧ (K s₀' s' ∧ s'.gpr .rax = BitVec.ofNat 64 j) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.1.kr h.2.1.kr e1 e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨j_wp hp h.1.1.kr h.1.2, j_wp hp' h.2.1.kr h.2.2⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have m1 : RelCT isa (fun s s' => (K s₀ s ∧ s.gpr .rax = BitVec.ofNat 64 j) ∧
        (K s₀' s' ∧ s'.gpr .rax = BitVec.ofNat 64 j))
      (.block [.mov .rdx (.reg .r12), .mov .rcx (.reg .r14)]) fun s s' =>
        (K s₀ s ∧ s.gpr .rax = BitVec.ofNat 64 j ∧ s.gpr .rdx = vP s₀ ∧
          s.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀)) ∧
        (K s₀' s' ∧ s'.gpr .rax = BitVec.ofNat 64 j ∧ s'.gpr .rdx = vP s₀' ∧
          s'.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀')) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rax] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.1 h.2.1 e1 e15 fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]) (by taint_decide)).wp
      fun _ _ h => ⟨m1_wp h.1.1 h.1.2, m1_wp h.2.1 h.2.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have ml : RelCT isa (fun s s' =>
        (K s₀ s ∧ s.gpr .rax = BitVec.ofNat 64 j ∧ s.gpr .rdx = vP s₀ ∧
          s.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀)) ∧
        (K s₀' s' ∧ s'.gpr .rax = BitVec.ofNat 64 j ∧ s'.gpr .rdx = vP s₀' ∧
          s'.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀')))
      mulLoop fun s s' => (K s₀ s ∧ s.gpr .rdx = vAt s₀ j) ∧ (K s₀' s' ∧ s'.gpr .rdx = vAt s₀' j) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rax, .rdx, .rcx] ++ kRegs))
      (fun _ _ ⟨⟨h, ax, dx, cx⟩, ⟨h', ax', dx', cx'⟩⟩ => agree_K hq h h' e1 e15 fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [ax, ax']
        · rw [dx, dx', vP, vP, hq.rdx]
        · rw [cx, cx', hq.rr]) (by taint_decide)).wp
      fun _ _ ⟨⟨h, ax, dx, cx⟩, ⟨h', ax', dx', cx'⟩⟩ =>
        ⟨mul_wp h hjl ax dx cx, mul_wp h' hjl ax' dx' cx'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have m2 : RelCT isa (fun s s' => (K s₀ s ∧ s.gpr .rdx = vAt s₀ j) ∧ (K s₀' s' ∧ s'.gpr .rdx = vAt s₀' j))
      (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rdx), .mov .r8 (.reg .r13),
        .alu .add .r8 (.imm 192), .mov .rcx (.reg .r14), .shift .shr .rcx 3]) fun s s' =>
        (K s₀ s ∧ s.gpr .rdi = bP s₀ ∧ s.gpr .rsi = vAt s₀ j ∧ s.gpr .r8 = tP s₀ ∧
          s.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀)) ∧
        (K s₀' s' ∧ s'.gpr .rdi = bP s₀' ∧ s'.gpr .rsi = vAt s₀' j ∧ s'.gpr .r8 = tP s₀' ∧
          s'.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀')) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rdx] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.1 h.2.1 e1 e15 fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2, hq.vAt])
      (by taint_decide)).wp
      fun _ _ h => ⟨m2_wp h.1.1 hp h.1.2, m2_wp h.2.1 hp' h.2.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have xl : RelCT isa (fun s s' =>
        (K s₀ s ∧ s.gpr .rdi = bP s₀ ∧ s.gpr .rsi = vAt s₀ j ∧ s.gpr .r8 = tP s₀ ∧
          s.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀)) ∧
        (K s₀' s' ∧ s'.gpr .rdi = bP s₀' ∧ s'.gpr .rsi = vAt s₀' j ∧ s'.gpr .r8 = tP s₀' ∧
          s'.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀')))
      xorLoop fun s s' => K s₀ s ∧ K s₀' s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rdi, .rsi, .r8, .rcx] ++ kRegs))
      (fun _ _ ⟨⟨h, di, si, r8, cx⟩, ⟨h', di', si', r8', cx'⟩⟩ => agree_K hq h h' e1 e15
        fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [di, di', bP, bP, hq.rdi]
          · rw [si, si', hq.vAt]
          · rw [r8, r8', hq.tP]
          · rw [cx, cx', hq.rr]) (by taint_decide)).wp
      fun _ _ ⟨⟨h, di, si, r8, cx⟩, ⟨h', di', si', r8', cx'⟩⟩ =>
        ⟨xor_wp h hp hj di si r8 cx, xor_wp h' hp' hj' di' si' r8' cx'⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have x : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block ([.mov .rdi (.reg .r13), .alu .add .rdi (.imm 192)] ++ bmTail)) fun s s' =>
        (K s₀ s ∧ Args s₀ (tP s₀) s) ∧ (K s₀' s' ∧ Args s₀' (tP s₀') s') :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨x3_wp hp h.1, x3_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cl := call_rel hp hp' hq (srcOK_t hp) (srcOK_t hp') hq.tP
    (bp := BitVec.ofNat 64 (NN s₀ - 1)) (q := BitVec.ofNat 64 (NN s₀ - i))
    (bp' := BitVec.ofNat 64 (NN s₀' - 1)) (q' := BitVec.ofNat 64 (NN s₀' - i))
  have e : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s') (.block [.alu .sub .r15 (.imm 1)])
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)
  have body := jb.seq (m1.seq (ml.seq (m2.seq (xl.seq ((x.seq cl).seq e)))))
  rw [← blockMixTo_eq] at body
  exact (body.wp fun _ _ h => ⟨step3_ok blockMixSpec hp hi h.1.1,
    step3_ok blockMixSpec hp' hi' h.2.1⟩).mono (fun _ _ h => h) fun _ _ h => h.2

variable (hL : Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀) =
  Spec.Scrypt.roMixIndices (rr s₀') (NN s₀') (B s₀'))
include hL

theorem body3_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv3 s₀ i s ∧ Inv3 s₀' i s') (step3 Impl.Scrypt.X86_64.blockMix)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = NN s₀))) ∧
        (Inv3 s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀'))) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  refine (RelCT.exists' fun (j : Fin (NN s₀)) => body3_rel_j hp hp' hq hi j.1 j.2).mono
    (fun s s' ⟨h, h'⟩ => ?_) fun _ _ h => h
  obtain ⟨r, hr⟩ := drop_js hi h
  obtain ⟨r', hr'⟩ := drop_js hi' h'
  rw [← hL, hr] at hr'
  have e := (List.cons.inj hr').1
  exact ⟨⟨jOf s₀ s.mem, jOf_lt hp s.mem⟩, ⟨h, rfl⟩, ⟨h', e.symm⟩⟩

theorem loop3_rel :
    RelCT isa (fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s') (.loop (step3 Impl.Scrypt.X86_64.blockMix) .ne)
      fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step3 Impl.Scrypt.X86_64.blockMix) (c := .ne)
    (Q := fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv3 s₀ i s ∧ Inv3 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body3_rel hp hp' hq hL hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      have ev : ∀ x : State, isa.eval .ne x = x.zf.map (!·) := fun _ => rfl
      beta_reduce
      rw [ev, ev, z, z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

theorem roMix_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') Impl.Scrypt.X86_64.roMix fun _ _ => True := by
  show RelCT isa _ (roMixWith Impl.Scrypt.X86_64.blockMix) _
  unfold roMixWith
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block rmPrologue)
      fun s s' => P1 s₀ s ∧ P1 s₀' s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) (c := .block rmPrologue) (by taint_decide)).wp
      (F₁ := P1 s₀) (F₂ := P1 s₀') fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have nl : RelCT isa (fun s s' => P1 s₀ s ∧ P1 s₀' s') nLoop fun s s' => N1 s₀ s ∧ N1 s₀' s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rax, .rdx, .rcx])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.rax, h'.rax, hq.rr]
        · rw [h.rdx, h'.rdx]
        · rw [h.rcx, h'.rcx, RoMix.vl, RoMix.vl, hq.rcx]) (c := nLoop) (by taint_decide)).wp
      fun _ _ h => ⟨nloop_ok hp h.1, nloop_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have st : RelCT isa (fun s s' => N1 s₀ s ∧ N1 s₀' s') (.block rmSetup)
      fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdx, .r12, .r13])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.rdx, h'.rdx, hq.NN]
        · rw [h.r12, h'.r12, vP, vP, hq.rdx]
        · rw [h.r13, h'.r13, sc, sc, hq.r8]) (c := .block rmSetup) (by taint_decide)).wp
      fun _ _ h => ⟨setup2_ok hp h.1, setup2_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have md : RelCT isa (fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s') (.block rmMid)
      fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.r13])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.r13, h'.r13, sc, sc, hq.r8]) (c := .block rmMid) (by taint_decide)).wp
      fun _ _ h => ⟨mid_ok hp h.1, mid_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have epi : RelCT isa (fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s') (.block rmEpilogue)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r13]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.r13, h.2.r13, sc, sc, hq.r8]) (by taint_decide)
  exact pro.seq (nl.seq (st.seq ((loop2_rel hp hp' hq).seq
    (md.seq ((loop3_rel hp hp' hq hL).seq epi)))))

end

/-! ## Verified -/

theorem pubEq_of {s₁ s₂ : State} (h : Proof.Scrypt.roMixX86_64.pub s₁ s₂) : PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 0x2000 | .rcx => 1 | .r8 => 0x3000 | .r9 => 3
    | .rsp => 0x5000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩, ⟨0x2000, 128⟩, ⟨0x3000, 384⟩]

theorem roMix_verified :
    Verified X86_64.target Impl.Scrypt.X86_64.roMix Proof.Scrypt.roMixX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct blockMixSpec (pre_of hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
    exact (roMix_rel (pre_of h₁) (pre_of h₂) (pubEq_of hpub) hpub.2.2.2.2.2.2.2
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide,
      ⟨0, rfl⟩, rfl⟩
    all_goals first
      | (intro a h₁ h₂; simp only [Region.Contains, satState] at h₁ h₂; bv_omega)
      | decide

end VG.Proof.Scrypt.X86_64.RoMix
