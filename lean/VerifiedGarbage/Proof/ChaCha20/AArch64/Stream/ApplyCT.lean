import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.Apply
import VerifiedGarbage.Proof.Framework.AArch64.RelCT

/-!
# Streaming ChaCha20 on AArch64: `apply`, constant time

Untrusted: everything here is checked by Lean. Two runs from states that
agree on the pointers, the length, the stack pointer and the number of bytes
of keystream left (which the contract lets `apply` leak) are related piece by
piece (`RelCT`): the taint analysis proves each piece without calls constant
time from the registers that hold public values (`taintRegs`), which
correctness determines in each run (`Apply.lean`) from those public values;
the calls of the block function and of the implementation `v` of
`vg_chacha20_xor` are constant time by their own proofs (`RelCT.call`), their
arguments agreeing; and the branches are on public values (`RelCT.ite`).
-/

namespace VG.Proof.ChaCha20.AArch64.Stream

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Stream
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (wp_addImm wp_mov eval_zero ofNat_beq_zero)

/-- Code the taint analysis proves constant time from the registers `rs`
(and the stack pointer). -/
theorem taintRegs {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun x y hp => ⟨(hr x y hp).1, fun r h' => (hr x y hp).2 r (Taint.mem_ofRegs.mp h')⟩) h

/-- What each run satisfies by correctness holds of the final states. -/
theorem RelCT.post {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x F₁ ∧ WP isa c y F₂) :
    RelCT isa P c fun x y => F₁ x ∧ F₂ y :=
  RelCT.mono (RelCT.wp h hw) (fun _ _ h => h) fun _ _ h => h.2

/-- `F` of the entry state `a`, with the stack pointer of `a`. -/
abbrev Sp (F : State → State → Prop) (a x : State) : Prop := F a x ∧ x.sp = a.sp

/-- Code keeps the stack pointer. -/
theorem wp_sp {c : Prog isa} {s a : State} {F : State → State → Prop} (h : WP isa c s (F a))
    (hs : s.sp = a.sp) : WP isa c s (Sp F a) := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, (Exec.sp he).trans hs⟩

/-- Two entry states that agree on what is public. -/
structure Two (a b : State) : Prop where
  pa : APre a
  pb : APre b
  hst : st a = st b
  hdp : dp a = dp b
  hx2 : a.gpr .x2 = b.gpr .x2
  hsp : a.sp = b.sp
  hleft : N a = N b

theorem Two.eqL {a b : State} (h : Two a b) : L a = L b := by
  show (a.gpr .x2).toNat = (b.gpr .x2).toNat; rw [h.hx2]
theorem Two.eqO {a b : State} (h : Two a b) : O a = O b := by
  show N a % 64 = N b % 64; rw [h.hleft]
theorem Two.eqH {a b : State} (h : Two a b) : H a = H b := by
  show min (N a % 64) (L a) = min (N b % 64) (L b); rw [h.hleft, h.eqL]
theorem Two.eqNB {a b : State} (h : Two a b) : NB a = NB b := by
  show (L a - H a) / 64 = (L b - H b) / 64; rw [h.eqH, h.eqL]
theorem Two.eqT {a b : State} (h : Two a b) : T a = T b := by
  show (L a - H a) % 64 = (L b - H b) % 64; rw [h.eqH, h.eqL]

/-! ## The call of `vg_chacha20_xor` -/

/-- The arguments of the call of `vg_chacha20_xor`. -/
structure Args (s₀ s : State) : Prop where
  x0 : s.gpr .x0 = st s₀ + BitVec.ofNat 64 192
  x1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 (H s₀)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (64 * NB s₀)
  x3 : s.gpr .x3 = st s₀ + BitVec.ofNat 64 256
  rd : s.rd = []
  wr : s.wr = [stR s₀, dR s₀]

theorem args_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s) :
    WP isa (.block blocksArgs) s (Args s₀) :=
  WP.mono (args_exec h.x21 (h.w hp) (by rw [h.rd, hp.rd])) fun _ ⟨_, x0₁, x1₁, x3₁, x2₁, _, _, _, _, rd₁, wr₁⟩ =>
    ⟨x0₁, by rw [x1₁, h.x22], by rw [x2₁, h.x2], x3₁, by rw [rd₁, h.rd, hp.rd], by rw [wr₁, h.wr, hp.wr]⟩

theorem Args.covers {s₀ s : State} (h : Args s₀ s) :
    Covers ([] ++ [cpR s₀, blR s₀, wkR s₀]) (s.rd ++ s.wr) ∧ Covers [cpR s₀, blR s₀, wkR s₀] s.wr := by
  have hcov : ∀ r ∈ [cpR s₀, blR s₀, wkR s₀], ∃ r' ∈ [stR s₀, dR s₀], ∃ o,
      r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 192, rfl, by simp⟩
    · exact ⟨dR s₀, by simp, H s₀, rfl, HNB_le s₀⟩
    · exact ⟨stR s₀, by simp, 256, rfl, by simp⟩
  exact ⟨by rw [h.rd, h.wr, List.nil_append, List.nil_append]; exact Covers.of_sub hcov,
    by rw [h.wr]; exact Covers.of_sub hcov⟩

theorem Args.pre {s₀ s : State} (hp : APre s₀) (h : Args s₀ s) :
    Proof.ChaCha20.xorAArch64.pre (s.callEntry.withRegions [] [cpR s₀, blR s₀, wkR s₀]) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHNB := HNB_le s₀
  have hwrap : (dp s₀ + BitVec.ofNat 64 (H s₀)).toNat + 64 * NB s₀ ≤ 2 ^ 64 := by
    have := hp.wrap_d
    rw [BitVec.toNat_add, Proof.ChaCha20.AArch64.toNat_ofNat_lt (by omega)]
    omega
  have hn : (BitVec.ofNat 64 (64 * NB s₀)).toNat = 64 * NB s₀ := Proof.ChaCha20.AArch64.toNat_ofNat_lt (by omega)
  simp only [Proof.ChaCha20.xorAArch64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.x2 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.x3 ∉ linkRegs), h.x0, h.x1, h.x2, h.x3, hn]
  exact ⟨trivial, trivial, (hp.st_d.sub_left (cpR_sub s₀)).sub_right (blR_sub s₀),
    Offset.disjoint _ (by omega) (by omega) (by omega),
    (hp.st_d.sub_left (wkR_sub s₀)).symm.sub_left (blR_sub s₀), hwrap⟩

/-! ## The call of the block function -/

/-- The arguments of the call of the block function, and the registers the
rest uses. -/
structure TArgs (s₀ s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x1 : s.gpr .x1 = st s₀ + BitVec.ofNat 64 64
  x21 : s.gpr .x21 = st s₀
  x22 : s.gpr .x22 = dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (T s₀)
  rd : s.rd = []
  wr : s.wr = [stR s₀, dR s₀]

theorem tailArgs_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q2 s₀ s) :
    WP isa (.block tailArgs) s (TArgs s₀) :=
  wp_mov fun s' u => wp_addImm (by decide) fun s'' u' => WP.block_nil
    ⟨by rw [u'.other _ (by decide), u.gpr, h.x21], by rw [u'.gpr, u.other _ (by decide), h.x21],
      by rw [u'.other _ (by decide), u.other _ (by decide), h.x21],
      by rw [u'.other _ (by decide), u.other _ (by decide), h.x22],
      by rw [u'.other _ (by decide), u.other _ (by decide), h.x23],
      by rw [u'.rd, u.rd, h.rd, hp.rd], by rw [u'.wr, u.wr, h.wr, hp.wr]⟩

/-- After the block function: the registers the rest uses. -/
structure TAfter (s₀ s : State) : Prop where
  x21 : s.gpr .x21 = st s₀
  x22 : s.gpr .x22 = dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (T s₀)

theorem TArgs.covers {s₀ s : State} (h : TArgs s₀ s) :
    Covers ([⟨st s₀, 64⟩] ++ [⟨st s₀ + BitVec.ofNat 64 64, 256⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨st s₀ + BitVec.ofNat 64 64, 256⟩] s.wr := by
  refine ⟨?_, ?_⟩
  · rw [h.rd, h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 768 by decide⟩
    · exact ⟨stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩
  · rw [h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩

theorem TArgs.pre {s₀ s : State} (h : TArgs s₀ s) :
    Proof.ChaCha20.blockAArch64.pre
      (s.callEntry.withRegions [⟨st s₀, 64⟩] [⟨st s₀ + BitVec.ofNat 64 64, 256⟩]) := by
  simp only [Proof.ChaCha20.blockAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs),
    h.x0, h.x1]
  exact ⟨trivial, trivial, Offset.disjoint_base _ (by omega) (by omega)⟩

theorem TArgs.call {s₀ s : State} (h : TArgs s₀ s) :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.AArch64.block) s (TAfter s₀) :=
  block_call h.x0 h.x1 (Offset.disjoint_base _ (by omega) (by omega)) h.covers.1 h.covers.2
    fun _ k _ => ⟨by rw [k.cs .x21 (by decide) (by decide), h.x21], by rw [k.cs .x22 (by decide) (by decide), h.x22],
      by rw [k.cs .x23 (by decide) (by decide), h.x23]⟩

/-! ## The pieces, related -/

section
variable {a b : State} (h : Two a b)
include h

theorem check_rel :
    RelCT isa (fun x y => x = a ∧ y = b) (.block check) fun x y => Sp Q0 a x ∧ Sp Q0 b y :=
  RelCT.post (taintRegs [.x0] (fun x y ⟨hx, hy⟩ => by
      subst hx hy
      refine ⟨h.hsp, fun r hr => ?_⟩
      simp only [List.mem_singleton] at hr; subst hr; exact h.hst) (by taint_decide))
    fun x y ⟨hx, hy⟩ => ⟨by subst hx; exact wp_sp (check_ok h.pa) rfl, by subst hy; exact wp_sp (check_ok h.pb) rfl⟩

theorem part1_rel (hle : L a ≤ N a) :
    RelCT isa (fun x y => Sp Q0 a x ∧ Sp Q0 b y) part1 fun x y => Sp Q1 a x ∧ Sp Q1 b y :=
  RelCT.post (taintRegs [.x0, .x1, .x2, .x10, .x12] (fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => by
      refine ⟨by rw [sx, sy, h.hsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hx.keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
          hy.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.hst
      · rw [hx.keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
          hy.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.hdp
      · rw [hx.keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
          hy.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.hx2
      · rw [hx.x10, hy.x10, h.eqO]
      · rw [hx.x12, hy.x12, h.eqO, h.eqL]) (by taint_decide))
    fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ⟨wp_sp (part1_ok h.pa hle hx) sx,
      wp_sp (part1_ok h.pb (by rw [← h.eqL, ← h.hleft]; exact hle) hy) sy⟩

theorem xor_rel (v : Proof.ChaCha20.AArch64.XorImpl) :
    RelCT isa (fun x y => Sp Args a x ∧ Sp Args b y) (.call v.callee.name v.callee.code) fun _ _ => True := by
  have ecp : cpR b = cpR a := by simp only [cpR, h.hst]
  have ebl : blR b = blR a := by simp only [blR, h.hdp, h.eqH, h.eqNB]
  have ewk : wkR b = wkR a := by simp only [wkR, h.hst]
  refine RelCT.call v.ok v.ct [] [cpR a, blR a, wkR a] fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ?_
  have py := hy.pre h.pb
  have cy := hy.covers
  rw [ecp, ebl, ewk] at py cy
  refine ⟨hx.pre h.pa, py, ?_, hx.covers.1, hx.covers.2, cy.1, cy.2⟩
  simp only [Proof.ChaCha20.xorAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' x (by decide : Reg.x0 ∉ linkRegs), callEntry_gpr' x (by decide : Reg.x1 ∉ linkRegs),
    callEntry_gpr' x (by decide : Reg.x2 ∉ linkRegs), callEntry_gpr' x (by decide : Reg.x3 ∉ linkRegs),
    callEntry_gpr' y (by decide : Reg.x0 ∉ linkRegs), callEntry_gpr' y (by decide : Reg.x1 ∉ linkRegs),
    callEntry_gpr' y (by decide : Reg.x2 ∉ linkRegs), callEntry_gpr' y (by decide : Reg.x3 ∉ linkRegs),
    hx.x0, hx.x1, hx.x2, hx.x3, hy.x0, hy.x1, hy.x2, hy.x3, h.hst, h.hdp, h.eqH, h.eqNB, sx, sy, h.hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem part2_rel (v : Proof.ChaCha20.AArch64.XorImpl) :
    RelCT isa (fun x y => Sp Q1 a x ∧ Sp Q1 b y) (part2 v.callee) fun x y => Sp Q2 a x ∧ Sp Q2 b y := by
  refine RelCT.post ?_ fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ⟨wp_sp (part2_ok v h.pa hx) sx, wp_sp (part2_ok v h.pb hy) sy⟩
  refine RelCT.ite (fun x y ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ => by
      have ex : isa.eval (.zero .x .x2) x = some (x.gpr .x2 == 0) := eval_zero x .x2
      have ey : isa.eval (.zero .x .x2) y = some (y.gpr .x2 == 0) := eval_zero y .x2
      rw [ex, ey, hx.x2, hy.x2, h.eqNB])
    (taintRegs [] (fun x y ⟨⟨⟨_, sx⟩, ⟨_, sy⟩⟩, _⟩ => ⟨by rw [sx, sy, h.hsp], fun r hr => by simp at hr⟩)
      (by taint_decide)) ?_
  refine RelCT.seq (R := fun x y => Sp Args a x ∧ Sp Args b y) ?_ (xor_rel h v)
  refine RelCT.post (taintRegs [.x21, .x22, .x2] (fun x y ⟨⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩, _⟩ => by
      refine ⟨by rw [sx, sy, h.hsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hx.x21, hy.x21, h.hst]
      · rw [hx.x22, hy.x22, h.hdp, h.eqH]
      · rw [hx.x2, hy.x2, h.eqNB]) (by taint_decide))
    fun x y ⟨⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩, _⟩ => ⟨wp_sp (args_ok h.pa hx) sx, wp_sp (args_ok h.pb hy) sy⟩

theorem part3_rel : RelCT isa (fun x y => Sp Q2 a x ∧ Sp Q2 b y) part3 fun x y => Sp Q3 a x ∧ Sp Q3 b y := by
  refine RelCT.post ?_ fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ⟨wp_sp (part3_ok h.pa hx) sx, wp_sp (part3_ok h.pb hy) sy⟩
  refine RelCT.ite (fun x y ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ => by
      have ex : isa.eval (.zero .x .x23) x = some (x.gpr .x23 == 0) := eval_zero x .x23
      have ey : isa.eval (.zero .x .x23) y = some (y.gpr .x23 == 0) := eval_zero y .x23
      rw [ex, ey, hx.x23, hy.x23, h.eqT])
    (taintRegs [] (fun x y ⟨⟨⟨_, sx⟩, ⟨_, sy⟩⟩, _⟩ => ⟨by rw [sx, sy, h.hsp], fun r hr => by simp at hr⟩)
      (by taint_decide)) ?_
  refine RelCT.seq (R := fun x y => Sp TArgs a x ∧ Sp TArgs b y)
    (RelCT.post (taintRegs [.x21] (fun x y ⟨⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩, _⟩ => by
        refine ⟨by rw [sx, sy, h.hsp], fun r hr => ?_⟩
        simp only [List.mem_singleton] at hr; subst hr; rw [hx.x21, hy.x21, h.hst]) (by taint_decide))
      fun x y ⟨⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩, _⟩ => ⟨wp_sp (tailArgs_ok h.pa hx) sx, wp_sp (tailArgs_ok h.pb hy) sy⟩) ?_
  refine RelCT.seq (R := fun x y => Sp TAfter a x ∧ Sp TAfter b y) ?_
    (taintRegs [.x21, .x22, .x23] (fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => by
      refine ⟨by rw [sx, sy, h.hsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hx.x21, hy.x21, h.hst]
      · rw [hx.x22, hy.x22, h.hdp, h.eqH, h.eqNB]
      · rw [hx.x23, hy.x23, h.eqT]) (by taint_decide))
  have est : st b = st a := h.hst.symm
  refine RelCT.post (RelCT.call Proof.ChaCha20.AArch64.block_correct Proof.ChaCha20.AArch64.block_ct
    [⟨st a, 64⟩] [⟨st a + BitVec.ofNat 64 64, 256⟩] fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ?_)
    fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ⟨wp_sp hx.call sx, wp_sp hy.call sy⟩
  have py := hy.pre
  have cy := hy.covers
  rw [est] at py cy
  refine ⟨hx.pre, py, ?_, hx.covers.1, hx.covers.2, cy.1, cy.2⟩
  simp only [Proof.ChaCha20.blockAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' x (by decide : Reg.x0 ∉ linkRegs), callEntry_gpr' x (by decide : Reg.x1 ∉ linkRegs),
    callEntry_gpr' y (by decide : Reg.x0 ∉ linkRegs), callEntry_gpr' y (by decide : Reg.x1 ∉ linkRegs),
    hx.x0, hx.x1, hy.x0, hy.x1, h.hst, sx, sy, h.hsp]
  exact ⟨trivial, trivial, trivial⟩

theorem apply_rel (v : Proof.ChaCha20.AArch64.XorImpl) :
    RelCT isa (fun x y => x = a ∧ y = b) (apply v.callee) fun _ _ => True := by
  rw [apply_eq]
  have e11 : ∀ {s₀ x : State}, Q0 s₀ x →
      isa.eval (.zero .x .x11) x = some (decide (N s₀ < L s₀)) := fun {s₀ x} hx => by
    have e : isa.eval (.zero .x .x11) x = some (x.gpr .x11 == 0) := eval_zero x .x11
    rw [e, hx.x11]; by_cases hh : L s₀ ≤ N s₀ <;> simp [hh] <;> omega
  refine RelCT.seq (check_rel h) (RelCT.ite (fun x y ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ => by
      rw [e11 hx, e11 hy, h.hleft, h.eqL])
    (taintRegs [] (fun x y ⟨⟨⟨_, sx⟩, ⟨_, sy⟩⟩, _⟩ => ⟨by rw [sx, sy, h.hsp], fun r hr => by simp at hr⟩)
      (by taint_decide)) ?_)
  by_cases hlt : N a < L a
  · refine RelCT.of_false fun x y hp => ?_
    have he := hp.2
    rw [e11 hp.1.1.1] at he
    simp [hlt] at he
  have hle : L a ≤ N a := by omega
  refine RelCT.seq (RelCT.mono (part1_rel h hle) (fun _ _ hp => hp.1) fun _ _ hq => hq)
    (RelCT.seq (part2_rel h v) (RelCT.seq (part3_rel h) ?_))
  exact taintRegs [.x21] (fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => by
    refine ⟨by rw [sx, sy, h.hsp], fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr; subst hr; rw [hx.x21, hy.x21, h.hst]) (by taint_decide)

end

theorem Two.of {a b : State} (ha : Proof.ChaCha20.applyAArch64.pre a) (hb : Proof.ChaCha20.applyAArch64.pre b)
    (hq : Proof.ChaCha20.applyAArch64.pub a b) : Two a b := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hq
  exact ⟨APre.of a ha, APre.of b hb, p1, p2, p3, p4, (List.cons.inj p5).1⟩

theorem apply_ct (v : Proof.ChaCha20.AArch64.XorImpl) :
    ConstantTime isa Proof.ChaCha20.applyAArch64.pre Proof.ChaCha20.applyAArch64.pub (apply v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (apply_rel (Two.of h₁ h₂ hq) v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem apply_keepsV (v : Proof.ChaCha20.AArch64.XorImpl) : (apply v.callee).allInstrs keepsV = true := by
  simp only [apply, part2, Code.allInstrs, v.keepsV, Bool.and_true, Bool.true_and]
  lit_decide

theorem apply_ok (v : Proof.ChaCha20.AArch64.XorImpl) (s : State) (hs : Proof.ChaCha20.applyAArch64.pre s) :
    ∃ t s', Exec isa (apply v.callee) s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.applyAArch64.post s s' := by
  obtain ⟨t, s', he, hf⟩ := apply_correct v (APre.of s hs)
  exact ⟨t, s', he, ⟨hf.1, Exec.sp he, Exec.preservedV he (apply_keepsV v)⟩, hf.2⟩

/-- A state satisfying the precondition of `apply` (with no data). -/
def applySat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 768⟩, ⟨0x2000, 0⟩]

theorem apply_verified (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (apply v.callee) (Spec.ChaCha20.applyContract AArch64.abi 0) :=
  Verified.of_correct (apply_ok v) (apply_ct v) (by
    sig_implies [Spec.ChaCha20.applyContract, Spec.ChaCha20.applySig, Proof.ChaCha20.applyAArch64,
      AArch64.abi, AArch64.argRegs] [applySat] using applySat)

end VG.Proof.ChaCha20.AArch64.Stream
