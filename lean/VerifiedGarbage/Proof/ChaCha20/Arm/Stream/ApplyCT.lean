import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.Apply

/-!
# Streaming ChaCha20 on ARMv7: `apply`, constant time

Untrusted: everything here is checked by Lean. Two runs from states that
agree on the pointers, the length and the number of bytes of keystream left
(which the contract lets `apply` leak) are related piece by piece (`RelCT`):
the taint analysis proves each piece without calls or branches on loaded
values constant time from the registers that hold public values
(`taintRegs`), which correctness determines in each run (`Apply.lean`) from
those public values; the calls of the block function and of
`vg_chacha20_xor` are constant time by their own proofs (`RelCT.call`), their
arguments agreeing; and the branches on Z after the check and in `start`,
`part2` and `part3` are on public values (`RelCT.ite`), as correctness shows.
-/

namespace VG.Proof.ChaCha20.Arm.Stream

open VG VG.Arm VG.Impl.ChaCha20.Arm.Stream
open VG.Proof.MdStream.Arm (op2_imm op2_reg wp_mov wp_add eval_eq)

/-- Code the taint analysis proves constant time from the registers `rs`. -/
theorem taintRegs {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun x y hp => Taint.agree_ofRegs (hr x y hp)) h

/-- What each run satisfies by correctness holds of the final states. -/
theorem RelCT.post {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x F₁ ∧ WP isa c y F₂) :
    RelCT isa P c fun x y => F₁ x ∧ F₂ y :=
  RelCT.mono (RelCT.wp h hw) (fun _ _ h => h) fun _ _ h => h.2

/-- Two entry states that agree on what is public. -/
structure Two (a b : State) : Prop where
  pa : APre a
  pb : APre b
  hst : ST a = ST b
  hdp : DP a = DP b
  hr2 : a.gpr .r2 = b.gpr .r2
  hleft : N a = N b

theorem Two.eqL {a b : State} (h : Two a b) : L a = L b := by
  show (a.gpr .r2).toNat = (b.gpr .r2).toNat; rw [h.hr2]
theorem Two.eqO {a b : State} (h : Two a b) : O a = O b := by
  show N a % 64 = N b % 64; rw [h.hleft]
theorem Two.eqH {a b : State} (h : Two a b) : H a = H b := by
  show min (N a % 64) (L a) = min (N b % 64) (L b); rw [h.hleft, h.eqL]
theorem Two.eqNB {a b : State} (h : Two a b) : NB a = NB b := by
  show (L a - H a) / 64 = (L b - H b) / 64; rw [h.eqH, h.eqL]
theorem Two.eqT {a b : State} (h : Two a b) : T a = T b := by
  show (L a - H a) % 64 = (L b - H b) % 64; rw [h.eqH, h.eqL]
theorem Two.eqst {a b : State} (h : Two a b) : st a = st b := by
  show State.addr (ST a) = State.addr (ST b); rw [h.hst]
theorem Two.eqdp {a b : State} (h : Two a b) : dp a = dp b := by
  show State.addr (DP a) = State.addr (DP b); rw [h.hdp]

/-- A branch on Z, which agrees in both runs. -/
theorem z_eq {x y : State} {p q : Bool} (hx : x.z = p) (hy : y.z = q) (hab : p = q) :
    isa.eval .eq x = isa.eval .eq y := by
  have ex : isa.eval .eq x = some x.z := eval_eq x
  have ey : isa.eval .eq y = some y.z := eval_eq y
  rw [ex, ey, hx, hy, hab]

/-! ## The call of `vg_chacha20_xor` -/

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

theorem Args.pre {s₀ s : State} (hp : APre s₀) (h : Args s₀ s) (hnb : 0 < NB s₀) :
    Proof.ChaCha20.xorArm.pre (s.callEntry.withRegions [] [cpR s₀, blR s₀, wkR s₀]) := by
  have hL := L_lt s₀
  have hHNB := HNB_le s₀
  have hst := hp.st_fit
  have hd := hp.d_fit
  have hn : (BitVec.ofNat 32 (64 * NB s₀)).toNat = 64 * NB s₀ := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [Proof.ChaCha20.xorArm, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs), h.r0, h.r1, h.r2, h.r3, hn,
    hp.eaS (d := 192) (by decide), hp.eaS (d := 256) (by decide), hp.eaD (d := H s₀) (by omega),
    hp.sNat (d := 192) (by decide), hp.sNat (d := 256) (by decide), hp.dNat (d := H s₀) (by omega)]
  exact ⟨trivial, trivial, (hp.st_d.sub_left (cpR_sub s₀)).sub_right (blR_sub s₀),
    Offset.disjoint _ (by omega) (by omega) (by omega),
    (hp.st_d.sub_left (wkR_sub s₀)).symm.sub_left (blR_sub s₀), by omega, by omega, by omega⟩

/-! ## The call of the block function -/

/-- The arguments of the call of the block function, and the registers the
rest uses. -/
structure TArgs (s₀ s : State) : Prop where
  r0 : s.gpr .r0 = ST s₀
  r1 : s.gpr .r1 = ST s₀ + BitVec.ofNat 32 64
  r4 : s.gpr .r4 = ST s₀
  r5 : s.gpr .r5 = DP s₀ + BitVec.ofNat 32 (H s₀ + 64 * NB s₀)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (T s₀)
  rd : s.rd = []
  wr : s.wr = [stR s₀, dR s₀]

theorem tailArgs_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q2 s₀ s) :
    WP isa (.block [.mov .r0 (.reg .r4), .dp .add .r1 .r4 (.imm 64)]) s (TArgs s₀) :=
  wp_mov (op2_reg _ _) fun s' u => wp_add (op2_imm (by decide)) fun s'' u' => WP.block_nil
    ⟨by rw [u'.other _ (by decide), u.gpr, h.r4], by rw [u'.gpr, u.other _ (by decide), h.r4]; rfl,
      by rw [u'.other _ (by decide), u.other _ (by decide), h.r4],
      by rw [u'.other _ (by decide), u.other _ (by decide), h.r5],
      by rw [u'.other _ (by decide), u.other _ (by decide), h.r6],
      by rw [u'.rd, u.rd, h.rd, hp.rd], by rw [u'.wr, u.wr, h.wr, hp.wr]⟩

/-- After the block function: the registers the rest uses. -/
structure TAfter (s₀ s : State) : Prop where
  r4 : s.gpr .r4 = ST s₀
  r5 : s.gpr .r5 = DP s₀ + BitVec.ofNat 32 (H s₀ + 64 * NB s₀)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (T s₀)

theorem TArgs.covers {s₀ s : State} (hp : APre s₀) (h : TArgs s₀ s) :
    Covers ([⟨st s₀, 64⟩] ++ [⟨State.addr (ST s₀ + BitVec.ofNat 32 64), 256⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨State.addr (ST s₀ + BitVec.ofNat 32 64), 256⟩] s.wr := by
  rw [hp.eaS (d := 64) (by decide)]
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

theorem TArgs.pre {s₀ s : State} (hp : APre s₀) (h : TArgs s₀ s) :
    Proof.ChaCha20.blockArm.pre
      (s.callEntry.withRegions [⟨st s₀, 64⟩] [⟨State.addr (ST s₀ + BitVec.ofNat 32 64), 256⟩]) := by
  have hst := hp.st_fit
  simp only [Proof.ChaCha20.blockArm, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs),
    h.r0, h.r1, hp.eaS (d := 64) (by decide), hp.sNat (d := 64) (by decide)]
  exact ⟨trivial, trivial, Offset.disjoint_base _ (by omega) (by omega), by omega, by omega⟩

theorem TArgs.call {s₀ s : State} (hp : APre s₀) (h : TArgs s₀ s) :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.Arm.block) s (TAfter s₀) := by
  have hst := hp.st_fit
  have c := h.covers hp
  exact block_call h.r0 h.r1 (by rw [hp.eaS (d := 64) (by decide)]; exact Offset.disjoint_base _ (by omega) (by omega))
    (by omega) (by rw [hp.sNat (d := 64) (by decide)]; omega) c.1 c.2
    fun _ k _ => ⟨by rw [k.cs .r4 (by decide) (by decide), h.r4], by rw [k.cs .r5 (by decide) (by decide), h.r5],
      by rw [k.cs .r6 (by decide) (by decide), h.r6]⟩

/-! ## The pieces, related -/

section
variable {a b : State} (h : Two a b)
include h

theorem check_rel :
    RelCT isa (fun x y => x = a ∧ y = b) (.block check) fun x y => Q0 a x ∧ Q0 b y :=
  RelCT.post (taintRegs [.r0] (fun x y ⟨hx, hy⟩ r hr => by
      subst hx hy
      simp only [List.mem_singleton] at hr; subst hr; exact h.hst) (by taint_decide))
    fun x y ⟨hx, hy⟩ => ⟨by subst hx; exact check_ok h.pa, by subst hy; exact check_ok h.pb⟩

theorem part1_rel (hle : L a ≤ N a) :
    RelCT isa (fun x y => Q0 a x ∧ Q0 b y) part1 fun x y => Q1 a x ∧ Q1 b y := by
  have hle' : L b ≤ N b := by rw [← h.eqL, ← h.hleft]; exact hle
  rw [part1_eq]
  refine RelCT.seq (R := fun (x y : State) => (R1 a (L a) x ∧ x.z = decide (O a < L a)) ∧
      (R1 b (L b) y ∧ y.z = decide (O b < L b)))
    (RelCT.post (taintRegs [.r0, .r1, .r2] (fun x y ⟨hx, hy⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [hx.keep _ (by decide) (by decide), hy.keep _ (by decide) (by decide)]; exact h.hst
        · rw [hx.keep _ (by decide) (by decide), hy.keep _ (by decide) (by decide)]; exact h.hdp
        · rw [hx.keep _ (by decide) (by decide), hy.keep _ (by decide) (by decide)]; exact h.hr2)
        (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨start_ok h.pa hle hx, start_ok h.pb hle' hy⟩) ?_
  refine RelCT.seq (R := fun x y => R1 a (H a) x ∧ R1 b (H b) y)
    (RelCT.post (RelCT.ite (fun x y ⟨⟨_, zx⟩, ⟨_, zy⟩⟩ => z_eq zx zy (by rw [h.eqO, h.eqL]))
        (taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide))
        (taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)))
      fun x y ⟨⟨hx, zx⟩, ⟨hy, zy⟩⟩ => ⟨sel_ok hx zx, sel_ok hy zy⟩) ?_
  refine RelCT.post (c := rest1) (taintRegs [.r4, .r5, .r6, .r2, .r12] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hx.r4, hy.r4, h.hst]
      · rw [hx.r5, hy.r5, h.hdp]
      · rw [hx.r6, hy.r6, h.eqL]
      · rw [hx.r2, hy.r2, h.eqH]
      · rw [hx.r12, hy.r12, h.eqO]) (by taint_decide))
    fun x y ⟨hx, hy⟩ => ⟨rest1_ok h.pa hx, rest1_ok h.pb hy⟩

theorem xor_rel :
    RelCT isa (fun x y => (Args a x ∧ 0 < NB a) ∧ Args b y)
      (.call "vg_chacha20_xor" Impl.ChaCha20.Arm.Xor.xor) fun _ _ => True := by
  have ecp : cpR b = cpR a := by simp only [cpR, h.eqst]
  have ebl : blR b = blR a := by simp only [blR, h.eqdp, h.eqH, h.eqNB]
  have ewk : wkR b = wkR a := by simp only [wkR, h.eqst]
  refine RelCT.call Proof.ChaCha20.Arm.Xor.xor_correct Proof.ChaCha20.Arm.Xor.xor_ct [] [cpR a, blR a, wkR a]
    fun x y ⟨⟨hx, hnb⟩, hy⟩ => ?_
  have py := hy.pre h.pb (by rw [← h.eqNB]; exact hnb)
  have cy := hy.covers
  rw [ecp, ebl, ewk] at py cy
  refine ⟨hx.pre h.pa hnb, py, ?_, hx.covers.1, hx.covers.2, cy.1, cy.2⟩
  simp only [Proof.ChaCha20.xorArm, State.withRegions_gpr,
    State.callEntry_gpr x (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr x (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr x (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr x (by decide : Reg.r3 ∉ linkRegs),
    State.callEntry_gpr y (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr y (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr y (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr y (by decide : Reg.r3 ∉ linkRegs),
    hx.r0, hx.r1, hx.r2, hx.r3, hy.r0, hy.r1, hy.r2, hy.r3, h.hst, h.hdp, h.eqH, h.eqNB]
  exact ⟨trivial, trivial, trivial, trivial⟩

theorem part2_rel :
    RelCT isa (fun x y => Q1 a x ∧ Q1 b y) part2 fun x y => Q2 a x ∧ Q2 b y := by
  refine RelCT.post ?_ fun x y ⟨hx, hy⟩ => ⟨part2_ok h.pa hx, part2_ok h.pb hy⟩
  refine RelCT.ite (fun x y ⟨hx, hy⟩ => z_eq hx.z hy.z (by rw [h.eqNB]))
    (taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_
  refine RelCT.seq (R := fun x y => (Args a x ∧ 0 < NB a) ∧ Args b y) ?_
    (RelCT.seq (xor_rel h) (taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)))
  refine RelCT.mono (P := fun x y => (Q1 a x ∧ Q1 b y) ∧ 0 < NB a)
    (RelCT.post (taintRegs [.r4, .r2, .r5] (fun x y ⟨⟨hx, hy⟩, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [hx.r4, hy.r4, h.hst]
        · rw [hx.r2, hy.r2, h.eqNB]
        · rw [hx.r5, hy.r5, h.hdp, h.eqH]) (by taint_decide))
      fun x y ⟨⟨hx, hy⟩, hnb⟩ => ⟨WP.mono (args_ok h.pa hx) fun _ h' => ⟨h'.1, hnb⟩,
        WP.mono (args_ok h.pb hy) fun _ h' => h'.1⟩)
    (fun x y ⟨⟨hx, hy⟩, he⟩ => ⟨⟨hx, hy⟩, by
      have e : isa.eval .eq x = some x.z := eval_eq x
      rw [e, hx.z] at he
      simp at he
      omega⟩) fun _ _ hq => hq

theorem part3_rel : RelCT isa (fun x y => Q2 a x ∧ Q2 b y) part3 fun x y => Q3 a x ∧ Q3 b y := by
  refine RelCT.post ?_ fun x y ⟨hx, hy⟩ => ⟨part3_ok h.pa hx, part3_ok h.pb hy⟩
  rw [part3_eq]
  refine RelCT.seq (R := fun (x y : State) => (Q2 a x ∧ x.z = decide (T a = 0)) ∧ (Q2 b y ∧ y.z = decide (T b = 0)))
    (RelCT.post (taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨cmp6_ok hx, cmp6_ok hy⟩) ?_
  refine RelCT.ite (fun x y ⟨⟨_, zx⟩, ⟨_, zy⟩⟩ => z_eq zx zy (by rw [h.eqT]))
    (taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_
  refine RelCT.seq (R := fun x y => TArgs a x ∧ TArgs b y)
    (RelCT.post (taintRegs [.r4] (fun x y ⟨⟨⟨hx, _⟩, ⟨hy, _⟩⟩, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hx.r4, hy.r4, h.hst]) (by taint_decide))
      fun x y ⟨⟨⟨hx, _⟩, ⟨hy, _⟩⟩, _⟩ => ⟨tailArgs_ok h.pa hx, tailArgs_ok h.pb hy⟩) ?_
  refine RelCT.seq (R := fun x y => TAfter a x ∧ TAfter b y) ?_
    (taintRegs [.r4, .r5, .r6] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hx.r4, hy.r4, h.hst]
      · rw [hx.r5, hy.r5, h.hdp, h.eqH, h.eqNB]
      · rw [hx.r6, hy.r6, h.eqT]) (by taint_decide))
  have est : ST b = ST a := h.hst.symm
  have est' : st b = st a := h.eqst.symm
  refine RelCT.post (RelCT.call Proof.ChaCha20.Arm.block_correct Proof.ChaCha20.Arm.block_ct
    [⟨st a, 64⟩] [⟨State.addr (ST a + BitVec.ofNat 32 64), 256⟩] fun x y ⟨hx, hy⟩ => ?_)
    fun x y ⟨hx, hy⟩ => ⟨hx.call h.pa, hy.call h.pb⟩
  have py := hy.pre h.pb
  have cy := hy.covers h.pb
  rw [est, est'] at py cy
  refine ⟨hx.pre h.pa, py, ?_, (hx.covers h.pa).1, (hx.covers h.pa).2, cy.1, cy.2⟩
  simp only [Proof.ChaCha20.blockArm, State.withRegions_gpr,
    State.callEntry_gpr x (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr x (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr y (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr y (by decide : Reg.r1 ∉ linkRegs),
    hx.r0, hx.r1, hy.r0, hy.r1, h.hst]
  exact ⟨trivial, trivial⟩

theorem apply_rel : RelCT isa (fun x y => x = a ∧ y = b) apply fun _ _ => True := by
  rw [apply_eq]
  refine RelCT.seq (check_rel h) (RelCT.ite (fun x y ⟨hx, hy⟩ => z_eq hx.z hy.z (by rw [h.hleft, h.eqL]))
    (taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_)
  by_cases hlt : N a < L a
  · refine RelCT.of_false fun x y hp => ?_
    have he := hp.2
    have e : isa.eval .eq x = some x.z := eval_eq x
    rw [e, hp.1.1.z] at he
    simp [hlt] at he
  have hle : L a ≤ N a := by omega
  refine RelCT.seq (RelCT.mono (part1_rel h hle) (fun _ _ hp => hp.1) fun _ _ hq => hq)
    (RelCT.seq (part2_rel h) (RelCT.seq (part3_rel h) ?_))
  exact taintRegs [.r4] (fun x y ⟨hx, hy⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [hx.r4, hy.r4, h.hst]) (by taint_decide)

end

theorem Two.of {a b : State} (ha : Proof.ChaCha20.applyArm.pre a) (hb : Proof.ChaCha20.applyArm.pre b)
    (hq : Proof.ChaCha20.applyArm.pub a b) : Two a b := by
  obtain ⟨p1, p2, p3, _, p5⟩ := hq
  exact ⟨APre.of a ha, APre.of b hb, p1, p2, p3, (List.cons.inj p5).1⟩

theorem apply_ct : ConstantTime isa Proof.ChaCha20.applyArm.pre Proof.ChaCha20.applyArm.pub apply :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (apply_rel (Two.of h₁ h₂ hq) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem apply_ok (s : State) (hs : Proof.ChaCha20.applyArm.pre s) :
    ∃ t s', Exec isa apply s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.applyArm.post s s' := by
  obtain ⟨t, s', he, hf⟩ := apply_correct (APre.of s hs)
  exact ⟨t, s', he, hf.1, hf.2⟩

/-- A state satisfying the precondition of `apply` (with no data). -/
def applySat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 768⟩, ⟨0x2000, 0⟩]

theorem ret_eq (x y : BitVec 32) : (x ++ y).setWidth 32 = y := by
  ext i hi
  rw [BitVec.getElem_setWidth, BitVec.getLsbD_append, ite_pos hi, BitVec.getLsbD_eq_getElem hi]

theorem apply_verified : Verified Arm.target apply (Spec.ChaCha20.applyContract Arm.abi 0) :=
  Verified.of_correct apply_ok apply_ct (by
    sig_implies [Spec.ChaCha20.applyContract, Spec.ChaCha20.applySig, Proof.ChaCha20.applyArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, State.addr, ret_eq] [applySat] using applySat)

end VG.Proof.ChaCha20.Arm.Stream
