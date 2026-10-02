import VerifiedGarbage.Proof.Scrypt.Arm.Whole.Correct
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-!
# scrypt on 32-bit ARM: constant time, up to the indices `j`

Untrusted: everything here is checked by Lean. As on the other targets
(`Proof/Scrypt/AArch64/Whole/CT.lean`): two runs whose public data agree
have the same layout, so they are related by `Two P`: both satisfy `P` with
that layout (each with its own registers on entry and memory), whatever
their secrets, and the indices of all the scryptROMix calls agree
(`LeakEq`). The blocks address only our stack arguments, from `sp`, and
`scratch` from registers that hold the same in both runs (the taint
analysis, with the stack arguments public); each call is of constant-time
code whose public data agree (`frame4_rel`, `frame2_rel`); the loop's
branch agrees since both runs count the same blocks.
-/

namespace VG.Proof.Scrypt.Arm.Whole

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Arm.FrameStack
open VG.Spec.Scrypt (bytesAt roMixIndices)
open VG.Proof.Pbkdf2.Whole.Arm (frame2_rel p2_arg0 p2_arg1)

/-- The indices of every scryptROMix agree in two runs from `m₁` and `m₂`. -/
def LeakEq (L : Lay) (m₁ m₂ : Mem) : Prop :=
  (Spec.Scrypt.blocks (bytesAt m₁ (State.addr L.pw) L.pwl.toNat) (bytesAt m₁ (State.addr L.salt) L.sl.toNat)
      L.r.toNat L.pp).flatMap (roMixIndices L.r.toNat L.NN) =
    (Spec.Scrypt.blocks (bytesAt m₂ (State.addr L.pw) L.pwl.toNat) (bytesAt m₂ (State.addr L.salt) L.sl.toNat)
      L.r.toNat L.pp).flatMap (roMixIndices L.r.toNat L.NN)

theorem leak_X {L : Lay} {m₁ m₂ : Mem} (h : LeakEq L m₁ m₂) {k : Nat} (hk : k < L.pp) :
    roMixIndices L.r.toNat L.NN (X L m₁ k) = roMixIndices L.r.toNat L.NN (X L m₂ k) := by
  have h₁ : k < (Spec.Scrypt.blocks (bytesAt m₁ (State.addr L.pw) L.pwl.toNat)
      (bytesAt m₁ (State.addr L.salt) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  have h₂ : k < (Spec.Scrypt.blocks (bytesAt m₂ (State.addr L.pw) L.pwl.toNat)
      (bytesAt m₂ (State.addr L.salt) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  simp only [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂,
    Option.getD_some]
  exact Whole.indices_eq h h₁ h₂

/-- The layout of two runs, and what each has on entry. -/
structure Env where
  L : Lay
  g₁ : Reg → BitVec 32
  g₂ : Reg → BitVec 32
  m₁ : Mem
  m₂ : Mem

/-- What one run has, from its layout, its registers and memory on entry. -/
abbrev Pred := Lay → (Reg → BitVec 32) → Mem → State → Prop

/-- Two runs with the same layout, each satisfying `P`. -/
def Two (P : Pred) (a b : State) : Prop :=
  ∃ e : Env, e.L.Ok ∧ LeakEq e.L e.m₁ e.m₂ ∧ P e.L e.g₁ e.m₁ a ∧ P e.L e.g₂ e.m₂ b

/-- `Ctx` and `Φ`. -/
abbrev C (Φ : Lay → Mem → State → Prop) : Pred := fun L g m₀ t => Ctx L g m₀ t ∧ Φ L m₀ t

/-- Code whose runs leak the same, and which establishes `Q`. -/
theorem two_wp {c : Prog isa} {P Q : Pred} (hct : RelCT isa (Two P) c fun _ _ => True)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t → WP isa c t (Q L g m₀)) :
    RelCT isa (Two P) c (Two Q) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨e, hL, hk, c₁, c₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ _ s₁ hL c₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ _ s₂ hL c₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, e, hL, hk, y₁, y₂⟩

/-- Two states agree on the taint with the stack arguments and `rs` public. -/
theorem agree_L {L : Lay} (hL : L.Ok) {a b : State} (ha : a.sp = L.sp) (hb : b.sp = L.sp)
    (wa : a.wr = [L.BB, L.VV, L.SC, L.OUT]) (wb : b.wr = [L.BB, L.VV, L.SC, L.OUT])
    (ka : Args L a.mem) (kb : Args L b.mem) {rs : List Reg} (hr : ∀ r ∈ rs, a.gpr r = b.gpr r) :
    VG.Arm.Taint.Agree (argTaint rs 36) a b := by
  have hA := hL.nA
  have out : ∀ (t : State), t.sp = L.sp → t.wr = [L.BB, L.VV, L.SC, L.OUT] →
      t.sp.toNat + 36 ≤ 2 ^ 32 ∧ ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 36⟩ r := fun t hs hw => by
    refine ⟨by rw [hs]; exact hA, fun r hr => ?_⟩
    rw [hw] at hr
    rw [hs]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hL.ba.symm, hL.va.symm, hL.ca.symm, hL.oa.symm]
  refine agree_argTaint hr (ha.trans hb.symm) (out a ha wa) (out b hb wb)
    (argMem_of (j := 9) (ha.trans hb.symm) (by rw [ha]; exact hA) fun i hi => ?_)
  have st : ∀ (t : State), t.sp = L.sp → ∀ i < 9,
      stackArg t i = t.mem.readW (State.addr L.sp + BitVec.ofNat 64 (4 * i)) 32 := fun t hs i hi => by
    simp only [stackArg, stackArgAddr, hs]
    rw [hL.arg_addr (by omega)]
  rw [st a ha i hi, st b hb i hi]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [ka.r.trans kb.r.symm, ka.b.trans kb.b.symm, ka.blen.trans kb.blen.symm, ka.v.trans kb.v.symm,
    ka.vlen.trans kb.vlen.symm, ka.scr.trans kb.scr.symm, ka.slen.trans kb.slen.symm,
    ka.out.trans kb.out.symm, ka.ol.trans kb.ol.symm]

/-- What every `P` of a piece of straight-line code gives the taint analysis. -/
structure Wfp (P : Pred) : Prop where
  sp : ∀ L g m₀ (t : State), P L g m₀ t → t.sp = L.sp
  wr : ∀ L g m₀ (t : State), P L g m₀ t → t.wr = [L.BB, L.VV, L.SC, L.OUT]
  args : ∀ L g m₀ (t : State), P L g m₀ t → Args L t.mem

theorem Wfp.ctx (Φ : Lay → Mem → State → Prop) : Wfp (C Φ) :=
  ⟨fun _ _ _ _ h => h.1.sp, fun _ _ _ _ h => h.1.wr, fun _ _ _ _ h => h.1.args⟩

/-- A block the taint analysis accepts with the stack arguments and `rs` public. -/
theorem two_blk {is : List Instr} {P Q : Pred} (hP : Wfp P) (rs : List Reg)
    (hr : ∀ (L : Lay) g₁ g₂ m₁ m₂ (a b : State), L.Ok → P L g₁ m₁ a → P L g₂ m₂ b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint VG.Arm.Taint.T} (h : (taint.check (argTaint rs 36) (.block is) hc).isSome = true)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t → WP isa (.block is) t (Q L g m₀)) :
    RelCT isa (Two P) (.block is) (Two Q) :=
  two_wp (RelCT.taint (A := taint) (argTaint rs 36) (fun _ _ ⟨_, hL, _, c₁, c₂⟩ =>
    agree_L hL (hP.sp _ _ _ _ c₁) (hP.sp _ _ _ _ c₂) (hP.wr _ _ _ _ c₁) (hP.wr _ _ _ _ c₂)
      (hP.args _ _ _ _ c₁) (hP.args _ _ _ _ c₂) (hr _ _ _ _ _ _ _ hL c₁ c₂)) h) hw

/-! ## The calls -/

/-- A call in a frame of four words, of verified code whose contract and
public data hold in both runs. -/
theorem two_call4 {n : String} {c : Prog isa} {k : Contract isa} {P Q : Pred}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t →
      k.pre ((pushed fr4 t).callEntry.withRegions (rd L) (wr L)) ∧
      Covers (rd L ++ wr L) ((pushed fr4 t).rd ++ (pushed fr4 t).wr) ∧ Covers (wr L) (pushed fr4 t).wr)
    (hpub : ∀ (L : Lay) g₁ g₂ m₁ m₂ (a b : State), L.Ok → LeakEq L m₁ m₂ → P L g₁ m₁ a → P L g₂ m₂ b →
      a.sp = b.sp ∧ k.pub ((pushed fr4 a).callEntry.withRegions (rd L) (wr L))
        ((pushed fr4 b).callEntry.withRegions (rd L) (wr L)))
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t →
      WP isa (.frame (.push fr4) (.call n c) (.pop .r12 16)) t (Q L g m₀)) :
    RelCT isa (Two P) (.frame (.push fr4) (.call n c) (.pop .r12 16)) (Two Q) :=
  two_wp (fun s₁ s₂ _ _ _ _ hp e₁ e₂ => by
    obtain ⟨e, hL, hk, c₁, c₂⟩ := hp
    obtain ⟨hsp, hpb⟩ := hpub _ _ _ _ _ _ _ hL hk c₁ c₂
    obtain ⟨p₁, v₁, w₁⟩ := hpre _ _ _ _ hL c₁
    obtain ⟨p₂, v₂, w₂⟩ := hpre _ _ _ _ hL c₂
    exact frame4_rel hv hct (P := fun a b => a = s₁ ∧ b = s₂) (rd e.L) (wr e.L)
      (fun _ _ ⟨h₁, h₂⟩ => by subst h₁ h₂; exact ⟨hsp, p₁, p₂, hpb, v₁, w₁, v₂, w₂⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂) hw

/-- The same for a frame of two words. -/
theorem two_call2 {n : String} {c : Prog isa} {k : Contract isa} {P Q : Pred}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t →
      k.pre ((pushed [.r12, .lr] t).callEntry.withRegions (rd L) (wr L)) ∧
      Covers (rd L ++ wr L) ((pushed [.r12, .lr] t).rd ++ (pushed [.r12, .lr] t).wr) ∧
      Covers (wr L) (pushed [.r12, .lr] t).wr)
    (hpub : ∀ (L : Lay) g₁ g₂ m₁ m₂ (a b : State), L.Ok → LeakEq L m₁ m₂ → P L g₁ m₁ a → P L g₂ m₂ b →
      a.sp = b.sp ∧ k.pub ((pushed [.r12, .lr] a).callEntry.withRegions (rd L) (wr L))
        ((pushed [.r12, .lr] b).callEntry.withRegions (rd L) (wr L)))
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t →
      WP isa (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8)) t (Q L g m₀)) :
    RelCT isa (Two P) (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8)) (Two Q) :=
  two_wp (fun s₁ s₂ _ _ _ _ hp e₁ e₂ => by
    obtain ⟨e, hL, hk, c₁, c₂⟩ := hp
    obtain ⟨hsp, hpb⟩ := hpub _ _ _ _ _ _ _ hL hk c₁ c₂
    obtain ⟨p₁, v₁, w₁⟩ := hpre _ _ _ _ hL c₁
    obtain ⟨p₂, v₂, w₂⟩ := hpre _ _ _ _ hL c₂
    exact frame2_rel (by decide) hv hct (P := fun a b => a = s₁ ∧ b = s₂) (rd e.L) (wr e.L)
      (fun _ _ ⟨h₁, h₂⟩ => by subst h₁ h₂; exact ⟨hsp, p₁, p₂, hpb, v₁, w₁, v₂, w₂⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂) hw

theorem pbk_pub_two {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem} {a b : State}
    (c₁ : Ctx L g₁ m₁ a) (c₂ : Ctx L g₂ m₂ b) (hL : L.Ok) {salt sl out ol : BitVec 32}
    (a₁ : PbkArgs L salt sl out ol a) (a₂ : PbkArgs L salt sl out ol b) :
    a.sp = b.sp ∧ pbkA.pub ((pushed fr4 a).callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol))
      ((pushed fr4 b).callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol)) := by
  have s1 : 16 ≤ a.sp.toNat := by rw [c₁.sp]; have := hL.nS; omega
  have s2 : 16 ≤ b.sp.toNat := by rw [c₂.sp]; have := hL.nS; omega
  refine ⟨c₁.sp.trans c₂.sp.symm, ?_⟩
  simp only [pbkA, State.withRegions_sp, State.callEntry_sp, p4_sp, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    pushed_gpr, p4_a0 s1, p4_a1 s1, p4_a2 s1, p4_a3 s1, p4_a0 s2, p4_a1 s2, p4_a2 s2, p4_a3 s2,
    c₁.sp, c₂.sp, a₁.r0, a₁.r1, a₁.r2, a₁.r3, a₁.r10, a₁.r11, a₁.r12, a₁.lr, a₂.r0, a₂.r1, a₂.r2, a₂.r3,
    a₂.r10, a₂.r11, a₂.r12, a₂.lr, and_self]

/-- The block ROMix works on in iteration `i`, on entry to it. -/
theorem romix_bytes {L : Lay} (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp) (hb : InvB L m₀ i t) (rd wr : List Region) :
    bytesAt ((pushed [.r12, .lr] t).callEntry.withRegions rd wr).mem (blkA L i) (128 * L.r.toNat) =
      X L m₀ i := by
  have hS := hL.nS
  have f₀ := pushed_frameA (rs := [Reg.r12, Reg.lr]) (s := t)
    (by simp only [List.length_cons, List.length_nil]; rw [hc.sp]; omega)
  rw [State.withRegions_mem, State.callEntry_mem, Memory.frame_bytesAt f₀ (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR
      have hs : Region.Sub ⟨State.addr (t.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)),
          4 * [Reg.r12, Reg.lr].length⟩ L.STK := by
        rw [hc.sp]; exact args8_sub hL
      rw [Nat.mul_comm]
      exact ((hL.stk_in (blk_in hL hi)).sub_left hs).symm) (by have := hL.r_lt; omega), hb.blks i hi]
  simp only [Nat.lt_irrefl, ite_false]

theorem romix_pub_two {L : Lay} (hL : L.Ok) {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem} {a b : State}
    (hk : LeakEq L m₁ m₂) (c₁ : Ctx L g₁ m₁ a) (c₂ : Ctx L g₂ m₂ b) {i : Nat} (hi : i < L.pp)
    (b₁ : InvB L m₁ i a) (b₂ : InvB L m₂ i b) (a₁ : RomixArgs L (blkAt L i) a)
    (a₂ : RomixArgs L (blkAt L i) b) :
    a.sp = b.sp ∧ Proof.Scrypt.roMixArm.pub ((pushed [.r12, .lr] a).callEntry.withRegions (romixRd L) (romixWr L i))
      ((pushed [.r12, .lr] b).callEntry.withRegions (romixRd L) (romixWr L i)) := by
  have s1 : 8 ≤ a.sp.toNat := by rw [c₁.sp]; have := hL.nS; omega
  have s2 : 8 ≤ b.sp.toNat := by rw [c₂.sp]; have := hL.nS; omega
  have y₁ := romix_bytes hL c₁ hi b₁ (romixRd L) (romixWr L i)
  have y₂ := romix_bytes hL c₂ hi b₂ (romixRd L) (romixWr L i)
  refine ⟨c₁.sp.trans c₂.sp.symm, ?_⟩
  simp only [Proof.Scrypt.roMixArm, State.withRegions_sp, State.callEntry_sp, pushed_sp, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    pushed_gpr, p2_arg0 s1, p2_arg1, p2_arg0 s2, c₁.sp, c₂.sp, a₁.r0, a₁.r1, a₁.r2, a₁.r3, a₁.r12, a₁.lr,
    a₂.r0, a₂.r1, a₂.r2, a₂.r3, a₂.r12, a₂.lr, addr_blk hL hi, true_and]
  rw [y₁, y₂]
  exact leak_X hk hi

/-! ## The pieces -/

theorem Wfp.e {P : Pred} (h : ∀ L g m₀ t, P L g m₀ t → E L g m₀ t) : Wfp P :=
  ⟨fun _ _ _ _ hp => (h _ _ _ _ hp).sp, fun _ _ _ _ hp => (h _ _ _ _ hp).wr,
    fun _ _ _ _ hp => (h _ _ _ _ hp).args⟩

abbrev P0 : Pred := fun L g m₀ t => E L g m₀ t ∧ t.gpr .lr = g .lr
abbrev P1 : Pred := fun L g m₀ t => E L g m₀ t ∧ t.gpr .r12 = L.scr ∧ t.mem.readW (State.addr L.scr) 32 = g .lr
abbrev P2 : Pred := fun L g m₀ t =>
  E L g m₀ t ∧ t.gpr .r12 = L.svb ∧ t.mem.readW (State.addr L.scr) 32 = g .lr ∧ Saved8 L g t.mem
abbrev P3 : Pred := fun L g m₀ t => E L g m₀ t ∧ Saved L g t.mem

theorem save1_ct : RelCT isa (Two P0) (.block save1) (Two P1) :=
  two_blk (Wfp.e fun _ _ _ _ h => h.1) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    fun _ _ _ _ hL ⟨he, hl⟩ => WP.mono (save1_ok hL he hl) fun _ ⟨e, _, r, w⟩ => ⟨e, r, w⟩

theorem save2_ct : RelCT isa (Two P1) (.block save2) (Two P2) :=
  two_blk (Wfp.e fun _ _ _ _ h => h.1) [.r12]
    (fun _ _ _ _ _ _ _ _ c₁ c₂ r h => by
      simp only [List.mem_singleton] at h; subst h; exact c₁.2.1.trans c₂.2.1.symm) (by taint_decide)
    fun _ _ _ _ hL ⟨he, hr, hw⟩ => save2_ok hL he hr hw

theorem save3_ct : RelCT isa (Two P2) (.block save3) (Two P3) :=
  two_blk (Wfp.e fun _ _ _ _ h => h.1) [.r12]
    (fun _ _ _ _ _ _ _ _ c₁ c₂ r h => by
      simp only [List.mem_singleton] at h; subst h; exact c₁.2.1.trans c₂.2.1.symm) (by taint_decide)
    fun _ _ _ _ hL ⟨he, hr, hw, h8⟩ => save3_ok hL he hr hw h8

/-- Iteration `pp - n` of the loop is next. -/
abbrev LoopAt (n : Nat) (L : Lay) (m₀ : Mem) (t : State) : Prop :=
  0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t

theorem body_ct (n : Nat) :
    RelCT isa (Two (C (LoopAt n))) (.seq (.block romixArgs) (.seq (.frame (.push [.r12, .lr])
      (.call "vg_scrypt_romix" Impl.Scrypt.Arm.roMix) (.pop .r12 8)) (.block nextBlock)))
      (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        t.z = decide (L.pp - n + 1 = L.pp))) := by
  have a : RelCT isa (Two (C (LoopAt n))) (.block romixArgs) (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧
      InvB L m₀ (L.pp - n) t ∧ RomixArgs L (blkAt L (L.pp - n)) t)) :=
    two_blk (Wfp.ctx _) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
      fun _ _ _ _ hL ⟨hc, h0, hn, hb⟩ =>
        WP.mono (romixArgs_ok hL hc) fun _ ⟨hc', hm, h4, ha⟩ =>
          ⟨hc', h0, hn, ⟨h4.trans hb.cur, by rw [hm]; exact hb.blks⟩, by rw [hb.cur] at ha; exact ha⟩
  have b : RelCT isa (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t ∧
      RomixArgs L (blkAt L (L.pp - n)) t)) (.frame (.push [.r12, .lr])
      (.call "vg_scrypt_romix" Impl.Scrypt.Arm.roMix) (.pop .r12 8))
      (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t)) :=
    two_call2 RoMix.roMix_correct RoMix.roMix_ct (fun L => romixRd L) (fun L => romixWr L (L.pp - n))
      (fun L _ _ _ hL ⟨hc, h0, hn, _, ha⟩ => ⟨romix_pre hL hc (i := L.pp - n) (by omega) ha,
        romix_cov hL hc (i := L.pp - n) (by omega)⟩)
      (fun _ _ _ _ _ _ _ hL hk ⟨c₁, h0, hn, b₁, a₁⟩ ⟨c₂, _, _, b₂, a₂⟩ =>
        romix_pub_two hL hk c₁ c₂ (by omega) b₁ b₂ a₁ a₂)
      (fun _ _ _ _ hL ⟨hc, h0, hn, hb, ha⟩ =>
        WP.mono (call_step hL (by omega) hc hb ha) fun _ ⟨hc', hm⟩ => ⟨hc', h0, hn, hm⟩)
  have c : RelCT isa (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t)) (.block nextBlock)
      (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        t.z = decide (L.pp - n + 1 = L.pp))) :=
    two_blk (Wfp.ctx _) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
      fun _ _ _ _ hL ⟨hc, h0, hn, hm⟩ =>
        WP.mono (nextBlock_ok hc) fun _ ⟨hc', hm', h4, hz⟩ =>
          ⟨hc', h0, hn, ⟨by rw [h4, hm.cur, next_eq], by rw [hm']; exact hm.blks⟩,
            by rw [hz, hm.cur, next_eq, z_eq hL (by omega)]⟩
  exact a.seq (b.seq c)

theorem loop_ct :
    RelCT isa (Two (C fun L m₀ t => InvB L m₀ 0 t)) romixLoop (Two (C fun L m₀ t => InvB L m₀ L.pp t)) := by
  have ev : ∀ x : State, isa.eval .ne x = some (!x.z) := fun x => VG.Proof.MdStream.Arm.eval_ne x
  have h := fun n => RelCT.loop (M := isa) (c := .ne) (Q := Two (C fun L m₀ t => InvB L m₀ L.pp t))
    (fun n => Two (C (LoopAt n))) (fun n => (body_ct n).mono (fun _ _ h => h) fun a b hab => by
      obtain ⟨e, hL, hk, ⟨c₁, h0, hn, b₁, z₁⟩, ⟨c₂, -, -, b₂, z₂⟩⟩ := hab
      rw [ev, ev, z₁, z₂]
      refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
      · have hl : e.L.pp - n + 1 = e.L.pp := by simpa using hf
        exact ⟨e, hL, hk, ⟨c₁, show InvB e.L e.m₁ e.L.pp a from hl ▸ b₁⟩,
          ⟨c₂, show InvB e.L e.m₂ e.L.pp b from hl ▸ b₂⟩⟩
      · have hl : e.L.pp - n + 1 ≠ e.L.pp := by simpa using ht
        have e₁ : e.L.pp - (n - 1) = e.L.pp - n + 1 := by omega
        exact ⟨n - 1, by omega, e, hL, hk, ⟨c₁, by omega, by omega, e₁ ▸ b₁⟩,
          ⟨c₂, by omega, by omega, e₁ ▸ b₂⟩⟩) n
  refine (RelCT.exists_ h).mono (fun a b ⟨e, hL, hk, ⟨c₁, b₁⟩, ⟨c₂, b₂⟩⟩ => ⟨e.L.pp, e, hL, hk,
    ⟨c₁, hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₁⟩,
    ⟨c₂, hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₂⟩⟩) fun _ _ h => h

/-! ## The whole function -/

abbrev Args1 (L : Lay) (_ : Mem) (t : State) : Prop :=
  t.gpr .r4 = L.b ∧ PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t
abbrev Args2 (L : Lay) (_ : Mem) (t : State) : Prop :=
  PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t

theorem pbk1_ct : RelCT isa (Two P3) (.block pbk1Args) (Two (C Args1)) :=
  two_blk (Wfp.e fun _ _ _ _ h => h.1) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    fun _ _ _ _ hL ⟨he, hs⟩ => WP.mono (pbk1Args_ok hL he hs) fun _ ⟨hc, _, h4, ha⟩ => ⟨hc, h4, ha⟩

theorem pbk2_ct : RelCT isa (Two (C fun L m₀ t => InvB L m₀ L.pp t)) (.block pbk2Args) (Two (C Args2)) :=
  two_blk (Wfp.ctx _) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    fun _ _ _ _ hL ⟨hc, _⟩ => WP.mono (pbk2Args_ok hL hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩

theorem restore_ct : RelCT isa (Two (C fun _ _ _ => True)) (.block restore) fun _ _ => True :=
  (two_blk (Q := fun _ _ _ _ => True) (Wfp.ctx _) [.r6, .r7]
    (fun _ _ _ _ _ _ _ _ c₁ c₂ r h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact c₁.1.r6.trans c₂.1.r6.symm
      · exact c₁.1.r7.trans c₂.1.r7.symm) (by taint_decide)
    fun _ _ _ _ hL ⟨hc, _⟩ => WP.mono (restore_ok hL hc) fun _ _ => trivial).mono (fun _ _ h => h)
    fun _ _ _ => trivial

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

theorem call1_ct : RelCT isa (Two (C Args1)) (pbkCall name pbk) (Two (C fun L m₀ t => InvB L m₀ 0 t)) :=
  two_call4 (pbk_correct hv) (pbk_ct hv) (fun L => pbkRd L L.salt L.sl)
    (fun L => pbkWr L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)))
    (fun _ _ _ _ hL ⟨hc, _, ha⟩ => ⟨pbk_pre' hL hc ha (pbk1_regions hL), pbk_cov hL hc (pbk1_regions hL)⟩)
    (fun _ _ _ _ _ _ _ hL _ ⟨c₁, _, a₁⟩ ⟨c₂, _, a₂⟩ => pbk_pub_two c₁ c₂ hL a₁ a₂)
    (fun _ _ _ _ hL ⟨hc, h4, ha⟩ => WP.mono (step1_ok hv hst name hL hc h4 ha) fun _ ⟨hc', h4', _, hx⟩ =>
      ⟨hc', by rw [h4', blk0], fun k hk => by rw [hx k hk]; simp only [Nat.not_lt_zero, ite_false]⟩)

theorem call2_ct : RelCT isa (Two (C Args2)) (pbkCall name pbk) (Two (C fun _ _ _ => True)) :=
  two_call4 (pbk_correct hv) (pbk_ct hv) (fun L => pbkRd L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)))
    (fun L => pbkWr L L.out L.ol)
    (fun _ _ _ _ hL ⟨hc, ha⟩ => ⟨pbk_pre' hL hc ha (pbk2_regions hL), pbk_cov hL hc (pbk2_regions hL)⟩)
    (fun _ _ _ _ _ _ _ hL _ ⟨c₁, a₁⟩ ⟨c₂, a₂⟩ => pbk_pub_two c₁ c₂ hL a₁ a₂)
    (fun _ _ _ _ hL ⟨hc, ha⟩ => WP.mono (pbk_call hv hst name hL hc ha (pbk2_regions hL)) fun _ h =>
      ⟨h.1, trivial⟩)

theorem scrypt_ct :
    ConstantTime isa Proof.Scrypt.scryptArm.pre Proof.Scrypt.scryptArm.pub (scrypt name pbk) := by
  refine RelCT.constantTime ((save1_ct.seq (save2_ct.seq (save3_ct.seq (pbk1_ct.seq
    ((call1_ct hv hst name).seq (loop_ct.seq (pbk2_ct.seq ((call2_ct hv hst name).seq restore_ct)))))))).mono
    ?_ fun _ _ _ => trivial)
  rintro s₁ s₂ ⟨h₁, h₂, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, hsp, hlk⟩
  have e : lay s₂ = lay s₁ := by
    simp only [lay, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, hsp]
  refine ⟨⟨lay s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok h₁, ?_, ⟨entry_E h₁, rfl⟩,
    ⟨e ▸ entry_E h₂, rfl⟩⟩
  rw [← h0, ← h1, ← h2, ← h3, ← a0, ← a2, ← a4] at hlk
  exact hlk

end

end VG.Proof.Scrypt.Arm.Whole
