import VerifiedGarbage.Proof.AesGcm.AArch64.StreamCryptCT
import VerifiedGarbage.Proof.AesGcm.AArch64.FinCT

/-!
# AES-GCM on AArch64: what `seal` and `open` share, in two runs

Untrusted: everything here is checked by Lean. The entry loads `work` from
the stack, which the taint analysis takes as secret (it reads memory): the
block is split after the load (`RelCT.block_split`), and the rest runs from
`x9`, which holds `work` (public) in both runs. Then `j0`, `oneAad` and
`encPrep` (`front_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- Two runs of `a; (b; c)` are two runs of `(a; b); c`. -/
theorem RelCT.assoc {a b c : Prog isa} {P Q : State → State → Prop}
    (h : RelCT isa P (.seq (.seq a b) c) Q) : RelCT isa P (.seq a (.seq b c)) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (Exec.seq_assoc e₁) (Exec.seq_assoc e₂)

theorem RelCT.assoc' {a b c : Prog isa} {P Q : State → State → Prop}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (Exec.seq_assoc' e₁) (Exec.seq_assoc' e₂)

/-- `oneAad`'s first block. -/
theorem aadBlk_ok {s : State} {W A : Addr} {al : Nat} (h19 : s.gpr .x19 = W)
    (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr)) (sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A)
    (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al) :
    WP isa (.block [.ldr .x .x23 .x19 aadO, .ldr .x .x24 .x19 alenO, imm .x25 0]) s fun s' =>
      s'.gpr .x23 = A ∧ s'.gpr .x24 = BitVec.ofNat 64 al ∧ s'.gpr .x25 = BitVec.ofNat 64 0 ∧
      Regs [.x23, .x24, .x25] s s' := by
  have q₁ := in_off hr (show 216 + 8 ≤ 2560 by decide) (by decide)
  have q₂ := in_off hr (show 224 + 8 ≤ 2560 by decide) (by decide)
  refine WP.run ⟨_, by arun [h19, q₁, q₂], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ?_, by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [← sA]; rfl
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [← sL]; rfl

/-- `encPrep`. -/
theorem encPrep_ok {s : State} {W D : Addr} {al n : Nat} (h19 : s.gpr .x19 = W)
    (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr)) (hlt : al < 2 ^ 64)
    (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) :
    WP isa (.block encPrep) s fun s' =>
      s'.gpr .x25 = BitVec.ofNat 64 (al % 16) ∧ s'.gpr .x26 = BitVec.ofNat 64 n ∧ s'.gpr .x27 = 0 ∧
      s'.gpr .x28 = D ∧ Regs [.x9, .x10, .x25, .x26, .x27, .x28] s s' := by
  have q₂ := in_off hr (show 224 + 8 ≤ 2560 by decide) (by decide)
  have q₃ := in_off hr (show 232 + 8 ≤ 2560 by decide) (by decide)
  have q₄ := in_off hr (show 240 + 8 ≤ 2560 by decide) (by decide)
  refine WP.run ⟨_, by simp only [encPrep]; arun [h19, q₂, q₃, q₄], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ?_, by simp [gpr_write], ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    rw [show s.mem.read (W + 224#64) 8 = s.mem.readW (W + BitVec.ofNat 64 224) 64 from rfl, sL,
      show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15, toNat_ofNat_of_lt hlt]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    rw [show s.mem.read (W + 240#64) 8 = s.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, sN]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    rw [show s.mem.read (W + 232#64) 8 = s.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl, sD]

/-- What `front_ok` needs of a run. -/
structure FrontIn (Ctx St W SP : Addr) (k : Reg → BitVec 64) (Np A D : Addr) (nl al n : Nat) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  x23 : s.gpr .x23 = Np
  x24 : s.gpr .x24 = BitVec.ofNat 64 nl
  x26 : s.gpr .x26 = BitVec.ofNat 64 nl
  x27 : s.gpr .x27 = 0
  non : DataOk St W s Np nl
  aad : DataOk St W s A al
  sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A
  sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al
  sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D
  sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n

/-- What `front_rel` leaves of a run. -/
structure FrontOut (Ctx St W SP : Addr) (k : Reg → BitVec 64) (D : Addr) (al n : Nat) (s₀ s : State) :
    Prop where
  env : Env Ctx St W SP s
  x22 : s.gpr .x22 = k .x22
  x25 : s.gpr .x25 = BitVec.ofNat 64 (al % 16)
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  x27 : s.gpr .x27 = 0
  x28 : s.gpr .x28 = D
  frame : Frame (frontFrame St W) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

/-- `j0`, `oneAad` and `encPrep` in two runs. -/
theorem front_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {Np A D : Addr} {nl al n : Nat} {σ₁ σ₂ : State}
    (h₁ : FrontIn Ctx St W SP k₁ Np A D nl al n σ₁) (h₂ : FrontIn Ctx St W SP k₂ Np A D nl al n σ₂)
    {rest : Prog isa}
    (hr : ∀ τ₁ τ₂, FrontOut Ctx St W SP k₁ D al n σ₁ τ₁ → FrontOut Ctx St W SP k₂ D al n σ₂ τ₂ →
      RelCT isa (Eq2 τ₁ τ₂) rest TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (j0 v.callees) (.seq (oneAad v.callees) (.seq (.block encPrep) rest))) TT := by
  have hlt := h₁.aad.lt
  have j₁ : J0In Ctx St W SP k₁ (blockAt σ₁.mem (Ctx + BitVec.ofNat 64 240)) Np nl σ₁ :=
    ⟨h₁.env, h₁.kept, h₁.x23, h₁.x24, h₁.x26, h₁.x27, h₁.non, rfl⟩
  have j₂ : J0In Ctx St W SP k₂ (blockAt σ₂.mem (Ctx + BitVec.ofNat 64 240)) Np nl σ₂ :=
    ⟨h₂.env, h₂.kept, h₂.x23, h₂.x24, h₂.x26, h₂.x27, h₂.non, rfl⟩
  refine rel_seq (j0_rel L v j₁ j₂) (WP.with_rdwr (j0_ok L v j₁)) (WP.with_rdwr (j0_ok L v j₂))
    fun s₁ s₂ ⟨o₁, rd₁, wr₁⟩ ⟨o₂, rd₂, wr₂⟩ => ?_
  have sl₁ := fun d (a : 216 ≤ d) (b : d + 8 ≤ 256) => slot_kept o₁.frame (slots_j0Frame L) a b
  have sl₂ := fun d (a : 216 ≤ d) (b : d + 8 ≤ 256) => slot_kept o₂.frame (slots_j0Frame L) a b
  refine RelCT.assoc' ?_
  refine rel_seq (rel_taint [.x19] (by rw [o₁.env.sp, o₂.env.sp]) (by agree_tac [o₁.env.x19, o₂.env.x19])
      ⟨_, by taint_decide⟩)
    (aadBlk_ok (A := A) (al := al) o₁.env.x19 (covers_left o₁.env.perm.w) (by rw [sl₁ 216 (by decide) (by decide), h₁.sA])
      (by rw [sl₁ 224 (by decide) (by decide), h₁.sL]))
    (aadBlk_ok (A := A) (al := al) o₂.env.x19 (covers_left o₂.env.perm.w) (by rw [sl₂ 216 (by decide) (by decide), h₂.sA])
      (by rw [sl₂ 224 (by decide) (by decide), h₂.sL]))
    fun s₁' s₂' ⟨x23₁, x24₁, x25₁, r₁⟩ ⟨x23₂, x24₂, x25₂, r₂⟩ => ?_
  have a₁ : AbsIn Ctx St W SP k₁ (blockAt s₁'.mem (Ctx + BitVec.ofNat 64 240)) [] A al 0 s₁' :=
    ⟨o₁.env.of_regs r₁, o₁.kept.of_others r₁.others, x23₁, x24₁, x25₁, rfl,
      h₁.aad.of_eq (by rw [r₁.rd, rd₁]) (by rw [r₁.wr, wr₁]), rfl⟩
  have a₂ : AbsIn Ctx St W SP k₂ (blockAt s₂'.mem (Ctx + BitVec.ofNat 64 240)) [] A al 0 s₂' :=
    ⟨o₂.env.of_regs r₂, o₂.kept.of_others r₂.others, x23₂, x24₂, x25₂, rfl,
      h₂.aad.of_eq (by rw [r₂.rd, rd₂]) (by rw [r₂.wr, wr₂]), rfl⟩
  refine rel_seq (absorb_rel L v (.inr rfl) a₁ a₂) (WP.with_rdwr (absorb_ok L (.inr rfl) v a₁))
    (WP.with_rdwr (absorb_ok L (.inr rfl) v a₂)) fun t₁ t₂ ⟨b₁, brd₁, bwr₁⟩ ⟨b₂, brd₂, bwr₂⟩ => ?_
  have f₁ : Frame (frontFrame St W) σ₁.mem t₁.mem :=
    (o₁.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩).trans
      (by rw [← r₁.mem]; exact b₁.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩)
  have f₂ : Frame (frontFrame St W) σ₂.mem t₂.mem :=
    (o₂.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩).trans
      (by rw [← r₂.mem]; exact b₂.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩)
  have tl₁ := fun d (a : 216 ≤ d) (b : d + 8 ≤ 256) => slot_kept f₁ (slots_frontFrame L) a b
  have tl₂ := fun d (a : 216 ≤ d) (b : d + 8 ≤ 256) => slot_kept f₂ (slots_frontFrame L) a b
  refine rel_seq (rel_taint [.x19] (by rw [b₁.env.sp, b₂.env.sp]) (by agree_tac [b₁.env.x19, b₂.env.x19])
      ⟨_, by taint_decide⟩)
    (encPrep_ok (D := D) (n := n) b₁.env.x19 (covers_left b₁.env.perm.w) hlt (by rw [tl₁ 224 (by decide) (by decide), h₁.sL])
      (by rw [tl₁ 232 (by decide) (by decide), h₁.sD]) (by rw [tl₁ 240 (by decide) (by decide), h₁.sN]))
    (encPrep_ok (D := D) (n := n) b₂.env.x19 (covers_left b₂.env.perm.w) hlt (by rw [tl₂ 224 (by decide) (by decide), h₂.sL])
      (by rw [tl₂ 232 (by decide) (by decide), h₂.sD]) (by rw [tl₂ 240 (by decide) (by decide), h₂.sN]))
    fun u₁ u₂ ⟨e25₁, e26₁, e27₁, e28₁, er₁⟩ ⟨e25₂, e26₂, e27₂, e28₂, er₂⟩ => ?_
  refine hr u₁ u₂ ⟨b₁.env.of_regs er₁, ?_, e25₁, e26₁, e27₁, e28₁, by rw [er₁.mem]; exact f₁,
      by rw [er₁.rd, brd₁, r₁.rd, rd₁], by rw [er₁.wr, bwr₁, r₁.wr, wr₁]⟩
    ⟨b₂.env.of_regs er₂, ?_, e25₂, e26₂, e27₂, e28₂, by rw [er₂.mem]; exact f₂,
      by rw [er₂.rd, brd₂, r₂.rd, rd₂], by rw [er₂.wr, bwr₂, r₂.wr, wr₂]⟩
  · rw [er₁.others _ (by decide), b₁.kept .x22 (by decide)]
  · rw [er₂.others _ (by decide), b₂.kept .x22 (by decide)]

end


/-- The load of `work`. -/
theorem ldr9_ok {s : State} {W : Addr} (hW : stackArg s 0 = W)
    (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8) :
    WP isa (.block [.ldrSp .x9 0]) s fun s' => s'.gpr .x9 = W ∧ (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.run ⟨_, by arun [hsp], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, fun r hr => by simp [gpr_write, hr], rfl, rfl, rfl⟩
  rw [← hW]
  simp [gpr_write, stackArg, stackArgAddr, Mem.readW]

/-- The entry of `seal` and `open` in two runs. -/
theorem entry_rel {σ₁ σ₂ : State} {W : Addr} (hW₁ : stackArg σ₁ 0 = W) (hW₂ : stackArg σ₂ 0 = W)
    (hsp₁ : InRegions (σ₁.rd ++ σ₁.wr) (σ₁.sp + BitVec.ofNat 64 0) 8)
    (hsp₂ : InRegions (σ₂.rd ++ σ₂.wr) (σ₂.sp + BitVec.ofNat 64 0) 8)
    (hw₁ : Covers [⟨W, 2560⟩] σ₁.wr) (hw₂ : Covers [⟨W, 2560⟩] σ₂.wr) (qsp : σ₁.sp = σ₂.sp)
    (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block oneEntry) TT := by
  have run : ∀ {σ : State}, stackArg σ 0 = W → InRegions (σ.rd ++ σ.wr) (σ.sp + BitVec.ofNat 64 0) 8 →
      Covers [⟨W, 2560⟩] σ.wr →
      WP isa (.block ([.ldrSp .x9 0] ++ save .x9)) σ fun s' => s'.gpr .x9 = W ∧
        (∀ r, r ≠ .x9 → s'.gpr r = σ.gpr r) ∧ s'.sp = σ.sp := fun hW hsp hw =>
    WP.block_append (WP.mono (ldr9_ok hW hsp) fun s₁ ⟨x9₁, g₁, sp₁, rd₁, wr₁⟩ => by
      obtain ⟨s₂, run₂, g₂, sp₂, _, _, _⟩ := save_ok s₁ .x9 x9₁ (by rw [wr₁]; exact hw)
      exact WP.of_runBlock ⟨s₂, run₂, by rw [g₂, x9₁], fun r hr => by rw [g₂, g₁ r hr], by rw [sp₂, sp₁]⟩)
  have t₁ : ∃ h, (taint.check (Taint.ofRegs []) (.block [.ldrSp .x9 0]) h).isSome = true := ⟨_, by taint_decide⟩
  have t₂ : ∃ h, (taint.check (Taint.ofRegs [.x9]) (.block (save .x9)) h).isSome = true := ⟨_, by taint_decide⟩
  show RelCT isa _ (.block ([.ldrSp .x9 0] ++ save .x9 ++ _)) _
  refine RelCT.block_split (rel_seq (RelCT.block_split (rel_seq (rel_taint [] qsp (by agree_tac []) t₁)
      (ldr9_ok hW₁ hsp₁) (ldr9_ok hW₂ hsp₂)
      fun τ₁ τ₂ ⟨x9₁, _, sp₁, _, _⟩ ⟨x9₂, _, sp₂, _, _⟩ =>
        rel_taint [.x9] (by rw [sp₁, sp₂, qsp]) (by agree_tac [x9₁, x9₂]) t₂))
    (run hW₁ hsp₁ hw₁) (run hW₂ hsp₂ hw₂) fun τ₁ τ₂ ⟨x9₁, g₁, sp₁⟩ ⟨x9₂, g₂, sp₂⟩ => ?_)
  refine rel_taint [.x9, .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] (by rw [sp₁, sp₂, qsp]) ?_ ⟨_, by taint_decide⟩
  intro r hr
  by_cases h9 : r = .x9
  · subst h9; rw [x9₁, x9₂]
  · rw [g₁ r h9, g₂ r h9]
    exact hq r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)

end VG.Proof.AesGcm.AArch64
