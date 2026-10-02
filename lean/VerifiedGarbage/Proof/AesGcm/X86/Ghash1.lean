import VerifiedGarbage.Proof.AesGcm.X86.Loops

/-!
# AES-GCM on x86: calling `vg_ghash` from the pieces

Untrusted: everything here is checked by Lean. `ghArgs yo` sets up the
arguments of `vg_ghash` but the data (`ebx`) and the number of blocks (`edi`):
the hash subkey `Ctx + 240`, the accumulator `St + yo` and the working space
`W + 512` (`GhReady`); the call and `ebp` moved back to `W` continue the
accumulator over the blocks (`ghW_ok`, `GhOut`). `ghash1 yo b o` does it for
the block at `b + o` (`ghash1_ok`). Each is constant time from its
precondition (`ghW_ct`, `ghash1_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-- The call of `vg_ghash` and `ebp` back to `W`. -/
abbrev ghW : Prog isa := .seq ghCall (.block unscr)

/-- Ready for `ghW`: the arguments of `vg_ghash` in their registers, `nb`
blocks at `P`. -/
structure GhReady (Ctx St W SP : BitVec 32) (K yo : Nat) (P : BitVec 32) (nb : Nat) (s : State) : Prop where
  eax : s.gpr .eax = Ctx + BitVec.ofNat 32 240
  edx : s.gpr .edx = St + BitVec.ofNat 32 yo
  ebx : s.gpr .ebx = P
  edi : s.gpr .edi = BitVec.ofNat 32 nb
  ebp : s.gpr .ebp = W + BitVec.ofNat 32 512
  esi : s.gpr .esi = St
  esp : s.gpr .esp = SP
  ctxR : Covers [⟨w64 Ctx, 256⟩] (s.rd ++ s.wr)
  stW : Covers [⟨w64 St, 80⟩] s.wr
  wW : Covers [⟨w64 W, 2560⟩] s.wr
  ctx : s.mem.readW (w64 W + BitVec.ofNat 64 ctxO) 32 = Ctx
  fP : P.toNat + 16 * nb ≤ 2 ^ 32
  rP : Covers [⟨w64 P, 16 * nb⟩] (s.rd ++ s.wr)
  py : (⟨w64 St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨w64 P, 16 * nb⟩
  pw : (⟨w64 P, 16 * nb⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 256⟩
  pk : (below SP K).Disjoint ⟨w64 P, 16 * nb⟩

/-- What `ghW` leaves. -/
structure GhOut (Ctx St W SP : BitVec 32) (K yo : Nat) (P : BitVec 32) (nb : Nat) (s s' : State) : Prop where
  env : Env Ctx St W SP s'
  frame : Frame [⟨w64 St + BitVec.ofNat 64 yo, 16⟩, ⟨w64 W + BitVec.ofNat 64 512, 256⟩, below SP K] s.mem s'.mem
  out : blockAt s'.mem (w64 St + BitVec.ofNat 64 yo) =
    ghashFrom (blockAt s.mem (w64 Ctx + BitVec.ofNat 64 240)) (blockAt s.mem (w64 St + BitVec.ofNat 64 yo))
      (blocksAt s.mem (w64 P) nb)
  ebx : s'.gpr .ebx = s.gpr .ebx
  edi : s'.gpr .edi = s.gpr .edi
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

theorem GhReady.call {P : BitVec 32} {nb : Nat} {s : State} (h : GhReady Ctx St W SP K yo P nb s) :
    GhCall s (Ctx + BitVec.ofNat 32 240) (St + BitVec.ofNat 32 yo) P (W + BitVec.ofNat 32 512) nb := by
  have eH := L.aC (o := 240) (by decide)
  have eY := L.aS (o := yo) (by omega)
  have eS := L.aW (o := 512) (by decide)
  have k24 := L.k24
  have hsp : below (s.gpr .esp) 24 = below SP 24 := by rw [h.esp]
  have bsub : Region.Sub (below (s.gpr .esp) 24) (below SP K) := by rw [hsp]; exact L.below_sub k24
  refine ⟨h.eax, h.edx, h.ebx, h.edi, h.ebp, by rw [h.esp]; have := L.sp; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eH, eY]; exact L.ctx_st (by decide) (by omega)
  · rw [eH, eS]; exact L.ctx_w (by decide) (by decide)
  · rw [eY]; exact h.py
  · rw [eY, eS]; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · rw [eS]; exact h.pw
  · rw [eH]; exact (L.stk_ctx (by decide)).sub_left bsub
  · rw [eY]; exact (L.stk_st (by omega)).sub_left bsub
  · exact h.pk.sub_left bsub
  · rw [eS]; exact (L.stk_w (by decide)).sub_left bsub
  · rw [L.nC (by decide)]; have := L.fc; omega
  · rw [L.nS (by omega)]; have := L.fs; omega
  · exact h.fP
  · rw [L.nW (by decide)]; have := L.fw; omega
  · rw [eH]
    exact covers_cons (covers_off h.ctxR (by decide) (by decide)) (covers_cons h.rP covers_nil)
  · rw [eY, eS]
    exact covers_cons (covers_off h.stW (by omega) (by decide)) (covers_cons (covers_off h.wW (by decide)
      (by decide)) covers_nil)

theorem ghW_ok {P : BitVec 32} {nb : Nat} {s : State} (h : GhReady Ctx St W SP K yo P nb s) :
    WP isa ghW s (GhOut Ctx St W SP K yo P nb s) := by
  have eH := L.aC (o := 240) (by decide)
  have eY := L.aS (o := yo) (by omega)
  have eS := L.aW (o := 512) (by decide)
  refine WP.seq (WP.mono (gh_call (h.call L hyo)) fun s₁ g => ?_)
  have gf := g.frame
  have go := g.out
  rw [eY, eS] at gf
  rw [eH, eY] at go
  have hsp : below (s.gpr .esp) 24 = below SP 24 := by rw [h.esp]
  rw [hsp] at gf
  have fr : Frame [⟨w64 St + BitVec.ofNat 64 yo, 16⟩, ⟨w64 W + BitVec.ofNat 64 512, 256⟩, below SP K] s.mem s₁.mem :=
    gf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, by simp, L.below_sub L.k24⟩
  have bp₁ : s₁.gpr .ebp = W + BitVec.ofNat 32 512 := by rw [g.saved .ebp (by decide), h.ebp]
  refine WP.of_runBlock ⟨_, by xrun [unscr, bp₁], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fr, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, bp₁]; exact BitVec.add_sub_cancel _ _
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, g.saved .esi (by decide), h.esi]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, g.saved .esp (by decide), h.esp]
  · simp only [rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, g.rd, g.wr]; exact h.ctxR
  · simp only [wr_setReg, wr_arithFlags, g.wr]; exact h.stW
  · simp only [wr_setReg, wr_arithFlags, g.wr]; exact h.wW
  · simp only [mem_setReg, mem_arithFlags]
    rw [slot_frame fr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)).symm
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w (by decide)).symm), h.ctx]
  · simp only [mem_setReg, mem_arithFlags]; exact go
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, g.saved .ebx (by decide)]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, g.saved .edi (by decide)]
  · mems [g.rd]
  · mems [g.wr]

theorem ghW_ct {P : BitVec 32} {nb : Nat} : CT (GhReady Ctx St W SP K yo P nb) ghW := by
  refine CT.seq (J := fun s => s.gpr .ebp = W + BitVec.ofNat 32 512)
    (gh_ct (E := SP) fun s h => ⟨h.call L hyo, h.esp⟩) (fun s h => WP.mono (gh_call (h.call L hyo))
      fun s₁ g => by rw [g.saved .ebp (by decide), h.ebp]) ?_
  exact CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide)

omit hyo in
/-- `ghArgs yo`, from a state with an environment and the data in `ebx`, `edi`. -/
theorem ghArgs_ok {s : State} (he : Env Ctx St W SP s) :
    ∃ s', runBlock isa (ghArgs yo) s = some s' ∧ s'.gpr .eax = Ctx + BitVec.ofNat 32 240 ∧
      s'.gpr .edx = St + BitVec.ofNat 32 yo ∧ s'.gpr .ebp = W + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebp → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by xrun [ghArgs, he.ebp, he.esi, L.aW, he.wIn'], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, he.ctx]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, he.esi]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, he.ebp]
  · intro r h₁ h₂ h₃; simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, ite_false]
  all_goals rfl

end

/-! ## `ghash1` -/

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

omit hyo in
/-- `ghash1 yo b o`'s block, for the block at `P = b + o`. -/
theorem ghash1Pre_ok {s : State} (he : Env Ctx St W SP s) (b : Reg) (o : Nat) (hb : b = .esi ∨ b = .ebp)
    {P : BitVec 32} (hP : s.gpr b + BitVec.ofNat 32 o = P) (fP : P.toNat + 16 ≤ 2 ^ 32)
    (rP : Covers [⟨w64 P, 16⟩] (s.rd ++ s.wr))
    (py : (⟨w64 St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨w64 P, 16⟩)
    (pw : (⟨w64 P, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 256⟩)
    (pk : (below SP K).Disjoint ⟨w64 P, 16⟩) :
    WP isa (.block (([.mov .ebx (.reg b), .alu .add .ebx (imm o), .mov .edi (imm 1)] : List Instr) ++ ghArgs yo)) s
      fun s' => GhReady Ctx St W SP K yo P 1 s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, bx, di, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .ebx (.reg b), .alu .add .ebx (imm o), .mov .edi (imm 1)] s = some s₁ ∧
      s₁.gpr .ebx = P ∧ s₁.gpr .edi = BitVec.ofNat 32 1 ∧ (∀ r, r ≠ .ebx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    rcases hb with rfl | rfl
    all_goals
      refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hP]
      · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
      · intro r h₁ h₂; simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, h₁, h₂, ite_false]
      all_goals rfl
  have he₁ : Env Ctx St W SP s₁ := he.keep (g₁ _ (by decide) (by decide)) (g₁ _ (by decide) (by decide))
    (g₁ _ (by decide) (by decide)) rd₁ wr₁ (by rw [m₁])
  obtain ⟨s₂, run₂, ax, dx, bp, g₂, m₂, rd₂, wr₂⟩ := ghArgs_ok L (yo := yo) he₁
  refine WP.of_runBlock ⟨s₂, runBlock_app_of run₁ run₂, ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  have e₂ : ∀ {r}, r ≠ .eax → r ≠ .edx → r ≠ .ebp → s₂.gpr r = s₁.gpr r := fun h₁ h₂ h₃ => g₂ _ h₁ h₂ h₃
  refine ⟨ax, dx, by rw [e₂ (by decide) (by decide) (by decide), bx], by rw [e₂ (by decide) (by decide) (by decide), di],
    bp, by rw [e₂ (by decide) (by decide) (by decide)]; exact he₁.esi,
    by rw [e₂ (by decide) (by decide) (by decide)]; exact he₁.esp, ?_, ?_, ?_, ?_, fP, ?_, py, pw, pk⟩
  · rw [rd₂, wr₂]; exact he₁.ctxR
  · rw [wr₂]; exact he₁.stW
  · rw [wr₂]; exact he₁.wW
  · rw [m₂]; exact he₁.ctx
  · rw [rd₂, wr₂, rd₁, wr₁]; exact rP

/-- What `ghash1 yo b o` leaves, from `s`, for the block at `P`. -/
structure G1Out (Ctx St W SP : BitVec 32) (K yo : Nat) (P : BitVec 32) (s s' : State) : Prop where
  env : Env Ctx St W SP s'
  frame : Frame [⟨w64 St + BitVec.ofNat 64 yo, 16⟩, ⟨w64 W + BitVec.ofNat 64 512, 256⟩, below SP K] s.mem s'.mem
  out : blockAt s'.mem (w64 St + BitVec.ofNat 64 yo) =
    ghashFrom (blockAt s.mem (w64 Ctx + BitVec.ofNat 64 240)) (blockAt s.mem (w64 St + BitVec.ofNat 64 yo))
      [blockAt s.mem (w64 P)]
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem ghash1_ok {s : State} (he : Env Ctx St W SP s) (b : Reg) (o : Nat) (hb : b = .esi ∨ b = .ebp)
    {P : BitVec 32} (hP : s.gpr b + BitVec.ofNat 32 o = P) (fP : P.toNat + 16 ≤ 2 ^ 32)
    (rP : Covers [⟨w64 P, 16⟩] (s.rd ++ s.wr))
    (py : (⟨w64 St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨w64 P, 16⟩)
    (pw : (⟨w64 P, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 256⟩)
    (pk : (below SP K).Disjoint ⟨w64 P, 16⟩) :
    WP isa (ghash1 yo b o) s (G1Out Ctx St W SP K yo P s) :=
  WP.seq (WP.mono (ghash1Pre_ok L (yo := yo) he b o hb hP fP rP py pw pk) fun s₁ ⟨h, m, rd, wr⟩ =>
    WP.mono (ghW_ok L hyo h) fun s' g => ⟨g.env, m ▸ g.frame, by
      have := g.out; rw [m] at this; rw [this, blocksAt_one], by rw [g.rd, rd], by rw [g.wr, wr]⟩)

theorem ghash1_ct {I : State → Prop} (b : Reg) (o : Nat) (hbo : (b = .esi ∧ o = 32) ∨ (b = .ebp ∧ o = 96))
    {P : BitVec 32}
    (h : ∀ s, I s → Env Ctx St W SP s ∧ s.gpr b + BitVec.ofNat 32 o = P ∧ P.toNat + 16 ≤ 2 ^ 32 ∧
      Covers [⟨w64 P, 16⟩] (s.rd ++ s.wr) ∧
      (⟨w64 St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨w64 P, 16⟩ ∧
      (⟨w64 P, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 256⟩ ∧ (below SP K).Disjoint ⟨w64 P, 16⟩) :
    CT I (ghash1 yo b o) := by
  have hb : b = .esi ∨ b = .ebp := by rcases hbo with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  refine CT.seq (J := GhReady Ctx St W SP K yo P 1) ?_ (fun s hs => by
    obtain ⟨he, hP, fP, rP, py, pw, pk⟩ := h s hs
    exact WP.mono (ghash1Pre_ok L (yo := yo) he b o hb hP fP rP py pw pk) fun _ h => h.1) (ghW_ct L hyo)
  have hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.ebp, .esi], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
    have e₁ := (h s₁ h₁).1; have e₂ := (h s₂ h₂).1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [e₁.ebp, e₂.ebp]
    · rw [e₁.esi, e₂.esi]
  rcases hbo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hyo with rfl | rfl <;>
    exact CT.taint [.ebp, .esi] hr (by taint_decide)

end

end VG.Proof.AesGcm.X86
