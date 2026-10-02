import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase

/-!
# AES-GCM on x86-64: GHASH over one block of the state or of `T`

Untrusted: everything here is checked by Lean. `ghash1 yo b o` continues
the accumulator at `St + yo` over the block at `P = b + o` (`ghash1_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-- What a call of `vg_ghash` from `s` leaves in `s'`, for the accumulator
at `Y`, the working space at `W + 512` and the data `ds` (as blocks). -/
structure GhOut (s : State) (Ctx Y W SP : Addr) (ds : List Block) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨Y, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩, below SP 8] s.mem s'.mem
  out : blockAt s'.mem Y = ghashFrom (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (blockAt s.mem Y) ds

theorem GhOut.env {s s' : State} {Ctx St W SP Y : Addr} {ds : List Block} (h : GhOut s Ctx Y W SP ds s')
    (he : Env Ctx St W SP s) : Env Ctx St W SP s' := he.of_saved h.saved h.rd h.wr

theorem blocksAt_one (m : Mem) (p : Addr) : blocksAt m p 1 = [blockAt m p] := by
  simp [blocksAt]

/-- A call's arguments, from a state whose registers are its arguments. -/
theorem ghCall_of {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : Env Ctx St W SP s) {P : Addr} {n : Nat}
    (hdi : s.gpr .rdi = Ctx + BitVec.ofNat 64 240) (hsi : s.gpr .rsi = St + BitVec.ofNat 64 yo)
    (hdx : s.gpr .rdx = P) (hcx : s.gpr .rcx = BitVec.ofNat 64 n) (hr8 : s.gpr .r8 = W + BitVec.ofNat 64 512)
    (hn : 16 * n < 2 ^ 64)
    (hpy : (⟨St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16 * n⟩)
    (hpw : (⟨P, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below SP 8).Disjoint ⟨P, 16 * n⟩) (hpr : Covers [⟨P, 16 * n⟩] (s.rd ++ s.wr)) :
    GhCall s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) P (W + BitVec.ofNat 64 512) n := by
  have hk := he.rsp
  refine ⟨hdi, hsi, hdx, hcx, hr8, hn, L.ctx_st (by decide) (by omega), L.ctx_w (by decide) (by decide),
    hpy, L.st_w (by omega) (.inr ⟨by decide, by decide⟩), hpw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk]; exact L.stk_ctx (by decide)
  · rw [hk]; exact L.stk_st (by omega)
  · rw [hk]; exact hpk
  · rw [hk]; exact L.stk_w (by decide)
  · exact covers_cons (he.perm.ctxC (by decide)) (covers_cons hpr (covers_cons
      (covers_left (he.perm.stC (by omega))) (covers_left (he.perm.wC (by decide)))))
  · exact covers_cons (he.perm.stC (by omega)) (he.perm.wC (by decide))

/-- The call itself, from a state whose registers are its arguments. -/
theorem ghCall_ok (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : Env Ctx St W SP s) {P : Addr} {n : Nat}
    (hdi : s.gpr .rdi = Ctx + BitVec.ofNat 64 240) (hsi : s.gpr .rsi = St + BitVec.ofNat 64 yo)
    (hdx : s.gpr .rdx = P) (hcx : s.gpr .rcx = BitVec.ofNat 64 n) (hr8 : s.gpr .r8 = W + BitVec.ofNat 64 512)
    (hn : 16 * n < 2 ^ 64)
    (hpy : (⟨St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16 * n⟩)
    (hpw : (⟨P, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below SP 8).Disjoint ⟨P, 16 * n⟩) (hpr : Covers [⟨P, 16 * n⟩] (s.rd ++ s.wr)) :
    WP isa (.call v.gh.fn.name v.gh.fn.code) s
      (GhOut s Ctx (St + BitVec.ofNat 64 yo) W SP (blocksAt s.mem P n)) := by
  refine WP.mono (gh_call v.gh (ghCall_of L hyo he hdi hsi hdx hcx hr8 hn hpy hpw hpk hpr)) fun s' h =>
    ⟨h.rd, h.wr, h.saved, ?_, h.out⟩
  rw [← he.rsp]; exact h.frame

/-- What the arguments of `ghash1 yo b o` leave, for the block at `P = b + o`. -/
structure Gh1Args (s₀ : State) (Ctx St W SP : Addr) (yo : Nat) (P : Addr) (s₁ : State) : Prop where
  rdi : s₁.gpr .rdi = Ctx + BitVec.ofNat 64 240
  rsi : s₁.gpr .rsi = St + BitVec.ofNat 64 yo
  rdx : s₁.gpr .rdx = P
  rcx : s₁.gpr .rcx = BitVec.ofNat 64 1
  r8 : s₁.gpr .r8 = W + BitVec.ofNat 64 512
  keep : ∀ r ∈ calleeSaved, s₁.gpr r = s₀.gpr r
  mem : s₁.mem = s₀.mem
  rd : s₁.rd = s₀.rd
  wr : s₁.wr = s₀.wr

theorem gh1Args_ok {Ctx St W SP : Addr} {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {s : State} (he : Env Ctx St W SP s)
    (b : Reg) (o : Nat) (hb : b = .r14 ∨ b = .r15) {P : Addr} (hP : s.gpr b + BitVec.ofNat 64 o = P)
    (ho : o < 2 ^ 31) :
    WP isa (.block (ptr .rdi .r13 240 ++ ptr .rsi .r14 yo ++ ptr .rdx b o ++ ([.mov32 .rcx (imm 1)] : List Instr) ++
        ptr .r8 .r15 scrO)) s (Gh1Args s Ctx St W SP yo P) := by
  have h13 := he.r13; have h14 := he.r14; have h15 := he.r15
  rcases hb with rfl | rfl <;> rcases hyo with rfl | rfl
  all_goals
    refine WP.of_runBlock ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h13]
    · simp [gpr_setReg, h14]
    · simp [gpr_setReg, ← hP]
    · simp [gpr_setReg]
    · simp [gpr_setReg, h15]
    · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals rfl

/-- `ghash1 yo b o`, for the block at `P = b + o`. -/
theorem ghash1_ok (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : Env Ctx St W SP s) (b : Reg) (o : Nat) (hb : b = .r14 ∨ b = .r15) {P : Addr}
    (hP : s.gpr b + BitVec.ofNat 64 o = P) (ho : o < 2 ^ 31)
    (hpy : (⟨St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16⟩)
    (hpw : (⟨P, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below SP 8).Disjoint ⟨P, 16⟩) (hpr : Covers [⟨P, 16⟩] (s.rd ++ s.wr)) :
    WP isa (ghash1 v.callees yo b o) s
      (GhOut s Ctx (St + BitVec.ofNat 64 yo) W SP [blockAt s.mem P]) := by
  refine WP.seq (WP.mono (gh1Args_ok hyo he b o hb hP ho) fun s₁ a => ?_)
  have he₁ : Env Ctx St W SP s₁ := he.of_saved a.keep a.rd a.wr
  refine WP.mono (ghCall_ok v L hyo he₁ (P := P) (n := 1) a.rdi a.rsi a.rdx a.rcx a.r8 (by decide)
    (by simpa using hpy) (by simpa using hpw) (by simpa using hpk)
    (by rw [a.rd, a.wr]; simpa using hpr)) fun s' h => ?_
  exact ⟨h.rd.trans a.rd, h.wr.trans a.wr, fun r hr => (h.saved r hr).trans (a.keep r hr), a.mem ▸ h.frame,
    by rw [h.out, blocksAt_one, a.mem]⟩

/-- `ghash1 yo b o` in two runs, for the same block address `P`. -/
theorem ghash1_rel (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    (b : Reg) (o : Nat) (hb : b = .r14 ∨ b = .r15) (ho : o < 2 ^ 31) {P : Addr}
    (hpy : (⟨St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16⟩)
    (hpw : (⟨P, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below SP 8).Disjoint ⟨P, 16⟩)
    (hc : ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15, .rsp]) (.block (ptr .rdi .r13 240 ++
      ptr .rsi .r14 yo ++ ptr .rdx b o ++ ([.mov32 .rcx (imm 1)] : List Instr) ++ ptr .r8 .r15 scrO)) hc).isSome = true)
    {F₁ F₂ : State → Prop}
    (hF : ∀ s, (F₁ s ∨ F₂ s) → Env Ctx St W SP s ∧ s.gpr b + BitVec.ofNat 64 o = P ∧
      Covers [⟨P, 16⟩] (s.rd ++ s.wr)) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (ghash1 v.callees yo b o) fun _ _ => True := by
  have hA : ∀ s, (F₁ s ∨ F₂ s) → WP isa (.block (ptr .rdi .r13 240 ++ ptr .rsi .r14 yo ++ ptr .rdx b o ++
      [.mov32 .rcx (imm 1)] ++ ptr .r8 .r15 scrO)) s (fun s₁ => Env Ctx St W SP s₁ ∧
        GhCall s₁ (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) P (W + BitVec.ofNat 64 512) 1) :=
    fun s hs => WP.mono (gh1Args_ok hyo (hF s hs).1 b o hb (hF s hs).2.1 ho) fun s₁ a =>
      have he₁ := (hF s hs).1.of_saved a.keep a.rd a.wr
      ⟨he₁, ghCall_of L hyo he₁ a.rdi a.rsi a.rdx a.rcx a.r8 (by decide) (by simpa using hpy)
        (by simpa using hpw) (by simpa using hpk) (by rw [a.rd, a.wr]; simpa using (hF s hs).2.2)⟩
  have a := rel_wp (rel_taint (P := fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) [.r13, .r14, .r15, .rsp] (fun s₁ s₂ h r hr => by
      have e₁ := (hF s₁ (.inl h.1)).1; have e₂ := (hF s₂ (.inr h.2)).1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [e₁.r13, e₂.r13]
      · rw [e₁.r14, e₂.r14]
      · rw [e₁.r15, e₂.r15]
      · rw [e₁.rsp, e₂.rsp]) hc)
    (fun _ _ h => h) (fun s h => hA s (.inl h)) (fun s h => hA s (.inr h))
  refine RelCT.seq a (gh_rel v.gh fun s₁ s₂ h => ⟨_, _, _, _, _, h.2.1.2, h.2.2.2, ?_⟩)
  rw [h.2.1.1.rsp, h.2.2.1.rsp]

end VG.Proof.AesGcm.X86_64
