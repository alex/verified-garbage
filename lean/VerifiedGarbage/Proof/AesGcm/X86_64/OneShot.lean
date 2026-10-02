import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCrypt

/-!
# AES-GCM on x86-64: what `seal` and `open` share

Untrusted: everything here is checked by Lean. Their streaming state is in
`work`, at `W + 16`. The entry keeps the public arguments in `W`
(`oneEntry_ok`); `oneAad` computes `J₀` and absorbs the additional data,
padded (`oneAad_ok`); `oneCrypt` runs counter mode over the data from the
first counter block (`oneCrypt_ok`); and `oneTag o` absorbs the ciphertext,
padded, and writes the tag to `W + o` (`oneTag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- What the entry of `seal` and `open` writes in `W`. -/
abbrev oneR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 112⟩

/-- What the precondition of `seal` (`k = 3`) and `open` (`k = 4`) gives. -/
structure OneCtx (s : State) (k : Nat) (Ctx W SP Np A D : Addr) (nl al n : Nat) : Prop where
  lay : Lay Ctx (W + BitVec.ofNat 64 16) W SP
  perm : Perm Ctx (W + BitVec.ofNat 64 16) W s
  ww : W.toNat + 2560 ≤ 2 ^ 64
  args : ∀ i < k, InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 (8 * (i + 1))) 8
  dA : (⟨SP + BitVec.ofNat 64 8, 8 * k⟩ : Region).Disjoint ⟨W, 2560⟩
  nonce : DataOk (W + BitVec.ofNat 64 16) W SP s Np nl
  aad : DataOk (W + BitVec.ofNat 64 16) W SP s A al
  data : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n
  rD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  rW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩
  dE : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩
  dAD : (⟨SP + BitVec.ofNat 64 8, 8 * k⟩ : Region).Disjoint ⟨D, n⟩
  rounds : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14

theorem OneCtx.of {k : Nat} {s : State} (hp : Proof.AesGcm.onePre k s) :
    OneCtx s k (s.gpr .rdi) (stackArg s 2) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (stackArg s 0)
      (s.gpr .rcx).toNat (s.gpr .r9).toNat (stackArg s 1).toNat := by
  simp only [Proof.AesGcm.onePre, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.args,
    Proof.AesGcm.arg, Proof.AesGcm.rounds] at hp
  obtain ⟨hrd, hwr, d_cd, d_cw, d_nd, d_nw, d_ad, d_aw, d_dw, d_da, d_wa, r_d, r_w, k_c, k_n, k_a, k_d, k_w,
    wc, wn, wa, wd, ww, wsp, hR⟩ := hp
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at hrd d_da d_wa
  have hSt : (⟨stackArg s 2 + BitVec.ofNat 64 16, 80⟩ : Region).Sub ⟨stackArg s 2, 2560⟩ := Lay.wSub (by decide)
  have L : Lay (s.gpr .rdi) (stackArg s 2 + BitVec.ofNat 64 16) (stackArg s 2) (s.gpr .rsp) := by
    refine ⟨wc, ?_, ww, d_cw.sub_right hSt, d_cw, ?_, ?_, k_c, k_w.sub_right hSt, k_w⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le ((stackArg s 2).toNat + 16 % 2 ^ 64) (2 ^ 64)
      omega
    · simpa using Offset.disjoint (stackArg s 2) (d := 16) (n := 80) (e := 0) (k := 16) (.inr (by decide))
        (by omega) (by omega)
    · exact Offset.disjoint (stackArg s 2) (d := 16) (n := 80) (e := 96) (k := 2464) (.inl (by decide))
        (by omega) (by omega)
  have pm : Covers [⟨s.gpr .rsp + BitVec.ofNat 64 8, 8 * k⟩] (s.rd ++ s.wr) := by
    rw [hrd]
    exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))
  have pW : Covers [⟨stackArg s 2, 2560⟩] s.wr := by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  refine ⟨L, ⟨?_, covers_off pW (show 16 + 80 ≤ 2560 by decide) (by decide), pW⟩, ww, fun i hi => ?_,
    d_wa.symm, ⟨?_, by have := (s.gpr .rcx).isLt; omega, wn, d_nw.sub_right hSt, d_nw, k_n⟩,
    ⟨?_, by have := (s.gpr .r9).isLt; omega, wa, d_aw.sub_right hSt, d_aw, k_a⟩,
    ⟨⟨?_, by have := (stackArg s 1).isLt; omega, wd, d_dw.sub_right hSt, d_dw, k_d⟩, ?_, d_cd⟩,
    r_d, r_w, d_dw, d_da.symm, hR⟩
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
  · have := in_off pm (d := 8 * i) (n := 8) (by omega) (by omega)
    rwa [add_ofNat_assoc, show 8 + 8 * i = 8 * (i + 1) by omega] at this
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
  · rw [hwr]; exact covers_left (covers_of_mem (List.mem_cons_self ..))
  · rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

/-- After `oneEntry`. -/
structure OneEntry (s₀ : State) (Ctx W SP A D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  rounds : RoundsAt s.mem W (s₀.gpr .rsi).toNat
  aad : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .r9
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  r12 : s.gpr .r12 = s₀.gpr .rdx
  rbp : s.gpr .rbp = s₀.gpr .rcx
  rsp : s.gpr .rsp = SP
  saved : SavedAt s.mem W s₀
  frame : Frame [oneR W] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem oneEntry_ok {s : State} {k : Nat} (hk : 3 ≤ k) {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s k Ctx W SP Np A D nl al n) (hCtx : s.gpr .rdi = Ctx) (hSP : s.gpr .rsp = SP) (hA : s.gpr .r8 = A)
    (hD : stackArg s 0 = D) (hn : (stackArg s 1).toNat = n) (hW : stackArg s 2 = W) :
    WP isa (.block oneEntry) s (OneEntry s Ctx W SP A D n) := by
  have hW' : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W := by rw [← hW, ← hSP]; rfl
  have hD' : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D := by rw [← hD, ← hSP]; rfl
  have hn' : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n := by
    rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hSP]; rfl
  have a₀ := C.args 0 (by omega)
  have a₁ := C.args 1 (by omega)
  have a₂ := C.args 2 (by omega)
  simp only [Nat.zero_add, Nat.mul_one] at a₀ a₁ a₂
  obtain ⟨s₀, run₀, hax₀, hg₀, hm₀, hrd₀, hwr₀⟩ : ∃ s₀', runBlock isa [.mov .rax (.mem (at_ .rsp 24))] s = some s₀' ∧
      s₀'.gpr .rax = W ∧ (∀ r, r ≠ .rax → s₀'.gpr r = s.gpr r) ∧ s₀'.mem = s.mem ∧ s₀'.rd = s.rd ∧ s₀'.wr = s.wr := by
    refine ⟨_, by xrun [hSP, a₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hW']
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  have hperm₀ : Perm Ctx (W + BitVec.ofNat 64 16) W s₀ := C.perm.of_eq hrd₀ hwr₀
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s₀ .rax hax₀ hperm₀.w
  have hsv₁' : SavedAt s₁.mem W s := by
    intro p hp; rw [hsv₁ p hp]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg₀ _ (by decide)
  have w₁ := in_off C.perm.w (show 176 + 8 ≤ 2560 by decide) (by decide)
  have w₂ := in_off C.perm.w (show 232 + 8 ≤ 2560 by decide) (by decide)
  have w₃ := in_off C.perm.w (show 184 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off C.perm.w (show 200 + 8 ≤ 2560 by decide) (by decide)
  have w₅ := in_off C.perm.w (show 208 + 8 ≤ 2560 by decide) (by decide)
  rw [← hwr₀, ← hwr₁] at w₁ w₂ w₃ w₄ w₅
  rw [← hrd₀, ← hwr₀, ← hrd₁, ← hwr₁] at a₀ a₁
  have dAW : ∀ i < 3, ∀ (m : Mem) (k' : Nat), Frame [⟨W + BitVec.ofNat 64 128, k'⟩] s.mem m → k' ≤ 2432 →
      m.readW (SP + BitVec.ofNat 64 (8 * (i + 1))) 64 = s.mem.readW (SP + BitVec.ofNat 64 (8 * (i + 1))) 64 :=
    fun i hi m k' hf hk' => hf.readW (r := ⟨SP + BitVec.ofNat 64 (8 * (i + 1)), 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := (C.dA.sub_left (show Region.Sub ⟨SP + BitVec.ofNat 64 (8 * (i + 1)), 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * k⟩ by
          rw [show 8 * (i + 1) = 8 + 8 * i by omega, ← add_ofNat_assoc]; exact Offset.sub_base _ (by omega)))
        exact this.sub_right (Lay.wSub (by omega))) (by decide)
  have hD₁ : s₁.mem.readW (SP + BitVec.ofNat 64 8) 64 = D := by
    have := dAW 0 (by decide) _ 48 (hm₀ ▸ f₁) (by decide); simpa [hD'] using this
  have hn₁ : s₁.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n := by
    have := dAW 1 (by decide) _ 48 (hm₀ ▸ f₁) (by decide); simpa [hn'] using this
  have sA : ∀ e d, (e = 8 ∨ e = 16) → 176 ≤ d → d + 8 ≤ 240 →
      Mem.Sep (SP + BitVec.ofNat 64 e) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) := by
    intro e d he h₁ h₂
    refine Region.Disjoint.sep (?_ : (⟨SP + BitVec.ofNat 64 e, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 8⟩)
      (Region.contains_self _ _) (Region.contains_self _ _)
    have hs : Region.Sub ⟨SP + BitVec.ofNat 64 e, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * k⟩ := by
      rcases he with rfl | rfl
      · exact Region.sub_prefix (by omega)
      · rw [show (16 : Nat) = 8 + 8 by rfl, ← add_ofNat_assoc]; exact Offset.sub_base _ (by omega)
    exact (C.dA.sub_left hs).sub_right (Lay.wSub (by omega))
  have p₁ := sA 8 176 (.inl rfl) (by decide) (by decide)
  have p₂ := sA 8 232 (.inl rfl) (by decide) (by decide)
  have p₃ := sA 8 184 (.inl rfl) (by decide) (by decide)
  have p₄ := sA 16 176 (.inr rfl) (by decide) (by decide)
  have p₅ := sA 16 232 (.inr rfl) (by decide) (by decide)
  have p₆ := sA 16 184 (.inr rfl) (by decide) (by decide)
  have p₇ := sA 16 200 (.inr rfl) (by decide) (by decide)
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega) (by omega)
  have q₀ := sep 176 232 (by decide) (by decide) (by decide)
  have q₁ := sep 176 184 (by decide) (by decide) (by decide)
  have q₂ := sep 176 200 (by decide) (by decide) (by decide)
  have q₃ := sep 176 208 (by decide) (by decide) (by decide)
  have q₄ := sep 232 184 (by decide) (by decide) (by decide)
  have q₅ := sep 232 200 (by decide) (by decide) (by decide)
  have q₆ := sep 232 208 (by decide) (by decide) (by decide)
  have q₇ := sep 184 200 (by decide) (by decide) (by decide)
  have q₈ := sep 184 208 (by decide) (by decide) (by decide)
  have q₉ := sep 200 208 (by decide) (by decide) (by decide)
  have e : oneEntry = [.mov .rax (.mem (at_ .rsp 24))] ++ save .rax ++
      [.mov .r15 (.reg .rax), .mov .r14 (.reg .r15), .alu .add .r14 (imm 16), .mov .r13 (.reg .rdi),
        .store (at_ .r15 roundsO) .rsi, .store (at_ .r15 aadO) .r8, .store (at_ .r15 alenO) .r9,
        .mov .rax (.mem (at_ .rsp 8)), .store (at_ .r15 dataO) .rax, .mov .rax (.mem (at_ .rsp 16)),
        .store (at_ .r15 lenO) .rax, .mov .r12 (.reg .rdx), .mov .rbp (.reg .rcx)] := by
    simp [oneEntry, ptr, stO]
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hsp, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .rax), .mov .r14 (.reg .r15), .alu .add .r14 (imm 16), .mov .r13 (.reg .rdi),
        .store (at_ .r15 roundsO) .rsi, .store (at_ .r15 aadO) .r8, .store (at_ .r15 alenO) .r9,
        .mov .rax (.mem (at_ .rsp 8)), .store (at_ .r15 dataO) .rax, .mov .rax (.mem (at_ .rsp 16)),
        .store (at_ .r15 lenO) .rax, .mov .r12 (.reg .rdx), .mov .rbp (.reg .rcx)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = W + BitVec.ofNat 64 16 ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .r12 = s.gpr .rdx ∧
      s₂.gpr .rbp = s.gpr .rcx ∧ s₂.gpr .rsp = SP ∧
      s₂.mem = ((((s₁.mem.writeW (W + BitVec.ofNat 64 176) (s.gpr .rsi)).writeW (W + BitVec.ofNat 64 232) A).writeW
        (W + BitVec.ofNat 64 184) (s.gpr .r9)).writeW (W + BitVec.ofNat 64 200) D).writeW
          (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 n) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have g : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r := fun r h => by rw [hg₁, hg₀ r h]
    have hax₁ : s₁.gpr .rax = W := by rw [hg₁, hax₀]
    have hsp₁ : s₁.gpr .rsp = SP := by rw [g _ (by decide), hSP]
    have hrdx := g .rdx (by decide); have hrdi := g .rdi (by decide); have hrsi := g .rsi (by decide)
    have hrcx := g .rcx (by decide); have hr8 := g .r8 (by decide); have hr9 := g .r9 (by decide)
    refine ⟨_, by xrun [hax₁, hsp₁, w₁, w₂, w₃, w₄, w₅, a₀, a₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hax₁]
    · simp [gpr_setReg, gpr_arithFlags, hax₁]
    · simp [gpr_setReg, gpr_arithFlags, hrdi, hCtx]
    · simp [gpr_setReg, gpr_arithFlags, hrdx]
    · simp [gpr_setReg, gpr_arithFlags, hrcx]
    · simp [gpr_setReg, gpr_arithFlags, hsp₁]
    · simp (disch := first | decide | assumption) [gpr_setReg, mem_setReg, mem_arithFlags, gpr_arithFlags,
        Mem.readW_writeW_sep, hD₁, hn₁, hrsi, hr8, hr9, hA]
    all_goals rfl
  rw [e]
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.of_runBlock ⟨s₁, run₁,
    WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩⟩))
  have hrd' : s₂.rd = s.rd := hrd₂.trans (hrd₁.trans hrd₀)
  have hwr' : s₂.wr = s.wr := hwr₂.trans (hwr₁.trans hwr₀)
  have f₂ : Frame [⟨W + BitVec.ofNat 64 176, 64⟩] s₁.mem s₂.mem := by
    rw [hm₂]
    have c : ∀ d, 176 ≤ d → d + 8 ≤ 240 → (⟨W + BitVec.ofNat 64 176, 64⟩ : Region).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 176 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 232 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))
  have rd : ∀ d (v : BitVec 64), (d = 176 ∧ v = s.gpr .rsi) ∨ (d = 232 ∧ v = A) ∨ (d = 184 ∧ v = s.gpr .r9) ∨
      (d = 200 ∧ v = D) ∨ (d = 208 ∧ v = BitVec.ofNat 64 n) → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = v := by
    intro d v h
    rw [hm₂]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp (disch := first | decide | assumption) only [Mem.readW_writeW_self64,
        Mem.readW_writeW_sep]
  refine ⟨⟨h13, h14, h15, hsp, C.perm.of_eq hrd' hwr'⟩, ⟨?_, C.rounds⟩, rd 232 _ (.inr (.inl ⟨rfl, rfl⟩)),
    rd 184 _ (.inr (.inr (.inl ⟨rfl, rfl⟩))), rd 200 _ (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))),
    rd 208 _ (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩)))), h12, hbp, hsp, ?_, ?_, hrd', hwr'⟩
  · rw [rd 176 _ (.inl ⟨rfl, rfl⟩)]; exact BitVec.eq_of_toNat_eq (by simp)
  · exact hsv₁'.frame f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by decide)) (by have := C.ww; omega) (by have := C.ww; omega)
  · rw [hm₀] at f₁
    exact (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- What `seal` and `open` write after their entry: `W` but for the saved
registers and the kept values, the data and the stack. -/
abbrev oneFrame (W D SP : Addr) (n : Nat) : List Region :=
  [⟨W, 128⟩, ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 2320⟩, ⟨D, n⟩, below SP 8]

/-- `oneFrame` without the data: what the pieces but `crypt` write. -/
abbrev wFrame (W SP : Addr) : List Region :=
  [⟨W, 128⟩, ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 2320⟩, below SP 8]

theorem wFrame_one {W D SP : Addr} {n : Nat} {m m' : Mem} (h : Frame (wFrame W SP) m m') :
    Frame (oneFrame W D SP n) m m' := h.mono fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with rfl | rfl | rfl | rfl <;> simp

theorem w_wFrame {W SP : Addr} {d k : Nat} (h : d + k ≤ 128 ∨ (216 ≤ d ∧ d + k ≤ 224) ∨ (240 ≤ d ∧ d + k ≤ 2560)) :
    ∃ r ∈ wFrame W SP, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r := by
  rcases h with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨⟨W, 128⟩, by simp, Offset.sub_base W h⟩
  · exact ⟨⟨W + BitVec.ofNat 64 216, 8⟩, by simp, Offset.sub _ h₁ (by omega)⟩
  · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ h₁ (by omega)⟩

theorem st_wFrame {W SP : Addr} {d k : Nat} (h : d + k ≤ 80) :
    ∃ r ∈ wFrame W SP, Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ r := by
  rw [add_ofNat_assoc]; exact w_wFrame (.inl (by omega))

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

omit L in
/-- A part of `W` in `oneFrame`. -/
theorem w_oneFrame {D SP : Addr} {n d k : Nat} (h : d + k ≤ 128 ∨ (216 ≤ d ∧ d + k ≤ 224) ∨ (240 ≤ d ∧ d + k ≤ 2560)) :
    ∃ r ∈ oneFrame W D SP n, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r := by
  rcases h with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨⟨W, 128⟩, by simp, Offset.sub_base W h⟩
  · exact ⟨⟨W + BitVec.ofNat 64 216, 8⟩, by simp, Offset.sub _ h₁ (by omega)⟩
  · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ h₁ (by omega)⟩

omit L in
theorem st_oneFrame {D SP : Addr} {n d k : Nat} (h : d + k ≤ 80) :
    ∃ r ∈ oneFrame W D SP n, Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ r := by
  rw [add_ofNat_assoc]; exact w_oneFrame (.inl (by omega))

/-- The kept values are outside `oneFrame`. -/
theorem kept_oneFrame {D : Addr} {n d : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (h : (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240)) :
    ∀ r ∈ oneFrame W D SP n, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := 8) (d := 0) (k := 128) (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (by omega) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (hD.sub_right (Lay.wSub (by omega))).symm
  · exact (L.stk_w (by omega)).symm

theorem saved_oneFrame {D : Addr} {n : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ oneFrame W D SP n, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 128) (n := 48) (d := 0) (k := 128) (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (hD.sub_right (Lay.wSub (by decide))).symm
  · exact (L.stk_w (by decide)).symm

end

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- After `oneAad`: `J₀`, the additional data absorbed and padded, and the
first counter block. -/
structure OneAad (Ctx W SP : Addr) (H : Block) (iv a : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H iv
  abs : Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
    (a ++ zeros (padLen a.length))
  cb : blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  frame : Frame (wFrame W SP) m₀ s.mem

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

omit L in
theorem j0Frame_one {m m' : Mem} (h : Frame (j0Frame (W + BitVec.ofNat 64 16) W SP) m m') :
    Frame (wFrame W SP) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact w_wFrame (.inl (by decide))
  · exact w_wFrame (.inl (by decide))
  · exact w_wFrame (.inr (.inl ⟨by decide, by decide⟩))
  · exact w_wFrame (.inr (.inr ⟨by decide, by decide⟩))
  · exact ⟨below SP 8, by simp, fun _ h => h⟩

omit L in
theorem absFrame_one {m m' : Mem} (h : Frame (absFrame (W + BitVec.ofNat 64 16) W SP 16) m m') :
    Frame (wFrame W SP) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact st_wFrame (by decide)
  · exact st_wFrame (by decide)
  · exact w_wFrame (.inr (.inr ⟨by decide, by decide⟩))
  · exact ⟨below SP 8, by simp, fun _ h => h⟩

omit L in
theorem tFrame_one {m m' : Mem} (h : Frame (tFrame (W + BitVec.ofNat 64 16) W SP 16) m m') :
    Frame (wFrame W SP) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact st_wFrame (by decide)
  · exact w_wFrame (.inl (by decide))
  · exact w_wFrame (.inr (.inr ⟨by decide, by decide⟩))
  · exact ⟨below SP 8, by simp, fun _ h => h⟩

omit L in
theorem crFrame_one {D : Addr} {n : Nat} {m m' : Mem} (h : Frame (crFrame (W + BitVec.ofNat 64 16) W SP D n) m m') :
    Frame (oneFrame W D SP n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩
  · exact st_oneFrame (by decide)
  · exact w_oneFrame (.inr (.inr ⟨by decide, by decide⟩))
  · exact ⟨below SP 8, by simp, fun _ h => h⟩

omit L in
theorem tagFrame_one {o : Nat} (ho : o = 0 ∨ o = 112) {m m' : Mem}
    (h : Frame (tagFrame (W + BitVec.ofNat 64 16) W SP o) m m') : Frame (wFrame W SP) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact w_wFrame (.inl (by decide))
  · exact w_wFrame (.inl (by decide))
  · exact w_wFrame (.inl (by omega))
  · exact w_wFrame (.inr (.inr ⟨by decide, by decide⟩))
  · exact ⟨below SP 8, by simp, fun _ h => h⟩

/-- `oneAad`. -/
theorem oneAad_ok {D Np A : Addr} {nl al n : Nat} {H : Block} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) (h12 : s.gpr .r12 = Np) (hbp : s.gpr .rbp = BitVec.ofNat 64 nl)
    (hN : DataOk (W + BitVec.ofNat 64 16) W SP s Np nl) (hAd : DataOk (W + BitVec.ofNat 64 16) W SP s A al)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (haad : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al) :
    WP isa (oneAad v.callees) s (OneAad Ctx W SP H (bytesAt s.mem Np nl) (bytesAt s.mem A al) s.mem) := by
  refine WP.seq (WP.mono (WP.with_rdwr (j0_ok v L ⟨he, hH, h12, hbp, hN⟩)) fun s₁ ⟨jo, hrd₁, hwr₁⟩ => ?_)
  have f₁ := wFrame_one (D := D) (n := n) (j0Frame_one jo.frame)
  have he₁ := jo.env
  have kp : ∀ {m m' : Mem}, Frame (oneFrame W D SP n) m m' → ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
    fun hf d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L hDW hd)
      (by decide)
  have q₁ := he₁.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have q₂ := he₁.perm.wR (show 184 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, h12₂, hbp₂, hbx₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .r12 (.mem (at_ .r15 aadO)),
      .mov .rbp (.mem (at_ .r15 alenO)), .mov32 .rbx (imm 0)] s₁ = some s₂ ∧
      s₂.gpr .r12 = A ∧ s₂.gpr .rbp = BitVec.ofNat 64 al ∧ s₂.gpr .rbx = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [he₁.r15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, kp f₁ 232 (.inr ⟨by decide, by decide⟩), haad]
    · simp [gpr_setReg, kp f₁ 184 (.inl ⟨by decide, by decide⟩), hal]
    · simp [gpr_setReg]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have dAj : ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W SP, (⟨A, al⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hAd.st
    · exact hAd.w.sub_right (Lay.wSub (by decide))
    · exact hAd.w.sub_right (Lay.wSub (by decide))
    · exact hAd.w.sub_right (Lay.wSub (by decide))
    · exact hAd.stk.symm
  have ha₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := by
    rw [hm₂]; exact bytesAt_frame jo.frame dAj (by have := hAd.lt; omega)
  have hai : AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 H [] A al s₂ :=
    ⟨he₂, h12₂, hbp₂, hbx₂, hAd.of_eq (by rw [hrd₂, hrd₁]) (by rw [hwr₂, hwr₁]), by rw [hm₂]; exact jo.hH⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absorb_ok v L (yo := 16) (.inr rfl) hai)) fun s₃ ⟨ho, hrd₃, hwr₃⟩ => ?_)
  rw [List.nil_append, ha₂] at ho
  have he₃ := ho.env
  have f₃ := wFrame_one (D := D) (n := n) (absFrame_one ho.frame)
  rw [hm₂] at f₃
  have q₃ := he₃.perm.wR (show 184 + 8 ≤ 2560 by decide)
  obtain ⟨s₄, run₄, hbx₄, hg₄, hm₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .alu .and .rbx (imm 15)] s₃ = some s₄ ∧ s₄.gpr .rbx = BitVec.ofNat 64 ((bytesAt s.mem A al).length % 16) ∧
      (∀ r, r ≠ .rbx → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    have hand := and15 (BitVec.ofNat 64 al)
    rw [imm_eq (by decide), toNat_ofNat_of_lt (by have := hAd.lt; omega)] at hand
    refine ⟨_, by xrun [he₃.r15, q₃], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, kp f₃ 184 (.inl ⟨by decide, by decide⟩),
        kp f₁ 184 (.inl ⟨by decide, by decide⟩), hal, hand, length_bytesAt]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide)) hrd₄ hwr₄
  have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ho.frame (ctx_absFrame L (.inr rfl)), hm₂, jo.hH]
  refine WP.mono (flush_ok v L (yo := 16) (.inr rfl) (H := H) ⟨he₄, by rw [hm₄, hH₃]⟩ hbx₄) fun s₅ hf => ?_
  rw [hm₄] at hf
  have dS0 : ∀ r ∈ absFrame (W + BitVec.ofNat 64 16) W SP 16, (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r ∧
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨L.st_st (.inl (by decide)) (by decide) (by decide), L.st_st (.inr (by decide)) (by decide) (by decide)⟩
    · exact ⟨L.st_st (.inl (by decide)) (by decide) (by decide), L.st_st (.inr (by decide)) (by decide) (by decide)⟩
    · exact ⟨L.st_w (by decide) (.inr ⟨by decide, by decide⟩), L.st_w (by decide) (.inr ⟨by decide, by decide⟩)⟩
    · exact ⟨(L.stk_st (by decide)).symm, (L.stk_st (by decide)).symm⟩
  have dT0 : ∀ r ∈ tFrame (W + BitVec.ofNat 64 16) W SP 16, (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r ∧
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨L.st_st (.inl (by decide)) (by decide) (by decide), L.st_st (.inr (by decide)) (by decide) (by decide)⟩
    · exact ⟨L.st_w (by decide) (.inr ⟨by decide, by decide⟩), L.st_w (by decide) (.inr ⟨by decide, by decide⟩)⟩
    · exact ⟨L.st_w (by decide) (.inr ⟨by decide, by decide⟩), L.st_w (by decide) (.inr ⟨by decide, by decide⟩)⟩
    · exact ⟨(L.stk_st (by decide)).symm, (L.stk_st (by decide)).symm⟩
  have hj₅ : blockAt s₅.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H (bytesAt s.mem Np nl) := by
    have e₁ : blockAt s₅.mem (W + BitVec.ofNat 64 16) = blockAt s₃.mem (W + BitVec.ofNat 64 16) :=
      blockAt_frame hf.frame fun r hr => by simpa using (dT0 r hr).1
    have e₂ : blockAt s₃.mem (W + BitVec.ofNat 64 16) = blockAt s₁.mem (W + BitVec.ofNat 64 16) := by
      rw [blockAt_frame ho.frame fun r hr => by simpa using (dS0 r hr).1, hm₂]
    rw [e₁, e₂]; exact jo.j0
  refine ⟨hf.env, hf.hH, hj₅, hf.abs (ho.abs (by rw [hm₂]; exact Proof.Gcm.absorbed_nil _ jo.y)), ?_, ?_⟩
  · rw [blockAt_frame hf.frame (fun r hr => (dT0 r hr).2), blockAt_frame ho.frame (fun r hr => (dS0 r hr).2), hm₂]
    exact jo.cb
  · have g₁ := j0Frame_one jo.frame
    have g₃ := absFrame_one ho.frame
    rw [hm₂] at g₃
    exact (g₁.trans g₃).trans (tFrame_one hf.frame)

end

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 zeros padLen ghashFrom ghash blocks
  ofBytes toBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

theorem padded_eq (a c : List Byte) :
    a ++ zeros (padLen a.length) ++ c ++ zeros (padLen (a ++ zeros (padLen a.length) ++ c).length) = padded a c := by
  by_cases hc : c = []
  · subst hc
    have : padLen (a ++ zeros (padLen a.length)).length = 0 := by
      apply Proof.Gcm.padLen_of_mod
      simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
    rw [List.append_nil, this, padded, Proof.Gcm.ghashInput_nil]
    simp [zeros]
  · rw [padded, Proof.Gcm.ghashInput_of_ne hc]

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `oneCrypt`: counter mode over the data, from the first counter block. -/
theorem oneCrypt_ok {R : Nat} {icb : Block} {D : Addr} {n : Nat} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hR : RoundsAt s.mem W R)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D) (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hd : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n) :
    WP isa (oneCrypt v.callees) s fun s' => CrOut Ctx (W + BitVec.ofNat 64 16) W SP R icb 0 D n s.mem s' ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, h12, hbp, hbx, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)] s = some s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 (0 % 16) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hdat]
    · simp [gpr_setReg, hlen]
    · simp [gpr_setReg]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have := WP.with_rdwr (crypt_ok v L (R := R) (icb := icb) (P := 0)
    ⟨he₁, h12, hbp, hbx, hd.of_eq hrd₁ hwr₁, by rw [hm₁]; exact hR⟩)
  rw [hm₁] at this
  exact WP.mono this fun s' ⟨h, a, b⟩ => ⟨h, a.trans hrd₁, b.trans hwr₁⟩

end

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 zeros padLen ghashFrom ghash blocks
  ofBytes toBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `oneTag o`: the ciphertext absorbed, padded, and the tag into `W + o`. -/
theorem oneTag_ok {o R : Nat} (ho : o = 0 ∨ o = 112) {D : Addr} {n al : Nat} {H : Block} {a : List Byte} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hR : RoundsAt s.mem W R) (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al) (ha : a.length = al)
    (hd : DataOk (W + BitVec.ofNat 64 16) W SP s D n) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hCD : (⟨Ctx, 256⟩ : Region).Disjoint ⟨D, n⟩) :
    WP isa (oneTag v.callees o) s fun s' => Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧
      Frame (wFrame W SP) s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
          (a ++ zeros (padLen a.length)) →
        bytesAt s'.mem (W + BitVec.ofNat 64 o) 16 =
          toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s.mem D n))))
            [ofBytes (lensBlock a.length n)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16)))) := by
  have kp : ∀ {m m' : Mem}, Frame (oneFrame W D SP n) m m' → ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
    fun hf d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L hDW hd)
      (by decide)
  have hlt := hd.lt
  generalize hx : a ++ zeros (padLen a.length) = x
  have hx16 : x.length % 16 = 0 := by
    rw [← hx]; simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  have q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, h12, hbp, hbx, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)] s = some s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 (x.length % 16) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hdat]
    · simp [gpr_setReg, hlen]
    · simp [gpr_setReg, hx16]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have hai : AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 H x D n s₁ :=
    ⟨he₁, h12, hbp, hbx, hd.of_eq hrd₁ hwr₁, by rw [hm₁, hH]⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absorb_ok v L (yo := 16) (.inr rfl) hai)) fun s₂ ⟨ho', hrd₂, hwr₂⟩ => ?_)
  rw [hm₁] at ho'
  have he₂ := ho'.env
  have g₂ := absFrame_one ho'.frame
  have f₂ := wFrame_one (D := D) (n := n) g₂
  have q₃ := he₂.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 lenO)),
      .alu .and .rbx (imm 15)] s₂ = some s₃ ∧ s₃.gpr .rbx = BitVec.ofNat 64 ((x ++ bytesAt s.mem D n).length % 16) ∧
      (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    have hand := and15 (BitVec.ofNat 64 n)
    rw [imm_eq (by decide), toNat_ofNat_of_lt hlt] at hand
    have e : (x ++ bytesAt s.mem D n).length % 16 = n % 16 := by
      simp only [List.length_append, length_bytesAt]; omega
    refine ⟨_, by xrun [he₂.r15, q₃], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, kp f₂ 208 (.inl ⟨by decide, by decide⟩), hlen, hand, e]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  have hH₂ : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ho'.frame (ctx_absFrame L (.inr rfl)), hH]
  refine WP.seq (WP.mono (WP.with_rdwr (flush_ok v L (yo := 16) (.inr rfl) (H := H) ⟨he₃, by rw [hm₃, hH₂]⟩ hbx₃))
    fun s₄ ⟨hf, hrd₄, hwr₄⟩ => ?_)
  rw [hm₃] at hf
  have he₄ := hf.env
  have g₄ := tFrame_one hf.frame
  have f₄ := wFrame_one (D := D) (n := n) g₄
  have q₄ := he₄.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have q₅ := he₄.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₅, run₅, hbx₅, hbp₅, hg₅, hm₅, hrd₅, hwr₅⟩ : ∃ s₅, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .mov .rbp (.mem (at_ .r15 lenO))] s₄ = some s₅ ∧ s₅.gpr .rbx = BitVec.ofNat 64 al ∧
      s₅.gpr .rbp = BitVec.ofNat 64 n ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧
      s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by xrun [he₄.r15, q₄, q₅], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, kp f₄ 184 (.inl ⟨by decide, by decide⟩), kp f₂ 184 (.inl ⟨by decide, by decide⟩), hal]
    · simp [gpr_setReg, kp f₄ 208 (.inl ⟨by decide, by decide⟩), kp f₂ 208 (.inl ⟨by decide, by decide⟩), hlen]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide)) hrd₅ hwr₅
  have g₅ : Frame (wFrame W SP) s.mem s₅.mem := by rw [hm₅]; exact g₂.trans g₄
  have f₅ : Frame (oneFrame W D SP n) s.mem s₅.mem := wFrame_one g₅
  have hR₅ : RoundsAt s₅.mem W R := ⟨by rw [kp f₅ 176 (.inl ⟨by decide, by decide⟩)]; exact hR.1, hR.2⟩
  have dC : ∀ r ∈ oneFrame W D SP n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.cw'.sub_right (Offset.sub_base W (show 0 + 128 ≤ 2560 by decide) |> fun h => by simpa using h)
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact hCD
    · exact L.kc.symm
  have dS0 : ∀ r ∈ absFrame (W + BitVec.ofNat 64 16) W SP 16, (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using L.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.st_st (a := 0) (n := 16) (d := 32) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using (L.stk_st (a := 0) (n := 16) (by decide)).symm
  have dT0 : ∀ r ∈ tFrame (W + BitVec.ofNat 64 16) W SP 16, (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using L.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using (L.stk_st (a := 0) (n := 16) (by decide)).symm
  have hJ₅ : blockAt s₅.mem (W + BitVec.ofNat 64 16) = blockAt s.mem (W + BitVec.ofNat 64 16) := by
    rw [hm₅, blockAt_frame hf.frame dT0, blockAt_frame ho'.frame dS0]
  have hH₅ : blockAt s₅.mem (Ctx + BitVec.ofNat 64 240) = H := by rw [hm₅, hf.hH]
  refine WP.mono (WP.with_rdwr (tag_ok v L ho he₅ hH₅ hR₅ hJ₅)) fun s₆ ⟨ht, hrd₆, hwr₆⟩ =>
    ⟨ht.env, g₅.trans (tagFrame_one ho ht.frame), by rw [hrd₆, hrd₅, hrd₄, hrd₃, hrd₂, hrd₁],
      by rw [hwr₆, hwr₅, hwr₄, hwr₃, hwr₂, hwr₁], fun hab => ?_⟩
  have hw := (hf.abs (ho'.abs (hx ▸ hab))).whole_eq (by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
  rw [ht.out, ciph_frame f₅ dC hR.2, hbx₅, hbp₅, toNat_ofNat_of_lt hlt, BitVec.toNat_ofNat, lensBlock_mod_left, ha,
    hm₅, hw, ← hx, padded_eq]

end

end VG.Proof.AesGcm.X86_64
