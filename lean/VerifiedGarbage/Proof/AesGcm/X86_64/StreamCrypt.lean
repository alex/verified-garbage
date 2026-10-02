import VerifiedGarbage.Proof.AesGcm.X86_64.TextAbsorb

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. The entry keeps the public
arguments in `W` (`cryptEntry_ok`); `encrypt` then runs counter mode over the
data (`crypt`) and absorbs the ciphertext it wrote (`textAbsorb`), and
`decrypt` absorbs the ciphertext first.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- What the entry writes in `W`. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 88⟩

/-- After `cryptEntry`. -/
structure CryptEntry (s₀ : State) (Ctx St W SP D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  rounds : RoundsAt s.mem W (s₀.gpr .rsi).toNat
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .rcx
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = s₀.gpr .r8
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  r12 : s.gpr .r12 = D
  rbp : s.gpr .rbp = BitVec.ofNat 64 n
  rbx : s.gpr .rbx = BitVec.ofNat 64 ((s₀.gpr .r8).toNat % 16)
  saved : SavedAt s.mem W s₀
  frame : Frame [entryR W] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem cryptEntry_ok {s : State} {Ctx St W SP D : Addr} {n : Nat} (hCtx : s.gpr .rdi = Ctx) (hSt : s.gpr .rdx = St)
    (hD : s.gpr .r9 = D) (hSP : s.gpr .rsp = SP) (hW : stackArg s 1 = W) (hn : (stackArg s 0).toNat = n)
    (hperm : Perm Ctx St W s) (_hww : W.toNat + 2560 ≤ 2 ^ 64)
    (hargs : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8 ∧ InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8)
    (hdA : (⟨SP + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hR : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) :
    WP isa (.block cryptEntry) s (CryptEntry s Ctx St W SP D n) := by
  have hW' : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = W := by rw [← hW, ← hSP]; rfl
  have hn' : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n := by
    rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hSP]; rfl
  obtain ⟨s₀, run₀, hax₀, hg₀, hm₀, hrd₀, hwr₀⟩ : ∃ s₀', runBlock isa [.mov .rax (.mem (at_ .rsp 16))] s = some s₀' ∧
      s₀'.gpr .rax = W ∧ (∀ r, r ≠ .rax → s₀'.gpr r = s.gpr r) ∧ s₀'.mem = s.mem ∧ s₀'.rd = s.rd ∧ s₀'.wr = s.wr := by
    refine ⟨_, by xrun [hSP, hargs.2], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hW']
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  have hperm₀ : Perm Ctx St W s₀ := hperm.of_eq hrd₀ hwr₀
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s₀ .rax hax₀ hperm₀.w
  have hsv₁' : SavedAt s₁.mem W s := by
    intro p hp; rw [hsv₁ p hp]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg₀ _ (by decide)
  have w₁ := in_off hperm.w (show 176 + 8 ≤ 2560 by decide) (by decide)
  have w₂ := in_off hperm.w (show 184 + 8 ≤ 2560 by decide) (by decide)
  have w₃ := in_off hperm.w (show 192 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off hperm.w (show 200 + 8 ≤ 2560 by decide) (by decide)
  have w₅ := in_off hperm.w (show 208 + 8 ≤ 2560 by decide) (by decide)
  rw [← hwr₀, ← hwr₁] at w₁ w₂ w₃ w₄ w₅
  have a₁ := hargs.1
  rw [← hrd₀, ← hwr₀, ← hrd₁, ← hwr₁] at a₁
  have hsepA : ∀ (m : Mem) (k : Nat), Frame [⟨W + BitVec.ofNat 64 128, k⟩] s.mem m → k ≤ 2432 →
      m.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n := fun m k hf hk => by
    rw [hf.readW (r := ⟨SP + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hdA.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by omega))) (by decide), hn']
  have hn₁ : s₁.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n := hsepA _ 48 (hm₀ ▸ f₁) (by decide)
  have sA : ∀ d, 176 ≤ d → d + 8 ≤ 216 → Mem.Sep (SP + BitVec.ofNat 64 8) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Region.Disjoint.sep ((hdA.sub_left (Region.sub_prefix (by decide))).sub_right
      (Lay.wSub (n := 8) (d := d) (by omega))) (Region.contains_self _ _) (Region.contains_self _ _)
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega) (by omega)
  have a₁₇₆ := sA 176 (by decide) (by decide)
  have a₁₈₄ := sA 184 (by decide) (by decide)
  have a₁₉₂ := sA 192 (by decide) (by decide)
  have a₂₀₀ := sA 200 (by decide) (by decide)
  have q0 := sep 176 184 (by decide) (by decide) (by decide)
  have q1 := sep 176 192 (by decide) (by decide) (by decide)
  have q2 := sep 176 200 (by decide) (by decide) (by decide)
  have q3 := sep 176 208 (by decide) (by decide) (by decide)
  have q4 := sep 184 192 (by decide) (by decide) (by decide)
  have q5 := sep 184 200 (by decide) (by decide) (by decide)
  have q6 := sep 184 208 (by decide) (by decide) (by decide)
  have q7 := sep 192 200 (by decide) (by decide) (by decide)
  have q8 := sep 192 208 (by decide) (by decide) (by decide)
  have q9 := sep 200 208 (by decide) (by decide) (by decide)
  have hand := and15 (s.gpr .r8)
  rw [imm_eq (by decide)] at hand
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hbx, hsp, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .rax), .mov .r14 (.reg .rdx), .mov .r13 (.reg .rdi),
        .store (at_ .r15 roundsO) .rsi, .store (at_ .r15 alenO) .rcx, .store (at_ .r15 tlenO) .r8,
        .store (at_ .r15 dataO) .r9, .mov .rbp (.mem (at_ .rsp 8)), .store (at_ .r15 lenO) .rbp,
        .mov .r12 (.reg .r9), .mov .rbx (.reg .r8), .alu .and .rbx (imm 15)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = St ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .r12 = D ∧ s₂.gpr .rbp = BitVec.ofNat 64 n ∧
      s₂.gpr .rbx = BitVec.ofNat 64 ((s.gpr .r8).toNat % 16) ∧ s₂.gpr .rsp = SP ∧
      s₂.mem = ((((s₁.mem.writeW (W + BitVec.ofNat 64 176) (s.gpr .rsi)).writeW (W + BitVec.ofNat 64 184)
        (s.gpr .rcx)).writeW (W + BitVec.ofNat 64 192) (s.gpr .r8)).writeW (W + BitVec.ofNat 64 200) D).writeW
          (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 n) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have g : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r := fun r h => by rw [hg₁, hg₀ r h]
    have hax₁ : s₁.gpr .rax = W := by rw [hg₁, hax₀]
    have hsp₁ : s₁.gpr .rsp = SP := by rw [g _ (by decide), hSP]
    have hrdx := g .rdx (by decide); have hrdi := g .rdi (by decide); have hrsi := g .rsi (by decide)
    have hrcx := g .rcx (by decide); have hr8 := g .r8 (by decide); have hr9 := g .r9 (by decide)
    refine ⟨_, by xrun [hax₁, hsp₁, w₁, w₂, w₃, w₄, w₅, a₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hax₁]
    · simp [gpr_setReg, hrdx, hSt]
    · simp [gpr_setReg, hrdi, hCtx]
    · simp [gpr_setReg, hr9, hD]
    · simp (disch := first | decide | assumption) [gpr_setReg, mem_setReg, Mem.readW_writeW_sep, hn₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hr8, hand]
    · simp [gpr_setReg, gpr_arithFlags, hsp₁]
    · simp (disch := first | decide | assumption) [gpr_setReg, mem_setReg, mem_arithFlags, Mem.readW_writeW_sep,
        hn₁, hrsi, hrcx, hr8, hr9, hD]
    all_goals rfl
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.of_runBlock ⟨s₁, run₁,
    WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩⟩))
  have hrd' : s₂.rd = s.rd := hrd₂.trans (hrd₁.trans hrd₀)
  have hwr' : s₂.wr = s.wr := hwr₂.trans (hwr₁.trans hwr₀)
  have f₂ : Frame [⟨W + BitVec.ofNat 64 176, 40⟩] s₁.mem s₂.mem := by
    rw [hm₂]
    have c : ∀ d, 176 ≤ d → d + 8 ≤ 216 → (⟨W + BitVec.ofNat 64 176, 40⟩ : Region).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 176 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))
  have rd : ∀ d (v : BitVec 64), (d = 176 ∧ v = s.gpr .rsi) ∨ (d = 184 ∧ v = s.gpr .rcx) ∨ (d = 192 ∧ v = s.gpr .r8) ∨
      (d = 200 ∧ v = D) ∨ (d = 208 ∧ v = BitVec.ofNat 64 n) → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = v := by
    intro d v h
    rw [hm₂]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp (disch := first | decide | assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
  refine ⟨⟨h13, h14, h15, hsp, hperm.of_eq hrd' hwr'⟩, ⟨?_, hR⟩, rd 184 _ (.inr (.inl ⟨rfl, rfl⟩)),
    rd 192 _ (.inr (.inr (.inl ⟨rfl, rfl⟩))), rd 200 _ (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))),
    rd 208 _ (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩)))), h12, hbp, hbx, ?_, ?_, hrd', hwr'⟩
  · rw [rd 176 _ (.inl ⟨rfl, rfl⟩)]; exact BitVec.eq_of_toNat_eq (by simp)
  · exact hsv₁'.frame f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by decide)) (by omega) (by omega)
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
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- What the precondition of `encrypt` and `decrypt` gives. -/
structure CryptCtx (s : State) (Ctx St W SP D : Addr) (n : Nat) : Prop where
  lay : Lay Ctx St W SP
  perm : Perm Ctx St W s
  ww : W.toNat + 2560 ≤ 2 ^ 64
  args : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8 ∧ InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8
  dA : (⟨SP + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W, 2560⟩
  data : DataW Ctx St W SP s D n
  rD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  rS : (⟨SP, 8⟩ : Region).Disjoint ⟨St, 80⟩
  rW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩
  dE : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩
  rounds : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14

theorem CryptCtx.of {s : State} (hp : Proof.AesGcm.streamCryptPre s) :
    CryptCtx s (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) (s.gpr .rsp) (s.gpr .r9) (stackArg s 0).toNat := by
  simp only [Proof.AesGcm.streamCryptPre, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.args,
    Proof.AesGcm.arg, Proof.AesGcm.rounds] at hp
  obtain ⟨hrd, hwr, d_cs, d_cd, d_cw, d_sd, d_sw, d_sa, d_dw, d_da, d_wa, r_s, r_d, r_w, k_c, k_s, k_d, k_w,
    wc, ws, wd, ww, wsp, hR⟩ := hp
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at hrd d_sa d_da d_wa
  have L : Lay (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) (s.gpr .rsp) := Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w
  have pm : Covers [⟨s.gpr .rsp + BitVec.ofNat 64 8, 16⟩] (s.rd ++ s.wr) := by
    rw [hrd]
    exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine ⟨L, ⟨?_, ?_, ?_⟩, ww, ⟨?_, ?_⟩, d_wa.symm, ⟨⟨?_, by have := (stackArg s 0).isLt; omega, wd, d_sd.symm, d_dw,
    k_d⟩, ?_, d_cd⟩, r_d, r_s, r_w, d_dw, hR⟩
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
  · rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  · rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · simpa using in_off pm (show 0 + 8 ≤ 16 by decide) (by decide)
  · have := in_off pm (show 8 + 8 ≤ 16 by decide) (by decide)
    rwa [add_ofNat_assoc] at this
  · rw [hwr]; exact covers_left (covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

section
variable {Ctx St W SP D : Addr} {n : Nat}

/-- The parts of the state, apart from the regions the entry, `crypt` and `textAbsorb` write. -/
theorem st_disj {s : State} (C : CryptCtx s Ctx St W SP D n) {d k : Nat} (hk : d + k ≤ 80) :
    (∀ r ∈ [entryR W], (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r) ∧
    (d + k ≤ 48 → ∀ r ∈ crFrame St W SP D n, (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r) ∧
    ((d + k ≤ 16 ∨ 48 ≤ d) → ∀ r ∈ taFrame St W SP, (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r) := by
  have L := C.lay
  refine ⟨fun r hr => ?_, fun h r hr => ?_, fun h r hr => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hk (.inr ⟨by decide, by decide⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (C.data.ok.st.sub_right (Lay.stSub hk)).symm
    · exact L.st_st (.inl (by omega)) hk (by decide)
    · exact L.st_w hk (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st hk).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.st_st (by omega) hk (by decide)
    · exact L.st_w hk (.inr ⟨by decide, by decide⟩)
    · exact L.st_w hk (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st hk).symm

end

/-- One run of `vg_aes_gcm_stream_encrypt`, for the message the state represents. -/
theorem streamEncrypt_run (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamEncryptX86_64.pre s)
    {iv a p : List Byte} (hA : s.gpr .rcx = BitVec.ofNat 64 a.length) (hT : (s.gpr .r8).toNat = p.length) :
    WP isa (streamEncrypt v.callees) s fun s' => gprPreserved s s' ∧
      let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
      let h := ctxH s.mem (s.gpr .rdi)
      (StreamRepr s.mem (s.gpr .rdx) ciph h iv a (gctr ciph (inc32 (Spec.Gcm.j0 h iv)) p) →
        let c := gctr ciph (inc32 (Spec.Gcm.j0 h iv)) (p ++ bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)
        StreamRepr s'.mem (s.gpr .rdx) ciph h iv a c ∧
          bytesAt s'.mem (s.gpr .r9) (stackArg s 0).toNat = c.drop p.length) := by
  have C := CryptCtx.of hp
  have hR := C.rounds
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rdx = St at *
  generalize hW : stackArg s 1 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hD : s.gpr .r9 = D at *
  generalize hn : (stackArg s 0).toNat = n at *
  have L := C.lay
  generalize hR' : (s.gpr .rsi).toNat = R at *
  generalize hH : ctxH s.mem Ctx = H
  generalize hciph : ctxCiph s.mem Ctx R = ciph
  generalize hicb : inc32 (Spec.Gcm.j0 H iv) = icb
  refine WP.seq (WP.mono (cryptEntry_ok hCtx hSt hD hSP hW hn C.perm C.ww C.args C.dA (by rw [hR']; exact hR))
    fun s₁ E => ?_)
  have hRo : RoundsAt s₁.mem W R := hR' ▸ E.rounds
  have hcr : CrIn Ctx St W SP R icb p.length D n s₁ :=
    ⟨E.env, E.r12, E.rbp, by rw [E.rbx, hT], C.data.of_eq E.rd E.wr, hRo⟩
  refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok v L hcr)) fun s₂ ⟨co, hrd₂, hwr₂⟩ => ?_)
  have kc : ∀ d, 176 ≤ d → d + 8 ≤ 512 → ∀ r ∈ crFrame St W SP D n, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    intro d h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (C.dE.sub_right (Lay.wSub (by omega))).symm
    · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact (L.stk_w (by omega)).symm
  have rd₂ : ∀ d, 176 ≤ d → d + 8 ≤ 512 → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => co.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kc d h₁ h₂) (by decide)
  have dCE : ∀ r ∈ [entryR W], (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by decide))
  have hH₂ : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame co.frame (fun r hr => (ctx_crFrame L C.data r hr).sub_left (Lay.ctxSub (by decide))),
      blockAt_frame E.frame (fun r hr => (dCE r hr).sub_left (Lay.ctxSub (by decide))), ← hH, ctxH_eq]
  have hta : TaIn Ctx St W SP H (s.gpr .rcx) (s.gpr .r8) D n s₂ :=
    ⟨co.env, hH₂, by rw [rd₂ 184 (by decide) (by decide)]; exact E.alen, by rw [rd₂ 192 (by decide) (by decide)]; exact E.tlen,
      by rw [rd₂ 200 (by decide) (by decide)]; exact E.dat, by rw [rd₂ 208 (by decide) (by decide)]; exact E.len,
      (C.data.of_eq (hrd₂.trans E.rd) (hwr₂.trans E.wr)).ok⟩
  refine WP.seq (WP.mono (textAbsorb_ok v L hta hA (c := gctr ciph icb p) (by rw [hT, Proof.Gcm.length_gctr]))
    fun s₃ ⟨he₃, f₃, hab⟩ => ?_)
  have dSa : ∀ r ∈ taFrame St W SP, (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm
  have hsv₃ : SavedAt s₃.mem W s := (E.saved.frame co.frame (saved_crFrame L (C.data.of_eq E.rd E.wr))).frame f₃ dSa
  have hret : s₃.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept f₃ (fun r hr => ?_), ret_kept co.frame (fun r hr => ?_), ret_kept E.frame (fun r hr => ?_)]
    · simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact C.rD
      · exact C.rS.sub_right (Lay.stSub (by decide))
      · exact C.rW.sub_right (Lay.wSub (by decide))
      · exact ret_below SP
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact C.rS.sub_right (Lay.stSub (by decide))
      · exact C.rW.sub_right (Lay.wSub (by decide))
      · exact C.rW.sub_right (Lay.wSub (by decide))
      · exact ret_below SP
  refine WP.mono (exit_ok he₃.r15 (by rw [he₃.rsp, hSP]) (covers_left he₃.perm.w) hsv₃ (by rw [hSP, hret]))
    fun s' ⟨hg, hm, _⟩ => ⟨hg, fun hsr => ?_⟩
  dsimp only at hsr ⊢
  rw [hicb] at hsr ⊢
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hsr ⊢
  obtain ⟨hj, habs, hctr⟩ := hsr
  rw [hicb] at hctr
  rw [Proof.Gcm.length_gctr] at hctr
  have dD : ∀ r ∈ [entryR W], (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact C.dE.sub_right (Lay.wSub (by decide))
  have hd₁ : bytesAt s₁.mem D n = bytesAt s.mem D n := bytesAt_frame E.frame dD (by have := C.data.ok.lt; omega)
  have hc₁ : ciphOf s₁.mem Ctx R = ciph := by rw [ciph_frame E.frame dCE hR, ← hciph]; rfl
  have hctr₁ : Ctr s₁.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s₁.mem Ctx R) icb p.length := by
    rw [hc₁]
    exact hctr.congr (blockAt_frame E.frame (st_disj C (d := 48) (k := 16) (by decide)).1)
      (blockAt_frame E.frame (st_disj C (d := 64) (k := 16) (by decide)).1)
  have habs₂ : Absorbed s₂.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a (gctr ciph icb p)) := by
    have hl := Nat.mod_lt (ghashInput a (gctr ciph icb p)).length (show 16 > 0 by decide)
    refine (habs.congr (blockAt_frame E.frame (st_disj C (d := 16) (k := 16) (by decide)).1)
      (bytesAt_frame E.frame (st_disj C (d := 32) (k := _ % 16) (by omega)).1 (by omega))).congr
      (blockAt_frame co.frame ((st_disj C (d := 16) (k := 16) (by decide)).2.1 (by decide)))
      (bytesAt_frame co.frame ((st_disj C (d := 32) (k := _ % 16) (by omega)).2.1 (by omega)) (by omega))
  have hout := co.out hctr₁
  rw [hd₁, hc₁] at hout
  have hd : gctr ciph icb (p ++ bytesAt s.mem D n) = gctr ciph icb p ++ bytesAt s₂.mem D n := by
    rw [Proof.Gcm.gctr_append, hout]
  have dDa : ∀ r ∈ taFrame St W SP, (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact C.data.ok.st.sub_right (Lay.stSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.data.ok.stk.symm
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hm, ← hj]
    simpa using (blockAt_frame f₃ ((st_disj C (d := 0) (k := 16) (by decide)).2.2 (.inl (by decide)))).trans
      ((blockAt_frame co.frame ((st_disj C (d := 0) (k := 16) (by decide)).2.1 (by decide))).trans
      (blockAt_frame E.frame (st_disj C (d := 0) (k := 16) (by decide)).1))
  · rw [hm, hd]; exact hab habs₂
  · rw [hm, hicb, Proof.Gcm.length_gctr, List.length_append, length_bytesAt]
    have := co.ctr hctr₁
    rw [hc₁] at this
    exact this.congr (blockAt_frame f₃ ((st_disj C (d := 48) (k := 16) (by decide)).2.2 (.inr (by decide))))
      (blockAt_frame f₃ ((st_disj C (d := 64) (k := 16) (by decide)).2.2 (.inr (by decide))))
  · rw [hm, hd, List.drop_left' (Proof.Gcm.length_gctr _ _ _), bytesAt_frame f₃ dDa
      (by have := C.data.ok.lt; omega)]

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- `vg_aes_gcm_stream_encrypt`. -/
theorem streamEncrypt_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamEncryptX86_64.pre s) :
    WP isa (streamEncrypt v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamEncryptX86_64.post s s' := by
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rcx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .r8).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (streamEncrypt_run v hp (iv := []) (a := List.replicate (s.gpr .rcx).toNat 0)
      (p := List.replicate (s.gpr .r8).toNat 0) (by simp) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (streamEncrypt_run v hp (iv := i.1) hi.1 hi.2) fun _ h => h.2
  exact WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a p hr hA hT => hq (iv, a, p) ⟨hA, hT⟩ hr⟩

end VG.Proof.AesGcm.X86_64
