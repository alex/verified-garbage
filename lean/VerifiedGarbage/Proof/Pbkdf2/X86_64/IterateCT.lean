import VerifiedGarbage.Proof.Pbkdf2.X86_64.Iterate
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Pbkdf2.Contract

/-!
# PBKDF2-HMAC-SHA-256's iteration on x86-64: constant time

Untrusted: everything here is checked by Lean.

This holds for any compression function `f` (`Callee.Ok`), so it is proven
once for every implementation. The taint analysis cannot prove it without
looking into `f`: `f` saves and restores our registers in memory it also
writes secrets to, so across a call the analysis forgets that our pointers
are public. So we relate two runs (`RelCT`): at every point, correctness
determines our registers from the public arguments alone, so they agree;
between the calls, the taint analysis proves each block constant time from
that; and the calls are constant time by `f`'s own proof.
-/

namespace VG.Proof.Pbkdf2.X86_64.Iterate

open VG VG.X86_64 VG.Impl.Pbkdf2.X86_64
open VG.Impl.Sha256.X86_64.Stream (Callee)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_mov wp_addi wp_mov32i)

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : (s₀.gpr .rdx).setWidth 32 = (s₀'.gpr .rdx).setWidth 32
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

theorem PubEq.nn {s₀ s₀' : State} (hq : PubEq s₀ s₀') : nn s₀ = nn s₀' :=
  congrArg BitVec.toNat hq.rdx

/-- The registers during a step, with `v` in `r13`. -/
structure St (s₀ : State) (v : Addr) (s : State) : Prop extends Regs s₀ s where
  r13 : s.gpr .r13 = v

/-- The registers the blocks use agree in two runs. -/
theorem St.agree {s₀ s₀' : State} (hq : PubEq s₀ s₀') {v : Addr} {s s' : State} (h : St s₀ v s)
    (h' : St s₀' v s') : ∀ r ∈ [Reg.rbx, .rbp, .rcx, .rdi, .rsp, .r13], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, key, key, hq.rdi]
  · rw [h.rbp, h'.rbp, tP, tP, hq.rcx]
  · rw [h.rcx, h'.rcx, scr, scr, hq.r8]
  · rw [h.rdi, h'.rdi, scr, scr, hq.r8]
  · rw [h.rsp, h'.rsp, hq.rsp]
  · rw [h.r13, h'.r13]

theorem St.of_inv {s₀ : State} {r : Nat} {s : State} (h : Inv s₀ (r + 1) s) :
    St s₀ (BitVec.ofNat 64 (r + 1)) s :=
  ⟨h.toRegs, h.r13⟩

/-- The registers the blocks use. -/
abbrev τS : X86_64.Taint.T := Taint.ofRegs [.rbx, .rbp, .rcx, .rdi, .rsp, .r13]

/-! ## What each piece of a step does to the registers -/

section
variable {s₀ : State} (hp : Pre s₀) {v : Addr}
include hp

theorem load_wp {o : Nat} (ho : o + 32 ≤ 192) {s : State} (h : St s₀ v s) :
    WP isa (.block (load o)) s (St s₀ v) := by
  rw [← List.append_nil (load o)]
  exact load_ok hp h.toRegs ho fun s' hk _ =>
    WP.block_nil ⟨h.toRegs.keep hk, (hk.gpr _ (by simp [kept])).trans h.r13⟩

theorem digestLoad_wp {s : State} (h : St s₀ v s) :
    WP isa (.block (Impl.Pbkdf2.X86_64.digest ++ load 96)) s (St s₀ v) :=
  digest_ok hp h.toRegs fun s' hr hg _ _ =>
    load_wp hp (o := 96) (by omega) ⟨hr, (hg _ (by decide)).trans h.r13⟩

theorem cmp_wp {f : Callee} (hf : f.Ok) {s : State} (h : St s₀ v s) :
    WP isa (compressBlock f) s (St s₀ v) :=
  cmp_ok hf hp h.toRegs fun _ hk _ => ⟨h.toRegs.keep hk, (hk.gpr _ (by simp [kept])).trans h.r13⟩

/-- The arguments of the call of the compression function. -/
abbrev setup : List Instr := [.mov .rsi (.reg .rcx), .alu .add .rsi (.imm 144), .mov32 .rdx (.imm 1)]

omit hp in
theorem setup_wp {s : State} (h : St s₀ v s) :
    WP isa (.block setup) s fun s' =>
      St s₀ v s' ∧ s'.gpr .rsi = scr s₀ + 144 ∧ s'.gpr .rdx = 1 := by
  refine wp_mov fun s₁ u₁ _ _ => wp_addi fun s₂ u₂ => wp_mov32i fun s₃ u₃ _ _ => WP.block_nil ?_
  have o : ∀ r : Reg, r ≠ .rsi → r ≠ .rdx → s₃.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [u₃.other _ h₂, u₂.other _ h₁, u₁.other _ h₁]
  have hm : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨⟨by rw [u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [u₃.wr, u₂.wr, u₁.wr, h.wr],
    (o _ (by decide) (by decide)).trans h.rbx, (o _ (by decide) (by decide)).trans h.rbp,
    (o _ (by decide) (by decide)).trans h.rcx, (o _ (by decide) (by decide)).trans h.rdi,
    (o _ (by decide) (by decide)).trans h.rsp, (o _ (by decide) (by decide)).trans h.r12,
    (o _ (by decide) (by decide)).trans h.r14, (o _ (by decide) (by decide)).trans h.r15,
    hm ▸ h.frame⟩, (o _ (by decide) (by decide)).trans h.r13⟩, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, h.rcx]; rfl
  · rw [u₃.gpr]; rfl

/-- What the call of the compression function needs, with the arguments set up. -/
theorem call_hyps {s : State} (h : Regs s₀ s) (hsi : s.gpr .rsi = scr s₀ + 144)
    (hdx : s.gpr .rdx = 1) :
    Proof.Sha256.compressX86_64.pre (s.callEntry.withRegions [⟨scr s₀ + 144, 64 * 1⟩]
      [⟨scr s₀ + 112, 32⟩, ⟨scr s₀, 112⟩]) ∧
    Covers ([⟨scr s₀ + 144, 64 * 1⟩] ++ [⟨scr s₀ + 112, 32⟩, ⟨scr s₀, 112⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨scr s₀ + 112, 32⟩, ⟨scr s₀, 112⟩] s.wr := by
  have hsp : below (s.gpr .rsp) 8 = stkR s₀ := by rw [h.rsp]
  have hsc : (scR s₀) ∈ s.wr := by simp [h.wr, hp.wr]
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Sha256.compressX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp),
      hne _ (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rcx, hsi, hdx,
      show (1 : BitVec 64).toNat = 1 from rfl, Nat.mul_one]
    refine ⟨by simp, by simp, scr_disj0 s₀ (a := 112) (by omega) (by omega),
      scr_disj s₀ (a := 144) (b := 112) (by omega) (by omega) (by omega),
      scr_disj0 s₀ (a := 144) (by omega) (by omega), ?_, ?_⟩
    · rw [h.rsp]; exact stk_scr hp (a := 112) (by omega)
    · rw [h.rsp]; simpa using stk_scr hp (a := 0) (m := 112) (by omega)
  · refine Covers.of_sub fun r hr => ⟨scR s₀, List.mem_append_right _ hsc, ?_⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨144, rfl, by simp⟩
    · exact ⟨112, rfl, by simp⟩
    · exact ⟨0, by simp, by simp⟩
  · refine Covers.of_sub fun r hr => ⟨scR s₀, hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨112, rfl, by simp⟩
    · exact ⟨0, by simp, by simp⟩

end

/-! ## Two runs -/

section
variable {f : Callee} (hf : f.Ok) {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀')
  (hq : PubEq s₀ s₀')
include hf hp hp' hq

theorem cmp_rel {v : Addr} :
    RelCT isa (fun s s' => St s₀ v s ∧ St s₀' v s') (compressBlock f) fun s s' =>
      St s₀ v s ∧ St s₀' v s' := by
  have es : scr s₀' = scr s₀ := hq.r8.symm
  have su : RelCT isa (fun s s' => St s₀ v s ∧ St s₀' v s') (.block setup) fun s s' =>
      (St s₀ v s ∧ s.gpr .rsi = scr s₀ + 144 ∧ s.gpr .rdx = 1) ∧
      (St s₀' v s' ∧ s'.gpr .rsi = scr s₀' + 144 ∧ s'.gpr .rdx = 1) :=
    ((RelCT.taint (A := taint) τS (fun _ _ h => Taint.agree_ofRegs (St.agree hq h.1 h.2))
      (by taint_decide)).wp fun _ _ h => ⟨setup_wp h.1, setup_wp h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have call := RelCT.call (n := f.name) (P := fun s s' =>
      (St s₀ v s ∧ s.gpr .rsi = scr s₀ + 144 ∧ s.gpr .rdx = 1) ∧
      (St s₀' v s' ∧ s'.gpr .rsi = scr s₀' + 144 ∧ s'.gpr .rdx = 1))
    hf.verified hf.ct [⟨scr s₀ + 144, 64 * 1⟩] [⟨scr s₀ + 112, 32⟩, ⟨scr s₀, 112⟩]
    fun s s' ⟨⟨h, hsi, hdx⟩, ⟨h', hsi', hdx'⟩⟩ => by
      obtain ⟨p₁, c₁, w₁⟩ := call_hyps hp h.toRegs hsi hdx
      obtain ⟨p₂, c₂, w₂⟩ := call_hyps hp' h'.toRegs hsi' hdx'
      rw [es] at p₂ c₂ w₂
      have ag := St.agree hq h h'
      refine ⟨p₁, p₂, ?_, c₁, w₁, c₂, w₂, ag _ (by simp)⟩
      simp only [Proof.Sha256.compressX86_64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), hsi, hsi', hdx, hdx', es]
      exact ⟨ag _ (by simp), trivial, trivial, ag _ (by simp)⟩
  exact ((su.seq call).wp fun _ _ h => ⟨cmp_wp hp hf h.1, cmp_wp hp' hf h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem body_rel {r : Nat} :
    RelCT isa (fun s s' => Inv s₀ (r + 1) s ∧ Inv s₀' (r + 1) s') (body f) fun s s' =>
      (eval .ne s = some (r != 0) ∧ Inv s₀ r s) ∧ (eval .ne s' = some (r != 0) ∧ Inv s₀' r s') := by
  have l0 : RelCT isa (fun s s' => Inv s₀ (r + 1) s ∧ Inv s₀' (r + 1) s') (.block (load 0))
      fun s s' => St s₀ (BitVec.ofNat 64 (r + 1)) s ∧ St s₀' (BitVec.ofNat 64 (r + 1)) s' :=
    ((RelCT.taint (A := taint) τS (fun _ _ h =>
      Taint.agree_ofRegs (St.agree hq (St.of_inv h.1) (St.of_inv h.2))) (by taint_decide)).wp
      fun _ _ h => ⟨load_wp hp (by omega) (St.of_inv h.1), load_wp hp' (by omega) (St.of_inv h.2)⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have dl : RelCT isa (fun s s' => St s₀ (BitVec.ofNat 64 (r + 1)) s ∧ St s₀' (BitVec.ofNat 64 (r + 1)) s')
      (.block (Impl.Pbkdf2.X86_64.digest ++ load 96))
      fun s s' => St s₀ (BitVec.ofNat 64 (r + 1)) s ∧ St s₀' (BitVec.ofNat 64 (r + 1)) s' :=
    ((RelCT.taint (A := taint) τS (fun _ _ h => Taint.agree_ofRegs (St.agree hq h.1 h.2))
      (by taint_decide)).wp fun _ _ h => ⟨digestLoad_wp hp h.1, digestLoad_wp hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have fin : RelCT isa (fun s s' => St s₀ (BitVec.ofNat 64 (r + 1)) s ∧ St s₀' (BitVec.ofNat 64 (r + 1)) s')
      (.block (Impl.Pbkdf2.X86_64.digest ++ (List.range 4).flatMap xorW ++ [.alu .sub .r13 (.imm 1)]))
      fun _ _ => True :=
    RelCT.taint (A := taint) τS (fun _ _ h => Taint.agree_ofRegs (St.agree hq h.1 h.2))
      (by taint_decide)
  have c := cmp_rel hf hp hp' hq (v := BitVec.ofNat 64 (r + 1))
  exact ((l0.seq (c.seq (dl.seq (c.seq fin)))).wp fun _ _ h =>
    ⟨body_ok hf hp h.1, body_ok hf hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

theorem loop_rel {n : Nat} :
    RelCT isa (fun s s' => Inv s₀ (n + 1) s ∧ Inv s₀' (n + 1) s') (.loop (body f) .ne)
      fun _ _ => True := by
  have lp := RelCT.loop (M := isa) (body := body f) (c := .ne) (Q := fun _ _ => True)
    (fun m s s' => Inv s₀ (m + 1) s ∧ Inv s₀' (m + 1) s') (fun m => by
      intro s s' t t' u u' h e e'
      obtain ⟨ht, ⟨z, i⟩, ⟨z', i'⟩⟩ := body_rel hf hp hp' hq _ _ _ _ _ _ h e e'
      refine ⟨ht, z.trans z'.symm, fun _ => trivial, fun hc => ?_⟩
      have hc' : some (m != 0) = some true := z.symm.trans hc
      cases m with
      | zero => cases hc'
      | succ m => exact ⟨m, by omega, i, i'⟩) n
  exact lp

theorem iterate_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (iterate f) fun _ _ => True := by
  have es : scr s₀' = scr s₀ := hq.r8.symm
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block prologue) fun s s' =>
      (Inv s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0))) ∧
      (Inv s₀' (nn s₀') s' ∧ s'.zf = some (decide (nn s₀' = 0))) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rcx, .r8, .rsp])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) (c := .block prologue) (by taint_decide)).wp
      fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have br : RelCT isa (fun s s' =>
        (Inv s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0))) ∧
        (Inv s₀' (nn s₀') s' ∧ s'.zf = some (decide (nn s₀' = 0))))
      (.ite .e (.block []) (.loop (body f) .ne)) fun s s' => Inv s₀ 0 s ∧ Inv s₀' 0 s' := by
    refine (RelCT.ite (fun s s' h => ?_) (RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)) ?_).wp
      (fun _ _ h => ⟨loop_ok hf hp h.1.1 h.1.2, loop_ok hf hp' h.2.1 h.2.2⟩) |>.mono
      (fun _ _ h => h) fun _ _ h => h.2
    · show s.zf = s'.zf
      rw [h.1.2, h.2.2, hq.nn]
    · intro s s' t t' u u' ⟨⟨⟨i, z⟩, ⟨i', _⟩⟩, hc⟩ e e'
      have hc' : some (decide (nn s₀ = 0)) = some false := z.symm.trans hc
      have hne : nn s₀ ≠ 0 := fun h0 => by rw [h0] at hc'; cases hc'
      obtain ⟨m, hm⟩ : ∃ m, nn s₀ = m + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hne).symm⟩
      rw [hm] at i
      rw [← hq.nn, hm] at i'
      exact loop_rel hf hp hp' hq _ _ _ _ _ _ ⟨i, i'⟩ e e'
  have epi : RelCT isa (fun s s' => Inv s₀ 0 s ∧ Inv s₀' 0 s') (.block epilogue) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.rcx]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.rcx, h.2.rcx, es]) (by taint_decide)
  exact pro.seq (br.seq epi)

end

/-! ## Verified -/

theorem pubEq_of {s₁ s₂ : State} (h : Proof.Pbkdf2.iterateSha256X86_64.pub s₁ s₂) : PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem constantTime {f : Callee} (hf : f.Ok) :
    ConstantTime isa Proof.Pbkdf2.iterateSha256X86_64.pre Proof.Pbkdf2.iterateSha256X86_64.pub
      (iterate f) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (iterate_rel hf (pre_of h₁) (pre_of h₂) (pubEq_of hpub) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem iterate_verified {f : Callee} (hf : f.Ok)
    (hm : f.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (iterate f) (Spec.Pbkdf2.iterateSha256Contract X86_64.abi 8) :=
  Verified.of_correct (iterate_ok hf (by
    simp only [iterate, body, compressBlock, Code.allInstrs, hm, Bool.and_true]
    decide +kernel)) (constantTime hf) (by
    sig_implies [Spec.Pbkdf2.iterateSha256Contract, Spec.Pbkdf2.iterateSha256Sig,
      Proof.Pbkdf2.iterateSha256X86_64, X86_64.abi, X86_64.argRegs] [sat] using sat)

theorem iterate_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (iterate f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [iterate, body, compressBlock, Code.all, h, Bool.and_true]
  decide +kernel

end VG.Proof.Pbkdf2.X86_64.Iterate
