import VerifiedGarbage.Proof.AesSiv.X86_64.FinishLong

/-!
# AES-SIV on x86-64: finishing S2V (`finish`)

`finish` branches on `L < 16` to the short case (`finishShort_wp`) or the
long one (`finishLong_wp`), which leave S2V's end at `W + out`. Every
branch and loop in it is on `L`, and the arguments of its calls are the same
in two runs with the same pointers and lengths (`finish_rel`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (k0 zero2 frame_store2)
open VG.Proof.CmacAes.Stream.X86_64 (UArgs FArgs toNat_ofNat upd_call upd_rel fin_rel)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem cmp16_ok {s : State} (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (hL : L < 2 ^ 64) :
    ∃ s', runBlock isa [.alu .cmp .r14 (imm 16)] s = some s' ∧ s'.cf = some (decide (L < 16)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cf_arithFlags, h14, sx_ofNat (by decide), toNat_ofNat hL, toNat_ofNat (by decide)]
  all_goals rfl

theorem FinPost.of_mem {s₁ s s' : State} {out : Nat} (hm : s₁.mem = s.mem) (h : FinPost s₀ C D P W R L out s₁ s') :
    FinPost s₀ C D P W R L out s s' :=
  ⟨h.regs, hm ▸ h.frame, hm ▸ h.out⟩

theorem finish_wp (v : Ctr32Impl) (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s)
    {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (finish v.callee v.suffix out) s (FinPost s₀ C D P W R L out s) := by
  obtain ⟨s₁, run₁, cf₁, g₁, m₁, rd₁, wr₁⟩ := cmp16_ok hr.r14 h.lt
  have hr₁ : Regs s₀ C D P W R L s₁ := hr.keep (fun r _ => by rw [g₁]) rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (L < 16)) cf₁ (fun hb => ?_) (fun hb => ?_)
  · exact WP.mono (finishShort_wp v h hr₁ (of_decide_eq_true hb) hout) fun _ p => p.of_mem m₁
  · exact WP.mono (finishLong_wp v h hr₁ (by have := of_decide_eq_false hb; omega) hout) fun _ p => p.of_mem m₁

/-! ## Constant time -/

/-- A slot of the working space below `W + 160`, apart from the state at
`W + out`, keeps its value across an update. -/
theorem upd_keep (v : Ctr32Impl) (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) {Q : Addr} {n : Nat}
    (hu : UArgs s C (W + BitVec.ofNat 64 out) Q (W + BitVec.ofNat 64 256) R n) {nm : String}
    (S : Nat → Prop) (hS : ∀ d, S d → 144 ≤ d ∧ d + 8 ≤ 160) :
    WP isa (.call nm (Impl.CmacAes.X86_64.update v.callee)) s fun s' => Regs s₀ C D P W R L s' ∧
      ∀ d, S d → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
  refine WP.mono (upd_call v nm hu) fun s' h' => ⟨hr.keep h'.saved h'.rd h'.wr, fun d hd => ?_⟩
  have := hS d hd
  have hwW := h.wW
  refine h'.frame.readW (Region.contains_self _ 8) (fun r hr' => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · rw [hr.rsp]; exact (h.stk_w.sub_right (h.sW (by omega))).symm

/-- The pair of runs, with the same arguments. -/
abbrev RR (s₀ s₀' : State) (C D P W : Addr) (R L : Nat) (a b : State) : Prop :=
  Regs s₀ C D P W R L a ∧ Regs s₀' C D P W R L b

theorem short_rel (v : Ctr32Impl) {s₀' : State} (h : Env s₀ C D P W R L) (h' : Env s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (hL : L < 16) {out : Nat} (hout : out = 0 ∨ out = 112) :
    RelCT isa (RR s₀ s₀' C D P W R L) (.seq shortTail (shortMac v.callee v.suffix out)) (RR s₀ s₀' C D P W R L) := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) shortTail
      hc).isSome = true := ⟨_, by taint_decide⟩
  have hB' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15,
      .rsp]) (.block (zero16 .r15 o ++
        [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (imm o),
         .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .mov32 .r8 (imm 16), .mov .r9 (.reg .r15),
         .alu .add .r9 (imm csOff)])) hc).isSome = true := by
    rintro o (rfl | rfl)
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ := hB' out hout
  have t₁ := (RelCT.taint (A := taint) (P := RR s₀ s₀' C D P W R L) _ (fun a b hab => regs_agree hq hab.1 hab.2)
    hA).wp (F₁ := Regs s₀ C D P W R L) (F₂ := Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (shortTail_wp h hab.1 hL) fun _ p => p.1, WP.mono (shortTail_wp h' hab.2 hL) fun _ p => p.1⟩
  have mpre {σ x : State} (hσ : Env σ C D P W R L) (hx : Regs σ C D P W R L x) :
      WP isa (.block (zero16 .r15 out ++
        [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (imm out),
         .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .mov32 .r8 (imm 16), .mov .r9 (.reg .r15),
         .alu .add .r9 (imm csOff)])) x fun y => Regs σ C D P W R L y ∧
        FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R := by
    obtain ⟨y, run, hy, fa, _⟩ := macPre_ok hσ hx hout
    exact WP.of_runBlock ⟨y, run, hy, fa⟩
  have t₂ := (RelCT.taint (A := taint) (P := RR s₀ s₀' C D P W R L) _ (fun a b hab => regs_agree hq hab.1 hab.2)
    hB).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧
      FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧
      FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R)
    fun a b hab => ⟨mpre h hab.1, mpre h' hab.2⟩
  have t₃ := (fin_rel v ("vg_cmac_aes_finalize" ++ v.suffix)
    (P := fun a b => (Regs s₀ C D P W R L a ∧
      FArgs a C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R) ∧
      Regs s₀' C D P W R L b ∧
      FArgs b C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R)
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.2, hab.2.2, by rw [hab.1.1.rsp, hab.2.1.rsp, hq]⟩).wp
    (F₁ := Regs s₀ C D P W R L) (F₂ := Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (finr_call v _ hab.1.2) fun _ p => hab.1.1.keep p.saved p.rd p.wr,
      WP.mono (finr_call v _ hab.2.2) fun _ p => hab.2.1.keep p.saved p.rd p.wr⟩
  exact (t₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((t₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    (t₃.mono (fun _ _ h => h) fun _ _ h => h.2))

theorem long_rel (v : Ctr32Impl) {s₀' : State} (h : Env s₀ C D P W R L) (h' : Env s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (hL16 : 16 ≤ L) {out : Nat} (hout : out = 0 ∨ out = 112) :
    RelCT isa (RR s₀ s₀' C D P W R L) (.seq longTail (longMac v.callee v.suffix out)) (RR s₀ s₀' C D P W R L) := by
  have hlt := h.lt
  have hj1 := jOf_le L
  have hwW := h.wW
  obtain ⟨_, hT⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) longTail
      hc).isSome = true := ⟨_, by taint_decide⟩
  have hM1' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14,
      .r15, .rsp]) (.block (zero16 .r15 o ++
        [.mov .r8 (.mem (at_ .r15 dbOff)), .shift .shr .r8 4, .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp),
         .mov .rdx (.reg .r15), .alu .add .rdx (imm o), .mov .rcx (.reg .r13), .mov .r9 (.reg .r15),
         .alu .add .r9 (imm csOff)])) hc).isSome = true := by
    rintro o (rfl | rfl)
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, hM1⟩ := hM1' out hout
  have hM3' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14,
      .r15, .rsp]) (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm o), .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff),
        .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff), .store (at_ .r15 (dbOff + 8)) .r8]) hc).isSome = true := by
    rintro o (rfl | rfl)
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, hM3⟩ := hM3' out hout
  have hM4' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14,
      .r15, .rsp]) (.block [.mov .rax (.mem (at_ .r15 (dbOff + 8))), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .mov .r8 (.reg .r14), .alu .sub .r8 (.mem (at_ .r15 dbOff)), .alu .sub .r8 (.reg .rax),
        .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .alu .add .rcx (.reg .rax),
        .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm o), .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)]) hc).isSome = true := by
    rintro o (rfl | rfl)
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, hM4⟩ := hM4' out hout
  obtain ⟨_, hM2⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block [.mov32 .r8 (.imm 0), .alu .cmp .r14 (imm 17)]) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hI0⟩ : ∃ hc, (taint.check (Taint.ofRegs []) (.block []) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hI1⟩ : ∃ hc, (taint.check (Taint.ofRegs []) (.block [.mov32 .r8 (imm 1)]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  -- What each run keeps between the calls.
  let A := fun (x : State) => x.mem.readW (W + BitVec.ofNat 64 dbOff) 64 = BitVec.ofNat 64 (16 * kOf L)
  let J := fun (x : State) => x.mem.readW (W + BitVec.ofNat 64 (dbOff + 8)) 64 = BitVec.ofNat 64 (jOf L)
  have wT {σ x : State} (hσ : Env σ C D P W R L) (hx : Regs σ C D P W R L x) :
      WP isa longTail x fun y => Regs σ C D P W R L y ∧ A y :=
    WP.mono (longTail_wp hσ hx hL16) fun _ p => ⟨p.regs, p.a⟩
  have wM1 {σ x : State} (hσ : Env σ C D P W R L) (hx : Regs σ C D P W R L x) (ha : A x) :
      WP isa (.block (zero16 .r15 out ++
        [.mov .r8 (.mem (at_ .r15 dbOff)), .shift .shr .r8 4, .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp),
         .mov .rdx (.reg .r15), .alu .add .rdx (imm out), .mov .rcx (.reg .r13), .mov .r9 (.reg .r15),
         .alu .add .r9 (imm csOff)])) x fun y => Regs σ C D P W R L y ∧
        UArgs y C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧ A y := by
    obtain ⟨y, run, hy, u, m⟩ := m1_ok hσ hx hout hL16 ha
    refine WP.of_runBlock ⟨y, run, hy, u, ?_⟩
    show y.mem.readW _ 64 = _
    rw [m, zero2, (frame_store2 _ _ _).readW (w := 64) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (d := dbOff) (n := 8) (e := out) (k := 16) (by simp only [dbOff]; omega)
        (by simp only [dbOff]; omega) (by omega)) (by decide)]
    exact ha
  have wU1 {σ x : State} (hσ : Env σ C D P W R L) (hx : Regs σ C D P W R L x)
      (hu : UArgs x C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L)) (ha : A x) :
      WP isa (.call ("vg_cmac_aes_update" ++ v.suffix) (Impl.CmacAes.X86_64.update v.callee)) x fun y => Regs σ C D P W R L y ∧ A y :=
    WP.mono (upd_keep v hσ hx hout hu (fun d => d = dbOff) (fun d hd => by subst hd; decide))
      fun _ p => ⟨p.1, (p.2 dbOff rfl).trans ha⟩
  have wM2 {σ x : State} (hx : Regs σ C D P W R L x) (ha : A x) :
      WP isa (.block [.mov32 .r8 (.imm 0), .alu .cmp .r14 (imm 17)]) x fun y => Regs σ C D P W R L y ∧
        y.gpr .r8 = 0 ∧ y.cf = some (decide (L < 17)) ∧ A y := by
    obtain ⟨y, run, r8, cf, g, m, rd, wr⟩ := m2_ok hx.r14 hlt
    exact WP.of_runBlock ⟨y, run, hx.keep (fun r hr => g r (by rintro rfl; simp [calleeSaved] at hr)) rd wr, r8, cf,
      by show y.mem.readW _ 64 = _; rw [m]; exact ha⟩
  have wI {σ x : State} (hx : Regs σ C D P W R L x) (h8 : x.gpr .r8 = 0)
      (hcf : x.cf = some (decide (L < 17))) (ha : A x) :
      WP isa (.ite .b (.block []) (.block [.mov32 .r8 (imm 1)])) x fun y => Regs σ C D P W R L y ∧
        y.gpr .r8 = BitVec.ofNat 64 (jOf L) ∧ A y :=
    WP.mono (jIte_wp h8 hcf) fun y ⟨r8, g, m, rd, wr⟩ =>
      ⟨hx.keep (fun r hr => g r (by rintro rfl; simp [calleeSaved] at hr)) rd wr, r8,
        by show y.mem.readW _ 64 = _; rw [m]; exact ha⟩
  have wM3 {σ x : State} (hσ : Env σ C D P W R L) (hx : Regs σ C D P W R L x)
      (h8 : x.gpr .r8 = BitVec.ofNat 64 (jOf L)) (ha : A x) :
      WP isa (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm out), .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff),
        .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff), .store (at_ .r15 (dbOff + 8)) .r8]) x fun y => Regs σ C D P W R L y ∧
        UArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) ∧
        A y ∧ J y := by
    obtain ⟨y, run, hy, u, m⟩ := m3_ok hσ hx hout h8
    refine WP.of_runBlock ⟨y, run, hy, u, ?_, ?_⟩
    · show y.mem.readW _ 64 = _
      rw [m, Mem.readW_writeW_sep (Offset.sep W (d := dbOff) (n := 8) (e := dbOff + 8) (k := 8) (by decide)
        (by decide) (by decide)) (by decide)]
      exact ha
    · show y.mem.readW _ 64 = _
      rw [m, Mem.readW_writeW_self64]
  have wU2 {σ x : State} (hσ : Env σ C D P W R L) (hx : Regs σ C D P W R L x)
      (hu : UArgs x C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L))
      (ha : A x) (hj : J x) :
      WP isa (.call ("vg_cmac_aes_update" ++ v.suffix) (Impl.CmacAes.X86_64.update v.callee)) x fun y => Regs σ C D P W R L y ∧ A y ∧ J y :=
    WP.mono (upd_keep v hσ hx hout hu (fun d => d = dbOff ∨ d = dbOff + 8)
        (fun d hd => by rcases hd with rfl | rfl <;> decide))
      fun _ p => ⟨p.1, (p.2 dbOff (Or.inl rfl)).trans ha, (p.2 (dbOff + 8) (Or.inr rfl)).trans hj⟩
  have wM4 {σ x : State} (hσ : Env σ C D P W R L) (hx : Regs σ C D P W R L x) (ha : A x) (hj : J x) :
      WP isa (.block [.mov .rax (.mem (at_ .r15 (dbOff + 8))), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .mov .r8 (.reg .r14), .alu .sub .r8 (.mem (at_ .r15 dbOff)), .alu .sub .r8 (.reg .rax),
        .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .alu .add .rcx (.reg .rax),
        .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm out), .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)]) x fun y => Regs σ C D P W R L y ∧
        FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
          (L - 16 * kOf L - 16 * jOf L) R := by
    obtain ⟨y, run, hy, fa, _⟩ := m4_ok hσ hx hout hL16 ha hj
    exact WP.of_runBlock ⟨y, run, hy, fa⟩
  -- The relations, segment by segment.
  have rT := (RelCT.taint (A := taint) (P := RR s₀ s₀' C D P W R L) _ (fun a b hab => regs_agree hq hab.1 hab.2)
    hT).wp (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧ A y) (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧ A y)
    fun a b hab => ⟨wT h hab.1, wT h' hab.2⟩
  have rM1 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧ A a) ∧ Regs s₀' C D P W R L b ∧ A b) _
    (fun a b hab => regs_agree hq hab.1.1 hab.2.1) hM1).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧
      UArgs y C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧ A y)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧
      UArgs y C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧ A y)
    fun a b hab => ⟨wM1 h hab.1.1 hab.1.2, wM1 h' hab.2.1 hab.2.2⟩
  have rU1 := (upd_rel v ("vg_cmac_aes_update" ++ v.suffix)
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧
      UArgs a C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧ A a) ∧
      Regs s₀' C D P W R L b ∧ UArgs b C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧ A b)
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.2.1, hab.2.2.1, by rw [hab.1.1.rsp, hab.2.1.rsp, hq]⟩).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧ A y) (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧ A y)
    fun a b hab => ⟨wU1 h hab.1.1 hab.1.2.1 hab.1.2.2, wU1 h' hab.2.1 hab.2.2.1 hab.2.2.2⟩
  have rM2 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧ A a) ∧ Regs s₀' C D P W R L b ∧ A b) _
    (fun a b hab => regs_agree hq hab.1.1 hab.2.1) hM2).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧ y.gpr .r8 = 0 ∧ y.cf = some (decide (L < 17)) ∧ A y)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧ y.gpr .r8 = 0 ∧ y.cf = some (decide (L < 17)) ∧ A y)
    fun a b hab => ⟨wM2 hab.1.1 hab.1.2, wM2 hab.2.1 hab.2.2⟩
  have rI := (RelCT.ite (P := fun (a b : State) =>
      (Regs s₀ C D P W R L a ∧ a.gpr .r8 = 0 ∧ a.cf = some (decide (L < 17)) ∧ A a) ∧
      Regs s₀' C D P W R L b ∧ b.gpr .r8 = 0 ∧ b.cf = some (decide (L < 17)) ∧ A b)
    (fun a b hab => by show a.cf = b.cf; rw [hab.1.2.2.1, hab.2.2.2.1])
    (RelCT.taint (A := taint) _ (fun _ _ _ => Taint.agree_ofRegs fun _ h => absurd h List.not_mem_nil) hI0)
    (RelCT.taint (A := taint) _ (fun _ _ _ => Taint.agree_ofRegs fun _ h => absurd h List.not_mem_nil) hI1)).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧ y.gpr .r8 = BitVec.ofNat 64 (jOf L) ∧ A y)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧ y.gpr .r8 = BitVec.ofNat 64 (jOf L) ∧ A y)
    fun a b hab => ⟨wI hab.1.1 hab.1.2.1 hab.1.2.2.1 hab.1.2.2.2, wI hab.2.1 hab.2.2.1 hab.2.2.2.1 hab.2.2.2.2⟩
  have rM3 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧ a.gpr .r8 = BitVec.ofNat 64 (jOf L) ∧ A a) ∧
      Regs s₀' C D P W R L b ∧ b.gpr .r8 = BitVec.ofNat 64 (jOf L) ∧ A b) _
    (fun a b hab => regs_agree hq hab.1.1 hab.2.1) hM3).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧
      UArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) ∧ A y ∧ J y)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧
      UArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) ∧ A y ∧ J y)
    fun a b hab => ⟨wM3 h hab.1.1 hab.1.2.1 hab.1.2.2, wM3 h' hab.2.1 hab.2.2.1 hab.2.2.2⟩
  have rU2 := (upd_rel v ("vg_cmac_aes_update" ++ v.suffix)
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧
      UArgs a C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) ∧ A a ∧ J a) ∧
      Regs s₀' C D P W R L b ∧
      UArgs b C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) ∧ A b ∧ J b)
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.2.1, hab.2.2.1, by rw [hab.1.1.rsp, hab.2.1.rsp, hq]⟩).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧ A y ∧ J y) (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧ A y ∧ J y)
    fun a b hab => ⟨wU2 h hab.1.1 hab.1.2.1 hab.1.2.2.1 hab.1.2.2.2, wU2 h' hab.2.1 hab.2.2.1 hab.2.2.2.1 hab.2.2.2.2⟩
  have rM4 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧ A a ∧ J a) ∧ Regs s₀' C D P W R L b ∧ A b ∧ J b) _
    (fun a b hab => regs_agree hq hab.1.1 hab.2.1) hM4).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧
      FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * kOf L - 16 * jOf L) R)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧
      FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * kOf L - 16 * jOf L) R)
    fun a b hab => ⟨wM4 h hab.1.1 hab.1.2.1 hab.1.2.2, wM4 h' hab.2.1 hab.2.2.1 hab.2.2.2⟩
  have rF := (fin_rel v ("vg_cmac_aes_finalize" ++ v.suffix)
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧
      FArgs a C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * kOf L - 16 * jOf L) R) ∧ Regs s₀' C D P W R L b ∧
      FArgs b C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * kOf L - 16 * jOf L) R)
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.2, hab.2.2, by rw [hab.1.1.rsp, hab.2.1.rsp, hq]⟩).wp
    (F₁ := Regs s₀ C D P W R L) (F₂ := Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (finr_call v _ hab.1.2) fun _ p => hab.1.1.keep p.saved p.rd p.wr,
      WP.mono (finr_call v _ hab.2.2) fun _ p => hab.2.1.keep p.saved p.rd p.wr⟩
  exact (rT.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rM1.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((rU1.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rM2.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((rI.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rM3.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((rU2.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rM4.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    (rF.mono (fun _ _ h => h) fun _ _ h => h.2))))))))

theorem finish_rel (v : Ctr32Impl) {s₀' : State} (h : Env s₀ C D P W R L) (h' : Env s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) {out : Nat} (hout : out = 0 ∨ out = 112) :
    RelCT isa (RR s₀ s₀' C D P W R L) (finish v.callee v.suffix out) (RR s₀ s₀' C D P W R L) := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block [.alu .cmp .r14 (imm 16)]) hc).isSome = true := ⟨_, by taint_decide⟩
  have w {σ x : State} (hx : Regs σ C D P W R L x) :
      WP isa (.block [.alu .cmp .r14 (imm 16)]) x fun y => Regs σ C D P W R L y ∧ y.cf = some (decide (L < 16)) := by
    obtain ⟨y, run, cf, g, _, rd, wr⟩ := cmp16_ok hx.r14 h.lt
    exact WP.of_runBlock ⟨y, run, hx.keep (fun r _ => by rw [g]) rd wr, cf⟩
  have a := (RelCT.taint (A := taint) (P := RR s₀ s₀' C D P W R L) _ (fun a b hab => regs_agree hq hab.1 hab.2)
    hA).wp (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧ y.cf = some (decide (L < 16)))
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧ y.cf = some (decide (L < 16)))
    fun a b hab => ⟨w hab.1, w hab.2⟩
  refine (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq (RelCT.ite (fun a b hab => by
    show a.cf = b.cf; rw [hab.1.2, hab.2.2]) ?_ ?_)
  · by_cases hL : L < 16
    · exact (short_rel v h h' hq hL hout).mono (fun _ _ p => ⟨p.1.1.1, p.1.2.1⟩) fun _ _ p => p
    · exact RelCT.of_false fun a b hab => by
        have e := hab.2; rw [show isa.eval .b a = a.cf from rfl, hab.1.1.2] at e; simp [hL] at e
  · by_cases hL : L < 16
    · exact RelCT.of_false fun a b hab => by
        have e := hab.2; rw [show isa.eval .b a = a.cf from rfl, hab.1.1.2] at e; simp [hL] at e
    · exact (long_rel v h h' hq (by omega) hout).mono (fun _ _ p => ⟨p.1.1.1, p.1.2.1⟩) fun _ _ p => p

end VG.Proof.AesSiv.X86_64
