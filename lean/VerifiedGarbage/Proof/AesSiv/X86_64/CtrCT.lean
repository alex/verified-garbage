import VerifiedGarbage.Proof.AesSiv.X86_64.Ctr
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-SIV on x86-64: CTR is constant time

Every block's pointers and lengths are public (`r13`, `r14`), so the code
around the call of `vg_aes_ctr32` passes the taint analysis, and the call's
arguments are the same in both runs (`ctr_rel` of `CmacAes.X86_64`). Both
runs leave the loop after the same block, the last one (`ctr_tail`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64 VG.WriteBytes
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (bytesAt_frame zero2 zero2_bytes CallPre ctr_call ctr_rel)
open VG.Proof.CmacAes.Stream.X86_64 (copyMem_frame toNat_ofNat)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-- The registers of block `i`. -/
structure CR (s₀ : State) (C D P W : Addr) (R L i : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = C
  rbp : s.gpr .rbp = BitVec.ofNat 64 R
  r12 : s.gpr .r12 = D
  r13 : s.gpr .r13 = P + BitVec.ofNat 64 (16 * i)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (L - 16 * i)
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem CR.keep {s₀ s s' : State} {C D P W : Addr} {R L i : Nat} (h : CR s₀ C D P W R L i s)
    (hs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    CR s₀ C D P W R L i s' :=
  ⟨by rw [hs _ (by decide), h.rbx], by rw [hs _ (by decide), h.rbp], by rw [hs _ (by decide), h.r12],
    by rw [hs _ (by decide), h.r13], by rw [hs _ (by decide), h.r14], by rw [hs _ (by decide), h.r15],
    by rw [hs _ (by decide), h.rsp], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

theorem CInv.cr {m₀ : Mem} {q x : List Byte} {i : Nat} {s : State} (hi : CInv s₀ C D P W R L m₀ q x i s) :
    CR s₀ C D P W R L i s :=
  ⟨hi.rbx, hi.rbp, hi.r12, hi.r13, hi.r14, hi.r15, hi.rsp, hi.rd, hi.wr⟩

theorem cr_agree {s₀' a b : State} {i : Nat} (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (ha : CR s₀ C D P W R L i a)
    (hb : CR s₀' C D P W R L i b) :
    taint.Agree (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) a b := by
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ha.rbx, hb.rbx]
  · rw [ha.rbp, hb.rbp]
  · rw [ha.r12, hb.r12]
  · rw [ha.r13, hb.r13]
  · rw [ha.r14, hb.r14]
  · rw [ha.r15, hb.r15]
  · rw [ha.rsp, hb.rsp, hq]

theorem ctrPre_wp (h : Env s₀ C D P W R L) {i : Nat} {s : State} (hr : CR s₀ C D P W R L i s) :
    WP isa (.block ctrPre) s fun t => CallPre t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ CR s₀ C D P W R L i t := by
  have hwW := h.wW
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, g₁, m₁, rd₁, wr₁⟩ := ctrPre_ok h hr.rbx hr.rbp hr.r15 hr.rd hr.wr
  have hz : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 80) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, bytesAt_frame (copyMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (by omega) (by omega) (by omega))
      (by decide), zero2_bytes]
  have hr₁ := hr.keep g₁ rd₁ wr₁
  exact WP.of_runBlock ⟨s₁, run₁, h.cargs hr₁.rd hr₁.wr hr₁.rsp rdi₁ rsi₁ rdx₁ rcx₁ r8₁ r9₁ hz, hr₁⟩

/-- A block is constant time. -/
theorem body_rel (v : Ctr32Impl) {s₀' : State} (h : Env s₀ C D P W R L) (h' : Env s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (i : Nat) :
    RelCT isa (fun a b => CR s₀ C D P W R L i a ∧ CR s₀' C D P W R L i b) (ctrBody v.callee) fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) (.block ctrPre)
      hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.seq ctrMin (.seq xorBytes (.block ctrPost))) hc).isSome = true := ⟨_, by taint_decide⟩
  have r₁ := (RelCT.taint (A := taint) (P := fun a b => CR s₀ C D P W R L i a ∧ CR s₀' C D P W R L i b) _
    (fun a b hab => cr_agree hq hab.1 hab.2) hA).wp
    (F₁ := fun (t : State) => CallPre t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ CR s₀ C D P W R L i t)
    (F₂ := fun (t : State) => CallPre t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ CR s₀' C D P W R L i t)
    fun a b hab => ⟨ctrPre_wp h hab.1, ctrPre_wp h' hab.2⟩
  have r₂ := (ctr_rel v (P := fun (a b : State) => (CallPre a (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ CR s₀ C D P W R L i a) ∧
      CallPre b (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ CR s₀' C D P W R L i b)
    fun a b hab => ⟨_, _, _, _, _, hab.1.1, hab.2.1, by rw [hab.1.2.rsp, hab.2.2.rsp, hq]⟩).wp
    (F₁ := CR s₀ C D P W R L i) (F₂ := CR s₀' C D P W R L i)
    fun a b hab => ⟨WP.mono (ctr_call v hab.1.1) fun _ p => hab.1.2.keep p.saved p.rd p.wr,
      WP.mono (ctr_call v hab.2.1) fun _ p => hab.2.2.keep p.saved p.rd p.wr⟩
  have r₃ := RelCT.taint (A := taint) (P := fun a b => CR s₀ C D P W R L i a ∧ CR s₀' C D P W R L i b) _
    (fun a b hab => cr_agree hq hab.1 hab.2) hB
  exact (r₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((r₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq r₃)

/-- Block `i` of a run, with the slots of the data and its length as at the start. -/
def CI (s₀ : State) (C D P W : Addr) (R L i : Nat) (s : State) : Prop :=
  ∃ m₀ q x, CInv s₀ C D P W R L m₀ q x i s ∧ m₀.readW (W + BitVec.ofNat 64 dataOff) 64 = P ∧
    m₀.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L

/-- After the loop: what the reload of the pointer and the length needs. -/
structure CEnd (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = C
  rbp : s.gpr .rbp = BitVec.ofNat 64 R
  r12 : s.gpr .r12 = D
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  d208 : s.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P
  d216 : s.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L

theorem slot_keep (h : Env s₀ C D P W R L) {m m' : Mem} (hf : Frame (ctrRegions W P L (s₀.gpr .rsp)) m m') {d : Nat}
    (hd : 208 ≤ d) (hd' : d + 8 ≤ 256) : m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 := by
  have hwW := h.wW
  refine hf.readW (w := 64) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.p_w.symm.sub_left (h.sW (by omega))
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact (h.stk_w.sub_right (h.sW (by omega))).symm

/-- What a block leaves, for the loop: the last block, or the next one. -/
def BPost (s₀ : State) (C D P W : Addr) (R L i : Nat) (s : State) : Prop :=
  (L - 16 * i ≤ 16 ∧ s.zf = some true ∧ CEnd s₀ C D P W R L s) ∨
    (16 < L - 16 * i ∧ s.zf = some false ∧ CI s₀ C D P W R L (i + 1) s)

theorem body_wp (v : Ctr32Impl) (h : Env s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {i : Nat} {s : State} (hs : CI s₀ C D P W R L i s) :
    WP isa (ctrBody v.callee) s (BPost s₀ C D P W R L i) := by
  obtain ⟨m₀, q, x, hi, h208, h216⟩ := hs
  refine ctr_head v h hcp hi fun t₃ hh => WP.mono (ctr_tail h hPw hi hh) fun t ht => ?_
  rcases ht with ⟨hc, hz, hd⟩ | ⟨hc, hz, hi'⟩
  · exact Or.inl ⟨hc, hz, ⟨hd.rbx, hd.rbp, hd.r12, hd.r15, hd.rsp, hd.rd, hd.wr,
      by rw [slot_keep h hd.frame (by decide) (by decide)]; exact h208,
      by rw [slot_keep h hd.frame (by decide) (by decide)]; exact h216⟩⟩
  · exact Or.inr ⟨hc, hz, m₀, q, x, hi', h208, h216⟩

theorem CI.cr {i : Nat} {s : State} (hs : CI s₀ C D P W R L i s) : CR s₀ C D P W R L i s :=
  let ⟨_, _, _, hi, _, _⟩ := hs; hi.cr

theorem loop_rel (v : Ctr32Impl) {s₀' : State} (h : Env s₀ C D P W R L) (h' : Env s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) (hPw' : (⟨P, L⟩ : Region) ∈ s₀'.wr) (n : Nat) :
    RelCT isa (fun a b => ∃ i, n = L - 16 * i ∧ CI s₀ C D P W R L i a ∧ CI s₀' C D P W R L i b)
      (.loop (ctrBody v.callee) .ne) fun a b => CEnd s₀ C D P W R L a ∧ CEnd s₀' C D P W R L b := by
  refine RelCT.loop (M := isa) (fun (k : Nat) (a b : State) => ∃ i, k = L - 16 * i ∧ CI s₀ C D P W R L i a ∧
    CI s₀' C D P W R L i b) (fun k => ?_) n
  refine RelCT.exists_ fun i => ?_
  by_cases hk : k = L - 16 * i
  swap
  · exact RelCT.of_false fun a b hab => hk hab.1
  refine (((body_rel v h h' hq i).mono (fun a b hab => ⟨hab.2.1.cr, hab.2.2.cr⟩) fun _ _ h => h).wp
    (F₁ := BPost s₀ C D P W R L i) (F₂ := BPost s₀' C D P W R L i)
    fun a b hab => ⟨body_wp v h hcp hPw hab.2.1, body_wp v h' hcp hPw' hab.2.2⟩).mono
    (fun _ _ h => h) fun a b ⟨_, ha, hb⟩ => ?_
  rcases ha with ⟨hc, hz, he⟩ | ⟨hc, hz, hci⟩ <;> rcases hb with ⟨hc', hz', he'⟩ | ⟨hc', hz', hci'⟩
  · exact ⟨by simp [eval, hz, hz'], fun _ => ⟨he, he'⟩, fun e => by simp [eval, hz] at e⟩
  · omega
  · omega
  · exact ⟨by simp [eval, hz, hz'], fun e => by simp [eval, hz] at e, fun _ =>
      ⟨L - 16 * (i + 1), by omega, i + 1, rfl, hci, hci'⟩⟩

/-- What `ctr` needs of a run: the registers, the counter `Q`, and the
slots of the data and its length. -/
structure CtrPre (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  regs : Regs s₀ C D P W R L s
  cnt : ∃ (hi lo : BitVec 64) (q : List Byte), s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
    s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧ (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes q
  d208 : s.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P
  d216 : s.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L

theorem CtrPre.ci {s : State} (hs : CtrPre s₀ C D P W R L s) (hL : 0 < L) : CI s₀ C D P W R L 0 s := by
  obtain ⟨hi₀, lo₀, q, hhi, hlo, hq⟩ := hs.cnt
  exact ⟨s.mem, q, Spec.Aes.bytesAt s.mem P L, ⟨hs.regs.rbx, hs.regs.rbp, hs.regs.r12,
    by rw [hs.regs.r13, Nat.mul_zero, Proof.CmacAes.X86_64.k0], by rw [hs.regs.r14, Nat.mul_zero, Nat.sub_zero],
    hs.regs.r15, hs.regs.rsp, hs.regs.rd, hs.regs.wr, by omega,
    ⟨hi₀, lo₀, hhi, hlo, by rw [hq]; exact (BitVec.add_zero _).symm⟩, by rw [Nat.mul_zero, ctrPart_zero],
    Frame.refl _ _⟩, hs.d208, hs.d216⟩

theorem CtrPre.cend {s : State} (hs : CtrPre s₀ C D P W R L s) : CEnd s₀ C D P W R L s :=
  ⟨hs.regs.rbx, hs.regs.rbp, hs.regs.r12, hs.regs.r15, hs.regs.rsp, hs.regs.rd, hs.regs.wr, hs.d208, hs.d216⟩

theorem ctr_rel' (v : Ctr32Impl) {s₀' : State} (h : Env s₀ C D P W R L) (h' : Env s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) (hPw' : (⟨P, L⟩ : Region) ∈ s₀'.wr) :
    RelCT isa (fun a b => CtrPre s₀ C D P W R L a ∧ CtrPre s₀' C D P W R L b) (ctr v.callee)
      fun a b => Regs s₀ C D P W R L a ∧ Regs s₀' C D P W R L b := by
  have hlt := h.lt
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block [.alu .test .r14 (.reg .r14)]) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r15])
      (.block [.mov .r13 (.mem (at_ .r15 dataOff)), .mov .r14 (.mem (at_ .r15 lenOff))]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have wt {σ s : State} (hs : CtrPre σ C D P W R L s) :
      WP isa (.block [.alu .test .r14 (.reg .r14)]) s fun t => CtrPre σ C D P W R L t ∧ t.zf = some (decide (L = 0)) := by
    refine WP.of_runBlock ⟨arithFlags s (s.gpr .r14 &&& s.gpr .r14) false false, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some],
      ⟨hs.regs.keep (fun _ _ => rfl) rfl rfl, hs.cnt, hs.d208, hs.d216⟩, ?_⟩
    rw [zf_arithFlags, hs.regs.r14, BitVec.and_self, Proof.CmacAes.Stream.X86_64.beq_zero_iff, toNat_ofNat hlt]
  have a := (RelCT.taint (A := taint) (P := fun a b => CtrPre s₀ C D P W R L a ∧ CtrPre s₀' C D P W R L b) _
    (fun a b hab => regs_agree hq hab.1.regs hab.2.regs) hA).wp
    (F₁ := fun (t : State) => CtrPre s₀ C D P W R L t ∧ t.zf = some (decide (L = 0)))
    (F₂ := fun (t : State) => CtrPre s₀' C D P W R L t ∧ t.zf = some (decide (L = 0)))
    fun a b hab => ⟨wt hab.1, wt hab.2⟩
  have i := RelCT.ite (M := isa) (c := .e)
    (P := fun a b => (CtrPre s₀ C D P W R L a ∧ a.zf = some (decide (L = 0))) ∧
      CtrPre s₀' C D P W R L b ∧ b.zf = some (decide (L = 0)))
    (Q := fun a b => CEnd s₀ C D P W R L a ∧ CEnd s₀' C D P W R L b)
    (fun a b hab => by show a.zf = b.zf; rw [hab.1.2, hab.2.2])
    (RelCT.block_nil fun a b hab => ⟨hab.1.1.1.cend, hab.1.2.1.cend⟩)
    ((loop_rel v h h' hq hcp hPw hPw' (L - 16 * 0)).mono (fun a b hab => by
      have hL : 0 < L := by
        have e := hab.2; rw [show isa.eval .e a = a.zf from rfl, hab.1.1.2] at e
        simp at e; omega
      exact ⟨0, rfl, hab.1.1.1.ci hL, hab.1.2.1.ci hL⟩) fun _ _ h => h)
  have we {σ s : State} (hσ : Env σ C D P W R L) (hs : CEnd σ C D P W R L s) :
      WP isa (.block [.mov .r13 (.mem (at_ .r15 dataOff)), .mov .r14 (.mem (at_ .r15 lenOff))]) s
        (Regs σ C D P W R L) := by
    obtain ⟨t, run, r13, r14, g, _, rd, wr⟩ := ctrEnd_ok hσ hs.r15 hs.rd hs.wr hs.d208 hs.d216
    exact WP.of_runBlock ⟨t, run, by rw [g _ (by decide) (by decide), hs.rbx], by rw [g _ (by decide) (by decide),
      hs.rbp], by rw [g _ (by decide) (by decide), hs.r12], r13, r14, by rw [g _ (by decide) (by decide), hs.r15],
      by rw [g _ (by decide) (by decide), hs.rsp], by rw [rd, hs.rd], by rw [wr, hs.wr]⟩
  have e := (RelCT.taint (A := taint) (P := fun a b => CEnd s₀ C D P W R L a ∧ CEnd s₀' C D P W R L b) _
    (fun a b hab => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.r15, hab.2.r15]) hB).wp
    (F₁ := Regs s₀ C D P W R L) (F₂ := Regs s₀' C D P W R L) fun a b hab => ⟨we h hab.1, we h' hab.2⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq (i.seq (e.mono (fun _ _ h => h) fun _ _ h => h.2))

end VG.Proof.AesSiv.X86_64
