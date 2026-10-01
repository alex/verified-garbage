import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Base
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig

/-!
# ML-DSA on AArch64: calls

Untrusted: everything here is checked by Lean. A call of verified code,
with the moves of its arguments before it (`callAt_ok`), leaves the
permissions, the stack pointer, the low halves of v8–v15 and the callee-saved GPRs but `x30` as
they were, and changes memory only within the buffers it writes and the `S`
bytes of stack below the stack pointer (`Post`); two runs whose callee's
preconditions hold and whose public data agree leak the same (`callAt_tr`).

A callee (`CalleeOk S`) is correct and constant time under its contract
with a stack of `S` bytes, and its frames use at most those `S` bytes; one
verified against its contract with any stack up to `S` is
(`CalleeOk.of_verified`, from `pre_stack`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlKem.AArch64 (Only Keep)

/-! ## Blocks that access no memory -/

theorem execBlock_nomem {is : List Instr} (h : ∀ i ∈ is, ∀ s, isa.addrs i s = []) :
    ∀ {s s' : State} {t : List Leak}, execBlock isa is s = some (s', t) → t = [] := by
  induction is with
  | nil => intro s s' t e; simp [execBlock] at e; exact e.2
  | cons i is ih =>
    intro s s' t e
    simp only [execBlock] at e
    split at e
    · cases e
    · obtain ⟨⟨s₂, t₂⟩, e₂, he⟩ := Option.map_eq_some_iff.mp e
      simp only [Prod.mk.injEq] at he
      rw [← he.2, show addrs i s = [] from h i (List.mem_cons_self ..) s,
        ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) e₂]
      rfl

/-- A block that accesses no memory leaks nothing. -/
theorem block_nomem_tr {is : List Instr} (h : ∀ i ∈ is, ∀ s, isa.addrs i s = []) {P : State → State → Prop} :
    RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨(execBlock_nomem h e₁).trans (execBlock_nomem h e₂).symm, trivial⟩

theorem movV_nomem (d : Reg) (v : Nat) : ∀ i ∈ movV d v, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  unfold movV Impl.MlKem.AArch64.movImm at hi
  split at hi <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hi <;>
    rcases hi with rfl | rfl | rfl | rfl <;> rfl

theorem lea_nomem (d b : Reg) (off : Nat) : ∀ i ∈ lea d b off, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  unfold lea at hi
  split at hi
  · simp only [List.mem_singleton] at hi; subst hi; rfl
  · rcases List.mem_append.mp hi with hi | hi
    · exact movV_nomem d off i hi s
    · simp only [List.mem_singleton] at hi; subst hi; rfl

theorem glue_nomem : ∀ (as : List (Reg × Arg)), ∀ i ∈ glue as, ∀ s, isa.addrs i s = []
  | [], _, h, _ => absurd h List.not_mem_nil
  | (d, a) :: as, i, h, s => by
    simp only [glue] at h
    rcases List.mem_append.mp h with h | h
    · cases a with
      | ptr p => exact lea_nomem d p.1 p.2 i h s
      | imm v => exact movV_nomem d v i h s
    · exact glue_nomem as i h s

/-! ## Callees -/

/-- A callee: correct and constant time under the contract `k` (a shared
contract with `S` bytes of stack), whose frames use at most those `S` bytes. -/
structure CalleeOk (S : Nat) (c : Prog isa) (k : Contract isa) : Prop where
  correct : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s'
  ct : ConstantTime isa k.pre k.pub c
  fd : 16 * c.aarch64Depth ≤ S

theorem stackBelow_sub (sp : Addr) {n S : Nat} (hn : n ≤ S) (hS : S < 2 ^ 64) :
    ∀ r ∈ stackBelow sp n, Region.Sub r (below sp S) := by
  intro r hr
  match n, hr with
  | m + 1, hr =>
    simp only [stackBelow, List.mem_singleton] at hr
    subst hr
    exact below_sub hn hS

/-- What `AArch64.abi.wf` asks of the stack pointer for a stack of `n` bytes. -/
def wfP (n sp : Nat) : Prop := match n with | 0 => True | n => n ≤ sp

theorem wf_mono {n S sp : Nat} (hn : n ≤ S) (h : wfP S sp) : wfP n sp := by
  unfold wfP at h ⊢
  rcases n with _ | n
  · trivial
  · rcases S with _ | S
    · omega
    · exact Nat.le_trans hn h

/-- A contract with a stack of at most `S` bytes asks no more than with `S`. -/
theorem pre_stack {sig : Sig} {pre : Curry (sig.words AArch64.abi.ptrBits) (Mem → Prop)}
    {post : sig.Post AArch64.abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words AArch64.abi.ptrBits) (Mem → List Nat))} {n S : Nat} (hn : n ≤ S)
    (hS : S < 2 ^ 64) {s : State}
    (h : (sig.contract AArch64.abi pre post wa S leak).pre s) : (sig.contract AArch64.abi pre post wa n leak).pre s := by
  unfold Sig.contract at h ⊢
  dsimp only at h ⊢
  generalize AArch64.abi.args ((sig.words AArch64.abi.ptrBits).map (·.bits AArch64.abi.ptrBits)) = o at h ⊢
  cases o with
  | none => exact h
  | some vals =>
    obtain ⟨hwf, hrd, hwr, hpw, hres, hnw, hpre⟩ := h
    refine ⟨?_, hrd, hwr, hpw, fun r hr a ha => ?_, hnw, hpre⟩
    · simp only [AArch64.abi] at hwf ⊢
      split at hwf
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ‹_›)]; exact wf_mono hn hwf
      · rw [ite_eq_right_of_eq_false _ _ (eq_false ‹_›)]; exact ⟨wf_mono hn hwf.1, hwf.2⟩
    · simp only [AArch64.abi] at hr hres
      rcases S with _ | S
      · rcases n with _ | n
        · simp [stackBelow] at hr
        · omega
      · exact (hres _ (List.mem_singleton_self _) a ha).sub_left (stackBelow_sub _ hn hS r hr)

/-- A callee verified against its shared contract with at most `S` bytes of
stack, whose frames use at most `S` bytes. -/
theorem CalleeOk.of_verified {S : Nat} (hS : S < 2 ^ 64) {c : Prog isa} {sig : Sig}
    {pre : Curry (sig.words AArch64.abi.ptrBits) (Mem → Prop)} {post : sig.Post AArch64.abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words AArch64.abi.ptrBits) (Mem → List Nat))} {n : Nat}
    (h : Verified AArch64.target c (sig.contract AArch64.abi pre post wa n leak)) (hn : n ≤ S)
    (hfd : 16 * c.aarch64Depth ≤ S) :
    CalleeOk S c (sig.contract AArch64.abi pre post wa S leak) :=
  ⟨fun s hs => h.1 s (pre_stack hn hS hs),
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
      h.2.1 s₁ s₂ t₁ t₂ s₁' s₂' (pre_stack hn hS h₁) (pre_stack hn hS h₂) hp e₁ e₂, hfd⟩

/-! ## Calls -/

theorem callAt_ok {S : Nat} (hS : S < 2 ^ 64) {n : String} {c : Prog isa} {k : Contract isa}
    (C : CalleeOk S c k) {as : List (Reg × Arg)} (hok : ∀ a ∈ as, a.2.Ok ∧ a.1 ∈ argRegs)
    (hnd : (as.map (·.1)).Nodup) {s : State} {rd wr : List Region}
    (hpre : ∀ s1, Args as s s1 → k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (callAt n c as) s fun s' => Post S s s' wr ∧
      ∃ s1, Args as s s1 ∧ k.post (s1.callEntry.withRegions rd wr) (s'.withRegions rd wr) := by
  refine WP.seq (WP.mono (glue_ok hok hnd s) fun s1 h1 => ?_)
  have k1 := h1.2
  refine WP.callFV C.correct (hpre s1 h1) (by rw [k1.rd, k1.wr]; exact hc) (by rw [k1.wr]; exact hw)
    (fun s' hrd hwr hsp hf hcs hvcs hpost => ?_) (by have := C.fd; omega)
  refine ⟨⟨hrd.trans k1.rd, hwr.trans k1.wr, hsp.trans k1.sp,
    fun r hr h30 => by rw [hcs r hr h30, k1.gpr r (argRegs_pres r hr)], ?_, fun r hr => (hvcs r hr).trans (k1.vcs r hr)⟩, s1, h1, hpost⟩
  rw [h1.1.2, k1.sp] at hf
  exact Frame.below_mono hf C.fd hS

/-- The trace of the moves then a call, from two runs whose callee's
preconditions hold and whose callee's public data agree. -/
theorem callAt_tr {S : Nat} {n : String} {c : Prog isa} {k : Contract isa} (C : CalleeOk S c k)
    {as : List (Reg × Arg)} (hok : ∀ a ∈ as, a.2.Ok ∧ a.1 ∈ argRegs) (hnd : (as.map (·.1)).Nodup)
    {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → Args as x x1 → Args as y y1 → ∃ rd wr : List Region,
      k.pre (x1.callEntry.withRegions rd wr) ∧ k.pre (y1.callEntry.withRegions rd wr) ∧
      k.pub (x1.callEntry.withRegions rd wr) (y1.callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) (x.rd ++ x.wr) ∧ Covers wr x.wr ∧
      Covers (rd ++ wr) (y.rd ++ y.wr) ∧ Covers wr y.wr) :
    RelCT isa P (callAt n c as) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ Args as x x1 ∧ Args as y y1)
      (block_nomem_tr (glue_nomem as)) (fun x y _ => ⟨glue_ok hok hnd x, glue_ok hok hnd y⟩)
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.mono (RelCT.exists_ (P := fun (a : List Region × List Region) (x1 y1 : State) =>
        k.pre (x1.callEntry.withRegions a.1 a.2) ∧ k.pre (y1.callEntry.withRegions a.1 a.2) ∧
        k.pub (x1.callEntry.withRegions a.1 a.2) (y1.callEntry.withRegions a.1 a.2) ∧
        Covers (a.1 ++ a.2) (x1.rd ++ x1.wr) ∧ Covers a.2 x1.wr ∧
        Covers (a.1 ++ a.2) (y1.rd ++ y1.wr) ∧ Covers a.2 y1.wr)
      fun a => RelCT.call C.correct C.ct a.1 a.2 fun _ _ h => h)
      (fun x1 y1 ⟨x, y, hp, h1, h2⟩ => by
        obtain ⟨rd, wr, p₁, p₂, pub, c₁, w₁, c₂, w₂⟩ := hP x y x1 y1 hp h1 h2
        exact ⟨(rd, wr), p₁, p₂, pub, by rw [h1.2.rd, h1.2.wr]; exact c₁, by rw [h1.2.wr]; exact w₁,
          by rw [h2.2.rd, h2.2.wr]; exact c₂, by rw [h2.2.wr]; exact w₂⟩)
      fun _ _ h => h)

end VG.Proof.MlDsa.AArch64.KeyGen
