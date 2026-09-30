import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Base
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA verification on x86-64: calls

Untrusted: everything here is checked by Lean. A call of verified code,
with the moves of its arguments before it (`callAt_ok`), leaves the
permissions and the callee-saved registers as they were, and changes memory
only within the buffers it writes and the 24 bytes of stack below `rsp`
(`Post`); two runs whose arguments agree and whose callee's public data
agree leak the same (`callAt_tr`). A callee may be verified against its
contract with any stack up to 16 bytes: its precondition follows from the
one with 16 (`pre_stack`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64

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

theorem glue_nomem : ∀ (as : List (Reg × Arg)), ∀ i ∈ glue as, ∀ s, isa.addrs i s = []
  | [], _, h, _ => absurd h List.not_mem_nil
  | (d, a) :: as, i, h, s => by
    simp only [glue] at h
    rcases List.mem_append.mp h with h | h
    · cases a <;> simp only [Arg.instrs, List.mem_cons, List.not_mem_nil, or_false] at h <;>
        rcases h with rfl | rfl <;> rfl
    · exact glue_nomem as i h s

/-! ## Calls -/

/-- The arguments of a call, in their registers. -/
abbrev Args (as : List (Reg × Arg)) (s s1 : State) : Prop :=
  ((∀ a ∈ as, s1.gpr a.1 = a.2.val s) ∧ s1.mem = s.mem) ∧ Keep argRegs s s1

theorem callAt_ok {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 2) {as : List (Reg × Arg)} (hok : ∀ a ∈ as, a.2.Ok ∧ a.1 ∈ argRegs)
    (hnd : (as.map (·.1)).Nodup) {s : State} {rd wr : List Region}
    (hpre : ∀ s1, Args as s s1 → k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (callAt n c as) s fun s' => Post s s' wr ∧
      ∃ s1, Args as s s1 ∧ ∃ s₂ : State, s₂.mem = s'.mem ∧
        (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧ k.post (s1.callEntry.withRegions rd wr) s₂ := by
  refine WP.seq (WP.mono (glue_ok' hok hnd s) fun s1 h1 => ?_)
  have hm := h1.1.2
  have k1 := h1.2
  refine WP.call hv hsp (by omega) (hpre s1 h1) (by rw [k1.2.1, k1.2.2]; exact hc)
    (by rw [k1.2.2]; exact hw) fun s' hrd hwr hcs hf _ hpost => ⟨⟨hrd.trans k1.2.1, hwr.trans k1.2.2,
      fun r hr => by rw [hcs r hr, k1.gpr (argRegs_cs r hr)], ?_⟩, s1, h1, hpost⟩
  have hsp1 : s1.gpr .rsp = s.gpr .rsp := k1.gpr (by decide)
  rw [hm, hsp1] at hf
  exact Frame.below_mono hf (by omega) (by omega)

/-- The trace of the moves then a call, from two runs where the moves are
the same and the callee's public data agree. -/
theorem callAt_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {as : List (Reg × Arg)} (hok : ∀ a ∈ as, a.2.Ok ∧ a.1 ∈ argRegs)
    (hnd : (as.map (·.1)).Nodup) {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → Args as x x1 → Args as y y1 → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (x1.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y1.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x.rd ++ x.wr) ∧ Covers wr₁ x.wr ∧
      Covers (rd₂ ++ wr₂) (y.rd ++ y.wr) ∧ Covers wr₂ y.wr ∧ x.gpr .rsp = y.gpr .rsp) :
    RelCT isa P (callAt n c as) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ Args as x x1 ∧ Args as y y1)
      (block_nomem_tr (glue_nomem as)) (fun x y _ => ⟨glue_ok' hok hnd x, glue_ok' hok hnd y⟩)
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.callEx hv hct fun x1 y1 ⟨x, y, hp, h1, h2⟩ => by
      obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, pub, c₁, w₁, c₂, w₂, e⟩ := hP x y x1 y1 hp h1 h2
      exact ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, pub, by rw [h1.2.2.1, h1.2.2.2]; exact c₁, by rw [h1.2.2.2]; exact w₁,
        by rw [h2.2.2.1, h2.2.2.2]; exact c₂, by rw [h2.2.2.2]; exact w₂,
        by rw [h1.2.gpr (by decide), h2.2.gpr (by decide), e]⟩)

/-! ## The callee's stack -/

theorem stackBelow_sub (sp : Addr) {n : Nat} (hn : n ≤ 16) :
    ∀ r ∈ stackBelow sp n, Region.Sub r (below sp 16) := by
  intro r hr
  match n, hr with
  | m + 1, hr =>
    simp only [stackBelow, List.mem_singleton] at hr
    subst hr
    exact below_sub (by omega) (by omega)

/-- A contract with a stack of at most 16 bytes asks no more than with 16. -/
theorem pre_stack {sig : Sig} {pre : Curry (sig.words X86_64.abi.ptrBits) (Mem → Prop)}
    {post : sig.Post X86_64.abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words X86_64.abi.ptrBits) (Mem → List Nat))} {n : Nat} (hn : n ≤ 16) {s : State}
    (h : (sig.contract X86_64.abi pre post wa 16 leak).pre s) : (sig.contract X86_64.abi pre post wa n leak).pre s := by
  unfold Sig.contract at h ⊢
  dsimp only at h ⊢
  generalize X86_64.abi.args ((sig.words X86_64.abi.ptrBits).map (·.bits X86_64.abi.ptrBits)) = o at h ⊢
  cases o with
  | none => exact h
  | some vals =>
    obtain ⟨hwf, hrd, hwr, hpw, hres, hnw, hpre⟩ := h
    refine ⟨?_, hrd, hwr, hpw, fun r hr a ha => ?_, hnw, hpre⟩
    · simp only [X86_64.abi] at hwf ⊢
      split at hwf
      · rw [ifp ‹_›]
        rcases n with _ | n
        · trivial
        · exact Nat.le_trans hn hwf
      · rw [ifn ‹_›]
        refine ⟨?_, hwf.2⟩
        rcases n with _ | n
        · trivial
        · exact Nat.le_trans hn hwf.1
    · simp only [X86_64.abi, List.mem_cons] at hr hres
      rcases hr with rfl | hr
      · exact hres _ (.inl rfl) a ha
      · exact (hres _ (.inr (List.mem_singleton_self _)) a ha).sub_left (stackBelow_sub _ hn r hr)

end VG.Proof.MlDsa.X86_64.Verify
