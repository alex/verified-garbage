import VerifiedGarbage.Proof.MlKem.X86_64.FragC

/-!
# ML-KEM-768 on x86-64: entry and exit of the top-level functions

Untrusted: everything here is checked by Lean. What holds of the state of
a top-level function throughout (`Top`): the permissions and the stack
pointer of entry, its pointers in their registers, its caller's
callee-saved registers saved in `scratch`, and the return address; its
buffers make a layout (`Lay.of`). The saves (`stores_read`), the return
(`topEpi_ok`), the branch on the results of `SampleNTT` (`ifOk_ok`,
`ifOk_tr`), and sequences of pieces indexed by a number (`seqR_ok`,
`seqR_tr`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## Layouts from the facts of a contract -/

theorem pairwise_sym {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: l, h, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with e | ha'
    · rcases List.mem_cons.mp hb with e' | hb'
      · exact absurd (e.trans e'.symm) hne
      · rw [e]; exact h.1 _ hb'
    · rcases List.mem_cons.mp hb with e' | hb'
      · rw [e']; exact hs _ _ (h.1 _ ha')
      · exact pairwise_sym hs h.2 ha' hb' hne

theorem Lay.of {rbs wbs : List (Reg × Nat)} {s : State} (small : ∀ b ∈ rbs ++ wbs, b.2 < 2 ^ 32)
    (pw : (rbs ++ wbs).Pairwise fun b b' => Region.Disjoint ⟨s.gpr b.1, b.2⟩ ⟨s.gpr b'.1, b'.2⟩)
    (stk : ∀ b ∈ rbs ++ wbs, (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr b.1, b.2⟩)
    (nw : ∀ b ∈ rbs ++ wbs, (s.gpr b.1).toNat + b.2 ≤ 2 ^ 64)
    (rd : ∀ b ∈ rbs ++ wbs, InRegions (s.rd ++ s.wr) (s.gpr b.1) b.2)
    (wr : ∀ b ∈ wbs, InRegions s.wr (s.gpr b.1) b.2)
    (ret : ∀ b ∈ rbs ++ wbs, (retR s).Disjoint ⟨s.gpr b.1, b.2⟩) : Lay rbs wbs s := by
  exact ⟨small, fun b hb b' hb' hne => pairwise_sym (fun _ _ h => h.symm) pw hb hb' (fun e => hne (by rw [e])),
    stk, nw, rd, wr, ret⟩

theorem fa2 {α : Type} {p : α → Prop} {a b : α} (ha : p a) (hb : p b) : ∀ x ∈ [a, b], p x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> assumption

theorem fa3 {α : Type} {p : α → Prop} {a b c : α} (ha : p a) (hb : p b) (hc : p c) : ∀ x ∈ [a, b, c], p x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

theorem fa4 {α : Type} {p : α → Prop} {a b c d : α} (ha : p a) (hb : p b) (hc : p c) (hd : p d) :
    ∀ x ∈ [a, b, c, d], p x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> assumption

theorem fa5 {α : Type} {p : α → Prop} {a b c d e : α} (ha : p a) (hb : p b) (hc : p c) (hd : p d) (he : p e) :
    ∀ x ∈ [a, b, c, d, e], p x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem pw4 {α : Type} {R : α → α → Prop} {a b c d : α} (hab : R a b) (hac : R a c) (had : R a d) (hbc : R b c)
    (hbd : R b d) (hcd : R c d) : [a, b, c, d].Pairwise R := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, false_implies, implies_true, and_true]
  exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩

theorem pw5 {α : Type} {R : α → α → Prop} {a b c d e : α} (hab : R a b) (hac : R a c) (had : R a d) (hae : R a e)
    (hbc : R b c) (hbd : R b d) (hbe : R b e) (hcd : R c d) (hce : R c e) (hde : R d e) :
    [a, b, c, d, e].Pairwise R := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, false_implies, implies_true, and_true]
  exact ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde⟩

/-! ## The state of a top-level function -/

/-- The register saved at `scratch + 840 + 8k`. -/
abbrev savedReg (k : Nat) : Reg := savedRegs.getD k .rbx

/-- What holds throughout a top-level function entered in `σ`, which keeps
the pointers of `m` (a register, and the register of entry it holds). -/
structure Top (m : List (Reg × Reg)) (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rsp : s.gpr .rsp = σ.gpr .rsp
  regs : ∀ p ∈ m, s.gpr p.1 = σ.gpr p.2
  saved : ∀ k < 6, s.mem.readW (pa s (sc (oSV + 8 * k))) 64 = σ.gpr (savedReg k)
  ret : s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64

/-- The saved registers and the return address are apart from the regions `ws`. -/
def topChk (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) : Bool :=
  (List.range 6).all (fun k => keepB bs ws (sc (oSV + 8 * k)) 8) && ws.all fun w => inB bs w.1 w.2

theorem Top.step {m : List (Reg × Reg)} {σ s s' : State} {rbs wbs : List (Reg × Nat)} (h : Top m σ s)
    (L : Lay rbs wbs s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hm : ∀ p ∈ m, p.1 ∈ bases)
    (hc : topChk (rbs ++ wbs) ws = true) : Top m σ s' := by
  simp only [topChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.rsp.trans h.rsp, fun p hp => (hP.bs _ (hm p hp)).trans (h.regs p hp),
    fun k hk => ?_, ?_⟩
  · rw [L.keepW hP (hc.1 k hk)]; exact h.saved k hk
  · have := L.keepRet hP hc.2
    rw [h.rsp] at this
    rw [this, h.ret]

/-! ## Saving the registers -/

theorem readW_writeW_slot (m : Mem) (a : Addr) {x y : Nat} (v : BitVec 64) (hxy : x + 8 ≤ y ∨ y + 8 ≤ x)
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (m.writeW (a + BitVec.ofNat 64 y) v).readW (a + BitVec.ofNat 64 x) 64 = m.readW (a + BitVec.ofNat 64 x) 64 := by
  refine Mem.readW_writeW_sep ?_ (by decide)
  rcases hxy with h | h
  · exact (off_disj (p := a) h (by omega)).sep (Region.contains_self _ _) (Region.contains_self _ _)
  · exact (off_disj (p := a) h (by omega)).symm.sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- The six stores of `topPro`: each slot holds its register. -/
theorem stores_read (m : Mem) (a : Addr) (v : Nat → BitVec 64) : ∀ k < 6,
    ((((((m.writeW (a + BitVec.ofNat 64 840) (v 0)).writeW (a + BitVec.ofNat 64 848) (v 1)).writeW
      (a + BitVec.ofNat 64 856) (v 2)).writeW (a + BitVec.ofNat 64 864) (v 3)).writeW (a + BitVec.ofNat 64 872)
      (v 4)).writeW (a + BitVec.ofNat 64 880) (v 5)).readW (a + BitVec.ofNat 64 (oSV + 8 * k)) 64 = v k := by
  intro k hk
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := omega) only [oSV, Nat.reduceMul, Nat.reduceAdd, readW_writeW_slot, Mem.readW_writeW_self64]

/-! ## The return -/

theorem topEpi_eq : topEpi = [.mov32 .rax (.reg .r15), .mov .r15 (.mem (at_ .rbx 880)), .mov .r14 (.mem (at_ .rbx 872)),
    .mov .r13 (.mem (at_ .rbx 864)), .mov .r12 (.mem (at_ .rbx 856)), .mov .rbp (.mem (at_ .rbx 848)),
    .mov .rbx (.mem (at_ .rbx 840))] := rfl

theorem topEpi_ok {m : List (Reg × Reg)} {σ s : State} (h : Top m σ s)
    (hin : ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8) :
    WP isa (.block topEpi) s fun s' => (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32 ∧
      gprPreserved σ s' ∧ s'.mem = s.mem := by
  have e : ∀ k < 6, s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (840 + 8 * k)) 64 = σ.gpr (savedReg k) :=
    fun k hk => h.saved k hk
  have i : ∀ k < 6, InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 (840 + 8 * k)) 8 := hin
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
  have e3 := e 3 (by decide); have e4 := e 4 (by decide); have e5 := e 5 (by decide)
  have i0 := i 0 (by decide); have i1 := i 1 (by decide); have i2 := i 2 (by decide)
  have i3 := i 3 (by decide); have i4 := i 4 (by decide); have i5 := i 5 (by decide)
  rw [show savedReg 0 = .rbx from rfl] at e0; rw [show savedReg 1 = .rbp from rfl] at e1
  rw [show savedReg 2 = .r12 from rfl] at e2; rw [show savedReg 3 = .r13 from rfl] at e3
  rw [show savedReg 4 = .r14 from rfl] at e4; rw [show savedReg 5 = .r15 from rfl] at e5
  simp only [Nat.reduceMul, Nat.reduceAdd] at e0 e1 e2 e3 e4 e5 i0 i1 i2 i3 i4 i5
  rw [topEpi_eq]
  refine WP.mono (WP.keep [.rax, .r15, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' =>
    s'.gpr .rax = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32) ∧ s'.gpr .r15 = σ.gpr .r15 ∧
    s'.gpr .r14 = σ.gpr .r14 ∧ s'.gpr .r13 = σ.gpr .r13 ∧ s'.gpr .r12 = σ.gpr .r12 ∧ s'.gpr .rbp = σ.gpr .rbp ∧
    s'.gpr .rbx = σ.gpr .rbx ∧ s'.mem = s.mem) (by xrun [i0, i1, i2, i3, i4, i5, e0, e1, e2, e3, e4, e5]) (by decide))
    fun s' ⟨⟨hax, h15, h14, h13, h12, hbp, hbx, hm⟩, k⟩ => ⟨?_, ⟨fun r hr => ?_, ?_⟩, hm⟩
  · rw [hax]; apply BitVec.eq_of_toNat_eq; simp
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hbx, hbp, by rw [k.gpr (by decide), h.rsp], h12, h13, h14, h15]
  · rw [hm]; exact h.ret

/-! ## The branch on the results of `SampleNTT` -/

/-- A block that writes only `r15`, with its old value, and flags. -/
theorem post_of_keep15 {s s' : State} (k : Keep [.r15] s s') (h15 : s'.gpr .r15 = s.gpr .r15)
    (hm : s'.mem = s.mem) (ws : List (Ptr × Nat)) : PPost s s' ws :=
  ⟨k.2.1, k.2.2, fun r _ => by
    by_cases e : r = .r15
    · rw [e, h15]
    · exact k.gpr (by simpa using e), by rw [hm]; exact Frame.refl _ _⟩

theorem test15_ok (s : State) :
    WP isa (.block [.alu32 .test .r15 (.reg .r15)]) s fun s₁ => PPost s s₁ [] ∧
      s₁.zf = some ((s.gpr .r15).setWidth 32 == 0) :=
  WP.mono (WP.keep [.r15] (Q := fun s₁ => s₁.mem = s.mem ∧ s₁.gpr .r15 = s.gpr .r15 ∧
      s₁.zf = some (((s.gpr .r15).setWidth 32 &&& (s.gpr .r15).setWidth 32) == 0)) (by xrun) (by decide))
    fun _ ⟨⟨hm, h15, hz⟩, k⟩ => ⟨post_of_keep15 k h15 hm [], by rw [hz, BitVec.and_self]⟩

theorem ifOk_ok {c : Prog isa} {s : State} {Q : State → Prop}
    (ht : ∀ s₁, PPost s s₁ [] → (s.gpr .r15).setWidth 32 ≠ 0 → WP isa c s₁ Q)
    (he : ∀ s₁, PPost s s₁ [] → (s.gpr .r15).setWidth 32 = 0 → Q s₁) : WP isa (ifOk c) s Q := by
  unfold ifOk
  refine WP.seq (WP.mono (test15_ok s) fun s₁ ⟨hP, hz⟩ => ?_)
  refine WP.ite (M := isa) (!((s.gpr .r15).setWidth 32 == 0))
    (show s₁.zf.map (!·) = _ by rw [hz]; rfl) (fun hb => ?_) fun hb => ?_
  · exact ht s₁ hP (by simpa using hb)
  · exact WP.block_nil (he s₁ hP (by simpa using hb))

theorem ifOk_tr {c : Prog isa} {P Q : State → State → Prop}
    (he : ∀ x y, P x y → (x.gpr .r15).setWidth 32 = (y.gpr .r15).setWidth 32)
    (ht : RelCT isa (fun x y => ∃ x₀ y₀, P x₀ y₀ ∧ PPost x₀ x [] ∧ PPost y₀ y [] ∧
      (x₀.gpr .r15).setWidth 32 ≠ 0) c Q)
    (hq : ∀ x y, (∃ x₀ y₀, P x₀ y₀ ∧ PPost x₀ x [] ∧ PPost y₀ y [] ∧ (x₀.gpr .r15).setWidth 32 = 0) → Q x y) :
    RelCT isa P (ifOk c) Q := by
  unfold ifOk
  refine RelCT.seq (RelCT.postDep (block_nomem_tr fun i hi s => by
      simp only [List.mem_singleton] at hi; subst hi; rfl)
    (F := fun x x₁ => PPost x x₁ [] ∧ x₁.zf = some ((x.gpr .r15).setWidth 32 == 0))
    (fun x y _ => ⟨test15_ok x, test15_ok y⟩) (Q := fun x₁ y₁ => ∃ x₀ y₀, P x₀ y₀ ∧
      (PPost x₀ x₁ [] ∧ x₁.zf = some ((x₀.gpr .r15).setWidth 32 == 0)) ∧
      (PPost y₀ y₁ [] ∧ y₁.zf = some ((y₀.gpr .r15).setWidth 32 == 0)))
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.ite ?_ ?_ ?_)
  · rintro x₁ y₁ ⟨x₀, y₀, hp, ⟨_, hx⟩, ⟨_, hy⟩⟩
    show x₁.zf.map (!·) = y₁.zf.map (!·)
    rw [hx, hy, he x₀ y₀ hp]
  · refine RelCT.mono ht (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, hx⟩, ⟨h2, _⟩⟩, hc⟩ => ⟨x₀, y₀, hp, h1, h2, ?_⟩) fun _ _ h => h
    have hc' : x₁.zf.map (!·) = some true := hc
    rw [hx] at hc'
    simpa using hc'
  · refine RelCT.mono nil_tr (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, hx⟩, ⟨h2, _⟩⟩, hc⟩ => ⟨x₀, y₀, hp, h1, h2, ?_⟩)
      fun x y h => hq x y h
    have hc' : x₁.zf.map (!·) = some false := hc
    rw [hx] at hc'
    simpa using hc'

/-! ## Sequences -/

theorem seqR_ok {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → ∀ s, I k s → WP isa (f k) s (I (k + 1))) →
      ∀ s, I a s → WP isa (seqR f a n) s (I (a + n))
  | 0, a, _, s, hs => WP.block_nil hs
  | n + 1, a, h, s, hs => by
    rw [seqR]
    refine WP.seq (WP.mono (h a (Nat.le_refl _) (by omega) s hs) fun s₁ h₁ => ?_)
    rw [show a + (n + 1) = a + 1 + n by omega]
    exact seqR_ok n (a + 1) (fun k hk hk' => h k (by omega) (by omega)) s₁ h₁

theorem seqR_tr {f : Nat → Prog isa} {R : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → RelCT isa (R k) (f k) (R (k + 1))) →
      RelCT isa (R a) (seqR f a n) (R (a + n))
  | 0, _, _ => nil_tr
  | n + 1, a, h => by
    rw [seqR, show a + (n + 1) = a + 1 + n by omega]
    exact RelCT.seq (h a (Nat.le_refl _) (by omega)) (seqR_tr n (a + 1) fun k hk hk' => h k (by omega) (by omega))

end VG.Proof.MlKem.X86_64
