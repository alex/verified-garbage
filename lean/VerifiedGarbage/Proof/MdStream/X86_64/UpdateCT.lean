import VerifiedGarbage.Proof.MdStream.X86_64.Update

/-!
# Streaming Merkle–Damgård hash functions on x86-64: `update` is constant time

Untrusted: everything here is checked by Lean.

This holds for any compression function (`CalleeOk`), so it is proven once
for every implementation. The taint analysis cannot prove it without
looking into the compression function, which saves and restores our
registers in memory it also writes secrets to. So we relate two runs
(`RelCT`), as for PBKDF2's iteration (`Proof/Pbkdf2/X86_64/IterateCT.lean`):
at the start of every iteration, both runs have absorbed the same number of
bytes, so correctness determines our registers from the public arguments
alone; between the calls, the taint analysis proves each piece constant time
from that (`Taints`, checked for each hash function's code), and shows that
the pieces agree on how many bytes they absorb; and the calls are constant
time by `compressAt_rel`.
-/

namespace VG.Proof.MdStream.X86_64.Update

open VG VG.X86_64 VG.Impl.MdStream.X86_64

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

theorem PubEq.len {s₀ s₀' : State} (hq : PubEq s₀ s₀') : len s₀ = len s₀' :=
  congrArg BitVec.toNat hq.rcx

theorem PubEq.src {P : Params} {s₀ s₀' : State} (hq : PubEq s₀ s₀') {c : Nat} :
    srcOf P s₀ c = srcOf P s₀' c := by
  have e : rr P s₀ c = rr P s₀' c := congrArg (fun x : BitVec 64 => (x.toNat + c) % P.B) hq.rsi
  simp only [srcOf, e, hq.len]
  rw [show dp s₀ = dp s₀' from hq.rdx, show st s₀ = st s₀' from hq.rdi]

/-- The registers the pieces between the calls use. -/
abbrev regs : List Reg := [.rbx, .r15, .rsp, .rbp, .r12, .r13]

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem Inv.agree {s₀ s₀' : State} (hq : PubEq s₀ s₀') {c : Nat} {s s' : State} (h : Inv H s₀ c s)
    (h' : Inv H s₀' c s') : ∀ r ∈ regs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [regs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx]; exact hq.rdi
  · rw [h.r15, h'.r15]; exact hq.r8
  · rw [h.rsp, h'.rsp]; exact hq.rsp
  · rw [h.rbp, h'.rbp]; exact congrArg (· + _) hq.rdx
  · rw [h.r12, h'.r12, hq.len]
  · rw [h.r13, h'.r13]; exact congrArg (fun x : BitVec 64 => BitVec.ofNat 64 ((x.toNat + c) % P.B)) hq.rsi

end

theorem test_rel {P : State → State → Prop} :
    RelCT isa P (.block [.alu .test .r14 (.reg .r14)]) fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧
      (s₁.gpr = σ₁.gpr ∧ s₁.mem = σ₁.mem ∧ s₁.rd = σ₁.rd ∧ s₁.wr = σ₁.wr ∧
        s₁.zf = some (σ₁.gpr .r14 &&& σ₁.gpr .r14 == 0)) ∧
      (s₂.gpr = σ₂.gpr ∧ s₂.mem = σ₂.mem ∧ s₂.rd = σ₂.rd ∧ s₂.wr = σ₂.wr ∧
        s₂.zf = some (σ₂.gpr .r14 &&& σ₂.gpr .r14 == 0)) :=
  (RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.alu .test .r14 (.reg .r14)]) (by taint_decide)).wpDep
    fun _ _ _ => ⟨test_ok .r14, test_ok .r14⟩

/-- `k` blocks, as a nonzero `r14`. -/
abbrev nz (k : Nat) : Prop := BitVec.ofNat 64 k ≠ 0
theorem zero_and : ((0 : BitVec 64) &&& 0 == 0) = true := by decide

section
variable {P : Params} {H : Md P.B P.N P.L} (hd : Dims P) (ht : Taints P) {name : String} {code : Prog isa}
  (hf : CalleeOk H code) {s₀ s₀' : State} (hp : Pre P s₀) (hp' : Pre P s₀') (hq : PubEq s₀ s₀')

/-- After the first half of an iteration: the same block is ready in both
runs, or all the data is buffered in both. -/
def Mid (H : Md P.B P.N P.L) (s₀ s₀' : State) (c : Nat) (s₁ s₂ : State) : Prop :=
  (∃ c' k, c < c' ∧ Pending H s₀ c' k s₁ ∧ Pending H s₀' c' k s₂ ∧ s₁.gpr .rsi = s₂.gpr .rsi) ∨
    (Done H s₀ s₁ ∧ Done H s₀' s₂)

include hd ht hp hp' hq in
theorem head_rel {c : Nat} :
    RelCT isa (fun s₁ s₂ => Inv H s₀ c s₁ ∧ Inv H s₀' c s₂) (updateHead P) (Mid H s₀ s₀' c) := by
  obtain ⟨_, htc⟩ := ht.updHead
  have t := (RelCT.taintRegs (τ := Taint.ofRegs regs) (P := fun s₁ s₂ => Inv H s₀ c s₁ ∧ Inv H s₀' c s₂)
    (fun _ _ h => Taint.agree_ofRegs (Inv.agree hq h.1 h.2)) [.r12, .r14] (c := updateHead P)
    htc).wp fun _ _ h => ⟨head_ok hd hp h.1, head_ok hd hp' h.2⟩
  refine t.mono (fun _ _ h => h) fun s₁ s₂ ⟨ag, h₁, h₂⟩ => ?_
  have e12 := ag .r12 (by simp)
  have e14 := ag .r14 (by simp)
  rcases h₁ with ⟨c₁, k₁, hc₁, P₁, si₁⟩ | D₁ <;> rcases h₂ with ⟨c₂, k₂, hc₂, P₂, si₂⟩ | D₂
  · have e := congrArg BitVec.toNat (P₁.r12.symm.trans (e12.trans P₂.r12))
    have l₁ := P₁.c_le; have l₂ := P₂.c_le; have hl := len_lt s₀; have hl' := hq.len
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at e
    obtain rfl : c₁ = c₂ := by omega
    have ek := congrArg BitVec.toNat (P₁.r14.symm.trans (e14.trans P₂.r14))
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (P₁.k_lt hd).2,
      Nat.mod_eq_of_lt (P₂.k_lt hd).2] at ek
    subst ek
    exact .inl ⟨c₁, k₁, hc₁, P₁, P₂, by rw [si₁, si₂]; exact hq.src⟩
  · have e := congrArg BitVec.toNat (P₁.r14.symm.trans (e14.trans D₂.2))
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (P₁.k_lt hd).2] at e
    exact absurd e (by have := P₁.k_pos; simp; omega)
  · have e := congrArg BitVec.toNat (D₁.2.symm.trans (e14.trans P₂.r14))
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (P₂.k_lt hd).2] at e
    exact absurd e (by have := P₂.k_pos; simp; omega)
  · exact .inr ⟨D₁, D₂⟩

include hd hf hp hp' hq in
/-- The second half, when blocks are ready. -/
theorem tail_pending {c' k : Nat} :
    RelCT isa (fun s₁ s₂ => Pending H s₀ c' k s₁ ∧ Pending H s₀' c' k s₂ ∧ s₁.gpr .rsi = s₂.gpr .rsi)
      (updateTail name code) fun s₁ s₂ =>
        eval .ne s₁ = some true ∧ eval .ne s₂ = some true ∧ Inv H s₀ c' s₁ ∧ Inv H s₀' c' s₂ := by
  unfold updateTail
  refine (test_rel.mono (fun _ _ h => h) fun s₁ s₂ ⟨_, σ₁, σ₂, ⟨P₁, P₂, esi⟩,
    ⟨g₁, m₁, rd₁, wr₁, z₁⟩, ⟨g₂, m₂, rd₂, wr₂, z₂⟩⟩ =>
      (⟨P₁.congr g₁ m₁ rd₁ wr₁, P₂.congr g₂ m₂ rd₂ wr₂, by rw [g₁, g₂]; exact esi,
        by rw [z₁, P₁.r14, ofNat_and_ne P₁.k_pos (P₁.k_lt hd).2],
        by rw [z₂, P₂.r14, ofNat_and_ne P₂.k_pos (P₂.k_lt hd).2]⟩ :
        Pending H s₀ c' k s₁ ∧ Pending H s₀' c' k s₂ ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
          s₁.zf = some false ∧ s₂.zf = some false)).seq ?_
  have cmp : RelCT isa (fun s₁ s₂ => (Pending H s₀ c' k s₁ ∧ Pending H s₀' c' k s₂ ∧
        s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.zf = some false ∧ s₂.zf = some false) ∧
        eval .ne s₁ = some true) (compressN name code)
      fun s₁ s₂ => (Inv H s₀ c' s₁ ∧ s₁.gpr .r14 = BitVec.ofNat 64 k ∧ nz k) ∧
        (Inv H s₀' c' s₂ ∧ s₂.gpr .r14 = BitVec.ofNat 64 k ∧ nz k) :=
    ((compressWith_rel H setsN_r14 ⟨_, by taint_decide⟩ hf fun s₁ s₂ ⟨⟨P₁, P₂, esi, _⟩, _⟩ =>
      ⟨⟨_, _, _, k, by rw [P₁.r14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (P₁.k_lt hd).2], P₁.callOk hd hp⟩,
        ⟨_, _, _, k, by rw [P₂.r14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (P₂.k_lt hd).2], P₂.callOk hd hp'⟩,
        by rw [P₁.rbx, P₂.rbx]; exact hq.rdi, by rw [P₁.r15, P₂.r15]; exact hq.r8, esi,
        by rw [P₁.rsp, P₂.rsp]; exact hq.rsp, by rw [P₁.r14, P₂.r14]⟩).wp
      fun _ _ h => ⟨WP.mono (h.1.1.compress_ok hd hf hp) fun _ r =>
          ⟨r.1, r.2, h.1.1.ne_zero hd⟩,
        WP.mono (h.1.2.1.compress_ok hd hf hp') fun _ r =>
          ⟨r.1, r.2, h.1.2.1.ne_zero hd⟩⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have fin : RelCT isa (fun s₁ s₂ => (Inv H s₀ c' s₁ ∧ s₁.gpr .r14 = BitVec.ofNat 64 k ∧ nz k) ∧
        (Inv H s₀' c' s₂ ∧ s₂.gpr .r14 = BitVec.ofNat 64 k ∧ nz k))
      (.block [.alu .test .r14 (.reg .r14)]) fun s₁ s₂ =>
        eval .ne s₁ = some true ∧ eval .ne s₂ = some true ∧ Inv H s₀ c' s₁ ∧ Inv H s₀' c' s₂ :=
    test_rel.mono (fun _ _ h => h) fun s₁ s₂ ⟨_, σ₁, σ₂, ⟨⟨I₁, r₁, n₁⟩, ⟨I₂, r₂, n₂⟩⟩,
      ⟨g₁, m₁, rd₁, wr₁, z₁⟩, ⟨g₂, m₂, rd₂, wr₂, z₂⟩⟩ =>
      ⟨by simp [eval, z₁, r₁]; exact n₁, by simp [eval, z₂, r₂]; exact n₂, I₁.congr g₁ m₁ rd₁ wr₁, I₂.congr g₂ m₂ rd₂ wr₂⟩
  refine (RelCT.ite (fun s₁ s₂ h => ?_) cmp (RelCT.of_false fun s₁ s₂ h => ?_)).seq fin
  · simp [eval, h.2.2.2.1, h.2.2.2.2]
  · have := h.2; simp [eval, h.1.2.2.2.1] at this

/-- The second half, when all the data is buffered. -/
theorem tail_done :
    RelCT isa (fun s₁ s₂ => Done H s₀ s₁ ∧ Done H s₀' s₂) (updateTail name code) fun s₁ s₂ =>
      eval .ne s₁ = some false ∧ eval .ne s₂ = some false ∧ Done H s₀ s₁ ∧ Done H s₀' s₂ := by
  unfold updateTail
  refine (test_rel.mono (fun _ _ h => h) fun s₁ s₂ ⟨_, σ₁, σ₂, ⟨D₁, D₂⟩,
    ⟨g₁, m₁, rd₁, wr₁, z₁⟩, ⟨g₂, m₂, rd₂, wr₂, z₂⟩⟩ =>
      (⟨⟨D₁.1.congr g₁ m₁ rd₁ wr₁, by rw [g₁]; exact D₁.2⟩, ⟨D₂.1.congr g₂ m₂ rd₂ wr₂, by rw [g₂]; exact D₂.2⟩,
        by rw [z₁, D₁.2, zero_and], by rw [z₂, D₂.2, zero_and]⟩ :
        Done H s₀ s₁ ∧ Done H s₀' s₂ ∧ s₁.zf = some true ∧ s₂.zf = some true)).seq ?_
  have skip : RelCT isa (fun s₁ s₂ => (Done H s₀ s₁ ∧ Done H s₀' s₂ ∧ s₁.zf = some true ∧
        s₂.zf = some true) ∧ eval .ne s₁ = some false) (.block [])
      fun s₁ s₂ => Done H s₀ s₁ ∧ Done H s₀' s₂ :=
    ((RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
      (c := .block []) (by taint_decide)).wp fun _ _ h => ⟨WP.block_nil h.1.1, WP.block_nil h.1.2.1⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have fin : RelCT isa (fun s₁ s₂ => Done H s₀ s₁ ∧ Done H s₀' s₂)
      (.block [.alu .test .r14 (.reg .r14)]) fun s₁ s₂ =>
        eval .ne s₁ = some false ∧ eval .ne s₂ = some false ∧ Done H s₀ s₁ ∧ Done H s₀' s₂ :=
    test_rel.mono (fun _ _ h => h) fun s₁ s₂ ⟨_, σ₁, σ₂, ⟨D₁, D₂⟩,
      ⟨g₁, m₁, rd₁, wr₁, z₁⟩, ⟨g₂, m₂, rd₂, wr₂, z₂⟩⟩ =>
      ⟨by simp [eval, z₁, D₁.2], by simp [eval, z₂, D₂.2],
        ⟨D₁.1.congr g₁ m₁ rd₁ wr₁, by rw [g₁]; exact D₁.2⟩, ⟨D₂.1.congr g₂ m₂ rd₂ wr₂, by rw [g₂]; exact D₂.2⟩⟩
  refine (RelCT.ite (fun s₁ s₂ h => ?_) (RelCT.of_false fun s₁ s₂ h => ?_) skip).seq fin
  · simp [eval, h.2.2.1, h.2.2.2]
  · have := h.2; simp [eval, h.1.2.2.1] at this

/-- The loop invariant of two runs: both absorbed the first `len - n` bytes. -/
def LoopInv (H : Md P.B P.N P.L) (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ c, n = len s₀ - c ∧ Inv H s₀ c s₁ ∧ Inv H s₀' c s₂

include hd ht hf hp hp' hq in
theorem body_rel (n : Nat) :
    RelCT isa (LoopInv H s₀ s₀' n) (updateBody P name code) fun s₁ s₂ => eval .ne s₁ = eval .ne s₂ ∧
      (eval .ne s₁ = some false → Inv H s₀ (len s₀) s₁ ∧ Inv H s₀' (len s₀) s₂) ∧
      (eval .ne s₁ = some true → ∃ m < n, LoopInv H s₀ s₀' m s₁ s₂) := by
  refine RelCT.exists_ fun c => fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨hn, h⟩ e₁ e₂ => ?_
  have tl : RelCT isa (Mid H s₀ s₀' c) (updateTail name code) fun s₁ s₂ =>
      (eval .ne s₁ = some true ∧ eval .ne s₂ = some true ∧ ∃ c', c < c' ∧ Inv H s₀ c' s₁ ∧ Inv H s₀' c' s₂) ∨
      (eval .ne s₁ = some false ∧ eval .ne s₂ = some false ∧ Done H s₀ s₁ ∧ Done H s₀' s₂) :=
    RelCT.or (RelCT.exists_ fun c' => RelCT.exists_ fun _ => fun _ _ _ _ _ _ ⟨hc, h⟩ e₁ e₂ =>
        let ⟨ht, z₁, z₂, I₁, I₂⟩ := tail_pending hd hf hp hp' hq _ _ _ _ _ _ h e₁ e₂
        ⟨ht, .inl ⟨z₁, z₂, c', hc, I₁, I₂⟩⟩)
      ((tail_done (name := name) (code := code) (s₀ := s₀) (s₀' := s₀')).mono (fun _ _ h => h)
        fun _ _ h => .inr h)
  have main : RelCT isa (fun s₁ s₂ => Inv H s₀ c s₁ ∧ Inv H s₀' c s₂) (updateBody P name code) fun s₁ s₂ =>
      eval .ne s₁ = eval .ne s₂ ∧
      (eval .ne s₁ = some false → Inv H s₀ (len s₀) s₁ ∧ Inv H s₀' (len s₀) s₂) ∧
      (eval .ne s₁ = some true → ∃ m < n, LoopInv H s₀ s₀' m s₁ s₂) :=
    ((head_rel hd ht hp hp' hq).seq tl).mono (fun _ _ h => h) fun s₁ s₂ h => by
      rcases h with ⟨z₁, z₂, c', hc, I₁, I₂⟩ | ⟨z₁, z₂, D₁, D₂⟩
      · have := I₁.c_le
        exact ⟨z₁.trans z₂.symm, ⟨fun h => absurd (z₁.symm.trans h) (by simp),
          fun _ => ⟨len s₀ - c', by omega, c', rfl, I₁, I₂⟩⟩⟩
      · exact ⟨z₁.trans z₂.symm, ⟨fun _ => ⟨D₁.1, by rw [hq.len]; exact D₂.1⟩,
          fun h => absurd (z₁.symm.trans h) (by simp)⟩⟩
  exact main _ _ _ _ _ _ h e₁ e₂

end

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem agree₀ (hd : Dims P) {s₁ s₂ : State} (h₁ : (updK H).pre s₁) (h₂ : (updK H).pre s₂) (hpub : (updK H).pub s₁ s₂) :
    X86_64.Taint.Agree (τ₀ P) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
  have wf : ∀ s, (updK H).pre s → X86_64.Taint.Wf (τ₀ P) s := by
    intro s hs
    obtain ⟨-, hw, hdj, -⟩ := hs
    have := hd.N; have := hd.B; have := hd.so
    refine ⟨fun _ => ⟨by simp [hw, τ₀], by simp [hw, hdj], by simp [hw]; omega⟩, fun p hp => ?_⟩
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p5]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

theorem pubEq_of {s₁ s₂ : State} (h : (updK H).pub s₁ s₂) : PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem constantTime (hd : Dims P) (ht : Taints P) {name : String} {code : Prog isa} (hf : CalleeOk H code) :
    ConstantTime isa (updK H).pre (updK H).pub (update P name code) := by
  intro s₀ s₀' t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  have hp := pre_of h₁; have hp' := pre_of h₂; have hq := pubEq_of hpub
  obtain ⟨_, hs⟩ := ht.updStart
  obtain ⟨_, he⟩ := ht.updEnd
  have pro : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block (updateStart P))
      fun s₁ s₂ => Inv H s₀ 0 s₁ ∧ Inv H s₀' 0 s₂ :=
    ((RelCT.taint (A := taint) (τ₀ P) (fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact agree₀ hd h₁ h₂ hpub)
      hs).wp fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hd hp, prologue_ok hd hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have lp := RelCT.loop (M := isa) (body := updateBody P name code) (c := .ne)
    (Q := fun s₁ s₂ => Inv H s₀ (len s₀) s₁ ∧ Inv H s₀' (len s₀) s₂) (LoopInv H s₀ s₀')
    (body_rel hd ht hf hp hp' hq) (len s₀)
  have epi : RelCT isa (fun s₁ s₂ => Inv H s₀ (len s₀) s₁ ∧ Inv H s₀' (len s₀) s₂) (.block (restore P))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r15]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.r15, h.2.r15]; exact hq.r8) he
  have lp' : RelCT isa (fun s₁ s₂ => Inv H s₀ 0 s₁ ∧ Inv H s₀' 0 s₂) (.loop (updateBody P name code) .ne)
      fun s₁ s₂ => Inv H s₀ (len s₀) s₁ ∧ Inv H s₀' (len s₀) s₂ :=
    lp.mono (fun _ _ h => ⟨0, by omega, h⟩) fun _ _ h => h
  exact (pro.seq (lp'.seq epi) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A state satisfying the precondition (with no data). -/
def sat (P : Params) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, P.N + P.B⟩, ⟨0x3000, P.so + 48⟩]

/-- `update` is verified if it never loads MXCSR. -/
theorem verified (hd : Dims P) (ht : Taints P) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hm : (update P name code).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (update P name code) (updK H) := by
  have := hd.N; have := hd.B; have := hd.so
  refine ⟨fun s hs => ?_, constantTime hd ht hf, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct hd hf (pre_of hs)
    exact ⟨t, s', he, abiPreserved_of_exec hm he h.1, h.2⟩
  · refine ⟨sat P, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [sat]
    · exact Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact Offset.disjoint_of_le (by simp) (by simp <;> omega)
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm

end

end VG.Proof.MdStream.X86_64.Update
